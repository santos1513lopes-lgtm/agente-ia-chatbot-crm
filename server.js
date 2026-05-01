/**
 * AGENTE DE IA + CHATBOT WHATSAPP
 * Backend com Express, WhatsApp Web.js, Groq AI e Socket.IO
 * QR Code aparece no navegador - sem terminal!
 */

const express = require("express");
const http = require("http");
const { Server } = require("socket.io");
const path = require("path");
const fs = require("fs");
const QRCode = require("qrcode");
const { Client, LocalAuth, MessageMedia } = require("whatsapp-web.js");
const OpenAI = require("openai");
const { createSilencio } = require("./silencio_whatsapp");
const silencio = createSilencio(__dirname);

// =====================================
// CONFIGURAÇÃO
// =====================================
const PORT = 3000;
const CONFIG_FILE = path.join(__dirname, "config.json");
const INBOX_FILE = path.join(__dirname, "inbox.json");
const SKIP_WHATSAPP = process.env.SKIP_WHATSAPP === "1";

let groqClient = null;
let whatsappClient = null;
let whatsappConectado = false;
let whatsappAutoReconnect = true;
let whatsappInicializadoEm = 0;
let reinicioWhatsAppEmAndamento = false;
let io = null;
const estadosConversa = new Map();
const WHATSAPP_WATCHDOG_INTERVAL_MS = 2 * 60 * 1000;
const WHATSAPP_STARTUP_TIMEOUT_MS = 5 * 60 * 1000;
const INBOX_MAX_CONVERSAS = 300;
const INBOX_MAX_MENSAGENS_POR_CHAT = 120;

function normalizeText(value) {
  return String(value || "")
    .normalize("NFD")
    .replace(/[\u0300-\u036f]/g, "")
    .trim()
    .toLowerCase();
}

function tokenMatch(registeredValue, queryValue) {
  const registeredTokens = normalizeText(registeredValue).split(/\s+/).filter(Boolean);
  const queryTokens = normalizeText(queryValue).split(/\s+/).filter(Boolean);
  if (!registeredTokens.length || !queryTokens.length) return false;
  const registeredInQuery = registeredTokens.every((token) => queryTokens.includes(token));
  const queryInRegistered = queryTokens.every((token) => registeredTokens.includes(token));
  return registeredInQuery || queryInRegistered;
}

function parseCsvLine(line) {
  const values = [];
  let current = "";
  let inQuotes = false;
  for (let i = 0; i < line.length; i++) {
    const char = line[i];
    const next = line[i + 1];
    if (char === '"' && inQuotes && next === '"') {
      current += '"';
      i++;
    } else if (char === '"') {
      inQuotes = !inQuotes;
    } else if (char === "," && !inQuotes) {
      values.push(current.trim());
      current = "";
    } else {
      current += char;
    }
  }
  values.push(current.trim());
  return values;
}

function parseCsv(text) {
  const lines = String(text || "").split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
  if (lines.length < 2) return [];
  const headers = parseCsvLine(lines[0]).map((header) => normalizeText(header));
  return lines.slice(1).map((line) => {
    const values = parseCsvLine(line);
    const row = {};
    headers.forEach((header, index) => {
      row[header] = values[index] || "";
    });
    return row;
  });
}

function formatTemplate(template, row) {
  return String(template || "").replace(/\{([^}]+)\}/g, (_, key) => {
    if (!String(key || "").trim()) return "";
    const normalizedKey = normalizeText(key);
    return row[normalizedKey] || row[key] || "";
  });
}

function looksLikeFileName(value) {
  return /\.(pdf|jpg|jpeg|png|webp|gif|mp3|ogg|wav|mp4|doc|docx|xls|xlsx|txt|zip|jwpub)$/i.test(String(value || "").trim());
}

function resolveConditionalFile(row) {
  const candidates = [
    row.arquivo,
    row.anexo,
    row.caminho,
    row.pix,
    row.link,
    row.material,
  ].filter(Boolean);

  for (const candidate of candidates) {
    if (!looksLikeFileName(candidate)) continue;
    const fullPath = resolveKnownUploadFile(candidate);
    if (fullPath) return { fullPath, fileRef: candidate };
  }

  const direct = row.arquivo || row.anexo || row.caminho;
  const fullPath = resolveKnownUploadFile(direct);
  return fullPath ? { fullPath, fileRef: direct } : { fullPath: null, fileRef: direct };
}

function parseConditionalRows(text) {
  const raw = String(text || "").trim();
  if (!raw) return [];

  const lines = raw.split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
  const firstLine = lines[0] || "";
  const possibleHeaders = parseCsvLine(firstLine).map((header) => normalizeText(header));
  const knownHeaders = ["nome", "nome completo", "aluno", "matricula", "matrícula", "telefone", "material", "link", "senha", "pix", "arquivo", "anexo"];
  const hasHeader = possibleHeaders.some((header) => knownHeaders.includes(header));

  if (hasHeader) return parseCsv(raw);

  if (lines.some((line) => parseCsvLine(line).length > 1)) {
    return lines.map((line) => {
      const values = parseCsvLine(line);
      const name = (values[0] || "").trim();
      const file = (values[1] || "").trim();
      const link = (values[2] || "").trim();
      const senha = (values[3] || "").trim();
      return {
        nome: name,
        aluno: name,
        arquivo: file,
        anexo: file,
        link,
        senha,
      };
    }).filter((row) => row.nome);
  }

  return raw
    .split(/,|\r?\n/)
    .map((name) => name.trim())
    .filter(Boolean)
    .map((name) => ({ nome: name, aluno: name }));
}

function defaultConditionalFlows() {
  return [
    {
      id: "material-aluno",
      ativo: true,
      gatilhos: ["pegar material", "pega meu material", "meu material", "material", "apostila"],
      pergunta: "Por favor, digite seu *nome e sobrenome* ou matrícula.",
      camposBusca: ["nome", "nome completo", "aluno", "matricula", "matrícula", "telefone"],
      respostaEncontrado: "Encontrei seu cadastro, {nome}. Segue seu material:\n{material}\n{link}\n{senha}",
      respostaNaoEncontrado: "Não encontrei seu cadastro. Confira se digitou nome e sobrenome corretamente ou aguarde um instrutor.",
      dadosCsv: "nome,matricula,material,link,senha\nJoão Nascimento,12345,Material do curso,https://exemplo.com/material,Senha: 1234",
    },
  ];
}

function defaultHandoffConfig() {
  return {
    ativo: true,
    numeroAtendente: "557185279135",
    gatilhos: ["atendente", "suporte", "humano", "falar com atendente", "falar com humano", "professor", "problema"],
    respostaCliente: "Certo, vou encaminhar você para um atendente. Aguarde um instante.",
    mensagemAtendente: "Novo atendimento solicitado.\n\nContato: {telefone}\nMensagem: {mensagem}",
  };
}

function getConditionalFlows() {
  const flows = Array.isArray(config.conditionalFlows) && config.conditionalFlows.length
    ? config.conditionalFlows
    : defaultConditionalFlows();
  return flows.filter((flow) => flow && flow.ativo !== false);
}

function findConditionalFlow(texto) {
  const normalized = normalizeText(texto);
  return getConditionalFlows().find((flow) => {
    return (flow.gatilhos || []).some((gatilho) => normalized.includes(normalizeText(gatilho)));
  }) || null;
}

function getHandoffConfig() {
  return { ...defaultHandoffConfig(), ...(config.handoff || {}) };
}

function shouldHandoff(texto) {
  const handoff = getHandoffConfig();
  if (handoff.ativo === false) return false;
  const normalized = normalizeText(texto);
  return (handoff.gatilhos || []).some((gatilho) => normalized.includes(normalizeText(gatilho)));
}

function renderHandoffMessage(template, data) {
  return String(template || "").replace(/\{([^}]+)\}/g, (_, key) => {
    return data[normalizeText(key)] || data[key] || "";
  });
}

function loadInbox() {
  try {
    if (fs.existsSync(INBOX_FILE)) {
      const data = JSON.parse(fs.readFileSync(INBOX_FILE, "utf8"));
      return data && typeof data === "object" ? data : { conversas: [] };
    }
  } catch (e) {
    console.error("Erro ao carregar inbox:", e);
  }
  return { conversas: [] };
}

function saveInbox(inbox) {
  try {
    const conversas = Array.isArray(inbox.conversas) ? inbox.conversas : [];
    const ordenadas = conversas
      .sort((a, b) => new Date(b.atualizadoEm || 0) - new Date(a.atualizadoEm || 0))
      .slice(0, INBOX_MAX_CONVERSAS)
      .map((conversa) => ({
        ...conversa,
        mensagens: (conversa.mensagens || []).slice(-INBOX_MAX_MENSAGENS_POR_CHAT),
      }));
    fs.writeFileSync(INBOX_FILE, JSON.stringify({ conversas: ordenadas }, null, 2));
  } catch (e) {
    console.error("Erro ao salvar inbox:", e);
  }
}

function getInboxSummary(inbox = loadInbox()) {
  return (inbox.conversas || [])
    .map(({ mensagens, ...conversa }) => ({
      ...conversa,
      ultimaMensagem: mensagens?.[mensagens.length - 1] || null,
      mensagensCount: mensagens?.length || 0,
    }))
    .sort((a, b) => new Date(b.atualizadoEm || 0) - new Date(a.atualizadoEm || 0));
}

function getInboxConversa(chatId, inbox = loadInbox()) {
  return (inbox.conversas || []).find((conversa) => conversa.chatId === chatId) || null;
}

function registrarInbox({ chatId, telefone, nome, direcao, texto, origem, tipo = "text", messageId = null }) {
  if (!chatId) return null;
  const inbox = loadInbox();
  const agora = new Date().toISOString();
  let conversa = getInboxConversa(chatId, inbox);
  if (!conversa) {
    conversa = {
      chatId,
      telefone: telefone || String(chatId).replace(/\D/g, ""),
      nome: nome || telefone || String(chatId).replace("@c.us", ""),
      status: "novo",
      responsavel: "",
      botSilenciado: false,
      criadoEm: agora,
      atualizadoEm: agora,
      mensagens: [],
    };
    inbox.conversas.push(conversa);
  }

  if (nome && (!conversa.nome || conversa.nome === conversa.telefone)) conversa.nome = nome;
  if (telefone) conversa.telefone = telefone;
  conversa.atualizadoEm = agora;
  if (direcao === "in" && conversa.status === "resolvido") conversa.status = "novo";

  conversa.mensagens.push({
    id: messageId || `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
    direcao,
    origem,
    tipo,
    texto: texto || "",
    criadoEm: agora,
  });
  conversa.mensagens = conversa.mensagens.slice(-INBOX_MAX_MENSAGENS_POR_CHAT);
  saveInbox(inbox);
  if (io) {
    io.emit("inbox:summary", getInboxSummary(inbox));
    io.emit("inbox:conversation", conversa);
  }
  return conversa;
}

function atualizarInboxConversa(chatId, updates = {}) {
  const inbox = loadInbox();
  const conversa = getInboxConversa(chatId, inbox);
  if (!conversa) return null;
  Object.assign(conversa, updates, { atualizadoEm: new Date().toISOString() });
  saveInbox(inbox);
  if (io) {
    io.emit("inbox:summary", getInboxSummary(inbox));
    io.emit("inbox:conversation", conversa);
  }
  return conversa;
}

function registrarSaidaInbox(chatId, texto, origem = "bot", message = null) {
  return registrarInbox({
    chatId,
    telefone: String(chatId || "").replace(/\D/g, ""),
    direcao: "out",
    texto,
    origem,
    messageId: message?.id?._serialized || null,
  });
}

function normalizarInboxChatId(value) {
  const chatId = String(value || "").trim();
  if (!chatId) return "";
  if (/@(c|g)\.us$/.test(chatId) || chatId.endsWith("@lid")) return chatId;
  const numero = chatId.replace(/\D/g, "");
  return numero ? `${numero}@c.us` : "";
}

function rowMatchesConditionalQuery(row, camposBusca, query) {
  return camposBusca.some((campo) => {
    const value = normalizeText(row[campo]);
    return value && (
      value === query ||
      value.includes(query) ||
      query.includes(value) ||
      tokenMatch(value, query)
    );
  });
}

function searchConditionalRecords(flow, texto) {
  const query = normalizeText(texto);
  if (!query) return [];
  const rows = parseConditionalRows(flow.dadosCsv || "");
  const camposBusca = (flow.camposBusca || []).map(normalizeText);
  return rows.filter((row) => rowMatchesConditionalQuery(row, camposBusca, query));
}

function searchConditionalRecord(flow, texto) {
  return searchConditionalRecords(flow, texto)[0] || null;
}

function findConditionalRecordsByText(texto) {
  for (const flow of getConditionalFlows()) {
    const rows = searchConditionalRecords(flow, texto);
    if (rows.length) return { flow, rows };
  }
  return null;
}

function findConditionalRecordByText(texto) {
  const result = findConditionalRecordsByText(texto);
  return result ? { flow: result.flow, row: result.rows[0] } : null;
}

async function sendConditionalRecordsResponse({ msg, chatId, flow, rows, typing }) {
  const validRows = Array.isArray(rows) ? rows.filter(Boolean) : [];
  if (!validRows.length) return;
  const finalRow = validRows.find((row) => row.mensagemfinal || row.mensagem_final) || validRows[0];
  const mensagemFinal = formatTemplate(finalRow.mensagemfinal || finalRow.mensagem_final || "", finalRow)
    .replace(/\n{3,}/g, "\n\n")
    .trim();

  await typing();
  for (let index = 0; index < validRows.length; index++) {
    const row = validRows[index];
    const resposta = formatTemplate(flow.respostaEncontrado, row)
      .replace(/\n{3,}/g, "\n\n")
      .trim();
    const arquivoResolvido = resolveConditionalFile(row);
    let r = null;
    if (arquivoResolvido.fullPath) {
      const media = MessageMedia.fromFilePath(arquivoResolvido.fullPath);
      r = await whatsappClient.sendMessage(chatId, media, resposta ? { caption: resposta } : undefined);
    } else {
      r = await msg.reply(resposta || "Encontrei seu cadastro.");
    }
    silencio.registrarMensagemDoBot(r);
    registrarSaidaInbox(chatId, resposta || "Encontrei seu cadastro.", "bot", r);
    if (index < validRows.length - 1) await delay(1000);
  }

  if (mensagemFinal) {
    await delay(1000);
    const finalMsg = await whatsappClient.sendMessage(chatId, mensagemFinal);
    silencio.registrarMensagemDoBot(finalMsg);
    registrarSaidaInbox(chatId, mensagemFinal, "bot", finalMsg);
  }
}

async function sendConditionalRecordResponse({ msg, chatId, flow, row, typing }) {
  return sendConditionalRecordsResponse({ msg, chatId, flow, rows: [row], typing });
}

// Carregar ou criar config
function loadConfig() {
  try {
    if (fs.existsSync(CONFIG_FILE)) {
      return JSON.parse(fs.readFileSync(CONFIG_FILE, "utf8"));
    }
  } catch (e) {
    console.error("Erro ao carregar config:", e);
  }
  const defaultConfig = {
    groqApiKey: "",
    useAI: true,
    model: "llama-3.1-8b-instant",
    promptSistema: "Você é o assistente virtual da empresa. Seja simpático, profissional e objetivo. Responda dúvidas sobre horário, preços e serviços. Se não souber algo, peça para a pessoa aguardar que um atendente responderá.",
    fallbackResposta: "Desculpe, não entendi. Digite 'menu' para ver as opções.",
    conditionalFlows: defaultConditionalFlows(),
    handoff: defaultHandoffConfig(),
    flows: [
      {
        id: "1",
        palavras: ["oi", "olá", "ola", "bom dia", "boa tarde", "boa noite", "menu"],
        resposta: "Olá! 👋 Sou o assistente virtual.\n\nComo posso ajudar?\n\n1 - Saber mais sobre nós\n2 - Falar com atendente\n3 - Horário de funcionamento\n\nDigite o número ou faça sua pergunta!",
      },
      {
        id: "2",
        palavras: ["1", "saber mais", "como funciona"],
        resposta: "Atendimento disponível! Envie sua dúvida que eu te ajudo ou repasso para um atendente.",
      },
      {
        id: "3",
        palavras: ["2", "atendente", "humano"],
        resposta: "Um atendente humano entrará em contato em breve. Por favor, aguarde.",
      },
      {
        id: "4",
        palavras: ["3", "horário", "horario", "funcionamento"],
        resposta: "Consulte nosso horário de atendimento. (Edite esta resposta na aba Fluxos com o horário da sua empresa)",
      },
    ],
  };
  saveConfig(defaultConfig);
  return defaultConfig;
}

function saveConfig(config) {
  fs.writeFileSync(CONFIG_FILE, JSON.stringify(config, null, 2), "utf8");
}

let config = loadConfig();

// Inicializar Groq se tiver API key
if (config.groqApiKey && config.groqApiKey.trim()) {
  groqClient = new OpenAI({
    apiKey: config.groqApiKey,
    baseURL: "https://api.groq.com/openai/v1",
  });
}

// =====================================
// EXPRESS + SOCKET.IO
// =====================================
const app = express();
const server = http.createServer(app);
io = new Server(server);

app.use(express.json({ limit: "100mb" }));
app.use(express.static(path.join(__dirname, "public")));

function ensureDir(dir) {
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
}

function safeFileName(name) {
  const original = String(name || "arquivo").replace(/[<>:"/\\|?*\x00-\x1F]/g, "_");
  return original.replace(/\s+/g, "_").slice(0, 120) || "arquivo";
}

function resolveUploadPath(relativePath) {
  const uploadsRoot = path.join(__dirname, "uploads");
  const full = path.resolve(__dirname, relativePath || "");
  if (!full.startsWith(uploadsRoot + path.sep)) return null;
  return full;
}

function resolveKnownUploadFile(fileRef) {
  const value = String(fileRef || "").trim();
  if (!value) return null;

  const direct = resolveUploadPath(value);
  if (direct && fs.existsSync(direct)) return direct;

  const safeName = path.basename(value);
  const dirs = ["fluxos", "ia", "agendamentos"];
  for (const dir of dirs) {
    const folder = path.join(__dirname, "uploads", dir);
    const full = path.join(folder, safeName);
    if (fs.existsSync(full)) return full;
    if (fs.existsSync(folder)) {
      const found = fs.readdirSync(folder).find((name) => normalizeText(name) === normalizeText(safeName));
      if (found) return path.join(folder, found);
    }
  }
  return null;
}

function extractTextFromUpload(fileName, mimeType, buffer) {
  const ext = path.extname(fileName || "").toLowerCase();
  const textTypes = [".txt", ".csv", ".json", ".md"];
  const isText = String(mimeType || "").startsWith("text/") || textTypes.includes(ext);
  if (!isText) return "";
  return buffer.toString("utf8").replace(/\u0000/g, "").slice(0, 50000);
}

// API: Salvar config
app.post("/api/config", (req, res) => {
  config = { ...config, ...req.body };
  saveConfig(config);
  if (config.groqApiKey && config.groqApiKey.trim()) {
    groqClient = new OpenAI({
      apiKey: config.groqApiKey,
      baseURL: "https://api.groq.com/openai/v1",
    });
  }
  res.json({ ok: true });
});

// API: Obter config (sem expor a chave completa por segurança no log)
app.get("/api/config", (req, res) => {
  config = loadConfig();
  const safe = { ...config };
  if (safe.groqApiKey) safe.groqApiKey = safe.groqApiKey.substring(0, 8) + "***";
  res.json(safe);
});

// API: Config completa para edição (front envia só se usuário editar)
app.get("/api/config/full", (req, res) => {
  config = loadConfig();
  res.json(config);
});

app.get("/api/respostas-rapidas", (req, res) => {
  config = loadConfig();
  res.json({ ok: true, respostas: Array.isArray(config.respostasRapidas) ? config.respostasRapidas : [] });
});

app.post("/api/respostas-rapidas", (req, res) => {
  config = loadConfig();
  const id = String(req.body.id || "").trim();
  const atalho = String(req.body.atalho || "").trim();
  const texto = String(req.body.texto || "").trim();
  if (!atalho || !texto) {
    return res.status(400).json({ ok: false, erro: "Atalho e mensagem são obrigatórios" });
  }

  const respostas = Array.isArray(config.respostasRapidas) ? config.respostasRapidas : [];
  const agora = new Date().toISOString();
  let resposta;
  if (id) {
    const index = respostas.findIndex((item) => item.id === id);
    if (index === -1) return res.status(404).json({ ok: false, erro: "Resposta rápida não encontrada" });
    resposta = { ...respostas[index], atalho, texto, atualizadoEm: agora };
    respostas[index] = resposta;
  } else {
    resposta = {
      id: `resp_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`,
      atalho,
      texto,
      criadoEm: agora,
      atualizadoEm: agora,
    };
    respostas.push(resposta);
  }
  config.respostasRapidas = respostas;
  saveConfig(config);
  res.json({ ok: true, resposta, respostas });
});

app.delete("/api/respostas-rapidas/:id", (req, res) => {
  config = loadConfig();
  const id = String(req.params.id || "").trim();
  const respostas = Array.isArray(config.respostasRapidas) ? config.respostasRapidas : [];
  const filtradas = respostas.filter((item) => item.id !== id);
  config.respostasRapidas = filtradas;
  saveConfig(config);
  res.json({ ok: true, respostas: filtradas });
});

app.get("/api/silencio-chats", (req, res) => {
  res.json({ ok: true, chats: silencio.listar() });
});
app.post("/api/silencio-chats", (req, res) => {
  const chatId = (req.body && req.body.chatId) ? String(req.body.chatId).trim() : "";
  const remover = !!(req.body && req.body.remover);
  if (!chatId) return res.status(400).json({ ok: false, erro: "chatId obrigatório" });
  if (remover) silencio.desilenciarChat(chatId);
  res.json({ ok: true, chats: silencio.listar() });
});

app.post("/api/silencio-chats/limpar", (req, res) => {
  silencio.limparTodos();
  res.json({ ok: true, chats: silencio.listar() });
});

app.get("/api/inbox", (req, res) => {
  const inbox = loadInbox();
  res.json({ ok: true, conversas: getInboxSummary(inbox) });
});

app.get("/api/inbox/conversa", (req, res) => {
  const chatId = normalizarInboxChatId(req.query.chatId || "");
  const conversa = getInboxConversa(chatId);
  res.json({ ok: true, conversa });
});

app.post("/api/inbox/send", async (req, res) => {
  try {
    if (!whatsappClient || !whatsappConectado) {
      return res.status(400).json({ ok: false, erro: "WhatsApp não está conectado" });
    }
    const chatId = normalizarInboxChatId(req.body.chatId || "");
    const texto = String(req.body.texto || "").trim();
    const arquivo = req.body.arquivo || null;
    if (!chatId) return res.status(400).json({ ok: false, erro: "Conversa inválida" });
    if (!texto && !arquivo) return res.status(400).json({ ok: false, erro: "Digite uma mensagem ou selecione um arquivo" });

    let sent;
    let textoInbox = texto;
    if (arquivo && arquivo.caminho) {
      const fullPath = resolveUploadPath(arquivo.caminho);
      if (!fullPath || !fs.existsSync(fullPath)) {
        return res.status(400).json({ ok: false, erro: "Arquivo não encontrado" });
      }
      const media = new MessageMedia(
        arquivo.tipo || "application/octet-stream",
        fs.readFileSync(fullPath).toString("base64"),
        arquivo.nomeOriginal || path.basename(fullPath)
      );
      sent = await whatsappClient.sendMessage(chatId, media, texto ? { caption: texto } : undefined);
      textoInbox = texto || `[arquivo] ${arquivo.nomeOriginal || arquivo.nome || path.basename(fullPath)}`;
    } else {
      sent = await whatsappClient.sendMessage(chatId, texto);
    }
    silencio.registrarMensagemDoBot(sent);
    silencio.silenciarChat(chatId);
    const conversa = registrarInbox({
      chatId,
      telefone: chatId.replace(/\D/g, ""),
      direcao: "out",
      texto: textoInbox,
      origem: "humano",
      tipo: arquivo ? "file" : "text",
      messageId: sent?.id?._serialized || null,
    });
    if (conversa) {
      atualizarInboxConversa(chatId, {
        status: conversa.status === "novo" ? "em_atendimento" : conversa.status,
        responsavel: conversa.responsavel || "Atendente",
        botSilenciado: true,
      });
    }
    res.json({ ok: true });
  } catch (e) {
    console.error("Erro ao enviar pela inbox:", e);
    res.status(500).json({ ok: false, erro: e.message || "Erro ao enviar mensagem" });
  }
});

app.post("/api/inbox/status", (req, res) => {
  const chatId = normalizarInboxChatId(req.body.chatId || "");
  const status = String(req.body.status || "novo");
  const permitidos = new Set(["novo", "em_atendimento", "aguardando_cliente", "resolvido", "bot"]);
  if (!chatId || !permitidos.has(status)) return res.status(400).json({ ok: false, erro: "Status inválido" });
  const conversa = atualizarInboxConversa(chatId, { status });
  res.json({ ok: true, conversa });
});

app.post("/api/inbox/assumir", (req, res) => {
  const chatId = normalizarInboxChatId(req.body.chatId || "");
  if (!chatId) return res.status(400).json({ ok: false, erro: "Conversa inválida" });
  silencio.silenciarChat(chatId);
  const conversa = atualizarInboxConversa(chatId, {
    status: "em_atendimento",
    responsavel: String(req.body.responsavel || "Atendente").trim() || "Atendente",
    botSilenciado: true,
  });
  res.json({ ok: true, conversa });
});

app.post("/api/inbox/liberar-bot", (req, res) => {
  const chatId = normalizarInboxChatId(req.body.chatId || "");
  if (!chatId) return res.status(400).json({ ok: false, erro: "Conversa inválida" });
  silencio.desilenciarChat(chatId);
  const conversa = atualizarInboxConversa(chatId, {
    status: "bot",
    responsavel: "",
    botSilenciado: false,
  });
  res.json({ ok: true, conversa });
});

app.post("/api/csv-url", async (req, res) => {
  try {
    const url = String((req.body && req.body.url) || "").trim();
    if (!url) return res.status(400).json({ ok: false, erro: "URL obrigatória" });

    const parsed = new URL(url);
    const allowedHosts = ["docs.google.com", "spreadsheets.google.com"];
    if (!["https:", "http:"].includes(parsed.protocol) || !allowedHosts.includes(parsed.hostname)) {
      return res.status(400).json({ ok: false, erro: "Use um link CSV publicado do Google Sheets" });
    }

    const response = await fetch(url);
    if (!response.ok) {
      return res.status(400).json({ ok: false, erro: "Não foi possível baixar a planilha" });
    }
    const csv = await response.text();
    res.json({ ok: true, csv });
  } catch (e) {
    console.error("Erro ao importar CSV:", e);
    res.status(500).json({ ok: false, erro: "Erro ao ler a URL da planilha" });
  }
});

app.post("/api/upload/agendamento", (req, res) => {
  try {
    const { nome, tipo, dataUrl } = req.body || {};
    if (!nome || !dataUrl || !String(dataUrl).includes(",")) {
      return res.status(400).json({ ok: false, erro: "Arquivo inválido" });
    }
    const [, base64] = String(dataUrl).split(",");
    const buffer = Buffer.from(base64, "base64");
    if (!buffer.length) return res.status(400).json({ ok: false, erro: "Arquivo vazio" });
    if (buffer.length > 64 * 1024 * 1024) {
      return res.status(400).json({ ok: false, erro: "Arquivo maior que 64 MB" });
    }

    const dir = path.join(__dirname, "uploads", "agendamentos");
    ensureDir(dir);
    const finalName = `${Date.now()}-${safeFileName(nome)}`;
    const fullPath = path.join(dir, finalName);
    fs.writeFileSync(fullPath, buffer);

    res.json({
      ok: true,
      arquivo: {
        nomeOriginal: nome,
        nomeSalvo: finalName,
        tipo: tipo || "application/octet-stream",
        tamanho: buffer.length,
        caminho: path.join("uploads", "agendamentos", finalName).replace(/\\/g, "/"),
      },
    });
  } catch (e) {
    console.error("Erro ao salvar upload:", e);
    res.status(500).json({ ok: false, erro: "Erro ao salvar arquivo" });
  }
});

app.post("/api/upload/ia", (req, res) => {
  try {
    const { nome, tipo, dataUrl } = req.body || {};
    if (!nome || !dataUrl || !String(dataUrl).includes(",")) {
      return res.status(400).json({ ok: false, erro: "Arquivo inválido" });
    }
    const [, base64] = String(dataUrl).split(",");
    const buffer = Buffer.from(base64, "base64");
    if (!buffer.length) return res.status(400).json({ ok: false, erro: "Arquivo vazio" });
    if (buffer.length > 20 * 1024 * 1024) {
      return res.status(400).json({ ok: false, erro: "Arquivo maior que 20 MB" });
    }

    const dir = path.join(__dirname, "uploads", "ia");
    ensureDir(dir);
    const finalName = `${Date.now()}-${safeFileName(nome)}`;
    const fullPath = path.join(dir, finalName);
    fs.writeFileSync(fullPath, buffer);

    config = loadConfig();
    const textoExtraido = extractTextFromUpload(nome, tipo, buffer);
    const arquivo = {
      nomeOriginal: nome,
      nomeSalvo: finalName,
      tipo: tipo || "application/octet-stream",
      tamanho: buffer.length,
      caminho: path.join("uploads", "ia", finalName).replace(/\\/g, "/"),
      textoExtraido: !!textoExtraido,
      criadoEm: new Date().toISOString(),
    };
    config.knowledgeFiles = [...(config.knowledgeFiles || []), arquivo].slice(-20);
    if (textoExtraido) {
      const bloco = `\n\n--- ARQUIVO: ${nome} ---\n${textoExtraido}`;
      config.knowledgeText = `${config.knowledgeText || ""}${bloco}`.slice(-120000);
    }
    saveConfig(config);

    res.json({ ok: true, arquivo });
  } catch (e) {
    console.error("Erro ao salvar arquivo da IA:", e);
    res.status(500).json({ ok: false, erro: "Erro ao salvar arquivo da IA" });
  }
});

app.get("/api/fluxos/arquivos", (req, res) => {
  try {
    const dir = path.join(__dirname, "uploads", "fluxos");
    ensureDir(dir);
    const arquivos = fs.readdirSync(dir)
      .filter((name) => name !== ".gitkeep")
      .map((name) => {
        const full = path.join(dir, name);
        const stat = fs.statSync(full);
        return { nome: name, tamanho: stat.size, criadoEm: stat.mtime.toISOString() };
      });
    res.json({ ok: true, arquivos });
  } catch (e) {
    res.status(500).json({ ok: false, erro: "Erro ao listar arquivos" });
  }
});

app.post("/api/upload/fluxo", (req, res) => {
  try {
    const { nome, tipo, dataUrl } = req.body || {};
    if (!nome || !dataUrl || !String(dataUrl).includes(",")) {
      return res.status(400).json({ ok: false, erro: "Arquivo inválido" });
    }
    const [, base64] = String(dataUrl).split(",");
    const buffer = Buffer.from(base64, "base64");
    if (!buffer.length) return res.status(400).json({ ok: false, erro: "Arquivo vazio" });
    if (buffer.length > 20 * 1024 * 1024) {
      return res.status(400).json({ ok: false, erro: "Arquivo maior que 20 MB" });
    }

    const dir = path.join(__dirname, "uploads", "fluxos");
    ensureDir(dir);
    const finalName = safeFileName(nome);
    const fullPath = path.join(dir, finalName);
    fs.writeFileSync(fullPath, buffer);
    res.json({
      ok: true,
      arquivo: {
        nome: finalName,
        tipo: tipo || "application/octet-stream",
        tamanho: buffer.length,
      },
    });
  } catch (e) {
    console.error("Erro ao salvar arquivo do fluxo:", e);
    res.status(500).json({ ok: false, erro: "Erro ao salvar arquivo do fluxo" });
  }
});

app.post("/api/whatsapp/send", async (req, res) => {
  try {
    config = loadConfig();
    if (config.silenciarEnvios) {
      return res.status(423).json({ ok: false, erro: "Fluxo de envios está silenciado" });
    }
    if (!whatsappClient || !whatsappConectado) {
      return res.status(400).json({ ok: false, erro: "WhatsApp não está conectado" });
    }
    const telefone = String(req.body.telefone || "").replace(/\D/g, "");
    const mensagem = String(req.body.mensagem || "").trim();
    const mensagemFinal = String(req.body.mensagemFinal || "").trim();
    const delayBlocos = req.body.delayBlocos;
    const arquivo = req.body.arquivo || null;
    const arquivos = Array.isArray(req.body.arquivos) ? req.body.arquivos : [];
    if (!telefone) return res.status(400).json({ ok: false, erro: "Telefone obrigatório" });
    if (!mensagem && !arquivo && !arquivos.length && !mensagemFinal) {
      return res.status(400).json({ ok: false, erro: "Mensagem, finalização ou arquivo obrigatório" });
    }

    await enviarSequenciaWhatsApp({ telefone, mensagem, arquivo, arquivos, mensagemFinal, delayBlocos });
    res.json({ ok: true });
  } catch (e) {
    console.error("Erro ao enviar WhatsApp:", e);
    res.status(500).json({ ok: false, erro: e.message || "Erro ao enviar" });
  }
});

// Rota principal
app.get("/", (req, res) => {
  res.sendFile(path.join(__dirname, "public", "index.html"));
});

// API: Desconectar WhatsApp
app.post("/api/whatsapp/disconnect", async (req, res) => {
  try {
    whatsappAutoReconnect = false;
    if (whatsappClient) {
      whatsappConectado = false;
      try { await whatsappClient.destroy(); } catch (e) {}
      whatsappClient = null;
      io.emit("status", { conectado: false, mensagem: "Desconectado. Clique em Gerar novo QR Code para conectar novamente." });
    }
    res.json({ ok: true });
  } catch (e) {
    whatsappClient = null;
    res.json({ ok: true });
  }
});

// API: Gerar novo QR Code (reinicia o WhatsApp)
// ?limpar=1 para limpar sessão e tentar do zero (quando trava)
app.post("/api/whatsapp/restart", async (req, res) => {
  try {
    whatsappAutoReconnect = true;
    if (whatsappClient) {
      try { await whatsappClient.destroy(); } catch (e) {}
      whatsappClient = null;
    }
    whatsappConectado = false;

    // Limpar sessão se solicitado (resolve "não conecta" ou travamentos)
    if (req.query.limpar === "1") {
      const authPath = path.join(__dirname, ".wwebjs_auth");
      if (fs.existsSync(authPath)) {
        try {
          fs.rmSync(authPath, { recursive: true });
          console.log("Sessão limpa. Iniciando do zero.");
        } catch (e) {
          console.error("Erro ao limpar sessão:", e);
        }
      }
    }

    io.emit("qr", "loading");
    io.emit("status", { conectado: false, mensagem: "Gerando QR Code... Pode levar 1-2 minutos na primeira vez." });
    initWhatsApp(true);
    res.json({ ok: true });
  } catch (e) {
    console.error("Erro ao reiniciar:", e);
    io.emit("status", { conectado: false, mensagem: "Erro. Clique em 'Limpar sessão e tentar' para recomeçar." });
    res.json({ ok: false, erro: e.message });
  }
});

// =====================================
// WHATSAPP
// =====================================
function initWhatsApp(force = false) {
  whatsappAutoReconnect = true;
  if (whatsappClient && !force) return;
  if (whatsappClient && force) {
    whatsappClient = null;
  }
  whatsappInicializadoEm = Date.now();
  
  whatsappClient = new Client({
    authStrategy: new LocalAuth({ clientId: "agente-ia" }),
    authTimeoutMs: 180000, // 3 min para escanear (evita timeout ao conectar)
    puppeteer: {
      headless: true,
      timeout: 120000, // 2 min para o navegador iniciar
      args: [
        "--no-sandbox",
        "--disable-setuid-sandbox",
        "--disable-dev-shm-usage",
        "--disable-gpu",
        "--disable-software-rasterizer",
        "--disable-extensions",
        "--no-first-run",
        "--disable-backgrounding-occluded-windows",
        "--disable-renderer-backgrounding",
        "--disable-features=VizDisplayCompositor",
      ],
    },
  });

  whatsappClient.on("qr", async (qr) => {
    try {
      const qrDataUrl = await QRCode.toDataURL(qr, { width: 300 });
      io.emit("qr", qrDataUrl);
      io.emit("status", { conectado: false, mensagem: "Escaneie o QR Code com seu WhatsApp" });
    } catch (e) {
      console.error("Erro ao gerar QR:", e);
    }
  });

  whatsappClient.on("ready", () => {
    whatsappConectado = true;
    io.emit("qr", null); // limpa QR
    io.emit("status", { conectado: true, mensagem: "WhatsApp conectado!" });
    console.log("✅ WhatsApp conectado.");
  });

  whatsappClient.on("disconnected", () => {
    whatsappConectado = false;
    io.emit("status", { conectado: false, mensagem: "WhatsApp desconectado" });
    agendarReinicioWhatsApp("WhatsApp desconectado");
  });

  whatsappClient.on("auth_failure", (msg) => {
    console.error("Falha na autenticação:", msg);
    io.emit("status", { conectado: false, mensagem: "Falha ao conectar. Clique em 'Limpar sessão e tentar'." });
  });

  whatsappClient.on("message", handleMessage);

  whatsappClient.initialize().catch((err) => {
    console.error("Erro ao inicializar WhatsApp:", err);
    whatsappClient = null;
    io.emit("status", { conectado: false, mensagem: "Erro ao iniciar. Feche outros programas e clique em 'Limpar sessão e tentar'." });
    agendarReinicioWhatsApp("Falha ao inicializar WhatsApp");
  });
}

async function agendarReinicioWhatsApp(motivo) {
  if (SKIP_WHATSAPP || !whatsappAutoReconnect || reinicioWhatsAppEmAndamento) return;
  reinicioWhatsAppEmAndamento = true;
  console.log(`Watchdog WhatsApp: reiniciando em 15s. Motivo: ${motivo}`);
  io.emit("status", { conectado: false, mensagem: "WhatsApp caiu/travou. Tentando reconectar automaticamente..." });
  setTimeout(async () => {
    try {
      if (whatsappClient) {
        try { await whatsappClient.destroy(); } catch (e) {}
        whatsappClient = null;
      }
      whatsappConectado = false;
      io.emit("qr", "loading");
      initWhatsApp(true);
    } catch (e) {
      console.error("Erro no reinício automático do WhatsApp:", e);
    } finally {
      reinicioWhatsAppEmAndamento = false;
    }
  }, 15000);
}

function iniciarWatchdogWhatsApp() {
  if (SKIP_WHATSAPP) return;
  setInterval(async () => {
    if (!whatsappAutoReconnect || reinicioWhatsAppEmAndamento) return;
    if (!whatsappClient) {
      agendarReinicioWhatsApp("Cliente inexistente");
      return;
    }

    const tempoInicializando = Date.now() - whatsappInicializadoEm;
    if (!whatsappConectado && tempoInicializando > WHATSAPP_STARTUP_TIMEOUT_MS) {
      agendarReinicioWhatsApp("Tempo limite sem conectar");
      return;
    }

    if (!whatsappConectado) return;

    try {
      const state = await whatsappClient.getState();
      if (state && state !== "CONNECTED") {
        whatsappConectado = false;
        agendarReinicioWhatsApp(`Estado inesperado: ${state}`);
      }
    } catch (e) {
      whatsappConectado = false;
      agendarReinicioWhatsApp("Falha ao consultar estado do WhatsApp");
    }
  }, WHATSAPP_WATCHDOG_INTERVAL_MS);
}

// =====================================
// LÓGICA DE MENSAGENS
// =====================================
const delay = (ms) => new Promise((r) => setTimeout(r, ms));

async function enviarSequenciaWhatsApp({ telefone, mensagem, arquivo, arquivos, mensagemFinal, delayBlocos }) {
  const chatId = `${telefone}@c.us`;
  const intervaloMs = Math.max(0, Math.min(120, Number(delayBlocos) || 0)) * 1000;
  let sentMsg = null;
  const listaArquivos = Array.isArray(arquivos) && arquivos.length
    ? arquivos
    : (arquivo ? [arquivo] : []);

  if (listaArquivos.length) {
    for (let i = 0; i < listaArquivos.length; i++) {
      const item = listaArquivos[i];
      if (!item || !item.caminho) continue;
      const fullPath = resolveUploadPath(item.caminho);
      if (!fullPath || !fs.existsSync(fullPath)) {
        throw new Error(`Arquivo não encontrado: ${item.nomeOriginal || item.nome || "anexo"}`);
      }
      if (sentMsg && intervaloMs > 0) await delay(intervaloMs);
      const media = new MessageMedia(
        item.tipo || "application/octet-stream",
        fs.readFileSync(fullPath).toString("base64"),
        item.nomeOriginal || path.basename(fullPath)
      );
      const options = i === 0 && mensagem ? { caption: mensagem } : undefined;
      sentMsg = await whatsappClient.sendMessage(chatId, media, options);
      if (sentMsg) silencio.registrarMensagemDoBot(sentMsg);
    }
  } else if (mensagem) {
    sentMsg = await whatsappClient.sendMessage(chatId, mensagem);
    if (sentMsg) silencio.registrarMensagemDoBot(sentMsg);
  }

  if (mensagemFinal) {
    if (sentMsg && intervaloMs > 0) await delay(intervaloMs);
    const finalMsg = await whatsappClient.sendMessage(chatId, mensagemFinal);
    silencio.registrarMensagemDoBot(finalMsg);
    sentMsg = finalMsg;
  }

  return sentMsg;
}

async function respostaPorFluxo(texto) {
  config = loadConfig();
  const txt = texto.trim().toLowerCase();
  for (const flow of config.flows || []) {
    for (const p of flow.palavras || []) {
      if (txt.includes(p.toLowerCase()) || txt === p.toLowerCase()) {
        return flow.resposta;
      }
    }
  }
  return null;
}

async function respostaPorIA(texto, contexto = "") {
  if (!groqClient || !config.groqApiKey) return null;
  try {
    const completion = await groqClient.chat.completions.create({
      model: config.model || "llama-3.1-8b-instant",
      messages: [
        { role: "system", content: config.promptSistema || "Você é um assistente prestativo." },
        ...(config.knowledgeText ? [{
          role: "system",
          content: `Base de conhecimento cadastrada pelo usuário. Use estes dados para responder quando forem relevantes. Se precisar conferir nome, telefone, turma, curso ou material, procure nesta base antes de responder:\n${config.knowledgeText}`,
        }] : []),
        ...(contexto ? [{ role: "user", content: contexto }] : []),
        { role: "user", content: texto },
      ],
      max_tokens: 500,
      temperature: 0.7,
    });
    const res = completion.choices?.[0]?.message?.content;
    return res ? res.trim() : null;
  } catch (e) {
    console.error("Erro Groq:", e.message);
    return null;
  }
}

async function handleMessage(msg) {
  try {
    config = loadConfig();
    const from = (msg.from || "").toString();
    if (from.includes("status") || from.includes("broadcast") || msg.broadcast || msg.isStatus) return;
    if (!msg.from || msg.from.endsWith("@g.us")) return;
    const chat = await msg.getChat();
    if (chat.isGroup) return;
    const chatId = chat.id._serialized;
    let contatoInfo = null;
    try {
      contatoInfo = await msg.getContact();
    } catch (e) {}
    const telefoneInbox = from.replace(/\D/g, "");
    const nomeInbox = contatoInfo?.name || contatoInfo?.pushname || chat.name || telefoneInbox;

    if (msg.fromMe) {
      if (silencio.ehMensagemDoBot(msg)) return;
      registrarInbox({
        chatId,
        telefone: telefoneInbox,
        nome: nomeInbox,
        direcao: "out",
        texto: msg.body || "",
        origem: "humano",
        messageId: msg.id?._serialized || null,
      });
      silencio.silenciarChat(chatId);
      return;
    }

    const MAX_IDADE_SEGUNDOS = 300;
    const agora = Math.floor(Date.now() / 1000);
    const ts = msg.timestamp || 0;
    if (ts > 0 && (agora - ts) > MAX_IDADE_SEGUNDOS) return;

    const texto = msg.body ? msg.body.trim() : "";
    if (texto) {
      registrarInbox({
        chatId,
        telefone: telefoneInbox,
        nome: nomeInbox,
        direcao: "in",
        texto,
        origem: "cliente",
        messageId: msg.id?._serialized || null,
      });
    }

    if (config.humanoAtendeu) return;
    if (silencio.estaSilenciado(chatId)) return;
    if (config.silenciarBot) return;

    if (silencio.textoEhOptOut(texto)) {
      silencio.silenciarChat(chatId);
      const r = await msg.reply("Ok! Pausamos o assistente automático nesta conversa. Quando precisar, é só chamar no suporte.");
      silencio.registrarMensagemDoBot(r);
      registrarSaidaInbox(chatId, "Ok! Pausamos o assistente automático nesta conversa. Quando precisar, é só chamar no suporte.", "bot", r);
      return;
    }
    if (!texto) return;

    const typing = async () => {
      await delay(800);
      await chat.sendStateTyping();
      await delay(1200);
    };

    if (shouldHandoff(texto)) {
      const handoff = getHandoffConfig();
      const telefoneCliente = from.replace(/\D/g, "");
      await typing();
      const r = await msg.reply(handoff.respostaCliente || "Certo, vou encaminhar você para um atendente. Aguarde um instante.");
      silencio.registrarMensagemDoBot(r);
      registrarSaidaInbox(chatId, handoff.respostaCliente || "Certo, vou encaminhar você para um atendente. Aguarde um instante.", "bot", r);
      silencio.silenciarChat(chatId);

      const numeroAtendente = String(handoff.numeroAtendente || "").replace(/\D/g, "");
      if (numeroAtendente && whatsappClient && whatsappConectado) {
        const aviso = renderHandoffMessage(handoff.mensagemAtendente, {
          telefone: telefoneCliente,
          mensagem: texto,
          chatid: chatId,
        });
        const sent = await whatsappClient.sendMessage(`${numeroAtendente}@c.us`, aviso);
        silencio.registrarMensagemDoBot(sent);
      }
      return;
    }

    const estadoAtual = estadosConversa.get(chatId);
    if (estadoAtual && estadoAtual.tipo === "conditional") {
      const flow = getConditionalFlows().find((item) => item.id === estadoAtual.flowId);
      if (flow) {
        const rows = searchConditionalRecords(flow, texto);
        if (rows.length) {
          estadosConversa.delete(chatId);
          await sendConditionalRecordsResponse({ msg, chatId, flow, rows, typing });
          return;
        }

        const tentativas = (estadoAtual.tentativas || 0) + 1;
        if (tentativas >= 3) {
          estadosConversa.delete(chatId);
        } else {
          estadosConversa.set(chatId, {
            ...estadoAtual,
            tentativas,
            atualizadoEm: Date.now(),
          });
        }
        await typing();
        const r = await msg.reply(flow.respostaNaoEncontrado || "Não encontrei seu cadastro. Confira os dados e tente novamente.");
        silencio.registrarMensagemDoBot(r);
        registrarSaidaInbox(chatId, flow.respostaNaoEncontrado || "Não encontrei seu cadastro. Confira os dados e tente novamente.", "bot", r);
        return;
      }
      estadosConversa.delete(chatId);
    }

    const conditionalFlow = findConditionalFlow(texto);
    if (conditionalFlow) {
      estadosConversa.set(chatId, {
        tipo: "conditional",
        flowId: conditionalFlow.id,
        tentativas: 0,
        criadoEm: Date.now(),
      });
      await typing();
      const r = await msg.reply(conditionalFlow.pergunta || "Digite os dados para consulta.");
      silencio.registrarMensagemDoBot(r);
      registrarSaidaInbox(chatId, conditionalFlow.pergunta || "Digite os dados para consulta.", "bot", r);
      return;
    }

    const conditionalRecord = findConditionalRecordsByText(texto);
    if (conditionalRecord) {
      await sendConditionalRecordsResponse({
        msg,
        chatId,
        flow: conditionalRecord.flow,
        rows: conditionalRecord.rows,
        typing,
      });
      return;
    }

    config = loadConfig();

    let resposta = await respostaPorFluxo(texto);
    if (!resposta && config.useAI) {
      resposta = await respostaPorIA(texto);
    }
    if (!resposta) {
      resposta = typeof config.fallbackResposta === "string"
        ? config.fallbackResposta.trim()
        : "Desculpe, não entendi. Digite 'menu' para ver as opções.";
    }
    if (!resposta) {
      return;
    }

    await typing();
    const r = await msg.reply(resposta);
    silencio.registrarMensagemDoBot(r);
    registrarSaidaInbox(chatId, resposta, "bot", r);
  } catch (error) {
    console.error("❌ Erro ao processar mensagem:", error);
    try {
      const r = await msg.reply("Ocorreu um erro. Tente novamente em instantes.");
      silencio.registrarMensagemDoBot(r);
      const chatId = msg.from && msg.from.endsWith("@c.us") ? msg.from : null;
      if (chatId) registrarSaidaInbox(chatId, "Ocorreu um erro. Tente novamente em instantes.", "bot", r);
    } catch (e) {}
  }
}

// =====================================
// SOCKET.IO - broadcast de status
// =====================================
io.on("connection", (socket) => {
  socket.emit("status", {
    conectado: whatsappConectado,
    mensagem: whatsappConectado ? "WhatsApp conectado!" : "Conecte escaneando o QR Code",
  });
  socket.emit("inbox:summary", getInboxSummary());
  if (!whatsappConectado) {
    socket.emit("qr", "loading");
  }
});

// =====================================
// INICIAR
// =====================================
  server.listen(PORT, () => {
  console.log(`
╔══════════════════════════════════════════════════════════╗
║  🤖 AGENTE DE IA + CHATBOT WHATSAPP                      ║
║                                                          ║
║  Abra no navegador:  http://localhost:${PORT}             ║
║                                                          ║
║  O QR Code aparecerá na tela - escaneie com o WhatsApp!  ║
╚══════════════════════════════════════════════════════════╝
  `);
  io.emit("qr", "loading");
  if (SKIP_WHATSAPP) {
    console.log("WhatsApp não iniciado porque SKIP_WHATSAPP=1.");
    io.emit("status", { conectado: false, mensagem: "Modo local: WhatsApp não iniciado" });
  } else {
    initWhatsApp();
    iniciarWatchdogWhatsApp();
  }
});
