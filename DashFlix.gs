/**
 * DashFlix - Analizador de Estratégias
 * Dashboard FUNCIONAL (Seletor de Período Ativo)
 * Data: 2026-01-08
 */

/* ================= CONFIG ================= */
const SHEET_DASHBOARD = "Dashboard";
const SHEET_TRADES = "Trades";
const PERIOD_CELL = "M1";
const TRADES_HEADER_ROW = 1;
const TRADES_DATA_START_ROW = TRADES_HEADER_ROW + 1;
const TRADES_COLUMNS = 4; // Date, PnL, Contracts, Asset

const THEME = {
  bg: "#121212",
  panel: "#1E1E1E",
  panel2: "#252525",
  black: "#000000",
  text: "#E0E0E0",
  textDim: "#B0BEC5",
  bronze: "#B08B4F",
  grid: "#333333",
};

/* ================= MENU ================= */
function onOpen() {
  SpreadsheetApp.getUi()
    .createMenu("DashFlix")
    .addItem("Atualizar Dashboard", "updateDashboard")
    .addToUi();
}

/* ================= EVENT ================= */
function onEdit(e) {
  if (!e) return;
  const sh = e.range.getSheet();
  if (sh.getName() !== SHEET_DASHBOARD) return;

  if (e.range.getA1Notation() === PERIOD_CELL) {
    updateDashboard();
  }
}

/* ================= ENTRY ================= */
function updateDashboard() {
  const ss = SpreadsheetApp.getActive();
  const sh = getSheetByNameInsensitive(ss, SHEET_DASHBOARD);
  if (!sh) {
    Logger.log("Dashboard sheet not found.");
    return;
  }

  const period = sh.getRange(PERIOD_CELL).getValue();
  const trades = getFilteredTrades(period);

  renderKpis(sh, trades);
  renderCharts(sh, trades);
  renderRightColumn(sh, trades);

  SpreadsheetApp.flush();
}

/* ================= DATA ================= */
function getFilteredTrades(period) {
  const ss = SpreadsheetApp.getActive();
  const sh = getTradesSheet(ss);
  if (!sh) {
    Logger.log(
      `Trades sheet not found. Expected a sheet named "${SHEET_TRADES}".`
    );
    return [];
  }

  const lastRow = sh.getLastRow();
  if (lastRow <= TRADES_HEADER_ROW) return [];

  const data = sh
    .getRange(TRADES_DATA_START_ROW, 1, lastRow - TRADES_HEADER_ROW, TRADES_COLUMNS)
    .getValues();

  const rows = data
    .filter((r) => r[0] instanceof Date && !isNaN(r[0].getTime()))
    .map((r) => ({
      date: r[0],
      pnl: Number(r[1]) || 0,
      contracts: r[2],
      asset: r[3],
    }));

  const normalizedPeriod = String(period || "")
    .trim()
    .toLowerCase();

  if (!normalizedPeriod || normalizedPeriod === "geral") return rows;

  const now = new Date();

  return rows.filter((r) => {
    if (normalizedPeriod === "diário" || normalizedPeriod === "diario") {
      return sameDay(r.date, now);
    }
    if (normalizedPeriod === "semanal") {
      return sameWeek(r.date, now);
    }
    if (normalizedPeriod === "mensal") {
      return (
        r.date.getMonth() === now.getMonth() &&
        r.date.getFullYear() === now.getFullYear()
      );
    }
    if (normalizedPeriod === "anual") {
      return r.date.getFullYear() === now.getFullYear();
    }
    return true;
  });
}

/* ================= HELPERS ================= */
function sameDay(a, b) {
  return (
    a.getDate() === b.getDate() &&
    a.getMonth() === b.getMonth() &&
    a.getFullYear() === b.getFullYear()
  );
}

function sameWeek(a, b) {
  const startA = startOfWeek(a).getTime();
  const startB = startOfWeek(b).getTime();
  return startA === startB;
}

function startOfWeek(date) {
  const d = new Date(date);
  d.setHours(0, 0, 0, 0);
  const day = (d.getDay() + 6) % 7; // Monday = 0
  d.setDate(d.getDate() - day);
  return d;
}

function getSheetByNameInsensitive(ss, name) {
  const direct = ss.getSheetByName(name);
  if (direct) return direct;
  const target = String(name || "").toLowerCase();
  return ss
    .getSheets()
    .find((sheet) => sheet.getName().toLowerCase() === target);
}

function getTradesSheet(ss) {
  const direct = ss.getSheetByName(SHEET_TRADES);
  if (direct) return direct;
  const lower = ss.getSheetByName(SHEET_TRADES.toLowerCase());
  if (lower) return lower;
  return null;
}

/* ================= KPIs ================= */
function renderKpis(sh, trades) {
  const totalPnL = trades.reduce((s, t) => s + t.pnl, 0);
  const days = [...new Set(trades.map((t) => t.date.toDateString()))].length;
  const wins = trades.filter((t) => t.pnl > 0).length;
  const winRate = trades.length ? Math.round((wins / trades.length) * 100) : 0;

  sh.getRange("B5").setValue("$ " + totalPnL.toFixed(2));
  sh.getRange("F5").setValue(winRate + "%");
  sh.getRange("D5").setValue(days);
}

/* ================= CHARTS ================= */
function renderCharts(sh, trades) {
  sh.getCharts().forEach((c) => sh.removeChart(c));
  if (!trades.length) return;

  const map = new Map();
  trades.forEach((t) => {
    const key = Utilities.formatDate(
      t.date,
      Session.getScriptTimeZone(),
      "yyyy-MM-dd"
    );
    const existing = map.get(key);
    if (existing) {
      existing.pnl += t.pnl;
    } else {
      const normalizedDate = new Date(t.date);
      normalizedDate.setHours(0, 0, 0, 0);
      map.set(key, { date: normalizedDate, pnl: t.pnl });
    }
  });

  const entries = Array.from(map.values()).sort((a, b) => a.date - b.date);
  let cum = 0;
  const curve = entries.map((entry) => {
    cum += entry.pnl;
    return [entry.date, cum];
  });

  const start = 200;
  const header = [["Data", "PnL"]];

  sh.getRange(start, 1, curve.length + 1, 2).clearContent();
  sh.getRange(start, 1, 1, 2).setValues(header);
  sh.getRange(start + 1, 1, curve.length, 2).setValues(curve);

  const dataRange = sh.getRange(start, 1, curve.length + 1, 2);

  const chart = sh
    .newChart()
    .setChartType(Charts.ChartType.LINE)
    .addRange(dataRange)
    .setPosition(8, 1, 0, 0)
    .setOption("colors", [THEME.bronze])
    .setOption("backgroundColor.fill", THEME.bg)
    .setOption("legend", { position: "none" })
    .build();

  sh.insertChart(chart);
}

/* ================= RIGHT COLUMN ================= */
function renderRightColumn(sh, trades) {
  const startCol = 13;
  const startRow = 6;
  const maxRows = 300;

  const clearRange = sh.getRange(startRow, startCol, maxRows, 4);
  clearRange.breakApart();
  clearRange.clearContent();

  if (trades.length) {
    const rows = trades.map((t) => [
      Utilities.formatDate(
        t.date,
        Session.getScriptTimeZone(),
        "dd/MM/yyyy"
      ),
      t.pnl,
      t.contracts,
      t.asset,
    ]);

    sh.getRange(startRow + 1, startCol, rows.length, 4).setValues(rows);
  }

  const total = trades.reduce((s, t) => s + t.pnl, 0);
  const totalRow = startRow + trades.length + 2;

  sh.getRange(totalRow, startCol, 1, 4).merge().setValue("TOTAL");
  sh.getRange(totalRow + 1, startCol, 1, 4).merge().setValue("$ " + total.toFixed(2));
}
