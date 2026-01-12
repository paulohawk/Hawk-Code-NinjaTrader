#region Using declarations
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Text;
using System.Xml.Serialization;
using System.Windows.Media;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using NinjaTrader.Cbi;
using NinjaTrader.Gui.Tools;
using NinjaTrader.Data;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.DrawingTools;
#endregion

namespace NinjaTrader.NinjaScript.Indicators
{
    public class AnchoredMidasIndicator : Indicator
    {
        private SessionIterator sessionIterator;
        private List<int> sessionStartIndices = new List<int>();
        private bool sessionStartsBuilt = false;

        private int anchorBarIndex_byBar = -1;
        private bool anchorValid_byBar = false;
        private int anchorSessionIndex = -1;

        private double cumPV_Bar_High, cumV_Bar_High, cumPV_Bar_Median, cumV_Bar_Median, cumPV_Bar_Low, cumV_Bar_Low;
        private int lastCumIndex_Bar = -1;

        private int _sessionOffset = 0;
        private int _barInSession = 1;
        private bool _useLastBarIfBarIndexTooLarge = true;
        private bool _plotOnlyNextSession = true;
        private bool _debugMode = false;
        private bool _anchorBySessionHighLow = false; // compat assinatura (não usado)
        private bool _fallbackToNearestSession = true;
        private bool _enableBarLogging = false;
        private int _logTimeframeMin = 60;
        private string _logFolder = null;
        private bool _logPerSessionFile = true;

        // Cores padrão (DimGray / White / DimGray)
        private Brush _barAnchorHighBrush = Brushes.DimGray;
        private Brush _barAnchorMedianBrush = Brushes.White;
        private Brush _barAnchorLowBrush = Brushes.DimGray;

        // Nuvem entre VWAP_Bar_High e VWAP_Bar_Low
        private bool _enableBandCloud = true;
        private Brush _bandCloudBrush = new SolidColorBrush(Color.FromArgb(51, 128, 128, 128)); // 20%
        private string _bandCloudBrushSerializable;
        private double _bandCloudOpacity = 20.0; // 0-100 %

        private DateTime lastTradingDay = Core.Globals.MinDate;

        private bool loggedReady = false;
        private bool loggedNotReady = false;
        private bool fallbackDisabledLogged = false;

        [XmlIgnore, Browsable(false)] public int LastRequestedTargetSessionIndex { get; private set; } = int.MinValue;
        [XmlIgnore, Browsable(false)] public int LastUsedAnchorSessionIndex { get; private set; } = int.MinValue;
        [XmlIgnore, Browsable(false)] public bool AnchorWasClamped { get; private set; } = false;
        [XmlIgnore, Browsable(false)] public DateTime LastUsedAnchorTime { get; private set; } = Core.Globals.MinDate;
        [XmlIgnore, Browsable(false)] public bool IsReady { get; private set; } = false;
        [XmlIgnore, Browsable(false)] public int ClampCount { get; private set; } = 0;

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description = "Anchored MIDAS (VWAP) — BarInSession anchoring, nuvem entre High/Low VWAP, logging opcional.";
                Name = "AnchoredMidasIndicator";
                Calculate = Calculate.OnBarClose;
                IsOverlay = true;
                DisplayInDataBox = true;
                DrawOnPricePanel = true;
                BarsRequiredToPlot = 0;

                SessionOffset = 0;
                BarInSession = 1;
                UseLastBarIfBarIndexTooLarge = true;
                PlotOnlyNextSession = true;
                DebugMode = false;
                AnchorBySessionHighLow = false; // compat
                FallbackToNearestSession = true;

                EnableBarLogging = false;
                LogTimeframeMin = 60;
                LogPerSessionFile = true;

                AddPlot(Brushes.DimGray, "VWAP_Bar_High");
                AddPlot(Brushes.White,   "VWAP_Bar_Median");
                AddPlot(Brushes.DimGray, "VWAP_Bar_Low");

                Plots[0].Width = 2; Plots[1].Width = 1; Plots[2].Width = 2;

                EnableBandCloud = true;
                BandCloudBrush = new SolidColorBrush(Color.FromArgb(51, 128, 128, 128));
                BandCloudOpacity = 20.0;
            }
            else if (State == State.DataLoaded)
            {
                try { sessionIterator = new SessionIterator(Bars); }
                catch (Exception ex) { if (DebugMode) Log($"[AnchoredVWAP] SessionIterator init failed: {ex.Message}", LogLevel.Warning); }

                if (string.IsNullOrEmpty(_logFolder))
                {
                    try
                    {
                        string docs = Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);
                        _logFolder = Path.Combine(docs, "NinjaTrader 8", "logs", "MIDAS");
                    }
                    catch { _logFolder = null; }
                }

                if (EnableBarLogging && !string.IsNullOrEmpty(_logFolder))
                {
                    try { Directory.CreateDirectory(_logFolder); }
                    catch (Exception ex) { if (DebugMode) Log($"[AnchoredVWAP] Could not create log folder {_logFolder}: {ex.Message}", LogLevel.Warning); }
                }

                try
                {
                    BuildSessionStarts();
                    lastTradingDay = sessionIterator != null && Bars.Count > 0
                        ? sessionIterator.GetTradingDay(Bars.GetTime(Math.Max(0, Bars.Count - 1)))
                        : Core.Globals.MinDate;
                }
                catch (Exception ex) { if (DebugMode) Log($"[AnchoredVWAP] BuildSessionStarts failed in DataLoaded: {ex.Message}", LogLevel.Warning); }
            }
        }

        protected override void OnBarUpdate()
        {
            IsReady = false;

            if (!Bars.BarsType.IsIntraday)
            {
                ClearAllValues();
                return;
            }

            if (!sessionStartsBuilt)
            {
                BuildSessionStarts();
                sessionStartsBuilt = true;
            }

            try
            {
                DateTime td = sessionIterator.GetTradingDay(Bars.GetTime(CurrentBar));
                if (td != lastTradingDay)
                {
                    BuildSessionStarts();
                    lastTradingDay = td;
                    loggedReady = false;
                    loggedNotReady = false;
                    fallbackDisabledLogged = false;
                }
            }
            catch { }

            int currentSessionIndex = GetSessionIndexContainingBar(CurrentBar);
            if (currentSessionIndex < 0) { ClearAllValues(); LogNotReadyOnce("No session index"); return; }

            int targetSessionIndex = currentSessionIndex + SessionOffset;

            LastRequestedTargetSessionIndex = targetSessionIndex;
            AnchorWasClamped = false;
            LastUsedAnchorSessionIndex = int.MinValue;
            LastUsedAnchorTime = Core.Globals.MinDate;

            if (PlotOnlyNextSession && targetSessionIndex != currentSessionIndex)
            {
                ClearAllValues();
                LogNotReadyOnce("PlotOnlyNextSession active and current session != target");
                return;
            }

            if (targetSessionIndex < 0 || targetSessionIndex >= sessionStartIndices.Count)
            {
                if (FallbackToNearestSession && sessionStartIndices.Count > 0)
                {
                    int clamped = Math.Max(0, Math.Min(targetSessionIndex, sessionStartIndices.Count - 1));
                    AnchorWasClamped = clamped != targetSessionIndex;
                    if (AnchorWasClamped) ClampCount++;
                    LastUsedAnchorSessionIndex = clamped;
                    targetSessionIndex = clamped;
                    fallbackDisabledLogged = false;
                }
                else
                {
                    ClearAllValues();
                    if (!fallbackDisabledLogged && DebugMode)
                    {
                        Log($"[AnchoredVWAP] targetSessionIndex {targetSessionIndex} out-of-range -> returning NaN (Fallback disabled)", LogLevel.Information);
                        fallbackDisabledLogged = true;
                    }
                    LogNotReadyOnce("Target session out of range and fallback disabled");
                    return;
                }
            }
            else
            {
                LastUsedAnchorSessionIndex = targetSessionIndex;
                AnchorWasClamped = false;
                fallbackDisabledLogged = false;
            }

            EnsureBarInSessionAnchor(targetSessionIndex);
            UpdatePlotBrushes();

            if (anchorValid_byBar)
            {
                CalculateVWAPForBarAnchor();
                IsReady = true;
            }
            else
            {
                IsReady = false;
            }

            if (IsReady) { LogReadyOnce(); loggedNotReady = false; }
            else { LogNotReadyOnce("Anchor/values not ready"); }

            TryLogBarIfEnabled();
            DrawAnchorDotsAlways();
            DrawBandCloud();
        }

        private void TryLogBarIfEnabled()
        {
            try
            {
                if (!EnableBarLogging) return;
                if (Bars.BarsPeriod == null) return;
                if (Bars.BarsPeriod.BarsPeriodType != BarsPeriodType.Minute) return;
                if (Bars.BarsPeriod.Value != LogTimeframeMin) return;
                if (CurrentBar < 1) return;

                DateTime barLocalTime = Bars.GetTime(CurrentBar);
                DateTime tradingDay = sessionIterator.GetTradingDay(barLocalTime);
                string symbolSafe = Instrument.FullName.Replace(' ', '_').Replace('/', '_').Replace('\\', '_');
                string fileName = LogPerSessionFile
                    ? $"{symbolSafe}_{LogTimeframeMin}_{tradingDay:yyyyMMdd}.csv"
                    : $"{symbolSafe}_{LogTimeframeMin}_accum.csv";
                string filePath = string.IsNullOrEmpty(_logFolder) ? fileName : Path.Combine(_logFolder, fileName);

                bool fileExists = File.Exists(filePath);
                double vwapHigh = Values[0].Count > 0 ? Values[0][0] : double.NaN;
                double vwapMedian = Values[1].Count > 0 ? Values[1][0] : double.NaN;
                double vwapLow = Values[2].Count > 0 ? Values[2][0] : double.NaN;

                string barEndUtc = barLocalTime.ToUniversalTime().ToString("o", CultureInfo.InvariantCulture);
                string barEndLocal = barLocalTime.ToString("yyyy-MM-dd HH:mm", CultureInfo.InvariantCulture);
                string anchorBarTimeStr = (LastUsedAnchorTime > Core.Globals.MinDate) ? LastUsedAnchorTime.ToString("o", CultureInfo.InvariantCulture) : "";
                string line = string.Join(",",
                    QuoteIfNeeded(Instrument.FullName),
                    LogTimeframeMin.ToString(CultureInfo.InvariantCulture),
                    QuoteIfNeeded(barEndUtc),
                    QuoteIfNeeded(barEndLocal),
                    QuoteIfNeeded(tradingDay.ToString("yyyy-MM-dd")),
                    CurrentBar.ToString(CultureInfo.InvariantCulture),
                    Open[0].ToString("F5", CultureInfo.InvariantCulture),
                    High[0].ToString("F5", CultureInfo.InvariantCulture),
                    Low[0].ToString("F5", CultureInfo.InvariantCulture),
                    Close[0].ToString("F5", CultureInfo.InvariantCulture),
                    Volume[0].ToString(CultureInfo.InvariantCulture),
                    LastUsedAnchorSessionIndex.ToString(CultureInfo.InvariantCulture),
                    QuoteIfNeeded(anchorBarTimeStr),
                    vwapHigh.ToString("F5", CultureInfo.InvariantCulture),
                    vwapMedian.ToString("F5", CultureInfo.InvariantCulture),
                    vwapLow.ToString("F5", CultureInfo.InvariantCulture),
                    AnchorWasClamped ? "1" : "0",
                    LastRequestedTargetSessionIndex.ToString(CultureInfo.InvariantCulture)
                );

                try
                {
                    if (!string.IsNullOrEmpty(_logFolder))
                        Directory.CreateDirectory(_logFolder);

                    using (var sw = new StreamWriter(filePath, true, Encoding.UTF8))
                    {
                        if (!fileExists)
                        {
                            sw.WriteLine("symbol,timeframe,barEndUtc,barEndLocal,tradingDay,barIndexAbs,open,high,low,close,volume,anchorSessionIndex,anchorBarTime,vwapHigh,vwapMedian,vwapLow,anchorWasClamped,lastRequestedTargetSessionIndex");
                        }
                        sw.WriteLine(line);
                        sw.Flush();
                    }
                }
                catch (Exception ex)
                {
                    if (DebugMode) Log($"[AnchoredVWAP] Failed to write log {filePath}: {ex.Message}", LogLevel.Warning);
                }
            }
            catch (Exception ex) { if (DebugMode) Log($"[AnchoredVWAP] TryLogBarIfEnabled error: {ex.Message}", LogLevel.Error); }
        }

        private string QuoteIfNeeded(string s)
        {
            if (s == null) return "\"\"";
            if (s.Contains(",") || s.Contains("\"")) return "\"" + s.Replace("\"", "\"\"") + "\"";
            return s;
        }

        private void EnsureBarInSessionAnchor(int targetSessionIndex)
        {
            if (anchorSessionIndex == targetSessionIndex && anchorValid_byBar) return;
            anchorSessionIndex = targetSessionIndex;

            if (sessionStartIndices == null || sessionStartIndices.Count == 0) { anchorValid_byBar = false; return; }

            int sessionStart = sessionStartIndices[anchorSessionIndex];
            int sessionEnd = (anchorSessionIndex == sessionStartIndices.Count - 1) ? Bars.Count - 1 : sessionStartIndices[anchorSessionIndex + 1] - 1;
            int candidate = sessionStart + (BarInSession - 1);
            if (candidate > sessionEnd)
            {
                if (_useLastBarIfBarIndexTooLarge)
                    candidate = sessionEnd;
                else { anchorValid_byBar = false; return; }
            }
            if (candidate < 0 || candidate >= Bars.Count) { anchorValid_byBar = false; return; }

            anchorBarIndex_byBar = candidate;
            anchorValid_byBar = true;

            cumPV_Bar_High = cumV_Bar_High = cumPV_Bar_Median = cumV_Bar_Median = cumPV_Bar_Low = cumV_Bar_Low = 0;
            lastCumIndex_Bar = anchorBarIndex_byBar - 1;

            LastUsedAnchorSessionIndex = anchorSessionIndex;
            LastUsedAnchorTime = Bars.GetTime(anchorBarIndex_byBar);
        }

        private void CalculateVWAPForBarAnchor()
        {
            if (CurrentBar < anchorBarIndex_byBar) { Values[0][0] = Values[1][0] = Values[2][0] = double.NaN; return; }
            int start = Math.Max(lastCumIndex_Bar + 1, anchorBarIndex_byBar);
            int end = Math.Min(CurrentBar, Bars.Count - 1);
            for (int abs = start; abs <= end; abs++)
            {
                int barsAgo = CurrentBar - abs; if (barsAgo < 0 || barsAgo >= Bars.Count) continue;
                double vol = Math.Max(0.0, (double)Volume[barsAgo]);
                double pH = High[barsAgo], pM = (High[barsAgo] + Low[barsAgo]) / 2.0, pL = Low[barsAgo];
                cumPV_Bar_High += pH * vol; cumV_Bar_High += vol;
                cumPV_Bar_Median += pM * vol; cumV_Bar_Median += vol;
                cumPV_Bar_Low += pL * vol; cumV_Bar_Low += vol;
            }
            lastCumIndex_Bar = Math.Min(CurrentBar, Bars.Count - 1);
            Values[0][0] = (cumV_Bar_High > 1e-12) ? cumPV_Bar_High / cumV_Bar_High : double.NaN;
            Values[1][0] = (cumV_Bar_Median > 1e-12) ? cumPV_Bar_Median / cumV_Bar_Median : double.NaN;
            Values[2][0] = (cumV_Bar_Low > 1e-12) ? cumPV_Bar_Low / cumV_Bar_Low : double.NaN;
        }

        private void ClearAllValues()
        {
            for (int i = 0; i < 3; i++) Values[i][0] = double.NaN;
            IsReady = false;
        }

        private void DrawAnchorDotsAlways()
        {
            try
            {
                Brush bHigh = BarAnchorHighColor?.Clone(); bHigh?.Freeze();
                Brush bMed  = BarAnchorMedianColor?.Clone(); bMed?.Freeze();
                Brush bLow  = BarAnchorLowColor?.Clone(); bLow?.Freeze();

                if (anchorValid_byBar && anchorBarIndex_byBar >= 0 && anchorBarIndex_byBar < Bars.Count)
                {
                    DateTime t = Bars.GetTime(anchorBarIndex_byBar);
                    int barsAgo = CurrentBar - anchorBarIndex_byBar;
                    if (barsAgo >= 0 && barsAgo < Bars.Count)
                    {
                        Draw.Dot(this, "BARANCH_H_" + anchorBarIndex_byBar, false, t, High[barsAgo], bHigh ?? Brushes.DimGray);
                        Draw.Dot(this, "BARANCH_M_" + anchorBarIndex_byBar, false, t, (High[barsAgo] + Low[barsAgo]) / 2.0, bMed ?? Brushes.White);
                        Draw.Dot(this, "BARANCH_L_" + anchorBarIndex_byBar, false, t, Low[barsAgo], bLow ?? Brushes.DimGray);
                    }
                }
            }
            catch (Exception ex) { if (DebugMode) Log($"[AnchoredVWAP] Draw dots error: {ex.Message}", LogLevel.Error); }
        }

        private void DrawBandCloud()
        {
            try
            {
                if (!EnableBandCloud) return;
                if (!IsReady) return;
                if (double.IsNaN(Values[0][0]) || double.IsNaN(Values[2][0])) return;

                var baseBrush = BandCloudBrush ?? new SolidColorBrush(Color.FromArgb(51, 128, 128, 128));
                Brush area = baseBrush;
                if (baseBrush.CanFreeze) area = baseBrush.Clone();
                byte alpha = (byte)Math.Max(0, Math.Min(255, (int)Math.Round(255.0 * (Math.Max(0.0, Math.Min(100.0, BandCloudOpacity)) / 100.0))));
                if (area is SolidColorBrush scb)
                {
                    area = new SolidColorBrush(Color.FromArgb(alpha, scb.Color.R, scb.Color.G, scb.Color.B));
                    area.Freeze();
                }
                else
                {
                    area.Freeze();
                }

                // startBarsAgo = CurrentBar (toda série), endBarsAgo = 0 (barra atual); areaOpacity=100 para não zerar a área
                Draw.Region(this, "VWAP_BandCloud", CurrentBar, 0, Values[0], Values[2], Brushes.Transparent, area, 100);
            }
            catch (Exception ex) { if (DebugMode) Log($"[AnchoredVWAP] DrawBandCloud error: {ex.Message}", LogLevel.Error); }
        }

        private void BuildSessionStarts()
        {
            sessionStartIndices.Clear();
            if (sessionIterator == null) sessionIterator = new SessionIterator(Bars);
            if (Bars.Count == 0) return;

            DateTime lastDay = Core.Globals.MinDate;
            for (int i = 0; i < Bars.Count; i++)
            {
                DateTime td = sessionIterator.GetTradingDay(Bars.GetTime(i));
                if (td != lastDay) { sessionStartIndices.Add(i); lastDay = td; }
            }
            sessionStartsBuilt = true;
        }

        private int GetSessionIndexContainingBar(int barIndex)
        {
            if (sessionStartIndices == null || sessionStartIndices.Count == 0) return -1;
            for (int s = sessionStartIndices.Count - 1; s >= 0; s--) if (sessionStartIndices[s] <= barIndex) return s;
            return -1;
        }

        private void UpdatePlotBrushes()
        {
            try
            {
                if (Plots == null || Plots.Length < 3) return;
            }
            catch (Exception ex) { if (DebugMode) Log($"[AnchoredVWAP] UpdatePlotBrushes error: {ex.Message}", LogLevel.Error); }
        }

        private void LogReadyOnce()
        {
            if (!DebugMode) return;
            if (!loggedReady)
            {
                Log("[AnchoredVWAP] Ready: anchor valid and values computed", LogLevel.Information);
                loggedReady = true;
            }
        }

        private void LogNotReadyOnce(string reason)
        {
            if (!DebugMode) return;
            if (!loggedNotReady)
            {
                Log($"[AnchoredVWAP] Not ready: {reason}", LogLevel.Information);
                loggedNotReady = true;
            }
        }

        #region Properties
        [NinjaScriptProperty] public int SessionOffset { get => _sessionOffset; set => _sessionOffset = value; }
        [NinjaScriptProperty] public int BarInSession { get => _barInSession; set => _barInSession = Math.Max(1, value); }
        [NinjaScriptProperty] public bool UseLastBarIfBarIndexTooLarge { get => _useLastBarIfBarIndexTooLarge; set => _useLastBarIfBarIndexTooLarge = value; }
        [NinjaScriptProperty] public bool PlotOnlyNextSession { get => _plotOnlyNextSession; set => _plotOnlyNextSession = value; }
        [NinjaScriptProperty] public bool DebugMode { get => _debugMode; set => _debugMode = value; }
        [NinjaScriptProperty] public bool AnchorBySessionHighLow { get => _anchorBySessionHighLow; set => _anchorBySessionHighLow = value; } // compat
        [NinjaScriptProperty] public bool FallbackToNearestSession { get => _fallbackToNearestSession; set => _fallbackToNearestSession = value; }
        [NinjaScriptProperty] public bool EnableBarLogging { get => _enableBarLogging; set => _enableBarLogging = value; }
        [NinjaScriptProperty] public int LogTimeframeMin { get => _logTimeframeMin; set => _logTimeframeMin = Math.Max(1, value); }
        [NinjaScriptProperty] public string LogFolder { get => _logFolder; set => _logFolder = value; }
        [NinjaScriptProperty] public bool LogPerSessionFile { get => _logPerSessionFile; set => _logPerSessionFile = value; }

        [NinjaScriptProperty]
        [Display(Name = "Enable Band Cloud", GroupName = "Visual", Order = 900)]
        public bool EnableBandCloud { get => _enableBandCloud; set => _enableBandCloud = value; }

        [NinjaScriptProperty]
        [Display(Name = "Band Cloud Opacity (%)", GroupName = "Visual", Order = 905)]
        public double BandCloudOpacity
        {
            get => _bandCloudOpacity;
            set => _bandCloudOpacity = Math.Max(0.0, Math.Min(100.0, value));
        }

        [XmlIgnore]
        [Display(Name = "Band Cloud Brush", GroupName = "Visual", Order = 910)]
        public Brush BandCloudBrush
        {
            get => _bandCloudBrush;
            set
            {
                _bandCloudBrush = value;
                _bandCloudBrushSerializable = (string)new BrushConverter().ConvertToString(value);
                UpdatePlotBrushes();
            }
        }

        [Browsable(false)]
        public string BandCloudBrushSerializable
        {
            get => _bandCloudBrushSerializable;
            set
            {
                _bandCloudBrushSerializable = value;
                try { _bandCloudBrush = (Brush)new BrushConverter().ConvertFromString(value); }
                catch { _bandCloudBrush = new SolidColorBrush(Color.FromArgb(51, 128, 128, 128)); }
            }
        }

        [XmlIgnore] public Brush BarAnchorHighColor { get => _barAnchorHighBrush; set { _barAnchorHighBrush = value; UpdatePlotBrushes(); } }
        [Browsable(false)] public string BarAnchorHighColorSerializable { get => (string)new BrushConverter().ConvertToString(BarAnchorHighColor); set => BarAnchorHighColor = (Brush)new BrushConverter().ConvertFromString(value); }
        [XmlIgnore] public Brush BarAnchorMedianColor { get => _barAnchorMedianBrush; set { _barAnchorMedianBrush = value; UpdatePlotBrushes(); } }
        [Browsable(false)] public string BarAnchorMedianColorSerializable { get => (string)new BrushConverter().ConvertToString(BarAnchorMedianColor); set => BarAnchorMedianColor = (Brush)new BrushConverter().ConvertFromString(value); }
        [XmlIgnore] public Brush BarAnchorLowColor { get => _barAnchorLowBrush; set { _barAnchorLowBrush = value; UpdatePlotBrushes(); } }
        [Browsable(false)] public string BarAnchorLowColorSerializable { get => (string)new BrushConverter().ConvertToString(BarAnchorLowColor); set => BarAnchorLowColor = (Brush)new BrushConverter().ConvertFromString(value); }
        #endregion
    }
}

#region NinjaScript generated code. Neither change nor remove.

namespace NinjaTrader.NinjaScript.Indicators
{
	public partial class Indicator : NinjaTrader.Gui.NinjaScript.IndicatorRenderBase
	{
		private AnchoredMidasIndicator[] cacheAnchoredMidasIndicator;
		public AnchoredMidasIndicator AnchoredMidasIndicator(int sessionOffset, int barInSession, bool useLastBarIfBarIndexTooLarge, bool plotOnlyNextSession, bool debugMode, bool anchorBySessionHighLow, bool fallbackToNearestSession, bool enableBarLogging, int logTimeframeMin, string logFolder, bool logPerSessionFile, bool enableBandCloud, double bandCloudOpacity)
		{
			return AnchoredMidasIndicator(Input, sessionOffset, barInSession, useLastBarIfBarIndexTooLarge, plotOnlyNextSession, debugMode, anchorBySessionHighLow, fallbackToNearestSession, enableBarLogging, logTimeframeMin, logFolder, logPerSessionFile, enableBandCloud, bandCloudOpacity);
		}

		public AnchoredMidasIndicator AnchoredMidasIndicator(ISeries<double> input, int sessionOffset, int barInSession, bool useLastBarIfBarIndexTooLarge, bool plotOnlyNextSession, bool debugMode, bool anchorBySessionHighLow, bool fallbackToNearestSession, bool enableBarLogging, int logTimeframeMin, string logFolder, bool logPerSessionFile, bool enableBandCloud, double bandCloudOpacity)
		{
			if (cacheAnchoredMidasIndicator != null)
				for (int idx = 0; idx < cacheAnchoredMidasIndicator.Length; idx++)
					if (cacheAnchoredMidasIndicator[idx] != null && cacheAnchoredMidasIndicator[idx].SessionOffset == sessionOffset && cacheAnchoredMidasIndicator[idx].BarInSession == barInSession && cacheAnchoredMidasIndicator[idx].UseLastBarIfBarIndexTooLarge == useLastBarIfBarIndexTooLarge && cacheAnchoredMidasIndicator[idx].PlotOnlyNextSession == plotOnlyNextSession && cacheAnchoredMidasIndicator[idx].DebugMode == debugMode && cacheAnchoredMidasIndicator[idx].AnchorBySessionHighLow == anchorBySessionHighLow && cacheAnchoredMidasIndicator[idx].FallbackToNearestSession == fallbackToNearestSession && cacheAnchoredMidasIndicator[idx].EnableBarLogging == enableBarLogging && cacheAnchoredMidasIndicator[idx].LogTimeframeMin == logTimeframeMin && cacheAnchoredMidasIndicator[idx].LogFolder == logFolder && cacheAnchoredMidasIndicator[idx].LogPerSessionFile == logPerSessionFile && cacheAnchoredMidasIndicator[idx].EnableBandCloud == enableBandCloud && cacheAnchoredMidasIndicator[idx].BandCloudOpacity == bandCloudOpacity && cacheAnchoredMidasIndicator[idx].EqualsInput(input))
						return cacheAnchoredMidasIndicator[idx];
			return CacheIndicator<AnchoredMidasIndicator>(new AnchoredMidasIndicator(){ SessionOffset = sessionOffset, BarInSession = barInSession, UseLastBarIfBarIndexTooLarge = useLastBarIfBarIndexTooLarge, PlotOnlyNextSession = plotOnlyNextSession, DebugMode = debugMode, AnchorBySessionHighLow = anchorBySessionHighLow, FallbackToNearestSession = fallbackToNearestSession, EnableBarLogging = enableBarLogging, LogTimeframeMin = logTimeframeMin, LogFolder = logFolder, LogPerSessionFile = logPerSessionFile, EnableBandCloud = enableBandCloud, BandCloudOpacity = bandCloudOpacity }, input, ref cacheAnchoredMidasIndicator);
		}
	}
}

namespace NinjaTrader.NinjaScript.MarketAnalyzerColumns
{
	public partial class MarketAnalyzerColumn : MarketAnalyzerColumnBase
	{
		public Indicators.AnchoredMidasIndicator AnchoredMidasIndicator(int sessionOffset, int barInSession, bool useLastBarIfBarIndexTooLarge, bool plotOnlyNextSession, bool debugMode, bool anchorBySessionHighLow, bool fallbackToNearestSession, bool enableBarLogging, int logTimeframeMin, string logFolder, bool logPerSessionFile, bool enableBandCloud, double bandCloudOpacity)
		{
			return indicator.AnchoredMidasIndicator(Input, sessionOffset, barInSession, useLastBarIfBarIndexTooLarge, plotOnlyNextSession, debugMode, anchorBySessionHighLow, fallbackToNearestSession, enableBarLogging, logTimeframeMin, logFolder, logPerSessionFile, enableBandCloud, bandCloudOpacity);
		}

		public Indicators.AnchoredMidasIndicator AnchoredMidasIndicator(ISeries<double> input , int sessionOffset, int barInSession, bool useLastBarIfBarIndexTooLarge, bool plotOnlyNextSession, bool debugMode, bool anchorBySessionHighLow, bool fallbackToNearestSession, bool enableBarLogging, int logTimeframeMin, string logFolder, bool logPerSessionFile, bool enableBandCloud, double bandCloudOpacity)
		{
			return indicator.AnchoredMidasIndicator(input, sessionOffset, barInSession, useLastBarIfBarIndexTooLarge, plotOnlyNextSession, debugMode, anchorBySessionHighLow, fallbackToNearestSession, enableBarLogging, logTimeframeMin, logFolder, logPerSessionFile, enableBandCloud, bandCloudOpacity);
		}
	}
}

namespace NinjaTrader.NinjaScript.Strategies
{
	public partial class Strategy : NinjaTrader.Gui.NinjaScript.StrategyRenderBase
	{
		public Indicators.AnchoredMidasIndicator AnchoredMidasIndicator(int sessionOffset, int barInSession, bool useLastBarIfBarIndexTooLarge, bool plotOnlyNextSession, bool debugMode, bool anchorBySessionHighLow, bool fallbackToNearestSession, bool enableBarLogging, int logTimeframeMin, string logFolder, bool logPerSessionFile, bool enableBandCloud, double bandCloudOpacity)
		{
			return indicator.AnchoredMidasIndicator(Input, sessionOffset, barInSession, useLastBarIfBarIndexTooLarge, plotOnlyNextSession, debugMode, anchorBySessionHighLow, fallbackToNearestSession, enableBarLogging, logTimeframeMin, logFolder, logPerSessionFile, enableBandCloud, bandCloudOpacity);
		}

		public Indicators.AnchoredMidasIndicator AnchoredMidasIndicator(ISeries<double> input , int sessionOffset, int barInSession, bool useLastBarIfBarIndexTooLarge, bool plotOnlyNextSession, bool debugMode, bool anchorBySessionHighLow, bool fallbackToNearestSession, bool enableBarLogging, int logTimeframeMin, string logFolder, bool logPerSessionFile, bool enableBandCloud, double bandCloudOpacity)
		{
			return indicator.AnchoredMidasIndicator(input, sessionOffset, barInSession, useLastBarIfBarIndexTooLarge, plotOnlyNextSession, debugMode, anchorBySessionHighLow, fallbackToNearestSession, enableBarLogging, logTimeframeMin, logFolder, logPerSessionFile, enableBandCloud, bandCloudOpacity);
		}
	}
}

#endregion
