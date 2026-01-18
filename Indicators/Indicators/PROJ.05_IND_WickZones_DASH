// WickZonesIndicator_v46_intrabar60_full.cs
// v46 (complete) + intrabar-on-60m detection + commit-on-close
// - Uses 60-minute bars as the single source of truth (no 5m series).
// - Detects intrabar touches (any price during the 60m candle crosses the zone) on each tick.
// - Commits the touch at the 60m close: marks UsedDateBuy/UsedDateSell according to ST direction and v46 rules (WaitingOpposite, reactivatedThisFlip).
// - Adds RectInfo.LastCommittedDate to avoid double commits.
// - Adds in-memory intrabar registry per 60m bar to record touched tags and running high/low.
// - Does not remove or modify existing v46 business logic — only adds the minimum required.
// IMPORTANT: Replace your existing WickZonesIndicator (v46) with this file and compile. EnableLogging = true recommended for testing.
//
// NOTE: This file is intentionally complete and self-contained. Do not truncate when copying to NinjaScript Editor.

using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.IO;
using System.Windows.Media;
using System.Xml.Serialization;
using NinjaTrader.Gui.Tools;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.DrawingTools;
using NinjaTrader.Data;
using NinjaTrader.Gui.Chart;

namespace NinjaTrader.NinjaScript.Indicators
{
    public enum ZoneDirection { Neutral = 0, Buy = 1, Sell = 2 }
    internal enum DrawModes { Rectangle = 0, Rays = 1 }

    public class WickZonesIndicator : Indicator
    {
        #region Configuráveis (inclui ST params + auto mark + debug)
        [NinjaScriptProperty][Range(1,int.MaxValue)][Display(Name="TimeFrameMinutes (padrão 60)", Order=1, GroupName="Config")] public int TimeFrameMinutes { get; set; }
        [NinjaScriptProperty][Range(1,int.MaxValue)][Display(Name="Threshold 1 (ticks)", Order=2, GroupName="Thresholds")] public int Th1 { get; set; }
        [NinjaScriptProperty][Range(1,int.MaxValue)][Display(Name="Threshold 2 (ticks)", Order=3, GroupName="Thresholds")] public int Th2 { get; set; }
        [NinjaScriptProperty][Range(1,int.MaxValue)][Display(Name="Threshold 3 (ticks)", Order=4, GroupName="Thresholds")] public int Th3 { get; set; }

        [NinjaScriptProperty][Range(1,5000)][Display(Name="Max Rectangles", Order=5, GroupName="Config")] public int MaxRectangles { get; set; }

        [NinjaScriptProperty][Range(0,100)][Display(Name="Fill Transparency (%)", Order=6, GroupName="Appearance")] public int FillTransparency { get; set; }
        [NinjaScriptProperty][Range(0,100)][Display(Name="Border Transparency (%)", Order=7, GroupName="Appearance")] public int BorderTransparency { get; set; }

        [NinjaScriptProperty][XmlIgnore][Display(Name="Fill Color - Threshold 1", Order=8, GroupName="Appearance")]
        public Brush FillColorTick1
        {
            get { try { if (!string.IsNullOrEmpty(FillColorTick1Hex)) { var c = (Color)ColorConverter.ConvertFromString(FillColorTick1Hex); var b = new SolidColorBrush(c); b.Freeze(); return b; } } catch { } return new SolidColorBrush(Colors.DimGray); }
            set { if (value is SolidColorBrush scb) FillColorTick1Hex = ColorToHex(scb.Color); else FillColorTick1Hex = null; UpdateBrushesIfNeeded(force:true); }
        }

        [NinjaScriptProperty][XmlIgnore][Display(Name="Fill Color - Threshold 2", Order=9, GroupName="Appearance")]
        public Brush FillColorTick2
        {
            get { try { if (!string.IsNullOrEmpty(FillColorTick2Hex)) { var c = (Color)ColorConverter.ConvertFromString(FillColorTick2Hex); var b = new SolidColorBrush(c); b.Freeze(); return b; } } catch { } return new SolidColorBrush(Color.FromRgb(184,134,11)); }
            set { if (value is SolidColorBrush scb) FillColorTick2Hex = ColorToHex(scb.Color); else FillColorTick2Hex = null; UpdateBrushesIfNeeded(force:true); }
        }

        [NinjaScriptProperty][XmlIgnore][Display(Name="Fill Color - Threshold 3", Order=10, GroupName="Appearance")]
        public Brush FillColorTick3
        {
            get { try { if (!string.IsNullOrEmpty(FillColorTick3Hex)) { var c = (Color)ColorConverter.ConvertFromString(FillColorTick3Hex); var b = new SolidColorBrush(c); b.Freeze(); return b; } } catch { } return new SolidColorBrush(Colors.Maroon); }
            set { if (value is SolidColorBrush scb) FillColorTick3Hex = ColorToHex(scb.Color); else FillColorTick3Hex = null; UpdateBrushesIfNeeded(force:true); }
        }

        [Browsable(false)] public string FillColorTick1Hex { get; set; }
        [Browsable(false)] public string FillColorTick2Hex { get; set; }
        [Browsable(false)] public string FillColorTick3Hex { get; set; }

        [NinjaScriptProperty][Range(0,100)][Display(Name="SessionsBack", Order=11, GroupName="Behavior")] public int SessionsBack { get; set; }
        [NinjaScriptProperty][Display(Name="ExtendToRight", Order=12, GroupName="Behavior")] public bool ExtendToRight { get; set; }
        [NinjaScriptProperty][Range(0,10)][Display(Name="ExtendYears", Order=13, GroupName="Behavior")] public int ExtendYears { get; set; }

        [NinjaScriptProperty][Display(Name="DrawHistorical", Order=14, GroupName="Behavior")] public bool DrawHistorical { get; set; }
        [NinjaScriptProperty][Display(Name="EnableLogging", Order=15, GroupName="Behavior")] public bool EnableLogging { get; set; }
        [NinjaScriptProperty][Display(Name="SingleWickPerBar", Order=16, GroupName="Behavior")] public bool SingleWickPerBar { get; set; }

        [NinjaScriptProperty][Display(Name="Render", Order=17, GroupName="Behavior")] public bool Render { get; set; }
        [NinjaScriptProperty][Display(Name="ForStrategy", Order=18, GroupName="Behavior")] public bool ForStrategy { get; set; }

        [NinjaScriptProperty][Range(0,1)][Display(Name="Draw Mode (0=Rectangle,1=Rays)", Order=19, GroupName="Behavior")] public int DrawModeValue { get; set; }
        [NinjaScriptProperty][Range(1,8)][Display(Name="Line Thickness (px) for Rays", Order=20, GroupName="Behavior")] public int LineThickness { get; set; }
        [NinjaScriptProperty][Range(0,10)][Display(Name="Marker Duration Minutes", Order=21, GroupName="Behavior")] public int MarkerDurationMinutes { get; set; }

        // Minimal ST params exposed
        [NinjaScriptProperty][Range(1, 500)][Display(Name="ST Length (internal)", Order=22, GroupName="ST")] public int STLength { get; set; }
        [NinjaScriptProperty][Range(0.1, 10.0)][Display(Name="ST Multiplier (internal)", Order=23, GroupName="ST")] public double STMultiplier { get; set; }

        // Auto-mark props
        [NinjaScriptProperty][Display(Name="AutoMarkByST (auto marca UsedDate por direção ST)", Order=24, GroupName="Behavior")]
        public bool AutoMarkByST { get; set; }

        [NinjaScriptProperty][Display(Name="RequireTouchConfirmation (exige confirmação candle seguinte)", Order=25, GroupName="Behavior")]
        public bool RequireTouchConfirmation { get; set; }

        // Debug dump to file
        [NinjaScriptProperty][Display(Name="DebugDumpToFile (grava CSV de diagnóstico)", Order=26, GroupName="Debug")]
        public bool DebugDumpToFile { get; set; }

        [NinjaScriptProperty][Display(Name="DebugDumpFilePath", Order=27, GroupName="Debug")]
        public string DebugDumpFilePath { get; set; }
        #endregion

        // brushes and cache
        private SolidColorBrush fillBrush1, fillBrush2, fillBrush3;
        private SolidColorBrush borderBrush1, borderBrush2, borderBrush3;
        private LinearGradientBrush zoneGradientBrush;

        private string lastFillHex1="", lastFillHex2="", lastFillHex3="";
        private int lastFillTransparency=-1, lastBorderTransparency=-1, lastSessionsBack=-1;

        private List<string> rectTags;
        private List<RectInfo> rectInfos;
        private int rectCounter;

        private struct RectInfo
        {
            public string Tag;
            public DateTime Start;
            public DateTime End;
            public double Top;
            public double Bottom;
            public int ThresholdLevel;
            public string LogicTag;
            public int WickTicks;

            // metadata
            public ZoneDirection Direction;
            public DateTime SessionDate;
            public DateTime? UsedDateBuy;
            public DateTime? UsedDateSell;
            public bool InvalidForFuture;
            public bool TouchedInPreMarket;

            // v45/v46 additions
            public bool WaitingOpposite;       // true if zone used one side and waiting for ST flip to allow opposite use
            public ZoneDirection LastUsedSide; // which side was used last (Buy/Sell) when WaitingOpposite==true

            // NEW minimal field to avoid duplicate commits for same bar close
            public DateTime? LastCommittedDate;
        }

        private HashSet<DateTime> processedBars;
        private bool realtimeStarted = false;
        private DateTime allowedStartDate = DateTime.MinValue;

        private Series<double> zoneTop, zoneBottom, zoneLevel;

        // touch detection defaults (internal)
        private TimeSpan touchWindowEnd = new TimeSpan(9,55,0);
        private TimeSpan touchWindowStartTimeOfDay = new TimeSpan(20,0,0);
        private DateTime lastTouchProcessedDate = DateTime.MinValue;

        // internal SuperTrend instance and state
        private TSSuperTrend stIndicator = null;
        private ZoneDirection lastSTDirection = ZoneDirection.Neutral;

        // pending confirmations for RequireTouchConfirmation
        private class PendingConfirmation { public string Tag; public ZoneDirection ExpectedDir; public DateTime DetectedTime; public int ZoneIndex; }
        private List<PendingConfirmation> pendingConfirmations;

        // reactivated tags by the most recent flip (strict policy)
        private HashSet<string> reactivatedThisFlip;

        // ------------------ Intrabar registry (per 60m bar) ------------------
        // Stores per-bar running high/low and set of tags touched intrabar.
        private class BarTouchInfo
        {
            public DateTime BarStart;
            public double High = double.MinValue;
            public double Low = double.MaxValue;
            public HashSet<string> TouchedTags = new HashSet<string>(StringComparer.Ordinal);
        }
        private Dictionary<DateTime, BarTouchInfo> intrabarTouches;
        private DateTime prevBarStart = DateTime.MinValue;
        // --------------------------------------------------------------------

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Name = "WickZonesIndicator";
                Description = "WickZonesIndicator NT8 — v46 with intrabar 60m detection (commit on close).";
                // IMPORTANT: to detect intrabar ticks on 60m, we need OnEachTick
                Calculate = Calculate.OnEachTick;

                IsOverlay = true;
                DisplayInDataBox = true;

                TimeFrameMinutes = 60;
                Th1 = 150; Th2 = 200; Th3 = 300; MaxRectangles = 500;

                FillColorTick1Hex = "#FF696969";
                FillColorTick2Hex = "#FFB8860B";
                FillColorTick3Hex = "#FF800000";

                FillTransparency = 85; BorderTransparency = 70;
                SessionsBack = 0; ExtendToRight = true; ExtendYears = 1;
                DrawHistorical = false; EnableLogging = false; SingleWickPerBar = true;

                Render = true; ForStrategy = false;

                DrawModeValue = (int)DrawModes.Rays;
                LineThickness = 2;
                MarkerDurationMinutes = 2;

                STLength = 14;
                STMultiplier = 2.618;

                AutoMarkByST = true;
                RequireTouchConfirmation = false;

                DebugDumpToFile = false;
                DebugDumpFilePath = Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments) + "\\WickZones_Debug.csv";

                rectCounter = 0;
                rectTags = new List<string>();
                rectInfos = new List<RectInfo>();
                intrabarTouches = new Dictionary<DateTime, BarTouchInfo>();
                processedBars = new HashSet<DateTime>();
                pendingConfirmations = new List<PendingConfirmation>();
                reactivatedThisFlip = new HashSet<string>();
                prevBarStart = DateTime.MinValue;
            }
            else if (State == State.Configure)
            {
                if (TimeFrameMinutes < 1) throw new ArgumentException("TimeFrameMinutes deve ser >= 1");

                if (!ForStrategy)
                    AddDataSeries(BarsPeriodType.Minute, TimeFrameMinutes);

                zoneTop = new Series<double>(this);
                zoneBottom = new Series<double>(this);
                zoneLevel = new Series<double>(this);
            }
            else if (State == State.DataLoaded)
            {
                UpdateBrushesIfNeeded(force:true);
                RecalculateAllowedStartDate();

                zoneGradientBrush = new LinearGradientBrush(new GradientStopCollection {
                    new GradientStop(Color.FromRgb(80,80,80), 0.0),
                    new GradientStop(Color.FromRgb(48,48,48), 1.0)
                }, 90.0);

                try
                {
                    int stIndex = GetWickBarsArrayIndex();
                    if (stIndex >= 0)
                    {
                        stIndicator = TSSuperTrend(Input, SuperTrendMode.ATR, STLength, STMultiplier, MovingAverageType.HMA, 14, false, false, false);
                        if (EnableLogging) Print("WZ INFO Created internal ST instance.");
                    }
                }
                catch { stIndicator = null; if (EnableLogging) Print("WZ WARN Could not instantiate internal ST (wrapper call failed)."); }

                rectTags = rectTags ?? new List<string>();
                rectInfos = rectInfos ?? new List<RectInfo>();
                intrabarTouches = intrabarTouches ?? new Dictionary<DateTime, BarTouchInfo>();
                lastTouchProcessedDate = DateTime.MinValue;
                pendingConfirmations = pendingConfirmations ?? new List<PendingConfirmation>();
                reactivatedThisFlip = reactivatedThisFlip ?? new HashSet<string>();

                // Initialize debug file if needed
                try
                {
                    if (DebugDumpToFile)
                    {
                        var header = "Time,Event,Tag,SessionDate,Top,Bottom,TouchedInPreMarket,UsedDateBuy,UsedDateSell,WaitingOpposite,LastUsedSide,Additional";
                        File.WriteAllText(DebugDumpFilePath, header + Environment.NewLine);
                        if (EnableLogging) Print($"WZ INFO DebugDumpToFile enabled: {DebugDumpFilePath}");
                    }
                }
                catch (Exception ex)
                {
                    if (EnableLogging) Print($"WZ WARN Could not initialize debug dump file: {ex.Message}");
                }
            }
            else if (State == State.Realtime)
            {
                realtimeStarted = true;
                RecalculateAllowedStartDate();
            }
        }

        // ---------------- Helper methods ----------------

        private string ColorToHex(Color c) => $"#{c.A:X2}{c.R:X2}{c.G:X2}{c.B:X2}";

        private Color SafeColorFromHex(string hex, Color fallback) { try { if (!string.IsNullOrEmpty(hex)) return (Color)ColorConverter.ConvertFromString(hex); } catch { } return fallback; }

        private SolidColorBrush MakeBrushFromColorWithAlpha(Color baseColor, byte alpha) { var colorWithAlpha = Color.FromArgb(alpha, baseColor.R, baseColor.G, baseColor.B); var brush = new SolidColorBrush(colorWithAlpha); brush.Freeze(); return brush; }

        private SolidColorBrush MakeDarkerBorderFromColorWithAlpha(Color baseColor, byte alpha) { byte r = (byte)Math.Round(baseColor.R * 0.75); byte g = (byte)Math.Round(baseColor.G * 0.75); byte b = (byte)Math.Round(baseColor.B * 0.75); var color = Color.FromArgb(alpha, r, g, b); var brush = new SolidColorBrush(color); brush.Freeze(); return brush; }

        private void UpdateBrushesIfNeeded(bool force = false)
        {
            string hex1 = FillColorTick1Hex ?? "";
            string hex2 = FillColorTick2Hex ?? "";
            string hex3 = FillColorTick3Hex ?? "";

            if (force || hex1 != lastFillHex1 || hex2 != lastFillHex2 || hex3 != lastFillHex3
                || FillTransparency != lastFillTransparency || BorderTransparency != lastBorderTransparency
                || SessionsBack != lastSessionsBack)
            {
                lastFillHex1 = hex1; lastFillHex2 = hex2; lastFillHex3 = hex3;
                lastFillTransparency = FillTransparency;
                lastBorderTransparency = BorderTransparency;
                lastSessionsBack = SessionsBack;

                RecalculateAllowedStartDate();

                Color c1 = SafeColorFromHex(hex1, Colors.DimGray);
                Color c2 = SafeColorFromHex(hex2, Color.FromRgb(184, 134, 11));
                Color c3 = SafeColorFromHex(hex3, Colors.Maroon);

                byte alphaFill = (byte)Math.Round(255.0 * (100 - Math.Max(0, Math.Min(100, FillTransparency))) / 100.0);
                byte alphaBorder = (byte)Math.Round(255.0 * (100 - Math.Max(0, Math.Min(100, BorderTransparency))) / 100.0);

                fillBrush1 = MakeBrushFromColorWithAlpha(c1, alphaFill);
                fillBrush2 = MakeBrushFromColorWithAlpha(c2, alphaFill);
                fillBrush3 = MakeBrushFromColorWithAlpha(c3, alphaFill);

                borderBrush1 = MakeDarkerBorderFromColorWithAlpha(c1, alphaBorder);
                borderBrush2 = MakeDarkerBorderFromColorWithAlpha(c2, alphaBorder);
                borderBrush3 = MakeDarkerBorderFromColorWithAlpha(c3, alphaBorder);

                if (Render && rectInfos != null && rectInfos.Count > 0)
                {
                    for (int i = 0; i < rectInfos.Count; i++)
                    {
                        var ri = rectInfos[i];
                        try { RemoveDrawObject(ri.Tag + "_TOP"); } catch { }
                        try { RemoveDrawObject(ri.Tag + "_BOT"); } catch { }
                        try { RemoveDrawObject(ri.Tag + "_MARK_TOP"); } catch { }
                        try { RemoveDrawObject(ri.Tag + "_MARK_BOT"); } catch { }
                        try { RemoveDrawObject(ri.Tag); } catch { }

                        if ((DrawModes)DrawModeValue == DrawModes.Rectangle)
                        {
                            SolidColorBrush useFill = (ri.ThresholdLevel == 3) ? fillBrush3 : (ri.ThresholdLevel == 2 ? fillBrush2 : fillBrush1);
                            SolidColorBrush useBorder = (ri.ThresholdLevel == 3) ? borderBrush3 : (ri.ThresholdLevel == 2 ? borderBrush2 : borderBrush1);
                            try { Draw.Rectangle(this, ri.Tag, true, ri.Start, ri.Top, ri.End, ri.Bottom, useBorder, useFill, 1); } catch { }
                        }
                        else
                        {
                            Brush drawBrush = ri.TouchedInPreMarket ? (Brush)zoneGradientBrush : (Brush)((ri.ThresholdLevel == 3) ? borderBrush3 : (ri.ThresholdLevel == 2 ? borderBrush2 : borderBrush1));
                            DateTime endTime = (ExtendToRight && ExtendYears > 0) ? ri.Start.AddYears(ExtendYears) : ri.End;
                            double lineHeight = Math.Max(Instrument.MasterInstrument.TickSize * 0.05, Instrument.MasterInstrument.TickSize * 0.5);

                            double topRectTop = ri.Top;
                            double topRectBottom = ri.Top - lineHeight;
                            try { Draw.Rectangle(this, ri.Tag + "_TOP", true, ri.Start, topRectTop, endTime, topRectBottom, drawBrush, Brushes.Transparent, LineThickness); } catch { }

                            double botRectTop = ri.Bottom + lineHeight;
                            double botRectBottom = ri.Bottom;
                            try { Draw.Rectangle(this, ri.Tag + "_BOT", true, ri.Start, botRectTop, endTime, botRectBottom, drawBrush, Brushes.Transparent, LineThickness); } catch { }

                            try
                            {
                                DateTime markEnd = ri.Start.AddMinutes(Math.Max(1, MarkerDurationMinutes));
                                double tick = Instrument.MasterInstrument.TickSize;
                                double markerHalfHeight = Math.Max(tick * 1.0, tick * 2.0);

                                double topMarkerTop = ri.Top + markerHalfHeight;
                                double topMarkerBottom = ri.Top - markerHalfHeight;
                                Draw.Ellipse(this, ri.Tag + "_MARK_TOP", true, ri.Start, topMarkerTop, markEnd, topMarkerBottom, drawBrush, drawBrush, 0);

                                double botMarkerTop = ri.Bottom + markerHalfHeight;
                                double botMarkerBottom = ri.Bottom - markerHalfHeight;
                                Draw.Ellipse(this, ri.Tag + "_MARK_BOT", true, ri.Start, botMarkerTop, markEnd, botMarkerBottom, drawBrush, drawBrush, 0);
                            }
                            catch { }
                        }
                    }
                }
            }
        }

        private void AppendDebugLine(string evt, RectInfo ri, string additional = "")
        {
            string line = $"{DateTime.UtcNow:O},{evt},{ri.Tag},{ri.SessionDate:yyyy-MM-dd},{ri.Top:F2},{ri.Bottom:F2},{ri.TouchedInPreMarket},{(ri.UsedDateBuy.HasValue?ri.UsedDateBuy.Value.ToString("yyyy-MM-dd"):"")},{(ri.UsedDateSell.HasValue?ri.UsedDateSell.Value.ToString("yyyy-MM-dd"):"")},{ri.WaitingOpposite},{ri.LastUsedSide},{additional}";
            try
            {
                if (DebugDumpToFile)
                {
                    File.AppendAllText(DebugDumpFilePath, line + Environment.NewLine);
                }
            }
            catch (Exception ex)
            {
                if (EnableLogging) Print($"WZ WARN DebugDump append failed: {ex.Message}");
            }
            if (EnableLogging) Print($"WZ DEBUG {line}");
        }

        private int GetWickBarsArrayIndex()
        {
            if (ForStrategy) return 0;
            if (BarsArray == null) return -1;
            for (int i = 0; i < BarsArray.Length; i++)
            {
                var bp = BarsArray[i].BarsPeriod;
                if (bp != null && bp.BarsPeriodType == BarsPeriodType.Minute && bp.Value == TimeFrameMinutes)
                    return i;
            }
            return -1;
        }

        private void RecalculateAllowedStartDate()
        {
            if (SessionsBack <= 0) { allowedStartDate = DateTime.MinValue; return; }
            int idx = ForStrategy ? 0 : 1;
            if (BarsArray == null || BarsArray.Length <= idx) { allowedStartDate = DateTime.MinValue; return; }
            var series = BarsArray[idx];
            int total = series.Count;
            if (total <= 0) { allowedStartDate = DateTime.MinValue; return; }

            var dates = new List<DateTime>();
            for (int i = total - 1; i >= 0 && dates.Count < SessionsBack; i--)
            {
                DateTime d = series.GetTime(i).Date;
                if (dates.Count == 0 || dates[dates.Count - 1] != d) dates.Add(d);
            }
            if (dates.Count < SessionsBack) { allowedStartDate = DateTime.MinValue; return; }
            allowedStartDate = dates[dates.Count - 1];
        }

        // ---------------- Intrabar detection & commit logic ----------------

        // Called once per completed 60m bar close (and also when bar rolls from prev->curr in OnEachTick)
        private void CommitTouchesByBarClose(DateTime barStart, double high, double low, HashSet<string> touchedTags = null)
        {
            if (barStart == DateTime.MinValue) return;
            if (rectInfos == null) return;

            for (int i = 0; i < rectInfos.Count; i++)
            {
                var ri = rectInfos[i];

                // Only consider zones from previous sessions (not the same session as the 60m bar)
                if (ri.SessionDate >= barStart.Date) continue;
                if (ri.InvalidForFuture) continue;

                // Avoid duplicate processing for same zone/bar
                if (ri.LastCommittedDate.HasValue && ri.LastCommittedDate.Value == barStart.Date) continue;

                // Determine if this bar touched the zone:
                // - prefer touchedTags if provided (intrabar detection), otherwise fallback to high/low
                bool touched = false;
                if (touchedTags != null && touchedTags.Contains(ri.Tag)) touched = true;
                else touched = (high >= ri.Bottom && low <= ri.Top);

                if (!touched) continue;

                // strict policy: if zone is waiting opposite and not reactivated by this flip, ignore commit (but mark lastCommitted)
                if (ri.WaitingOpposite && !reactivatedThisFlip.Contains(ri.Tag))
                {
                    if (EnableLogging) Print($"WZ DEBUG Commit ignored for WaitingOpposite not reactivated tag={ri.Tag} barStart={barStart:yyyy-MM-dd HH:mm}");
                    AppendDebugLine("IGNORED_COMMIT", ri, $"waitingOpposite-not-reactivated barStart={barStart:yyyy-MM-dd HH:mm}");
                    ri.LastCommittedDate = barStart.Date;
                    rectInfos[i] = ri;
                    continue;
                }

                ZoneDirection currentDir = GetCurrentSTDirection();
                DateTime today = DateTime.UtcNow.Date;
                bool changed = false;

                if (AutoMarkByST)
                {
                    if (currentDir == ZoneDirection.Buy && !ri.UsedDateBuy.HasValue)
                    {
                        ri.UsedDateBuy = today;
                        ri.LastUsedSide = ZoneDirection.Buy;
                        if (!ri.UsedDateSell.HasValue) ri.WaitingOpposite = true;
                        if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                        changed = true;
                        if (EnableLogging) Print($"WZ INFO ZoneCommittedOnClose AutoMarked UsedDateBuy tag={ri.Tag} barStart={barStart:yyyy-MM-dd HH:mm} WaitingOpposite={ri.WaitingOpposite}");
                        AppendDebugLine("ZONE_COMMITTED_ON_CLOSE", ri, $"autormark by ST {currentDir} barStart={barStart:yyyy-MM-dd HH:mm}");
                    }
                    else if (currentDir == ZoneDirection.Sell && !ri.UsedDateSell.HasValue)
                    {
                        ri.UsedDateSell = today;
                        ri.LastUsedSide = ZoneDirection.Sell;
                        if (!ri.UsedDateBuy.HasValue) ri.WaitingOpposite = true;
                        if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                        changed = true;
                        if (EnableLogging) Print($"WZ INFO ZoneCommittedOnClose AutoMarked UsedDateSell tag={ri.Tag} barStart={barStart:yyyy-MM-dd HH:mm} WaitingOpposite={ri.WaitingOpposite}");
                        AppendDebugLine("ZONE_COMMITTED_ON_CLOSE", ri, $"autormark by ST {currentDir} barStart={barStart:yyyy-MM-dd HH:mm}");
                    }
                    else
                    {
                        if (EnableLogging) Print($"WZ DEBUG ZoneCommit skipped tag={ri.Tag} currentDir={currentDir} UsedBuy={ri.UsedDateBuy.HasValue} UsedSell={ri.UsedDateSell.HasValue}");
                        AppendDebugLine("ZONE_COMMIT_SKIPPED", ri, $"currentDir={currentDir} barStart={barStart:yyyy-MM-dd HH:mm}");
                    }
                }
                else
                {
                    if (EnableLogging) Print($"WZ INFO ZoneCommit detected but AutoMarkByST=false tag={ri.Tag} barStart={barStart:yyyy-MM-dd HH:mm}");
                    AppendDebugLine("ZONE_COMMIT_NOT_AUTOMARK", ri, $"barStart={barStart:yyyy-MM-dd HH:mm}");
                }

                ri.LastCommittedDate = barStart.Date;
                if (changed)
                {
                    rectInfos[i] = ri;
                    UpdateBrushesIfNeeded(force:true);
                    try { reactivatedThisFlip.Remove(ri.Tag); } catch { }
                }
                else
                {
                    rectInfos[i] = ri;
                }
            }
        }

        // ---------------- End Intrabar logic ----------------

        protected override void OnRender(ChartControl chartControl, ChartScale chartScale) { UpdateBrushesIfNeeded(); base.OnRender(chartControl, chartScale); }

        protected override void OnBarUpdate()
        {
            // Ensure brushes kept updated
            UpdateBrushesIfNeeded();

            int wickIndex = GetWickBarsArrayIndex();
            if (wickIndex < 0) return;

            // Only process ticks/bars from the wick series (60m) or strategy series
            int targetForZones = ForStrategy ? 0 : wickIndex;
            if (BarsInProgress != targetForZones) return;

            // Ensure we only draw historical if allowed
            if (!DrawHistorical && !realtimeStarted) return;
            if (CurrentBar < 0) return;
            if (allowedStartDate != DateTime.MinValue && Time[0].Date < allowedStartDate) return;

            // Intrabar registry: update running high/low and detect touches per tick
            DateTime currBarStart = Time[0];
            BarTouchInfo currInfo;
            if (!intrabarTouches.TryGetValue(currBarStart, out currInfo))
            {
                currInfo = new BarTouchInfo() { BarStart = currBarStart, High = High[0], Low = Low[0], TouchedTags = new HashSet<string>(StringComparer.Ordinal) };
                intrabarTouches[currBarStart] = currInfo;
            }
            else
            {
                // update running high/low
                if (High[0] > currInfo.High) currInfo.High = High[0];
                if (Low[0] < currInfo.Low) currInfo.Low = Low[0];
            }

            // If bar rolled (prevBarStart != currBarStart) commit previous
            if (prevBarStart == DateTime.MinValue) prevBarStart = currBarStart;
            if (currBarStart != prevBarStart)
            {
                // commit the previous bar data
                BarTouchInfo prevInfo;
                if (intrabarTouches.TryGetValue(prevBarStart, out prevInfo))
                {
                    CommitTouchesByBarClose(prevInfo.BarStart, prevInfo.High, prevInfo.Low, prevInfo.TouchedTags);
                    try { intrabarTouches.Remove(prevBarStart); } catch { }
                }
                prevBarStart = currBarStart;
            }

            // For each zone, if not already touched in this bar, check intrabar condition (High/Low crossing)
            if (rectInfos != null && rectInfos.Count > 0)
            {
                for (int i = 0; i < rectInfos.Count; i++)
                {
                    var ri = rectInfos[i];
                    if (ri.SessionDate >= currBarStart.Date) continue;
                    if (ri.InvalidForFuture) continue;
                    if (currInfo.TouchedTags.Contains(ri.Tag)) continue;

                    // Intrabar touch condition: any price (High/Low) during this bar crossed the zone
                    // We use the current tick's High[0]/Low[0] (cumulative above) to decide; if so, record tag
                    if (High[0] >= ri.Bottom && Low[0] <= ri.Top)
                    {
                        currInfo.TouchedTags.Add(ri.Tag);
                        intrabarTouches[currBarStart] = currInfo;
                        AppendDebugLine("INTRABAR_TOUCH_DETECTED", ri, $"barStart={currBarStart:yyyy-MM-dd HH:mm} H={High[0]:F2} L={Low[0]:F2}");
                        if (EnableLogging) Print($"WZ DEBUG INTRABAR_TOUCH_DETECTED tag={ri.Tag} barStart={currBarStart:yyyy-MM-dd HH:mm} H={High[0]:F2} L={Low[0]:F2} zoneTop={ri.Top:F2} zoneBottom={ri.Bottom:F2}");
                    }
                }
            }

            // Now normal per-bar processing (the sample v46 code workflow):
            DateTime startTime = currBarStart;
            if (processedBars.Contains(startTime)) return;
            processedBars.Add(startTime);

            DateTime endTime = (ExtendToRight && ExtendYears > 0) ? startTime.AddYears(ExtendYears) : startTime.AddMinutes(TimeFrameMinutes);

            double open = Open[0], high = High[0], low = Low[0], close = Close[0];
            double bodyTop = Math.Max(open, close), bodyBottom = Math.Min(open, close);

            double upperWickPrice = Math.Max(0.0, high - close);
            double altLowerWickPrice = (open > low) ? (open - low) : 0.0;
            double lowerWickPrice = Math.Max(0.0, close - low);
            double altUpperWickPrice = (high > open) ? (high - open) : 0.0;

            double tickSize = Instrument.MasterInstrument.TickSize;
            int PriceToTicks(double priceDiff) { if (tickSize <= 0) return 0; return (int)Math.Round(priceDiff / tickSize); }

            var candidates = new List<Tuple<double, double, int, string, int>>();
            double eps = tickSize * 0.5;

            void AddCandidate(double rawTop, double rawBottom, double priceDiff, string logicTag)
            {
                if (priceDiff <= 0) return;
                int wickTicks = PriceToTicks(priceDiff);
                if (wickTicks <= 0) return;

                int thresholdLevel = 0;
                if (wickTicks >= Th3) thresholdLevel = 3;
                else if (wickTicks >= Th2) thresholdLevel = 2;
                else if (wickTicks >= Th1) thresholdLevel = 1;
                else return;

                double yTop = Math.Max(rawTop, rawBottom);
                double yBottom = Math.Min(rawTop, rawBottom);

                bool isAboveBody = yBottom >= (bodyTop - eps);
                bool isBelowBody = yTop <= (bodyBottom + eps);
                if (!(isAboveBody || isBelowBody)) return;

                candidates.Add(Tuple.Create(yTop, yBottom, wickTicks, logicTag, thresholdLevel));
            }

            AddCandidate(high, close, upperWickPrice, "BULL_UPPER");
            AddCandidate(open, low, altLowerWickPrice, "BULL_ALTLOWER");
            AddCandidate(close, low, lowerWickPrice, "BEAR_LOWER");
            AddCandidate(high, open, altUpperWickPrice, "BEAR_ALTUPPER");

            if (candidates.Count > 0)
            {
                if (SingleWickPerBar)
                {
                    var best = candidates[0];
                    foreach (var c in candidates) if (c.Item3 > best.Item3) best = c;
                    DrawAndStore(startTime, endTime, best.Item1, best.Item2, best.Item5, best.Item4, best.Item3);
                }
                else
                {
                    foreach (var c in candidates) DrawAndStore(startTime, endTime, c.Item1, c.Item2, c.Item5, c.Item4, c.Item3);
                }
            }

            // Call commit again for this bar close path (in case this OnBarUpdate invocation is the close)
            // Use intrabarTouches entry (if exists) to pass touched tags; if not exist, fallback to high/low
            BarTouchInfo infoForThisBar;
            if (intrabarTouches.TryGetValue(startTime, out infoForThisBar))
                CommitTouchesByBarClose(startTime, infoForThisBar.High, infoForThisBar.Low, infoForThisBar.TouchedTags);
            else
                CommitTouchesByBarClose(startTime, high, low, null);

            // ST: check and reactivate on flip (w/ logging)
            try
            {
                if (stIndicator != null)
                {
                    double upVal = double.NaN, downVal = double.NaN;
                    try { if (stIndicator.UpTrend != null && stIndicator.UpTrend.Count > 0) upVal = stIndicator.UpTrend[0]; } catch { }
                    try { if (stIndicator.DownTrend != null && stIndicator.DownTrend.Count > 0) downVal = stIndicator.DownTrend[0]; } catch { }
                    if (EnableLogging) Print($"WZ DEBUG ST values (UpTrend[0]={upVal}, DownTrend[0]={downVal}, Close={Close[0]})");

                    ZoneDirection currentDir = GetCurrentSTDirection();
                    if (lastSTDirection == ZoneDirection.Neutral)
                    {
                        lastSTDirection = currentDir;
                        if (EnableLogging) Print($"WZ INFO Initialized ST direction = {lastSTDirection}");
                    }
                    else if (currentDir != lastSTDirection && currentDir != ZoneDirection.Neutral)
                    {
                        if (EnableLogging) Print($"WZ INFO ST flip detected: {lastSTDirection} -> {currentDir}");
                        // reactivation (v46 strict behavior)
                        ReactivateZonesBySTFlip(currentDir);
                        lastSTDirection = currentDir;

                        // immediate scan: check current candle for touches on reactivated zones
                        AutoDetectTouchesPostFlipOnCurrentBar(currentDir, startTime, high, low);
                    }
                }
            }
            catch (Exception ex)
            {
                if (EnableLogging) Print($"WZ WARN ST check error: {ex.Message}");
            }

            // premarket evaluation trigger (unchanged)
            try
            {
                DateTime barTime = Time[0];
                DateTime sessionDate = barTime.Date;
                TimeSpan tod = barTime.TimeOfDay;
                if (tod >= touchWindowEnd)
                {
                    if (lastTouchProcessedDate.Date != sessionDate)
                    {
                        if (EnableLogging) Print($"WZ DEBUG Wick series bar reached touchWindowEnd: {barTime:yyyy-MM-dd HH:mm} (sessionDate={sessionDate:yyyy-MM-dd})");
                        EvaluateTouchesUsingWickSeries(sessionDate);
                        lastTouchProcessedDate = sessionDate;
                    }
                }
            }
            catch { }

            // Intraday monitoring (every wick bar) for touches post-flip / general touches:
            try
            {
                DetectAndAutoMarkTouchesOnCurrentBar(startTime, high, low, open, close);
            }
            catch { }
        }

        // ---------------- v46 existing helper functions (kept intact) ----------------

        // When a cross (high >= bottom && low <= top) is found, print + optional file dump so you can audit
        private void LogCrossDetected(RectInfo ri, DateTime currentBarTime, string context)
        {
            string add = $"CrossDetected at {currentBarTime:yyyy-MM-dd HH:mm} context={context}";
            AppendDebugLine("CROSS", ri, add);
        }

        private void AutoDetectTouchesPostFlipOnCurrentBar(ZoneDirection currentDir, DateTime barTime, double high, double low)
        {
            for (int i = 0; i < rectInfos.Count; i++)
            {
                var ri = rectInfos[i];
                if (ri.SessionDate >= barTime.Date) continue;
                if (ri.InvalidForFuture) continue;

                bool canUseForBuy = !ri.UsedDateBuy.HasValue;
                bool canUseForSell = !ri.UsedDateSell.HasValue;

                if (!canUseForBuy && !canUseForSell) continue;

                if (high >= ri.Bottom && low <= ri.Top)
                {
                    // Log cross details to help debugging color/state mismatches
                    LogCrossDetected(ri, barTime, "postflip-immediate");

                    // If zone is waiting opposite, only allow auto-mark if this tag was reactivated by THIS flip (strict)
                    if (ri.WaitingOpposite)
                    {
                        if (!reactivatedThisFlip.Contains(ri.Tag))
                        {
                            if (EnableLogging) Print($"WZ DEBUG Touch on WaitingOpposite zone ignored (not reactivated this flip) tag={ri.Tag}");
                            continue;
                        }
                    }

                    // proceed to auto-mark based on ST direction (currentDir)
                    if (AutoMarkByST)
                    {
                        DateTime today = DateTime.UtcNow.Date;
                        if (currentDir == ZoneDirection.Buy && canUseForBuy)
                        {
                            // FIRST TIME buy use: set UsedDateBuy and set WaitingOpposite=true if opposite not used yet
                            ri.UsedDateBuy = today;
                            ri.LastUsedSide = ZoneDirection.Buy;
                            if (!ri.UsedDateSell.HasValue) ri.WaitingOpposite = true;
                            if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                            rectInfos[i] = ri;
                            if (EnableLogging) Print($"WZ INFO AutoMarked UsedDateBuy tag={ri.Tag} today={today:yyyy-MM-dd} WaitingOpposite={ri.WaitingOpposite} (post-flip strict)");
                            AppendDebugLine("AUTOMARK", ri, "postflip-strict");
                            UpdateBrushesIfNeeded(force:true);
                            try { reactivatedThisFlip.Remove(ri.Tag); } catch { }
                        }
                        else if (currentDir == ZoneDirection.Sell && canUseForSell)
                        {
                            ri.UsedDateSell = today;
                            ri.LastUsedSide = ZoneDirection.Sell;
                            if (!ri.UsedDateBuy.HasValue) ri.WaitingOpposite = true;
                            if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                            rectInfos[i] = ri;
                            if (EnableLogging) Print($"WZ INFO AutoMarked UsedDateSell tag={ri.Tag} today={today:yyyy-MM-dd} WaitingOpposite={ri.WaitingOpposite} (post-flip strict)");
                            AppendDebugLine("AUTOMARK", ri, "postflip-strict");
                            UpdateBrushesIfNeeded(force:true);
                            try { reactivatedThisFlip.Remove(ri.Tag); } catch { }
                        }
                    }
                    else
                    {
                        if (EnableLogging) Print($"WZ INFO Touch detected post-flip (auto-mark disabled) tag={ri.Tag} time={barTime:yyyy-MM-dd HH:mm}");
                        AppendDebugLine("TOUCH", ri, "postflip-not-automark");
                    }
                }
            }
        }

        private void DetectAndAutoMarkTouchesOnCurrentBar(DateTime barTime, double high, double low, double open, double close)
        {
            // 1) Resolve any pending confirmations from previous bars
            if (RequireTouchConfirmation && pendingConfirmations.Count > 0)
            {
                var resolved = new List<PendingConfirmation>();
                foreach (var pc in pendingConfirmations.ToArray())
                {
                    int idx = pc.ZoneIndex;
                    if (idx < 0 || idx >= rectInfos.Count) { resolved.Add(pc); continue; }
                    var ri = rectInfos[idx];
                    bool confirmed = false;
                    if (pc.ExpectedDir == ZoneDirection.Buy && close > open) confirmed = true;
                    if (pc.ExpectedDir == ZoneDirection.Sell && close < open) confirmed = true;

                    if (confirmed)
                    {
                        DateTime today = DateTime.UtcNow.Date;
                        if (pc.ExpectedDir == ZoneDirection.Buy && !ri.UsedDateBuy.HasValue)
                        {
                            ri.UsedDateBuy = today;
                            ri.LastUsedSide = ZoneDirection.Buy;
                            if (!ri.UsedDateSell.HasValue) ri.WaitingOpposite = true;
                            if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                            rectInfos[idx] = ri;
                            if (EnableLogging) Print($"WZ INFO Confirmation succeeded — AutoMarked UsedDateBuy tag={ri.Tag} today={today:yyyy-MM-dd}");
                            AppendDebugLine("CONFIRM", ri, "succeeded");
                            UpdateBrushesIfNeeded(force:true);
                        }
                        else if (pc.ExpectedDir == ZoneDirection.Sell && !ri.UsedDateSell.HasValue)
                        {
                            ri.UsedDateSell = today;
                            ri.LastUsedSide = ZoneDirection.Sell;
                            if (!ri.UsedDateBuy.HasValue) ri.WaitingOpposite = true;
                            if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                            rectInfos[idx] = ri;
                            if (EnableLogging) Print($"WZ INFO Confirmation succeeded — AutoMarked UsedDateSell tag={ri.Tag} today={today:yyyy-MM-dd}");
                            AppendDebugLine("CONFIRM", ri, "succeeded");
                            UpdateBrushesIfNeeded(force:true);
                        }
                        resolved.Add(pc);
                    }
                    else
                    {
                        if (EnableLogging) Print($"WZ INFO Confirmation FAILED for tag={pc.Tag} expectedDir={pc.ExpectedDir} detected={pc.DetectedTime:yyyy-MM-dd HH:mm} currentBar={barTime:yyyy-MM-dd HH:mm}");
                        AppendDebugLine("CONFIRM", ri, "failed");
                        resolved.Add(pc);
                    }
                }
                foreach (var r in resolved) pendingConfirmations.Remove(r);
            }

            // 2) Intraday direct detection (auto mark if conditions met and not waitingOpposite or reactivated)
            if (AutoMarkByST && !RequireTouchConfirmation)
            {
                ZoneDirection currentDir = GetCurrentSTDirection();
                for (int i = 0; i < rectInfos.Count; i++)
                {
                    var ri = rectInfos[i];
                    if (ri.SessionDate >= barTime.Date) continue;
                    if (ri.InvalidForFuture) continue;

                    bool canUseForBuy = !ri.UsedDateBuy.HasValue;
                    bool canUseForSell = !ri.UsedDateSell.HasValue;
                    if (!canUseForBuy && !canUseForSell) continue;

                    if (high >= ri.Bottom && low <= ri.Top)
                    {
                        // Log detection for auditing color/state mismatches
                        LogCrossDetected(ri, barTime, "intraday-monitor");

                        // If zone was WaitingOpposite, allow auto-mark only if reactivatedThisFlip contains it (strict)
                        if (ri.WaitingOpposite && !reactivatedThisFlip.Contains(ri.Tag))
                        {
                            if (EnableLogging) Print($"WZ DEBUG Ignored touch for WaitingOpposite zone not reactivated this flip tag={ri.Tag}");
                            AppendDebugLine("IGNORED", ri, "waitingOpposite-not-reactivated");
                            continue;
                        }

                        DateTime today = DateTime.UtcNow.Date;
                        if (currentDir == ZoneDirection.Buy && canUseForBuy)
                        {
                            ri.UsedDateBuy = today;
                            ri.LastUsedSide = ZoneDirection.Buy;
                            if (!ri.UsedDateSell.HasValue) ri.WaitingOpposite = true;
                            if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                            rectInfos[i] = ri;
                            if (EnableLogging) Print($"WZ INFO AutoMarked UsedDateBuy tag={ri.Tag} today={today:yyyy-MM-dd} (intraday monitor)");
                            AppendDebugLine("AUTOMARK", ri, "intraday");
                            UpdateBrushesIfNeeded(force:true);
                            try { reactivatedThisFlip.Remove(ri.Tag); } catch { }
                        }
                        else if (currentDir == ZoneDirection.Sell && canUseForSell)
                        {
                            ri.UsedDateSell = today;
                            ri.LastUsedSide = ZoneDirection.Sell;
                            if (!ri.UsedDateBuy.HasValue) ri.WaitingOpposite = true;
                            if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                            rectInfos[i] = ri;
                            if (EnableLogging) Print($"WZ INFO AutoMarked UsedDateSell tag={ri.Tag} today={today:yyyy-MM-dd} (intraday monitor)");
                            AppendDebugLine("AUTOMARK", ri, "intraday");
                            UpdateBrushesIfNeeded(force:true);
                            try { reactivatedThisFlip.Remove(ri.Tag); } catch { }
                        }
                    }
                }
            }
        }

        private ZoneDirection GetCurrentSTDirection()
        {
            try
            {
                double up = double.NaN, down = double.NaN;
                if (stIndicator != null)
                {
                    try { if (stIndicator.UpTrend != null && stIndicator.UpTrend.Count > 0) up = stIndicator.UpTrend[0]; } catch { }
                    try { if (stIndicator.DownTrend != null && stIndicator.DownTrend.Count > 0) down = stIndicator.DownTrend[0]; } catch { }
                }

                double latestClose = Close[0];
                if (!double.IsNaN(down) && latestClose > down) return ZoneDirection.Buy;
                if (!double.IsNaN(up) && latestClose < up) return ZoneDirection.Sell;
            }
            catch { }
            return ZoneDirection.Neutral;
        }

        // Evaluate touches using wick series for premarket (unchanged)
        private void EvaluateTouchesUsingWickSeries(DateTime sessionDate)
        {
            int wickIdx = GetWickBarsArrayIndex();
            if (wickIdx < 0 || BarsArray == null || BarsArray.Length <= wickIdx) { if (EnableLogging) Print("WZ WARN EvaluateTouchesUsingWickSeries: wick series not available"); return; }
            var series = BarsArray[wickIdx];
            if (series == null || series.Count == 0) { if (EnableLogging) Print("WZ WARN EvaluateTouchesUsingWickSeries: wick series empty"); return; }

            DateTime prevDate = sessionDate.AddDays(-1);
            var candidateIndices = new List<int>();

            for (int i = 0; i < series.Count; i++)
            {
                DateTime t = series.GetTime(i);
                if ((t.Date == prevDate && t.TimeOfDay >= touchWindowStartTimeOfDay) ||
                    (t.Date == sessionDate && t.TimeOfDay <= touchWindowEnd))
                    candidateIndices.Add(i);
            }

            bool usedFallback = false;
            if (candidateIndices.Count == 0)
            {
                usedFallback = true;
                for (int i = 0; i < series.Count; i++)
                {
                    DateTime t = series.GetTime(i);
                    if (t.Date == sessionDate && t.TimeOfDay <= touchWindowEnd) candidateIndices.Add(i);
                }
            }

            if (candidateIndices.Count == 0)
            {
                if (EnableLogging) Print($"WZ WARN Could not determine valid wick touch bars for session {sessionDate:yyyy-MM-dd}. No candidate bars found. Wick series first/last: {(series.Count>0?series.GetTime(0).ToString():"-")}/{(series.Count>0?series.GetTime(series.Count-1).ToString():"-")}");
                return;
            }

            if (EnableLogging)
            {
                DateTime firstBar = series.GetTime(candidateIndices[0]);
                DateTime lastBar = series.GetTime(candidateIndices[candidateIndices.Count - 1]);
                Print($"WZ DEBUG Evaluating touches (using wick series) for session {sessionDate:yyyy-MM-dd} (usedFallback={usedFallback}) candidateBars={candidateIndices.Count} first={firstBar:yyyy-MM-dd HH:mm} last={lastBar:yyyy-MM-dd HH:mm}");
            }

            for (int zi = 0; zi < rectInfos.Count; zi++)
            {
                var ri = rectInfos[zi];
                if (ri.SessionDate >= sessionDate) continue;
                if (ri.InvalidForFuture) continue;
                if (ri.TouchedInPreMarket) continue;

                bool touched = false;
                DateTime touchedBarTime = DateTime.MinValue;
                double touchedBarHigh = double.NaN, touchedBarLow = double.NaN;
                int touchedBarIdx = -1;

                for (int idx = 0; idx < candidateIndices.Count; idx++)
                {
                    int bi = candidateIndices[idx];
                    double bh = series.GetHigh(bi);
                    double bl = series.GetLow(bi);
                    if (bh >= ri.Bottom && bl <= ri.Top)
                    {
                        touched = true;
                        touchedBarTime = series.GetTime(bi);
                        touchedBarHigh = bh;
                        touchedBarLow = bl;
                        touchedBarIdx = bi;
                        break;
                    }
                }

                if (touched)
                {
                    ri.TouchedInPreMarket = true;
                    rectInfos[zi] = ri;
                    if (EnableLogging) Print($"WZ INFO zone touched in premarket (wick bars) tag={ri.Tag} session={sessionDate:yyyy-MM-dd} touchedBarIdx={touchedBarIdx} touchedTime={touchedBarTime:yyyy-MM-dd HH:mm} H={touchedBarHigh:F2} L={touchedBarLow:F2} zoneTop={ri.Top:F2} zoneBottom={ri.Bottom:F2}");
                    AppendDebugLine("PREMARKET_TOUCH", ri, $"touchedBarIdx={touchedBarIdx}");
                }
                else
                {
                    if (EnableLogging) Print($"WZ DEBUG zone NOT touched (wick bars) tag={ri.Tag} session={sessionDate:yyyy-MM-dd} zoneTop={ri.Top:F2} zoneBottom={ri.Bottom:F2} scannedBars={candidateIndices.Count}");
                }
            }

            UpdateBrushesIfNeeded(force:true);
        }

        private void ReactivateZonesBySTFlip(ZoneDirection newDir)
        {
            reactivatedThisFlip.Clear();
            bool changedAny = false;

            for (int i = 0; i < rectInfos.Count; i++)
            {
                var ri = rectInfos[i];
                if (!ri.TouchedInPreMarket) continue;
                if (ri.Direction == ZoneDirection.Buy && newDir == ZoneDirection.Sell)
                {
                    ri.TouchedInPreMarket = false;
                    rectInfos[i] = ri;
                    changedAny = true;
                    reactivatedThisFlip.Add(ri.Tag);
                    if (EnableLogging) Print($"WZ INFO Reactivated tag={ri.Tag} by ST flip to SELL (from premarket touched)");
                    AppendDebugLine("REACTIVATED", ri, "from premarket touched");
                }
                else if (ri.Direction == ZoneDirection.Sell && newDir == ZoneDirection.Buy)
                {
                    ri.TouchedInPreMarket = false;
                    rectInfos[i] = ri;
                    changedAny = true;
                    reactivatedThisFlip.Add(ri.Tag);
                    if (EnableLogging) Print($"WZ INFO Reactivated tag={ri.Tag} by ST flip to BUY (from premarket touched)");
                    AppendDebugLine("REACTIVATED", ri, "from premarket touched");
                }
            }

            // allow opposite use only for zones waiting for opposite where lastused side is opposite of newDir
            for (int i = 0; i < rectInfos.Count; i++)
            {
                var ri = rectInfos[i];
                if (!ri.WaitingOpposite) continue;
                if (ri.LastUsedSide == ZoneDirection.Buy && newDir == ZoneDirection.Sell)
                {
                    reactivatedThisFlip.Add(ri.Tag);
                    if (EnableLogging) Print($"WZ INFO ReactivatedForOpposite tag={ri.Tag} by ST flip: LastUsed=Buy -> now Sell (eligible for opposite use)");
                    AppendDebugLine("REACTIVATED_FOR_OPPOSITE", ri, "lastUsed=Buy");
                }
                else if (ri.LastUsedSide == ZoneDirection.Sell && newDir == ZoneDirection.Buy)
                {
                    reactivatedThisFlip.Add(ri.Tag);
                    if (EnableLogging) Print($"WZ INFO ReactivatedForOpposite tag={ri.Tag} by ST flip: LastUsed=Sell -> now Buy (eligible for opposite use)");
                    AppendDebugLine("REACTIVATED_FOR_OPPOSITE", ri, "lastUsed=Sell");
                }
            }

            if (changedAny) UpdateBrushesIfNeeded(force:true);

            if (EnableLogging) Print($"WZ DEBUG reactivatedThisFlip count={reactivatedThisFlip.Count} (tags will be eligible for strict post-flip AutoMark)");
        }

        private void DrawAndStore(DateTime s, DateTime e, double yTop, double yBottom, int thresholdLevel, string logicTag, int wickTicks)
        {
            string tag = $"WZ_RECT_{rectCounter++}_{s:yyyyMMddHHmmss}_{rectCounter}";
            SolidColorBrush useFill = (thresholdLevel == 3) ? fillBrush3 : (thresholdLevel == 2 ? fillBrush2 : fillBrush1);
            SolidColorBrush useBorder = (thresholdLevel == 3) ? borderBrush3 : (thresholdLevel == 2 ? borderBrush2 : borderBrush1);

            try { zoneTop[0] = yTop; zoneBottom[0] = yBottom; zoneLevel[0] = thresholdLevel; } catch { }

            if (Render)
            {
                if ((DrawModes)DrawModeValue == DrawModes.Rectangle)
                {
                    try { Draw.Rectangle(this, tag, true, s, yTop, e, yBottom, useBorder, useFill, 1); } catch { }
                }
                else
                {
                    Brush drawBrush = (Brush)((thresholdLevel == 3) ? borderBrush3 : (thresholdLevel == 2 ? borderBrush2 : borderBrush1));
                    DateTime endForRay = (ExtendToRight && ExtendYears > 0) ? s.AddYears(ExtendYears) : e;
                    double lineHeight = Math.Max(Instrument.MasterInstrument.TickSize * 0.05, Instrument.MasterInstrument.TickSize * 0.5);

                    try { Draw.Rectangle(this, tag + "_TOP", true, s, yTop, endForRay, yTop - lineHeight, drawBrush, Brushes.Transparent, LineThickness); } catch { }
                    try { Draw.Rectangle(this, tag + "_BOT", true, s, yBottom + lineHeight, endForRay, yBottom, drawBrush, Brushes.Transparent, LineThickness); } catch { }

                    try
                    {
                        DateTime markEnd = s.AddMinutes(Math.Max(1, MarkerDurationMinutes));
                        double tickSize = Instrument.MasterInstrument.TickSize;
                        double markerHalfHeight = Math.Max(tickSize * 1.0, tickSize * 2.0);

                        Draw.Ellipse(this, tag + "_MARK_TOP", true, s, yTop + markerHalfHeight, markEnd, yTop - markerHalfHeight, drawBrush, drawBrush, 0);
                        Draw.Ellipse(this, tag + "_MARK_BOT", true, s, yBottom + markerHalfHeight, markEnd, yBottom - markerHalfHeight, drawBrush, drawBrush, 0);
                    }
                    catch { }
                }
            }

            rectTags.Add(tag);

            var ri = new RectInfo
            {
                Tag = tag,
                Start = s,
                End = e,
                Top = yTop,
                Bottom = yBottom,
                ThresholdLevel = thresholdLevel,
                LogicTag = logicTag,
                WickTicks = wickTicks,
                Direction = MapLogicTagToDirection(logicTag),
                SessionDate = s.Date,
                UsedDateBuy = null,
                UsedDateSell = null,
                InvalidForFuture = false,
                TouchedInPreMarket = false,
                WaitingOpposite = false,
                LastUsedSide = ZoneDirection.Neutral,
                LastCommittedDate = null
            };

            rectInfos.Add(ri);

            if (EnableLogging) Print($"WZ MARK [{logicTag}] time={s:yyyy-MM-dd HH:mm} ticks={wickTicks} priceTop={yTop:F2} priceBottom={yBottom:F2} tag={tag}");
            AppendDebugLine("MARK", ri, "created");

            if (rectTags.Count > MaxRectangles)
            {
                var oldest = rectInfos[0];
                try { RemoveDrawObject(oldest.Tag + "_TOP"); } catch { }
                try { RemoveDrawObject(oldest.Tag + "_BOT"); } catch { }
                try { RemoveDrawObject(oldest.Tag + "_MARK_TOP"); } catch { }
                try { RemoveDrawObject(oldest.Tag + "_MARK_BOT"); } catch { }
                rectTags.RemoveAt(0);
                rectInfos.RemoveAt(0);
            }
        }

        private ZoneDirection MapLogicTagToDirection(string logicTag)
        {
            try
            {
                if (string.IsNullOrEmpty(logicTag)) return ZoneDirection.Neutral;
                if (logicTag.StartsWith("BULL_", StringComparison.OrdinalIgnoreCase)) return ZoneDirection.Buy;
                if (logicTag.StartsWith("BEAR_", StringComparison.OrdinalIgnoreCase)) return ZoneDirection.Sell;
            }
            catch { }
            return ZoneDirection.Neutral;
        }

        // APIs (unchanged except MarkZoneUsed logging)
        public bool MarkZoneUsed(string tag, bool usedBuy, bool usedSell)
        {
            if (string.IsNullOrEmpty(tag) || rectInfos == null) return false;
            for (int i = 0; i < rectInfos.Count; i++)
            {
                if (rectInfos[i].Tag == tag)
                {
                    var ri = rectInfos[i]; DateTime today = DateTime.UtcNow.Date;
                    if (usedBuy && !ri.UsedDateBuy.HasValue)
                    {
                        ri.UsedDateBuy = today;
                        ri.LastUsedSide = ZoneDirection.Buy;
                        if (!ri.UsedDateSell.HasValue) ri.WaitingOpposite = true;
                    }
                    if (usedSell && !ri.UsedDateSell.HasValue)
                    {
                        ri.UsedDateSell = today;
                        ri.LastUsedSide = ZoneDirection.Sell;
                        if (!ri.UsedDateBuy.HasValue) ri.WaitingOpposite = true;
                    }
                    if (ri.UsedDateBuy.HasValue && ri.UsedDateSell.HasValue) ri.InvalidForFuture = true;
                    rectInfos[i] = ri;
                    if (EnableLogging) Print($"WZ INFO MarkZoneUsed tag={tag} usedBuy={usedBuy} usedSell={usedSell} today={today:yyyy-MM-dd} invalidFuture={ri.InvalidForFuture} WaitingOpposite={ri.WaitingOpposite} LastUsedSide={ri.LastUsedSide}");
                    AppendDebugLine("MARKUSED", ri, $"manual usedBuy={usedBuy} usedSell={usedSell}");
                    UpdateBrushesIfNeeded(force:true);
                    return true;
                }
            }
            return false;
        }

        public struct ZoneInfo { public string Tag; public DateTime Start; public DateTime End; public double Top; public double Bottom; public int Level; public int WickTicks; public ZoneDirection Direction; public DateTime SessionDate; public DateTime? UsedDateBuy; public DateTime? UsedDateSell; public bool InvalidForFuture; public bool TouchedInPreMarket; public bool WaitingOpposite; public ZoneDirection LastUsedSide; }

        public ZoneInfo? GetZoneByTag(string tag)
        {
            if (string.IsNullOrEmpty(tag) || rectInfos == null) return null;
            for (int i = 0; i < rectInfos.Count; i++)
            {
                var r = rectInfos[i];
                if (r.Tag == tag) return new ZoneInfo { Tag = r.Tag, Start = r.Start, End = r.End, Top = r.Top, Bottom = r.Bottom, Level = r.ThresholdLevel, WickTicks = r.WickTicks, Direction = r.Direction, SessionDate = r.SessionDate, UsedDateBuy = r.UsedDateBuy, UsedDateSell = r.UsedDateSell, InvalidForFuture = r.InvalidForFuture, TouchedInPreMarket = r.TouchedInPreMarket, WaitingOpposite = r.WaitingOpposite, LastUsedSide = r.LastUsedSide };
            }
            return null;
        }

        public override string ToString() => Name;
    }
}

#region NinjaScript generated code. Neither change nor remove.

namespace NinjaTrader.NinjaScript.Indicators
{
    public partial class Indicator : NinjaTrader.Gui.NinjaScript.IndicatorRenderBase
    {
        private WickZonesIndicator[] cacheWickZonesIndicator;
        public WickZonesIndicator WickZonesIndicator(int timeFrameMinutes, int th1, int th2, int th3, int maxRectangles, int fillTransparency, int borderTransparency, Brush fillColorTick1, Brush fillColorTick2, Brush fillColorTick3, int sessionsBack, bool extendToRight, int extendYears, bool drawHistorical, bool enableLogging, bool singleWickPerBar, bool render, bool forStrategy, int drawModeValue, int lineThickness, int markerDurationMinutes, int sTLength, double sTMultiplier, bool autoMarkByST, bool requireTouchConfirmation, bool debugDumpToFile, string debugDumpFilePath)
        {
            return WickZonesIndicator(Input, timeFrameMinutes, th1, th2, th3, maxRectangles, fillTransparency, borderTransparency, fillColorTick1, fillColorTick2, fillColorTick3, sessionsBack, extendToRight, extendYears, drawHistorical, enableLogging, singleWickPerBar, render, forStrategy, drawModeValue, lineThickness, markerDurationMinutes, sTLength, sTMultiplier, autoMarkByST, requireTouchConfirmation, debugDumpToFile, debugDumpFilePath);
        }

        public WickZonesIndicator WickZonesIndicator(ISeries<double> input, int timeFrameMinutes, int th1, int th2, int th3, int maxRectangles, int fillTransparency, int borderTransparency, Brush fillColorTick1, Brush fillColorTick2, Brush fillColorTick3, int sessionsBack, bool extendToRight, int extendYears, bool drawHistorical, bool enableLogging, bool singleWickPerBar, bool render, bool forStrategy, int drawModeValue, int lineThickness, int markerDurationMinutes, int sTLength, double sTMultiplier, bool autoMarkByST, bool requireTouchConfirmation, bool debugDumpToFile, string debugDumpFilePath)
        {
            if (cacheWickZonesIndicator != null)
                for (int idx = 0; idx < cacheWickZonesIndicator.Length; idx++)
                    if (cacheWickZonesIndicator[idx] != null && cacheWickZonesIndicator[idx].TimeFrameMinutes == timeFrameMinutes && cacheWickZonesIndicator[idx].Th1 == th1 && cacheWickZonesIndicator[idx].Th2 == th2 && cacheWickZonesIndicator[idx].Th3 == th3 && cacheWickZonesIndicator[idx].MaxRectangles == maxRectangles && cacheWickZonesIndicator[idx].FillTransparency == fillTransparency && cacheWickZonesIndicator[idx].BorderTransparency == borderTransparency && cacheWickZonesIndicator[idx].FillColorTick1 == fillColorTick1 && cacheWickZonesIndicator[idx].FillColorTick2 == fillColorTick2 && cacheWickZonesIndicator[idx].FillColorTick3 == fillColorTick3 && cacheWickZonesIndicator[idx].SessionsBack == sessionsBack && cacheWickZonesIndicator[idx].ExtendToRight == extendToRight && cacheWickZonesIndicator[idx].ExtendYears == extendYears && cacheWickZonesIndicator[idx].DrawHistorical == drawHistorical && cacheWickZonesIndicator[idx].EnableLogging == enableLogging && cacheWickZonesIndicator[idx].SingleWickPerBar == singleWickPerBar && cacheWickZonesIndicator[idx].Render == render && cacheWickZonesIndicator[idx].ForStrategy == forStrategy && cacheWickZonesIndicator[idx].DrawModeValue == drawModeValue && cacheWickZonesIndicator[idx].LineThickness == lineThickness && cacheWickZonesIndicator[idx].MarkerDurationMinutes == markerDurationMinutes && cacheWickZonesIndicator[idx].STLength == sTLength && cacheWickZonesIndicator[idx].STMultiplier == sTMultiplier && cacheWickZonesIndicator[idx].AutoMarkByST == autoMarkByST && cacheWickZonesIndicator[idx].RequireTouchConfirmation == requireTouchConfirmation && cacheWickZonesIndicator[idx].DebugDumpToFile == debugDumpToFile && cacheWickZonesIndicator[idx].DebugDumpFilePath == debugDumpFilePath && cacheWickZonesIndicator[idx].EqualsInput(input))
                        return cacheWickZonesIndicator[idx];
            return CacheIndicator<WickZonesIndicator>(new WickZonesIndicator(){ TimeFrameMinutes = timeFrameMinutes, Th1 = th1, Th2 = th2, Th3 = th3, MaxRectangles = maxRectangles, FillTransparency = fillTransparency, BorderTransparency = borderTransparency, FillColorTick1 = fillColorTick1, FillColorTick2 = fillColorTick2, FillColorTick3 = fillColorTick3, SessionsBack = sessionsBack, ExtendToRight = extendToRight, ExtendYears = extendYears, DrawHistorical = drawHistorical, EnableLogging = enableLogging, SingleWickPerBar = singleWickPerBar, Render = render, ForStrategy = forStrategy, DrawModeValue = drawModeValue, LineThickness = lineThickness, MarkerDurationMinutes = markerDurationMinutes, STLength = sTLength, STMultiplier = sTMultiplier, AutoMarkByST = autoMarkByST, RequireTouchConfirmation = requireTouchConfirmation, DebugDumpToFile = debugDumpToFile, DebugDumpFilePath = debugDumpFilePath }, input, ref cacheWickZonesIndicator);
        }
    }
}

namespace NinjaTrader.NinjaScript.MarketAnalyzerColumns
{
    public partial class MarketAnalyzerColumn : MarketAnalyzerColumnBase
    {
        public Indicators.WickZonesIndicator WickZonesIndicator(int timeFrameMinutes, int th1, int th2, int th3, int maxRectangles, int fillTransparency, int borderTransparency, Brush fillColorTick1, Brush fillColorTick2, Brush fillColorTick3, int sessionsBack, bool extendToRight, int extendYears, bool drawHistorical, bool enableLogging, bool singleWickPerBar, bool render, bool forStrategy, int drawModeValue, int lineThickness, int markerDurationMinutes, int sTLength, double sTMultiplier, bool autoMarkByST, bool requireTouchConfirmation, bool debugDumpToFile, string debugDumpFilePath)
        {
            return indicator.WickZonesIndicator(Input, timeFrameMinutes, th1, th2, th3, maxRectangles, fillTransparency, borderTransparency, fillColorTick1, fillColorTick2, fillColorTick3, sessionsBack, extendToRight, extendYears, drawHistorical, enableLogging, singleWickPerBar, render, forStrategy, drawModeValue, lineThickness, markerDurationMinutes, sTLength, sTMultiplier, autoMarkByST, requireTouchConfirmation, debugDumpToFile, debugDumpFilePath);
        }

        public Indicators.WickZonesIndicator WickZonesIndicator(ISeries<double> input , int timeFrameMinutes, int th1, int th2, int th3, int maxRectangles, int fillTransparency, int borderTransparency, Brush fillColorTick1, Brush fillColorTick2, Brush fillColorTick3, int sessionsBack, bool extendToRight, int extendYears, bool drawHistorical, bool enableLogging, bool singleWickPerBar, bool render, bool forStrategy, int drawModeValue, int lineThickness, int markerDurationMinutes, int sTLength, double sTMultiplier, bool autoMarkByST, bool requireTouchConfirmation, bool debugDumpToFile, string debugDumpFilePath)
        {
            return indicator.WickZonesIndicator(input, timeFrameMinutes, th1, th2, th3, maxRectangles, fillTransparency, borderTransparency, fillColorTick1, fillColorTick2, fillColorTick3, sessionsBack, extendToRight, extendYears, drawHistorical, enableLogging, singleWickPerBar, render, forStrategy, drawModeValue, lineThickness, markerDurationMinutes, sTLength, sTMultiplier, autoMarkByST, requireTouchConfirmation, debugDumpToFile, debugDumpFilePath);
        }
    }
}

namespace NinjaTrader.NinjaScript.Strategies
{
    public partial class Strategy : NinjaTrader.Gui.NinjaScript.StrategyRenderBase
    {
        public Indicators.WickZonesIndicator WickZonesIndicator(int timeFrameMinutes, int th1, int th2, int th3, int maxRectangles, int fillTransparency, int borderTransparency, Brush fillColorTick1, Brush fillColorTick2, Brush fillColorTick3, int sessionsBack, bool extendToRight, int extendYears, bool drawHistorical, bool enableLogging, bool singleWickPerBar, bool render, bool forStrategy, int drawModeValue, int lineThickness, int markerDurationMinutes, int sTLength, double sTMultiplier, bool autoMarkByST, bool requireTouchConfirmation, bool debugDumpToFile, string debugDumpFilePath)
        {
            return indicator.WickZonesIndicator(Input, timeFrameMinutes, th1, th2, th3, maxRectangles, fillTransparency, borderTransparency, fillColorTick1, fillColorTick2, fillColorTick3, sessionsBack, extendToRight, extendYears, drawHistorical, enableLogging, singleWickPerBar, render, forStrategy, drawModeValue, lineThickness, markerDurationMinutes, sTLength, sTMultiplier, autoMarkByST, requireTouchConfirmation, debugDumpToFile, debugDumpFilePath);
        }

        public Indicators.WickZonesIndicator WickZonesIndicator(ISeries<double> input , int timeFrameMinutes, int th1, int th2, int th3, int maxRectangles, int fillTransparency, int borderTransparency, Brush fillColorTick1, Brush fillColorTick2, Brush fillColorTick3, int sessionsBack, bool extendToRight, int extendYears, bool drawHistorical, bool enableLogging, bool singleWickPerBar, bool render, bool forStrategy, int drawModeValue, int lineThickness, int markerDurationMinutes, int sTLength, double sTMultiplier, bool autoMarkByST, bool requireTouchConfirmation, bool debugDumpToFile, string debugDumpFilePath)
        {
            return indicator.WickZonesIndicator(input, timeFrameMinutes, th1, th2, th3, maxRectangles, fillTransparency, borderTransparency, fillColorTick1, fillColorTick2, fillColorTick3, sessionsBack, extendToRight, extendYears, drawHistorical, enableLogging, singleWickPerBar, render, forStrategy, drawModeValue, lineThickness, markerDurationMinutes, sTLength, sTMultiplier, autoMarkByST, requireTouchConfirmation, debugDumpToFile, debugDumpFilePath);
        }
    }
}

#endregion
