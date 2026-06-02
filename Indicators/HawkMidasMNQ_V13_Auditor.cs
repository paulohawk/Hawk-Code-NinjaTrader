#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Globalization;
using System.IO;
using System.Text;
using System.Windows;
using System.Xml.Serialization;
using System.Windows.Media;
using NinjaTrader.Data;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Tools;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.DrawingTools;
#endregion

// HawkMidas MNQ V1.3 Auditor
// Indicator-only virtual audit engine.  No NinjaTrader order methods are used in this file.
namespace NinjaTrader.NinjaScript.Indicators
{
    public class HawkMidasMNQ_V13_Auditor : Indicator
    {
        private const string VersionName = "HawkMidasMNQ_V13_Auditor";
        private const int TrendBull = 1;
        private const int TrendBear = -1;
        private const int TrendUnknown = 0;

        private enum PivotType { None, High, Low }
        private enum TradeDirection { None, Long, Short }
        private enum ExitType { None, Stop, Target, EOD }

        private sealed class PivotInfo
        {
            public int BarIndex;
            public DateTime TimeBrt;
            public double Price;
            public PivotType Type;
        }

        private sealed class TradeRecord
        {
            public int TradeId;
            public string Version;
            public string Instrument;
            public DateTime EntryTimeBrt;
            public DateTime ExitTimeBrt;
            public TradeDirection Direction;
            public double EntryPrice;
            public double ExitPrice;
            public double StopPrice;
            public double TargetPrice;
            public ExitType ExitType;
            public double GrossPnl;
            public double Cost;
            public double NetPnl;
            public double DayPnlAfterTrade;
            public int TradesTodayAfterTrade;
            public bool IsBridgeTrade;
            public DateTime AnchorTimeBrt;
            public double AnchorPrice;
            public double AvwapEntryReference;
            public double EntryLevel;
            public double OffsetPoints;
            public double EffectiveOffset;
            public double VisualEntryLevelAtSignalBar;
        }

        private Series<double> trueRangeSeries;
        private Series<double> atrSeries;
        private Series<double> upperBandSeries;
        private Series<double> lowerBandSeries;
        private Series<double> superTrendSeries;
        private Series<double> avwapSeries;
        private Series<double> entryLevelSeries;

        private TimeZoneInfo brtTimeZone;
        private readonly List<PivotInfo> pivots = new List<PivotInfo>();
        private readonly List<TradeRecord> closedTrades = new List<TradeRecord>();
        private HashSet<DateTime> blockedDates = new HashSet<DateTime>();
        private readonly HashSet<DateTime> loggedCalendarBlocks = new HashSet<DateTime>();

        private DateTime currentBrtDate = DateTime.MinValue;
        private double dayPnl;
        private int tradesToday;
        private bool dailyLocked;
        private bool calendarBlocked;
        private bool loggedDailyLock;

        private int trendSide = TrendUnknown;
        private int previousTrendSide = TrendUnknown;
        private bool contextActive;
        private int contextSide = TrendUnknown;
        private int contextStartBar = -1;
        private int anchorBarIndex = -1;
        private DateTime anchorTimeBrt = DateTime.MinValue;
        private double anchorPrice = double.NaN;
        private PivotType anchorType = PivotType.None;
        private double avwapCurrent = double.NaN;
        private double avwapPrevious = double.NaN;
        private double entryLevel = double.NaN;
        private double avwapEntryReference = double.NaN;
        private double currentVisualEntryLevel = double.NaN;
        private double currentSignalAvwapReference = double.NaN;
        private double currentSignalEntryLevel = double.NaN;
        private double currentSignalEffectiveOffset = double.NaN;

        private bool inTrade;
        private TradeDirection tradeDirection = TradeDirection.None;
        private int entryBarIndex = -1;
        private DateTime entryTimeBrt = DateTime.MinValue;
        private double entryPrice = double.NaN;
        private double stopPrice = double.NaN;
        private double targetPrice = double.NaN;
        private bool currentTradeIsBridge;
        private DateTime currentTradeAnchorTimeBrt = DateTime.MinValue;
        private double currentTradeAnchorPrice = double.NaN;
        private double currentTradeAvwapReference = double.NaN;
        private double currentTradeEntryLevel = double.NaN;
        private double currentTradeEffectiveOffset = double.NaN;
        private double currentTradeVisualEntryLevelAtSignalBar = double.NaN;

        private double totalNetPnl;
        private double grossProfit;
        private double grossLossAbs;
        private double longNetPnl;
        private double shortNetPnl;
        private int wins;
        private int losses;
        private int targets;
        private int stops;
        private int eods;
        private int maxConsecutiveLosses;
        private int currentConsecutiveLosses;
        private double equityPeak;
        private double maxDrawdown;
        private int tradeSequence;
        private string resolvedCsvPath;
        private bool csvHeaderWritten;
        private string lastCsvExportStatus = "aguardando trade fechado";

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description = "Auditor indicador HawkMidas MNQ V1.3 com motor virtual, SuperTrend, ZigZag 2/2, AVWAP ancorada, CSV e logs.";
                Name = VersionName;
                Calculate = Calculate.OnBarClose;
                IsOverlay = true;
                DisplayInDataBox = true;
                DrawOnPricePanel = true;
                PaintPriceMarkers = true;
                IsSuspendedWhileInactive = true;

                AtrLength = 10;
                SuperTrendFactor = 3.0;
                ZigZagLegs = 2;
                ZigZagReversal = 0.00001;
                AvwapOffsetPoints = 0.25;
                PointValueUsd = 2.0;
                TickSizePoints = 0.25;
                Contracts = 1;
                StopPoints = 25.0;
                TargetPoints = 100.0;
                RoundTripCostUsd = 2.0;
                InitialCapital = 1500.0;
                MaxTradesPerDay = 2;
                DailyProfitTargetUsd = 198.0;
                DailyStopUsd = -104.0;
                OperationalTimeZoneId = "E. South America Standard Time";
                SourceTimeZoneMode = "LocalMachine";
                TradingStartBrt = "10:35";
                LastEntryBrt = "16:45";
                EodBrt = "17:00";
                BlockedDatesCsv = "2026-05-25";
                EnableCsvExport = false;
                CsvExportPath = string.Empty;
                EnableDebugLogs = false;
                ShowZigZagMarkers = true;
                ZigZagMarkerFontSize = 10;
                ZigZagMarkerOffsetTicks = 4;
                ZigZagHighBrush = Brushes.OrangeRed;
                ZigZagLowBrush = Brushes.LimeGreen;
                SuperTrendBullBrush = Brushes.LimeGreen;
                SuperTrendBearBrush = Brushes.Red;

                AddPlot(Brushes.DodgerBlue, "SuperTrend");
                AddPlot(Brushes.Goldenrod, "ActiveAVWAP");
                AddPlot(Brushes.Gray, "EntryLevel");
            }
            else if (State == State.DataLoaded)
            {
                trueRangeSeries = new Series<double>(this);
                atrSeries = new Series<double>(this);
                upperBandSeries = new Series<double>(this);
                lowerBandSeries = new Series<double>(this);
                superTrendSeries = new Series<double>(this);
                avwapSeries = new Series<double>(this);
                entryLevelSeries = new Series<double>(this);
                brtTimeZone = ResolveTimeZone(OperationalTimeZoneId);
                blockedDates = ParseBlockedDates(BlockedDatesCsv);
                ResetAllState();
            }
            else if (State == State.Terminated)
            {
                if (EnableDebugLogs)
                    Print(string.Format(CultureInfo.InvariantCulture, "{0} terminated. Trades={1} NetPnL={2:F2}", VersionName, closedTrades.Count, totalNetPnl));
            }
        }

        protected override void OnBarUpdate()
        {
            if (CurrentBar < 1)
            {
                Values[0][0] = double.NaN;
                Values[1][0] = double.NaN;
                Values[2][0] = double.NaN;
                return;
            }

            DateTime timeBrt = ToBrt(Time[0]);
            DateTime dateBrt = timeBrt.Date;
            LogTimeConversion(Time[0], timeBrt, dateBrt);
            HandleDailyReset(dateBrt, timeBrt);
            calendarBlocked = blockedDates.Contains(dateBrt);
            if (calendarBlocked && !loggedCalendarBlocks.Contains(dateBrt))
            {
                loggedCalendarBlocks.Add(dateBrt);
                DebugLog(timeBrt, "CALENDAR_BLOCKED", "date=" + dateBrt.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture));
            }

            CalculateSuperTrend(timeBrt);
            ConfirmZigZagPivot(timeBrt);

            if (inTrade)
                CheckOpenTradeExit(timeBrt, false);

            if (!inTrade)
            {
                bool trendChanged = previousTrendSide != TrendUnknown && trendSide != TrendUnknown && trendSide != previousTrendSide;

                if (trendChanged)
                {
                    DebugLog(timeBrt, "SUPERTREND_FLIP", string.Format(CultureInfo.InvariantCulture, "old={0} new={1}", SideName(previousTrendSide), SideName(trendSide)));
                    TryBridgeTradeBeforeContextInvalidation(timeBrt);
                    if (!inTrade)
                        InvalidateContext(timeBrt, "supertrend flip");
                }

                if (!inTrade)
                {
                    if (!calendarBlocked)
                    {
                        EnsureStaticContext(timeBrt);
                        CalculateAvwapAndEntryLevel(timeBrt);
                        TryRegularEntry(timeBrt);
                    }
                    else
                    {
                        ClearIntrabarPlotValues();
                    }
                }
            }

            UpdatePlotsAndPanel(timeBrt);
            previousTrendSide = trendSide;
        }

        private void ResetAllState()
        {
            pivots.Clear();
            closedTrades.Clear();
            loggedCalendarBlocks.Clear();
            currentBrtDate = DateTime.MinValue;
            dayPnl = 0;
            tradesToday = 0;
            dailyLocked = false;
            calendarBlocked = false;
            loggedDailyLock = false;
            trendSide = TrendUnknown;
            previousTrendSide = TrendUnknown;
            InvalidateContext(DateTime.MinValue, "reset");
            inTrade = false;
            totalNetPnl = 0;
            grossProfit = 0;
            grossLossAbs = 0;
            longNetPnl = 0;
            shortNetPnl = 0;
            wins = 0;
            losses = 0;
            targets = 0;
            stops = 0;
            eods = 0;
            maxConsecutiveLosses = 0;
            currentConsecutiveLosses = 0;
            equityPeak = InitialCapital;
            maxDrawdown = 0;
            tradeSequence = 0;
            resolvedCsvPath = string.Empty;
            csvHeaderWritten = false;
            lastCsvExportStatus = EnableCsvExport ? "aguardando trade fechado" : "desativado";
        }

        private void HandleDailyReset(DateTime dateBrt, DateTime timeBrt)
        {
            if (currentBrtDate == dateBrt)
                return;

            currentBrtDate = dateBrt;
            dayPnl = 0;
            tradesToday = 0;
            dailyLocked = false;
            calendarBlocked = false;
            loggedDailyLock = false;
            ResetDailyMarketStructure(timeBrt);
            DebugLog(timeBrt, "NEW_BRT_DAY", "date=" + dateBrt.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture));
        }

        private void ResetDailyMarketStructure(DateTime timeBrt)
        {
            pivots.Clear();
            InvalidateContext(timeBrt, "new BRT day");
            avwapCurrent = double.NaN;
            avwapPrevious = double.NaN;
            entryLevel = double.NaN;
            avwapEntryReference = double.NaN;
            avwapSeries[0] = double.NaN;
            entryLevelSeries[0] = double.NaN;
            DebugLog(timeBrt, "DAILY_MARKET_STRUCTURE_RESET", "pivots/context/anchor/avwap/entry cleared");
        }

        private void CalculateSuperTrend(DateTime timeBrt)
        {
            double trueRange = CurrentBar == 0
                ? High[0] - Low[0]
                : Math.Max(High[0] - Low[0], Math.Max(Math.Abs(High[0] - Close[1]), Math.Abs(Low[0] - Close[1])));
            trueRangeSeries[0] = trueRange;

            double atr = double.NaN;
            if (CurrentBar == AtrLength - 1)
            {
                double sum = 0;
                for (int barsAgo = 0; barsAgo < AtrLength; barsAgo++)
                    sum += trueRangeSeries[barsAgo];
                atr = sum / AtrLength;
            }
            else if (CurrentBar >= AtrLength)
            {
                atr = ((atrSeries[1] * (AtrLength - 1)) + trueRange) / AtrLength;
            }
            atrSeries[0] = atr;

            if (double.IsNaN(atr))
            {
                trendSide = TrendUnknown;
                upperBandSeries[0] = double.NaN;
                lowerBandSeries[0] = double.NaN;
                superTrendSeries[0] = double.NaN;
                return;
            }

            double hl2 = (High[0] + Low[0]) / 2.0;
            double basicUpper = hl2 + SuperTrendFactor * atr;
            double basicLower = hl2 - SuperTrendFactor * atr;
            double finalUpper = basicUpper;
            double finalLower = basicLower;

            if (CurrentBar > AtrLength - 1 && !double.IsNaN(upperBandSeries[1]) && !double.IsNaN(lowerBandSeries[1]))
            {
                double prevUpper = upperBandSeries[1];
                double prevLower = lowerBandSeries[1];
                finalLower = basicLower > prevLower || Close[1] < prevLower ? basicLower : prevLower;
                finalUpper = basicUpper < prevUpper || Close[1] > prevUpper ? basicUpper : prevUpper;
            }

            int pineDirection;
            if (CurrentBar <= AtrLength || double.IsNaN(atrSeries[1]))
            {
                pineDirection = 1;
            }
            else
            {
                double prevSuperTrend = superTrendSeries[1];
                double prevUpper = upperBandSeries[1];
                if (NearlyEqual(prevSuperTrend, prevUpper))
                    pineDirection = Close[0] > finalUpper ? -1 : 1;
                else
                    pineDirection = Close[0] < finalLower ? 1 : -1;
            }

            trendSide = pineDirection < 0 ? TrendBull : TrendBear;
            double superTrend = pineDirection < 0 ? finalLower : finalUpper;
            upperBandSeries[0] = finalUpper;
            lowerBandSeries[0] = finalLower;
            superTrendSeries[0] = superTrend;
        }

        private void ConfirmZigZagPivot(DateTime confirmationTimeBrt)
        {
            if (CurrentBar < ZigZagLegs * 2)
                return;

            int pivotBarsAgo = ZigZagLegs;
            int pivotBar = CurrentBar - pivotBarsAgo;
            double candidateHigh = High[pivotBarsAgo];
            double candidateLow = Low[pivotBarsAgo];
            bool isPivotHigh = true;
            bool isPivotLow = true;

            for (int offset = 1; offset <= ZigZagLegs; offset++)
            {
                if (candidateHigh < High[pivotBarsAgo + offset] || candidateHigh < High[pivotBarsAgo - offset])
                    isPivotHigh = false;
                if (candidateLow > Low[pivotBarsAgo + offset] || candidateLow > Low[pivotBarsAgo - offset])
                    isPivotLow = false;
            }

            if (isPivotHigh)
                AddPivot(pivotBar, ToBrt(Time[pivotBarsAgo]), candidateHigh, PivotType.High, confirmationTimeBrt);
            if (isPivotLow)
                AddPivot(pivotBar, ToBrt(Time[pivotBarsAgo]), candidateLow, PivotType.Low, confirmationTimeBrt);
        }

        private void AddPivot(int barIndex, DateTime pivotTimeBrt, double price, PivotType type, DateTime confirmationTimeBrt)
        {
            PivotInfo newPivot = new PivotInfo { BarIndex = barIndex, TimeBrt = pivotTimeBrt, Price = price, Type = type };

            if (pivots.Count > 0)
            {
                PivotInfo last = pivots[pivots.Count - 1];
                if (last.BarIndex == barIndex && last.Type == type)
                    return;

                if (last.Type == type)
                {
                    bool moreExtreme = type == PivotType.High ? price > last.Price : price < last.Price;
                    if (!moreExtreme)
                        return;

                    RemoveDrawObject(PivotTag(last));
                    pivots[pivots.Count - 1] = newPivot;
                    DrawPivot(newPivot);
                    DebugLog(confirmationTimeBrt, "ZIGZAG_PIVOT_REPLACED", string.Format(CultureInfo.InvariantCulture, "type={0} old_bar={1} old_price={2:F2} new_bar={3} new_time_brt={4:yyyy-MM-dd HH:mm} new_price={5:F2}", type, last.BarIndex, last.Price, barIndex, pivotTimeBrt, price));
                    return;
                }

                if (!PassesZigZagDeviation(price, last.Price))
                {
                    DebugLog(confirmationTimeBrt, "ZIGZAG_PIVOT_FILTERED", string.Format(CultureInfo.InvariantCulture, "type={0} pivot_bar={1} price={2:F2} last_type={3} last_price={4:F2} reversal_pct={5:F8}", type, barIndex, price, last.Type, last.Price, ZigZagReversal));
                    return;
                }
            }

            pivots.Add(newPivot);
            DrawPivot(newPivot);
            DebugLog(confirmationTimeBrt, "ZIGZAG_PIVOT_CONFIRMED", string.Format(CultureInfo.InvariantCulture, "type={0} pivot_bar={1} pivot_time_brt={2:yyyy-MM-dd HH:mm} price={3:F2}", type, barIndex, pivotTimeBrt, price));
        }

        private void DrawPivot(PivotInfo pivot)
        {
            if (!ShowZigZagMarkers || !ShouldPlotVisualMarker(pivot.TimeBrt))
                return;

            bool isHigh = pivot.Type == PivotType.High;
            string glyph = isHigh ? "▼" : "▲";
            Brush brush = isHigh
                ? (ZigZagHighBrush ?? Brushes.OrangeRed)
                : (ZigZagLowBrush ?? Brushes.LimeGreen);
            double offset = TickSizePoints * ZigZagMarkerOffsetTicks;
            double y = isHigh ? pivot.Price + offset : pivot.Price - offset;

            Draw.Text(
                this,
                PivotTag(pivot),
                false,
                glyph,
                CurrentBar - pivot.BarIndex,
                y,
                0,
                brush,
                new SimpleFont("Arial", ZigZagMarkerFontSize),
                TextAlignment.Center,
                Brushes.Transparent,
                Brushes.Transparent,
                0);
        }

        private bool ShouldPlotVisualMarker(DateTime timeBrt)
        {
            TimeSpan tod = timeBrt.TimeOfDay;
            return tod >= ParseTime(TradingStartBrt)
                && tod <= ParseTime(LastEntryBrt)
                && !calendarBlocked;
        }

        private string PivotTag(PivotInfo pivot)
        {
            return "HM13_ZZ_" + pivot.Type + "_" + pivot.BarIndex;
        }

        private bool PassesZigZagDeviation(double newPrice, double lastPrice)
        {
            if (double.IsNaN(lastPrice) || Math.Abs(lastPrice) <= 0.0000001)
                return true;

            double pct = Math.Abs(newPrice - lastPrice) / Math.Abs(lastPrice) * 100.0;
            return pct >= ZigZagReversal;
        }

        private void TryBridgeTradeBeforeContextInvalidation(DateTime timeBrt)
        {
            double signalAvwapReference;
            double signalEntryLevel;
            double effectiveOffset;

            if (!TryGetOperationalSignalLevel(out signalAvwapReference, out signalEntryLevel, out effectiveOffset))
                return;

            if (!contextActive || !CanEnter(timeBrt) || double.IsNaN(signalEntryLevel))
                return;

            DebugLog(timeBrt, "OPERATIONAL_SIGNAL_LEVEL_CALCULATED",
                string.Format(CultureInfo.InvariantCulture,
                    "side={0} signal_avwap_reference={1:F4} signal_entry_level={2:F4} configured_offset={3:F4} effective_offset={4:F4}",
                    SideName(contextSide),
                    signalAvwapReference,
                    signalEntryLevel,
                    AvwapOffsetPoints,
                    effectiveOffset));

            bool touched = Low[0] <= signalEntryLevel && High[0] >= signalEntryLevel;
            if (!touched)
                return;

            DebugLog(timeBrt, "BRIDGE_TRADE_DETECTED",
                string.Format(CultureInfo.InvariantCulture,
                    "side={0} signal_avwap_reference={1:F4} signal_entry_level={2:F4} configured_offset={3:F4} effective_offset={4:F4}",
                    SideName(contextSide),
                    signalAvwapReference,
                    signalEntryLevel,
                    AvwapOffsetPoints,
                    effectiveOffset));

            EnterVirtualTrade(
                timeBrt,
                contextSide == TrendBull ? TradeDirection.Long : TradeDirection.Short,
                signalEntryLevel,
                signalAvwapReference,
                signalEntryLevel,
                effectiveOffset,
                true);

            CheckOpenTradeExit(timeBrt, true);
        }

        private void EnsureStaticContext(DateTime timeBrt)
        {
            if (contextActive || !CanBuildContext(timeBrt))
                return;

            PivotType neededType = trendSide == TrendBull ? PivotType.Low : PivotType.High;
            PivotInfo pivot = FindLastPivot(neededType);
            if (pivot == null)
                return;

            contextActive = true;
            contextSide = trendSide;
            contextStartBar = CurrentBar;
            anchorBarIndex = pivot.BarIndex;
            anchorTimeBrt = pivot.TimeBrt;
            anchorPrice = pivot.Price;
            anchorType = pivot.Type;
            avwapCurrent = double.NaN;
            avwapPrevious = double.NaN;
            entryLevel = double.NaN;
            avwapEntryReference = double.NaN;
            currentVisualEntryLevel = double.NaN;
            currentSignalAvwapReference = double.NaN;
            currentSignalEntryLevel = double.NaN;
            currentSignalEffectiveOffset = double.NaN;
            DebugLog(timeBrt, "AVWAP_ANCHOR_CREATED", string.Format(CultureInfo.InvariantCulture, "side={0} anchor_bar={1} anchor_time_brt={2:yyyy-MM-dd HH:mm} anchor_price={3:F2} anchor_type={4}", SideName(contextSide), anchorBarIndex, anchorTimeBrt, anchorPrice, anchorType));
        }

        private PivotInfo FindLastPivot(PivotType type)
        {
            for (int i = pivots.Count - 1; i >= 0; i--)
            {
                if (pivots[i].Type == type)
                    return pivots[i];
            }
            return null;
        }

        private void CalculateAvwapAndEntryLevel(DateTime timeBrt)
        {
            avwapPrevious = double.NaN;
            avwapCurrent = double.NaN;
            entryLevel = double.NaN;
            avwapEntryReference = double.NaN;
            currentVisualEntryLevel = double.NaN;

            if (!contextActive || anchorBarIndex < 0 || anchorBarIndex > CurrentBar)
            {
                ClearIntrabarPlotValues();
                return;
            }

            double pv = 0;
            double vv = 0;
            for (int bar = anchorBarIndex; bar <= CurrentBar; bar++)
            {
                int barsAgo = CurrentBar - bar;
                double volume = Volume[barsAgo];
                double sourcePrice = contextSide == TrendBull ? Low[barsAgo] : High[barsAgo];
                pv += sourcePrice * volume;
                vv += volume;
            }

            if (Math.Abs(vv) <= 0.0000001)
            {
                avwapSeries[0] = double.NaN;
                entryLevelSeries[0] = double.NaN;
                return;
            }

            avwapCurrent = pv / vv;
            avwapSeries[0] = avwapCurrent;

            avwapPrevious = CurrentBar > 0 ? avwapSeries[1] : double.NaN;
            currentVisualEntryLevel = contextSide == TrendBull ? avwapCurrent + AvwapOffsetPoints : avwapCurrent - AvwapOffsetPoints;
            entryLevel = currentVisualEntryLevel;
            entryLevelSeries[0] = currentVisualEntryLevel;
            avwapEntryReference = avwapCurrent;

            if (CurrentBar <= contextStartBar)
                DebugLog(timeBrt, "CONTEXT_NOT_READY", string.Format(CultureInfo.InvariantCulture, "context_start_bar={0} current_bar={1} avwap_current={2:F4} visual_entry_level={3:F4}", contextStartBar, CurrentBar, avwapCurrent, currentVisualEntryLevel));

            DebugLog(timeBrt, "VISUAL_ENTRY_LEVEL_CALCULATED",
                string.Format(CultureInfo.InvariantCulture,
                    "side={0} avwap_current={1:F4} visual_entry_level={2:F4} offset={3:F4}",
                    SideName(contextSide),
                    avwapCurrent,
                    currentVisualEntryLevel,
                    AvwapOffsetPoints));
        }

        private bool CanBuildContext(DateTime timeBrt)
        {
            return timeBrt.TimeOfDay >= ParseTime(TradingStartBrt)
                && trendSide != TrendUnknown
                && !calendarBlocked;
        }

        private bool IsContextReady()
        {
            return contextActive
                && contextStartBar >= 0
                && CurrentBar > contextStartBar
                && CurrentBar > 0
                && !double.IsNaN(avwapSeries[1]);
        }

        private bool TryGetOperationalSignalLevel(out double signalAvwapReference, out double signalEntryLevel, out double effectiveOffset)
        {
            signalAvwapReference = double.NaN;
            signalEntryLevel = double.NaN;
            effectiveOffset = double.NaN;
            currentSignalAvwapReference = double.NaN;
            currentSignalEntryLevel = double.NaN;
            currentSignalEffectiveOffset = double.NaN;

            if (!contextActive || CurrentBar <= 0)
                return false;

            signalAvwapReference = avwapSeries[1];

            if (double.IsNaN(signalAvwapReference))
                return false;

            signalEntryLevel = contextSide == TrendBull
                ? signalAvwapReference + AvwapOffsetPoints
                : signalAvwapReference - AvwapOffsetPoints;

            effectiveOffset = signalEntryLevel - signalAvwapReference;

            double expected = contextSide == TrendBull ? AvwapOffsetPoints : -AvwapOffsetPoints;
            if (Math.Abs(effectiveOffset - expected) > 0.0001)
            {
                Print(string.Format(CultureInfo.InvariantCulture,
                    "{0} OFFSET WARNING | bar={1} side={2} expected={3:F4} effective={4:F4} avwap_ref={5:F4} entry={6:F4}",
                    VersionName,
                    CurrentBar,
                    SideName(contextSide),
                    expected,
                    effectiveOffset,
                    signalAvwapReference,
                    signalEntryLevel));
            }

            currentSignalAvwapReference = signalAvwapReference;
            currentSignalEntryLevel = signalEntryLevel;
            currentSignalEffectiveOffset = effectiveOffset;
            return true;
        }

        private void TryRegularEntry(DateTime timeBrt)
        {
            double signalAvwapReference;
            double signalEntryLevel;
            double effectiveOffset;

            if (!TryGetOperationalSignalLevel(out signalAvwapReference, out signalEntryLevel, out effectiveOffset))
                return;

            if (!contextActive || !IsContextReady() || !CanEnter(timeBrt) || double.IsNaN(signalEntryLevel))
                return;

            DebugLog(timeBrt, "OPERATIONAL_SIGNAL_LEVEL_CALCULATED",
                string.Format(CultureInfo.InvariantCulture,
                    "side={0} signal_avwap_reference={1:F4} signal_entry_level={2:F4} configured_offset={3:F4} effective_offset={4:F4}",
                    SideName(contextSide),
                    signalAvwapReference,
                    signalEntryLevel,
                    AvwapOffsetPoints,
                    effectiveOffset));

            if (Low[0] <= signalEntryLevel && High[0] >= signalEntryLevel)
            {
                TradeDirection direction = contextSide == TrendBull ? TradeDirection.Long : TradeDirection.Short;

                DebugLog(timeBrt, "ENTRY_DETECTED",
                    string.Format(CultureInfo.InvariantCulture,
                        "direction={0} signal_avwap_reference={1:F4} signal_entry_level={2:F4} configured_offset={3:F4} effective_offset={4:F4}",
                        direction,
                        signalAvwapReference,
                        signalEntryLevel,
                        AvwapOffsetPoints,
                        effectiveOffset));

                EnterVirtualTrade(
                    timeBrt,
                    direction,
                    signalEntryLevel,
                    signalAvwapReference,
                    signalEntryLevel,
                    effectiveOffset,
                    false);

                CheckOpenTradeExit(timeBrt, true);
            }
        }

        private bool CanEnter(DateTime timeBrt)
        {
            TimeSpan tod = timeBrt.TimeOfDay;
            bool insideWindow = tod >= ParseTime(TradingStartBrt) && tod <= ParseTime(LastEntryBrt);
            UpdateDailyLock(timeBrt);
            return insideWindow
                && !inTrade
                && !calendarBlocked
                && !dailyLocked
                && tradesToday < MaxTradesPerDay
                && dayPnl > DailyStopUsd
                && dayPnl < DailyProfitTargetUsd;
        }

        private void UpdateDailyLock(DateTime timeBrt)
        {
            bool lockedNow = tradesToday >= MaxTradesPerDay || dayPnl <= DailyStopUsd || dayPnl >= DailyProfitTargetUsd || calendarBlocked;
            if (lockedNow && !dailyLocked && !loggedDailyLock && !calendarBlocked)
            {
                loggedDailyLock = true;
                DebugLog(timeBrt, "DAILY_LOCK_ACTIVATED", string.Format(CultureInfo.InvariantCulture, "trades_today={0} day_pnl={1:F2}", tradesToday, dayPnl));
            }
            dailyLocked = lockedNow;
        }

        private void EnterVirtualTrade(DateTime timeBrt, TradeDirection direction, double virtualEntryPrice, double signalAvwapReference, double signalEntryLevel, double effectiveOffset, bool bridge)
        {
            inTrade = true;
            tradeDirection = direction;
            entryBarIndex = CurrentBar;
            entryTimeBrt = timeBrt;
            entryPrice = RoundToTick(virtualEntryPrice);
            stopPrice = direction == TradeDirection.Long ? entryPrice - StopPoints : entryPrice + StopPoints;
            targetPrice = direction == TradeDirection.Long ? entryPrice + TargetPoints : entryPrice - TargetPoints;
            currentTradeIsBridge = bridge;
            currentTradeAnchorTimeBrt = anchorTimeBrt;
            currentTradeAnchorPrice = anchorPrice;
            currentTradeAvwapReference = signalAvwapReference;
            currentTradeEntryLevel = signalEntryLevel;
            currentTradeEffectiveOffset = effectiveOffset;
            currentTradeVisualEntryLevelAtSignalBar = entryLevel;

            if (direction == TradeDirection.Long)
                Draw.ArrowUp(this, "HM13_ENTRY_LONG_" + CurrentBar + "_" + tradeSequence, false, 0, entryPrice - TickSizePoints * 8.0, Brushes.LimeGreen);
            else
                Draw.ArrowDown(this, "HM13_ENTRY_SHORT_" + CurrentBar + "_" + tradeSequence, false, 0, entryPrice + TickSizePoints * 8.0, Brushes.Red);

            DebugLog(timeBrt, "VIRTUAL_TRADE_OPENED", string.Format(CultureInfo.InvariantCulture, "direction={0} entry={1:F2} stop={2:F2} target={3:F2} bridge={4} signal_avwap_reference={5:F4} signal_entry_level={6:F4} effective_offset={7:F4}", direction, entryPrice, stopPrice, targetPrice, bridge, signalAvwapReference, signalEntryLevel, effectiveOffset));
        }

        private void CheckOpenTradeExit(DateTime timeBrt, bool entryCandleCheck)
        {
            if (!inTrade)
                return;

            ExitType exitType = ExitType.None;
            double exitPrice = double.NaN;
            bool entryCandle = CurrentBar == entryBarIndex;

            if (tradeDirection == TradeDirection.Long)
            {
                if (Low[0] <= stopPrice)
                {
                    exitType = ExitType.Stop;
                    exitPrice = stopPrice;
                }
                else if (!entryCandle && High[0] >= targetPrice)
                {
                    exitType = ExitType.Target;
                    exitPrice = targetPrice;
                }
            }
            else if (tradeDirection == TradeDirection.Short)
            {
                if (High[0] >= stopPrice)
                {
                    exitType = ExitType.Stop;
                    exitPrice = stopPrice;
                }
                else if (!entryCandle && Low[0] <= targetPrice)
                {
                    exitType = ExitType.Target;
                    exitPrice = targetPrice;
                }
            }

            if (exitType == ExitType.None && timeBrt.TimeOfDay >= ParseTime(EodBrt))
            {
                exitType = ExitType.EOD;
                exitPrice = Close[0];
            }

            if (exitType != ExitType.None)
                CloseVirtualTrade(timeBrt, exitPrice, exitType);
        }

        private void CloseVirtualTrade(DateTime timeBrt, double exitPriceRaw, ExitType exitType)
        {
            double virtualExitPrice = RoundToTick(exitPriceRaw);
            double points = tradeDirection == TradeDirection.Long ? virtualExitPrice - entryPrice : entryPrice - virtualExitPrice;
            double gross = points * PointValueUsd * Contracts;
            double net = gross - RoundTripCostUsd;
            dayPnl += net;
            tradesToday++;
            totalNetPnl += net;
            if (net >= 0)
            {
                wins++;
                grossProfit += net;
                currentConsecutiveLosses = 0;
            }
            else
            {
                losses++;
                grossLossAbs += Math.Abs(net);
                currentConsecutiveLosses++;
                maxConsecutiveLosses = Math.Max(maxConsecutiveLosses, currentConsecutiveLosses);
            }

            if (exitType == ExitType.Target)
                targets++;
            else if (exitType == ExitType.Stop)
                stops++;
            else if (exitType == ExitType.EOD)
                eods++;

            if (tradeDirection == TradeDirection.Long)
                longNetPnl += net;
            else if (tradeDirection == TradeDirection.Short)
                shortNetPnl += net;

            double currentEquity = InitialCapital + totalNetPnl;
            equityPeak = Math.Max(equityPeak, currentEquity);
            maxDrawdown = Math.Max(maxDrawdown, equityPeak - currentEquity);

            tradeSequence++;
            TradeRecord record = new TradeRecord
            {
                TradeId = tradeSequence,
                Version = VersionName,
                Instrument = Instrument != null ? Instrument.FullName : string.Empty,
                EntryTimeBrt = entryTimeBrt,
                ExitTimeBrt = timeBrt,
                Direction = tradeDirection,
                EntryPrice = entryPrice,
                ExitPrice = virtualExitPrice,
                StopPrice = stopPrice,
                TargetPrice = targetPrice,
                ExitType = exitType,
                GrossPnl = gross,
                Cost = RoundTripCostUsd,
                NetPnl = net,
                DayPnlAfterTrade = dayPnl,
                TradesTodayAfterTrade = tradesToday,
                IsBridgeTrade = currentTradeIsBridge,
                AnchorTimeBrt = currentTradeAnchorTimeBrt,
                AnchorPrice = currentTradeAnchorPrice,
                AvwapEntryReference = currentTradeAvwapReference,
                EntryLevel = currentTradeEntryLevel,
                OffsetPoints = AvwapOffsetPoints,
                EffectiveOffset = currentTradeEffectiveOffset,
                VisualEntryLevelAtSignalBar = currentTradeVisualEntryLevelAtSignalBar
            };
            closedTrades.Add(record);
            ExportTrade(record);

            string tag = "HM13_EXIT_" + exitType + "_" + CurrentBar + "_" + tradeSequence;
            Brush brush = exitType == ExitType.Target ? Brushes.LimeGreen : exitType == ExitType.Stop ? Brushes.Red : Brushes.DeepSkyBlue;
            Draw.Diamond(this, tag, false, 0, virtualExitPrice, brush);
            Draw.Text(this, tag + "_LBL", false, string.Format(CultureInfo.InvariantCulture, "{0} {1:C2}", exitType, net), 0, virtualExitPrice, 0, brush, new SimpleFont("Arial", 11), TextAlignment.Center, Brushes.Transparent, Brushes.Transparent, 0);

            DebugLog(timeBrt, exitType == ExitType.Target ? "TARGET_DETECTED" : exitType == ExitType.Stop ? "STOP_DETECTED" : "EOD_DETECTED",
                string.Format(CultureInfo.InvariantCulture, "trade_id={0} direction={1} entry={2:F2} exit={3:F2} gross={4:F2} net={5:F2} day_pnl={6:F2}", record.TradeId, record.Direction, record.EntryPrice, record.ExitPrice, record.GrossPnl, record.NetPnl, record.DayPnlAfterTrade));

            inTrade = false;
            tradeDirection = TradeDirection.None;
            entryBarIndex = -1;
            entryPrice = double.NaN;
            stopPrice = double.NaN;
            targetPrice = double.NaN;
            currentTradeIsBridge = false;
            currentTradeAnchorTimeBrt = DateTime.MinValue;
            currentTradeAnchorPrice = double.NaN;
            currentTradeAvwapReference = double.NaN;
            currentTradeEntryLevel = double.NaN;
            currentTradeEffectiveOffset = double.NaN;
            currentTradeVisualEntryLevelAtSignalBar = double.NaN;
            UpdateDailyLock(timeBrt);
        }

        private void InvalidateContext(DateTime timeBrt, string reason)
        {
            contextActive = false;
            contextSide = TrendUnknown;
            contextStartBar = -1;
            anchorBarIndex = -1;
            anchorTimeBrt = DateTime.MinValue;
            anchorPrice = double.NaN;
            anchorType = PivotType.None;
            avwapCurrent = double.NaN;
            avwapPrevious = double.NaN;
            entryLevel = double.NaN;
            avwapEntryReference = double.NaN;
            currentVisualEntryLevel = double.NaN;
            currentSignalAvwapReference = double.NaN;
            currentSignalEntryLevel = double.NaN;
            currentSignalEffectiveOffset = double.NaN;
            if (timeBrt != DateTime.MinValue)
                DebugLog(timeBrt, "CONTEXT_INVALIDATED", "reason=" + reason);
        }

        private void ClearIntrabarPlotValues()
        {
            avwapSeries[0] = double.NaN;
            entryLevelSeries[0] = double.NaN;
        }

        private void UpdatePlotsAndPanel(DateTime timeBrt)
        {
            Values[0][0] = superTrendSeries[0];
            Values[1][0] = contextActive ? avwapCurrent : double.NaN;
            Values[2][0] = contextActive ? entryLevel : double.NaN;

            if (trendSide == TrendBull)
                PlotBrushes[0][0] = SuperTrendBullBrush ?? Brushes.LimeGreen;
            else if (trendSide == TrendBear)
                PlotBrushes[0][0] = SuperTrendBearBrush ?? Brushes.Red;

            string status = calendarBlocked ? "BLOQUEADO CALENDARIO" : dailyLocked ? "TRAVADO" : "LIBERADO";
            double winRate = closedTrades.Count == 0 ? 0 : wins * 100.0 / closedTrades.Count;
            double profitFactor = Math.Abs(grossLossAbs) <= 0.0000001 ? 0 : grossProfit / grossLossAbs;
            double avgWin = wins == 0 ? 0 : grossProfit / wins;
            double avgLoss = losses == 0 ? 0 : grossLossAbs / losses;
            double payoff = Math.Abs(avgLoss) <= 0.0000001 ? 0 : avgWin / avgLoss;

            string panel = string.Format(CultureInfo.InvariantCulture,
                "{0}\nInstrumento: {1} | TF: {2}\nCapital: {3:C2} -> {4:C2}\nPnL liquido: {5:C2}\nTrades: {6} W/L: {7}/{8} Win%: {9:F1}\nPF: {10:F2} Payoff: {11:F2} MaxDD: {12:C2}\nMax perdas seq.: {13}\nTargets/Stops/EOD: {14}/{15}/{16}\nLong: {17:C2} Short: {18:C2}\nDia BRT: {19:yyyy-MM-dd} PnL: {20:C2} Trades: {21} Status: {22}\nCSV: {23}",
                VersionName,
                Instrument != null ? Instrument.FullName : string.Empty,
                BarsPeriod != null ? BarsPeriod.ToString() : string.Empty,
                InitialCapital,
                InitialCapital + totalNetPnl,
                totalNetPnl,
                closedTrades.Count,
                wins,
                losses,
                winRate,
                profitFactor,
                payoff,
                maxDrawdown,
                maxConsecutiveLosses,
                targets,
                stops,
                eods,
                longNetPnl,
                shortNetPnl,
                currentBrtDate,
                dayPnl,
                tradesToday,
                status,
                lastCsvExportStatus);
            Draw.TextFixed(this, "HM13_PANEL", panel, TextPosition.TopLeft, Brushes.White, new SimpleFont("Consolas", 12), Brushes.Black, Brushes.DimGray, 70);
        }

        private void ExportTrade(TradeRecord trade)
        {
            if (!EnableCsvExport)
                return;

            try
            {
                if (string.IsNullOrWhiteSpace(resolvedCsvPath))
                    resolvedCsvPath = ResolveCsvPath();

                string directory = Path.GetDirectoryName(resolvedCsvPath);
                if (!string.IsNullOrWhiteSpace(directory))
                    Directory.CreateDirectory(directory);

                bool writeHeader = !File.Exists(resolvedCsvPath) || new FileInfo(resolvedCsvPath).Length == 0;
                using (StreamWriter writer = new StreamWriter(resolvedCsvPath, true, Encoding.UTF8))
                {
                    if (writeHeader)
                        writer.WriteLine("trade_id,version,instrument,entry_time_brt,exit_time_brt,direction,entry_price,exit_price,stop_price,target_price,exit_type,gross_pnl,cost,net_pnl,day_pnl_after_trade,trades_today_after_trade,is_bridge_trade,anchor_time_brt,anchor_price,avwap_entry_reference,entry_level,offset_points,effective_offset,visual_entry_level_at_entry_bar");

                    writer.WriteLine(BuildTradeCsvLine(trade));
                }

                csvHeaderWritten = true;
                lastCsvExportStatus = "OK: " + resolvedCsvPath;
                DebugLog(DateTime.Now, "CSV_EXPORT_OK", resolvedCsvPath);
            }
            catch (Exception ex)
            {
                lastCsvExportStatus = "ERRO CSV: " + ex.Message;
                Print(VersionName + " CSV export error: " + ex.Message);
            }
        }

        private string BuildTradeCsvLine(TradeRecord trade)
        {
            return string.Join(",", new string[]
            {
                trade.TradeId.ToString(CultureInfo.InvariantCulture),
                Csv(trade.Version),
                Csv(trade.Instrument),
                Csv(trade.EntryTimeBrt.ToString("yyyy-MM-dd HH:mm:ss", CultureInfo.InvariantCulture)),
                Csv(trade.ExitTimeBrt.ToString("yyyy-MM-dd HH:mm:ss", CultureInfo.InvariantCulture)),
                trade.Direction.ToString(),
                trade.EntryPrice.ToString("F2", CultureInfo.InvariantCulture),
                trade.ExitPrice.ToString("F2", CultureInfo.InvariantCulture),
                trade.StopPrice.ToString("F2", CultureInfo.InvariantCulture),
                trade.TargetPrice.ToString("F2", CultureInfo.InvariantCulture),
                trade.ExitType.ToString(),
                trade.GrossPnl.ToString("F2", CultureInfo.InvariantCulture),
                trade.Cost.ToString("F2", CultureInfo.InvariantCulture),
                trade.NetPnl.ToString("F2", CultureInfo.InvariantCulture),
                trade.DayPnlAfterTrade.ToString("F2", CultureInfo.InvariantCulture),
                trade.TradesTodayAfterTrade.ToString(CultureInfo.InvariantCulture),
                trade.IsBridgeTrade ? "true" : "false",
                Csv(trade.AnchorTimeBrt == DateTime.MinValue ? string.Empty : trade.AnchorTimeBrt.ToString("yyyy-MM-dd HH:mm:ss", CultureInfo.InvariantCulture)),
                double.IsNaN(trade.AnchorPrice) ? string.Empty : trade.AnchorPrice.ToString("F2", CultureInfo.InvariantCulture),
                double.IsNaN(trade.AvwapEntryReference) ? string.Empty : trade.AvwapEntryReference.ToString("F4", CultureInfo.InvariantCulture),
                double.IsNaN(trade.EntryLevel) ? string.Empty : trade.EntryLevel.ToString("F4", CultureInfo.InvariantCulture),
                trade.OffsetPoints.ToString("F4", CultureInfo.InvariantCulture),
                trade.EffectiveOffset.ToString("F4", CultureInfo.InvariantCulture),
                double.IsNaN(trade.VisualEntryLevelAtSignalBar) ? string.Empty : trade.VisualEntryLevelAtSignalBar.ToString("F4", CultureInfo.InvariantCulture)
            });
        }

        private static string Csv(string value)
        {
            if (value == null)
                return string.Empty;
            return "\"" + value.Replace("\"", "\"\"") + "\"";
        }

        private void DebugLog(DateTime timeBrt, string evt, string details)
        {
            if (!EnableDebugLogs)
                return;
            Print(string.Format(CultureInfo.InvariantCulture, "{0} | {1:yyyy-MM-dd HH:mm:ss} BRT | bar={2} | {3} | {4}", VersionName, timeBrt, CurrentBar, evt, details));
        }

        private DateTime ToBrt(DateTime sourceTime)
        {
            string mode = string.IsNullOrWhiteSpace(SourceTimeZoneMode) ? "LocalMachine" : SourceTimeZoneMode.Trim();

            if (mode.Equals("AlreadyBrt", StringComparison.OrdinalIgnoreCase))
                return DateTime.SpecifyKind(sourceTime, DateTimeKind.Unspecified);

            if (mode.Equals("Utc", StringComparison.OrdinalIgnoreCase))
            {
                DateTime utc = sourceTime.Kind == DateTimeKind.Utc
                    ? sourceTime
                    : DateTime.SpecifyKind(sourceTime, DateTimeKind.Utc);
                return TimeZoneInfo.ConvertTimeFromUtc(utc, brtTimeZone);
            }

            // LocalMachine is the default. Exchange is intentionally routed through the same
            // conversion path in this auditor build because NinjaTrader chart timestamps can
            // vary by data series/session template; EnableDebugLogs exposes the raw and BRT
            // values so the selected source mode can be validated against TradingView.
            DateTime normalized = sourceTime;
            if (sourceTime.Kind == DateTimeKind.Unspecified)
                normalized = DateTime.SpecifyKind(sourceTime, DateTimeKind.Local);
            return TimeZoneInfo.ConvertTime(normalized, brtTimeZone);
        }

        private void LogTimeConversion(DateTime rawTime, DateTime timeBrt, DateTime dateBrt)
        {
            if (!EnableDebugLogs)
                return;

            string horaBrt = timeBrt.TimeOfDay.ToString(@"hh\:mm\:ss", CultureInfo.InvariantCulture);
            DebugLog(timeBrt, "TIMEZONE_AUDIT", string.Format(CultureInfo.InvariantCulture,
                "raw_time={0:yyyy-MM-dd HH:mm:ss} raw_kind={1} brt_converted={2:yyyy-MM-dd HH:mm:ss} date_brt={3:yyyy-MM-dd} hora_brt={4} operational_tz={5} source_mode={6} local_tz={7}",
                rawTime,
                rawTime.Kind,
                timeBrt,
                dateBrt,
                horaBrt,
                brtTimeZone != null ? brtTimeZone.Id : string.Empty,
                SourceTimeZoneMode,
                TimeZoneInfo.Local.Id));
        }

        private TimeZoneInfo ResolveTimeZone(string requestedId)
        {
            string[] candidates = new string[] { requestedId, "E. South America Standard Time", "America/Sao_Paulo" };
            foreach (string candidate in candidates)
            {
                if (string.IsNullOrWhiteSpace(candidate))
                    continue;
                try { return TimeZoneInfo.FindSystemTimeZoneById(candidate); }
                catch { }
            }
            return TimeZoneInfo.Local;
        }

        private HashSet<DateTime> ParseBlockedDates(string datesCsv)
        {
            HashSet<DateTime> dates = new HashSet<DateTime>();
            if (string.IsNullOrWhiteSpace(datesCsv))
                return dates;
            string[] parts = datesCsv.Split(new[] { ',', ';', '|', ' ', '\n', '\r', '\t' }, StringSplitOptions.RemoveEmptyEntries);
            foreach (string part in parts)
            {
                DateTime parsed;
                if (DateTime.TryParseExact(part.Trim(), "yyyy-MM-dd", CultureInfo.InvariantCulture, DateTimeStyles.None, out parsed))
                    dates.Add(parsed.Date);
            }
            return dates;
        }

        private string ResolveCsvPath()
        {
            string baseName = string.Format(
                CultureInfo.InvariantCulture,
                "{0}_{1}_{2}_trades.csv",
                VersionName,
                Instrument != null ? SanitizeFileName(Instrument.FullName) : "Instrument",
                DateTime.Now.ToString("yyyyMMdd_HHmmss", CultureInfo.InvariantCulture));

            if (string.IsNullOrWhiteSpace(CsvExportPath))
            {
                string documents = Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);
                string folder = Path.Combine(documents, "NinjaTrader 8", "export", VersionName);
                Directory.CreateDirectory(folder);
                return Path.Combine(folder, baseName);
            }

            string path = CsvExportPath.Trim();
            bool looksLikeCsvFile = path.EndsWith(".csv", StringComparison.OrdinalIgnoreCase);

            if (looksLikeCsvFile)
            {
                string directory = Path.GetDirectoryName(path);
                if (!string.IsNullOrWhiteSpace(directory))
                    Directory.CreateDirectory(directory);

                return path;
            }

            Directory.CreateDirectory(path);
            return Path.Combine(path, baseName);
        }

        private string SanitizeFileName(string value)
        {
            if (string.IsNullOrWhiteSpace(value))
                return "Instrument";

            foreach (char c in Path.GetInvalidFileNameChars())
                value = value.Replace(c, '_');

            return value.Replace(' ', '_');
        }

        private TimeSpan ParseTime(string value)
        {
            TimeSpan parsed;
            if (TimeSpan.TryParseExact(value, new[] { "hh\\:mm", "h\\:mm", "hh\\:mm\\:ss", "h\\:mm\\:ss" }, CultureInfo.InvariantCulture, out parsed))
                return parsed;
            return TimeSpan.Zero;
        }

        private double RoundToTick(double price)
        {
            if (TickSizePoints <= 0 || double.IsNaN(price))
                return price;
            return Math.Round(price / TickSizePoints, MidpointRounding.AwayFromZero) * TickSizePoints;
        }

        private static bool NearlyEqual(double a, double b)
        {
            return Math.Abs(a - b) <= 0.0000001;
        }

        private string SideName(int side)
        {
            if (side == TrendBull)
                return "BULL_LONG";
            if (side == TrendBear)
                return "BEAR_SHORT";
            return "UNKNOWN";
        }

        #region Parameters
        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "SuperTrend ATR Length", GroupName = "01 Indicadores", Order = 1)]
        public int AtrLength { get; set; }

        [NinjaScriptProperty]
        [Range(0.0001, double.MaxValue)]
        [Display(Name = "SuperTrend Factor", GroupName = "01 Indicadores", Order = 2)]
        public double SuperTrendFactor { get; set; }

        [NinjaScriptProperty]
        [Range(1, 20)]
        [Display(Name = "ZigZag Legs", GroupName = "01 Indicadores", Order = 3)]
        public int ZigZagLegs { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, double.MaxValue)]
        [Display(Name = "ZigZag Reversal %", Description = "Filtro percentual estilo Pine: abs(novo - ultimo) / ultimo * 100 >= valor.", GroupName = "01 Indicadores", Order = 4)]
        public double ZigZagReversal { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, double.MaxValue)]
        [Display(Name = "Offset AVWAP (pontos)", GroupName = "01 Indicadores", Order = 5)]
        public double AvwapOffsetPoints { get; set; }

        [NinjaScriptProperty]
        [Range(0.0001, double.MaxValue)]
        [Display(Name = "Valor por ponto USD", GroupName = "02 Mercado", Order = 1)]
        public double PointValueUsd { get; set; }

        [NinjaScriptProperty]
        [Range(0.0001, double.MaxValue)]
        [Display(Name = "Tick minimo em pontos", GroupName = "02 Mercado", Order = 2)]
        public double TickSizePoints { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Contratos", GroupName = "02 Mercado", Order = 3)]
        public int Contracts { get; set; }

        [NinjaScriptProperty]
        [Range(0.0001, double.MaxValue)]
        [Display(Name = "Stop em pontos", GroupName = "03 Gestao", Order = 1)]
        public double StopPoints { get; set; }

        [NinjaScriptProperty]
        [Range(0.0001, double.MaxValue)]
        [Display(Name = "Target em pontos", GroupName = "03 Gestao", Order = 2)]
        public double TargetPoints { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, double.MaxValue)]
        [Display(Name = "Custo round-trip USD", GroupName = "03 Gestao", Order = 3)]
        public double RoundTripCostUsd { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, double.MaxValue)]
        [Display(Name = "Capital inicial visual", GroupName = "03 Gestao", Order = 4)]
        public double InitialCapital { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Max trades por dia", GroupName = "03 Gestao", Order = 5)]
        public int MaxTradesPerDay { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Meta diaria liquida USD", GroupName = "03 Gestao", Order = 6)]
        public double DailyProfitTargetUsd { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Stop diario liquido USD", GroupName = "03 Gestao", Order = 7)]
        public double DailyStopUsd { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Timezone operacional", GroupName = "04 Horario", Order = 1)]
        public string OperationalTimeZoneId { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "SourceTimeZoneMode", Description = "LocalMachine, Exchange, Utc ou AlreadyBrt. Exchange mantém a conversão de máquina local e registra auditoria explícita.", GroupName = "04 Horario", Order = 2)]
        public string SourceTimeZoneMode { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Inicio operacional BRT", GroupName = "04 Horario", Order = 3)]
        public string TradingStartBrt { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Limite nova entrada BRT", GroupName = "04 Horario", Order = 4)]
        public string LastEntryBrt { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Fechamento EOD BRT", GroupName = "04 Horario", Order = 5)]
        public string EodBrt { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Datas bloqueadas yyyy-MM-dd", GroupName = "05 Calendario", Order = 1)]
        public string BlockedDatesCsv { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "EnableCsvExport", GroupName = "06 Auditoria", Order = 1)]
        public bool EnableCsvExport { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "CsvExportPath", GroupName = "06 Auditoria", Order = 2)]
        public string CsvExportPath { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "EnableDebugLogs", GroupName = "06 Auditoria", Order = 3)]
        public bool EnableDebugLogs { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Mostrar marcadores ZigZag", GroupName = "07 Visual", Order = 1)]
        public bool ShowZigZagMarkers { get; set; }

        [NinjaScriptProperty]
        [Range(6, 30)]
        [Display(Name = "Tamanho marcador ZigZag", GroupName = "07 Visual", Order = 2)]
        public int ZigZagMarkerFontSize { get; set; }

        [NinjaScriptProperty]
        [Range(0, 50)]
        [Display(Name = "Offset visual marcador ZigZag em ticks", GroupName = "07 Visual", Order = 3)]
        public int ZigZagMarkerOffsetTicks { get; set; }

        [XmlIgnore]
        [Display(Name = "Cor ZigZag Topo", GroupName = "07 Visual", Order = 4)]
        public Brush ZigZagHighBrush { get; set; }

        [Browsable(false)]
        public string ZigZagHighBrushSerializable
        {
            get { return NinjaTrader.Gui.Serialize.BrushToString(ZigZagHighBrush ?? Brushes.OrangeRed); }
            set { ZigZagHighBrush = NinjaTrader.Gui.Serialize.StringToBrush(value) ?? Brushes.OrangeRed; }
        }

        [XmlIgnore]
        [Display(Name = "Cor ZigZag Fundo", GroupName = "07 Visual", Order = 5)]
        public Brush ZigZagLowBrush { get; set; }

        [Browsable(false)]
        public string ZigZagLowBrushSerializable
        {
            get { return NinjaTrader.Gui.Serialize.BrushToString(ZigZagLowBrush ?? Brushes.LimeGreen); }
            set { ZigZagLowBrush = NinjaTrader.Gui.Serialize.StringToBrush(value) ?? Brushes.LimeGreen; }
        }

        [XmlIgnore]
        [Display(Name = "Cor SuperTrend Comprador", GroupName = "07 Visual", Order = 6)]
        public Brush SuperTrendBullBrush { get; set; }

        [Browsable(false)]
        public string SuperTrendBullBrushSerializable
        {
            get { return NinjaTrader.Gui.Serialize.BrushToString(SuperTrendBullBrush ?? Brushes.LimeGreen); }
            set { SuperTrendBullBrush = NinjaTrader.Gui.Serialize.StringToBrush(value) ?? Brushes.LimeGreen; }
        }

        [XmlIgnore]
        [Display(Name = "Cor SuperTrend Vendedor", GroupName = "07 Visual", Order = 7)]
        public Brush SuperTrendBearBrush { get; set; }

        [Browsable(false)]
        public string SuperTrendBearBrushSerializable
        {
            get { return NinjaTrader.Gui.Serialize.BrushToString(SuperTrendBearBrush ?? Brushes.Red); }
            set { SuperTrendBearBrush = NinjaTrader.Gui.Serialize.StringToBrush(value) ?? Brushes.Red; }
        }
        #endregion
    }
}
