#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using NinjaTrader.Cbi;
using NinjaTrader.Data;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.Strategies;
#endregion

namespace NinjaTrader
{
    public static class HawkSmartPanel_EndDayBridge
    {
        public static volatile bool AutoCloseRequested;
        public static volatile bool AutoCloseCompleted;
        public static volatile bool AutoCloseRunning;

        public static volatile int LastRequestId;
        public static volatile int LastCompletedRequestId;
        public static string LastStatus = "Idle";
        public static string LastMessage = string.Empty;

        public static void RequestAutoClose()
        {
            LastRequestId++;
            AutoCloseRequested = true;
            AutoCloseCompleted = false;
            LastStatus = "Requested";
            LastMessage = "AutoClose requested by SmartPanel.";
        }

        public static void Reset()
        {
            AutoCloseRequested = false;
            AutoCloseCompleted = false;
            AutoCloseRunning = false;
            LastStatus = "Idle";
            LastMessage = string.Empty;
        }
    }
}

namespace NinjaTrader.NinjaScript.Strategies
{
    public class HawkSmartPanel_EndDayAutoClose : Strategy
    {
        private enum AutoCloseState
        {
            Idle,
            Requested,
            Flattening,
            FlatConfirmed,
            Failed
        }

        private AutoCloseState state = AutoCloseState.Idle;
        private int activeRequestId = -1;
        private int flattenAttempts;
        private DateTime lastAttemptUtc = DateTime.MinValue;

        [NinjaScriptProperty]
        [Range(1, 20)]
        [Display(Name = "MaxFlattenAttempts", GroupName = "Parameters", Order = 1)]
        public int MaxFlattenAttempts { get; set; }

        [NinjaScriptProperty]
        [Range(50, 5000)]
        [Display(Name = "RetryIntervalMs", GroupName = "Parameters", Order = 2)]
        public int RetryIntervalMs { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "EnableDebugLogs", GroupName = "Parameters", Order = 3)]
        public bool EnableDebugLogs { get; set; }

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Name = "HawkSmartPanel_EndDayAutoClose";
                Description = "Service strategy to flatten only the current account/instrument when requested by HawkSmartPanel.";
                Calculate = Calculate.OnEachTick;
                EntriesPerDirection = 1;
                EntryHandling = EntryHandling.AllEntries;
                IsExitOnSessionCloseStrategy = false;
                IsInstantiatedOnEachOptimizationIteration = false;

                MaxFlattenAttempts = 8;
                RetryIntervalMs = 250;
                EnableDebugLogs = true;
            }
            else if (State == State.Realtime)
            {
                LogInfo("Realtime started. Waiting for AutoClose request.");
                PublishBridgeState(AutoCloseState.Idle, "Strategy ready.");
            }
            else if (State == State.Terminated)
            {
                if (HawkSmartPanel_EndDayBridge.AutoCloseRunning)
                    HawkSmartPanel_EndDayBridge.AutoCloseRunning = false;

                LogInfo("Terminated.");
            }
        }

        protected override void OnBarUpdate()
        {
            if (State != State.Realtime)
                return;

            if (Instrument == null || Account == null)
                return;

            if (HawkSmartPanel_EndDayBridge.AutoCloseRequested && !HawkSmartPanel_EndDayBridge.AutoCloseRunning)
            {
                StartNewRequest();
            }

            if (state == AutoCloseState.Flattening)
            {
                TryFlattenLoop();
            }
        }

        private void StartNewRequest()
        {
            activeRequestId = HawkSmartPanel_EndDayBridge.LastRequestId;
            flattenAttempts = 0;

            HawkSmartPanel_EndDayBridge.AutoCloseRunning = true;
            HawkSmartPanel_EndDayBridge.AutoCloseCompleted = false;

            state = AutoCloseState.Requested;
            PublishBridgeState(state, "AutoClose request captured.");
            LogInfo($"Request #{activeRequestId} captured for account={Account?.Name ?? "?"}, instrument={Instrument?.FullName ?? "?"}.");

            if (IsFlat())
            {
                ConfirmFlat("Position already FLAT.");
                return;
            }

            state = AutoCloseState.Flattening;
            PublishBridgeState(state, "Flattening started.");
            ForceFlatten("Initial flatten trigger.");
        }

        private void TryFlattenLoop()
        {
            if (IsFlat())
            {
                ConfirmFlat("Position became FLAT.");
                return;
            }

            var elapsedMs = (DateTime.UtcNow - lastAttemptUtc).TotalMilliseconds;
            if (elapsedMs < RetryIntervalMs)
                return;

            if (flattenAttempts >= MaxFlattenAttempts)
            {
                state = AutoCloseState.Failed;
                HawkSmartPanel_EndDayBridge.AutoCloseRunning = false;
                PublishBridgeState(state, $"Failed after {flattenAttempts} attempts.");
                LogInfo($"[FAILED] Request #{activeRequestId}. Position still {Position.MarketPosition}, qty={Position.Quantity}.");
                return;
            }

            ForceFlatten($"Retry flatten attempt {flattenAttempts + 1}/{MaxFlattenAttempts}.");
        }

        private void ForceFlatten(string reason)
        {
            flattenAttempts++;
            lastAttemptUtc = DateTime.UtcNow;

            try
            {
                CancelWorkingOrdersForInstrument();
            }
            catch (Exception ex)
            {
                LogInfo($"CancelWorkingOrdersForInstrument exception: {ex.Message}");
            }

            try
            {
                var mp = Position.MarketPosition;
                if (mp == MarketPosition.Long)
                {
                    ExitLong("EndDayAutoClose_ExitLong", "");
                    LogInfo($"ExitLong submitted. attempt={flattenAttempts}. reason={reason}");
                }
                else if (mp == MarketPosition.Short)
                {
                    ExitShort("EndDayAutoClose_ExitShort", "");
                    LogInfo($"ExitShort submitted. attempt={flattenAttempts}. reason={reason}");
                }
                else
                {
                    ConfirmFlat("Flat during flatten loop.");
                    return;
                }
            }
            catch (Exception ex)
            {
                LogInfo($"Exit exception: {ex.Message}");
            }

            try
            {
                var accountPosition = Account?.Positions?.FirstOrDefault(p => p.Instrument == Instrument);
                if (accountPosition == null || accountPosition.Quantity == 0)
                {
                    LogInfo("Account position already flat for instrument. Flatten fallback skipped.");
                    return;
                }

                TryAccountFlattenForCurrentInstrument();
                LogInfo($"Account.Flatten fallback executed for instrument={Instrument?.FullName ?? "?"}. attempt={flattenAttempts}.");
            }
            catch (Exception ex)
            {
                LogInfo($"Account.Flatten exception: {ex.Message}");
            }
        }

        private void CancelWorkingOrdersForInstrument()
        {
            try
            {
                if (Account == null || Instrument == null || Account.Orders == null)
                    return;

                var ordersToCancel = Account.Orders
                    .Where(o =>
                        o != null
                        && o.Instrument != null
                        && o.Instrument == Instrument
                        && (o.OrderState == OrderState.Working
                            || o.OrderState == OrderState.Accepted
                            || o.OrderState == OrderState.Submitted
                            || o.OrderState == OrderState.PartFilled))
                    .ToList();

                foreach (var ord in ordersToCancel)
                {
                    try
                    {
                        Account.Cancel(new[] { ord });
                        LogInfo($"Order cancel requested: {ord.Name} state={ord.OrderState}");
                    }
                    catch (Exception ex)
                    {
                        LogInfo($"Order cancel exception: {ex.Message}");
                    }
                }
            }
            catch (Exception ex)
            {
                LogInfo($"CancelWorkingOrdersForInstrument failed: {ex.Message}");
            }
        }

        private void TryAccountFlattenForCurrentInstrument()
        {
            try
            {
                if (Account == null || Instrument == null)
                    return;

                Account.Flatten(new List<Instrument> { Instrument });
            }
            catch (Exception ex)
            {
                LogInfo($"Account.Flatten exception: {ex.Message}");
                throw;
            }
        }

        private bool IsFlat()
        {
            return Position != null
                && Position.MarketPosition == MarketPosition.Flat
                && Position.Quantity == 0;
        }

        private void ConfirmFlat(string message)
        {
            state = AutoCloseState.FlatConfirmed;

            HawkSmartPanel_EndDayBridge.AutoCloseCompleted = true;
            HawkSmartPanel_EndDayBridge.AutoCloseRequested = false;
            HawkSmartPanel_EndDayBridge.AutoCloseRunning = false;
            HawkSmartPanel_EndDayBridge.LastCompletedRequestId = activeRequestId;

            PublishBridgeState(state, message);
            LogInfo($"[SUCCESS] Request #{activeRequestId}: {message}");
        }

        private void PublishBridgeState(AutoCloseState newState, string message)
        {
            HawkSmartPanel_EndDayBridge.LastStatus = newState.ToString();
            HawkSmartPanel_EndDayBridge.LastMessage = message;
        }

        private void LogInfo(string message)
        {
            if (!EnableDebugLogs)
                return;

            Print($"[HawkSmartPanel_EndDayAutoClose] {DateTime.Now:HH:mm:ss.fff} | {message}");
        }
    }
}
