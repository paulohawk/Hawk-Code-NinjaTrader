#region Using declarations
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Globalization;
using System.IO;
using IOPath = System.IO.Path;
using System.Linq;
using System.Threading;
using System.Windows; // TextAlignment
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Shapes;
using System.Windows.Threading;
using System.Xml.Serialization;
using NinjaTrader.Cbi;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Chart;
using NinjaTrader.Gui.Tools;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.Indicators;
using NinjaTrader.NinjaScript.DrawingTools;
using NinjaTrader.Data;              // Necessário para BarsPeriodType
using WpfEllipse = System.Windows.Shapes.Ellipse;
using WpfRectangle = System.Windows.Shapes.Rectangle;
using SharpDX;
using SharpDX.DirectWrite;
// Removido SharpDX.Mathematics.Interop para evitar dependência ausente

// Evitar ambiguidades com SharpDX
using Color = System.Windows.Media.Color;
using Point = System.Windows.Point;
using Stretch = System.Windows.Media.Stretch;
using TextAlignment = System.Windows.TextAlignment;
#endregion

// Hawk - Smart Panel (SmartBoletaIndicator)
namespace NinjaTrader.NinjaScript.Indicators
{
    public class SmartBoletaIndicator : Indicator
    {
        #region Constantes e campos
        private const int AttachPollMs = 1000;
        private const double EmbedHeightPx = 320.0;
        private const int AtrLabelOffsetTicks = 80; // default fixado
        private readonly string LogPath = IOPath.Combine(Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments), "NinjaTrader 8", "logs", "smartboleta_indicator.log");
        private static int BoletaCounter = 0;

        private static readonly Dictionary<int, WeakReference<SmartBoletaIndicator>> ActivePerChart = new Dictionary<int, WeakReference<SmartBoletaIndicator>>();
        private static readonly Dictionary<int, string> BoletaIdPerChart = new Dictionary<int, string>();

        // Persistência leve por BoletaId
        private class SavedPrefs
        {
            public int Qty;
            public double StopFinancial;
            public bool AtrOn;
            public bool BeOn;
            public bool OnClickOn;
            public bool RiskOn;
            public DesiredKey BuyKey;
            public DesiredKey SellKey;
            public TimeSpan? EndDayTime;
            public SBEndDayScope EndDayScope;
            // ATR config
            public bool AtrAuto;
            public int AtrFixedMinutes;
            public int AtrFixedPeriod;
            public double AtrFixedMultiplier;
        }
        private static readonly ConcurrentDictionary<string, SavedPrefs> PrefsById = new ConcurrentDictionary<string, SavedPrefs>();

        private readonly Brush BronzeBrush = new SolidColorBrush(Color.FromRgb(170, 120, 60));
        private readonly Brush GraphiteBrush = new SolidColorBrush(Color.FromRgb(72, 72, 72));

        private Gui.Chart.Chart chartWindow;
        private Gui.Chart.ChartTrader chartTrader;
        private Grid chartTraderGrid;
        private Border embeddedWrapper;
        private RowDefinition addedRow;
        private SelectionChangedEventHandler tabHandler;
        private DispatcherTimer attachTimer;
        private DispatcherTimer decoTimer; // timer para recomputar decorações
        private bool panelActive = false;
        private bool _mainEnabled = false; // estado do botão ON/OFF da boleta

        private SmartBoletaEmbeddedControl embeddedControl;

        private int atrPeriod = 14;
        private double atrMultiplier = 1.0;
        private readonly Queue<double> trQueue = new Queue<double>();
        private double trSum = 0.0;

        // Secundário (ATR fixo em TF escolhido)
        private readonly Queue<double> trQueueFixed = new Queue<double>();
        private double trSumFixed = 0.0;

        private int _lastAtrTicks = 0;
        private double _lastAtrDollarPerContract = 0.0;

        // Tags do desenho ATR
        private string _atrLineTag;
        private string _atrTextTag1;
        private string _atrTextTag2;

        private Account myAccount;
        private ChartScale MyChartScale;
        private Order myOrder;
        private int myQuantity;
        private bool buyButton = false;
        private bool sellButton = false;

        private DesiredKey buyKey = DesiredKey.LeftShift;
        private DesiredKey sellKey = DesiredKey.LeftAlt;
        private Key kbuyKey;
        private Key ksellKey;

        private StopOrderTypes stopOrderType = StopOrderTypes.StopMarket;
        private OrderType orderType;
        private bool tradingFromChart = false;

        public TimeSpan? EndDayTime { get; set; } = null;
        public SBEndDayScope EndDayScope { get; set; } = SBEndDayScope.ThisChartOnly;

        public string BoletaId { get; private set; }

        private EndDayOverlayController overlayController;

        // BE state (mini one-shot)
        private bool _beFireRequest = false;
        private bool _beActive = false;

        [Display(Name = "Scan interval (seconds)", Order = 2, GroupName = "Debug")]
        public int ScanIntervalSeconds { get; set; } = 3;
        private DateTime _lastScanUtc = DateTime.MinValue;

        // RISK
        private bool _riskOn = true;
        private bool _riskBlocked = false;
        private DateTime _riskBlockedUntil = DateTime.MinValue;
        private DateTime _riskDay = DateTime.MinValue;
        private int _riskTrades = 0;
        private int _riskContracts = 0;
        private bool _warnedLoss = false;
        private bool _warnedTrades = false;
        private bool _warnedContracts = false;
        private bool _warnedProfit = false;
        private bool _riskOverlayShown = false;
        private bool _mainToggleLockedByRisk = false;

        // account selector hook/cache
        private AccountSelector accountSelector;
        private Account selectedAccountCached;

        // Flag de limpeza pós-flat
        private bool _flatCleanupDone = false;
        #endregion

        #region Decorator (STOP/TARGET labels)
        private readonly List<OrderType> decoStopTypes = new List<OrderType> { OrderType.StopMarket, OrderType.StopLimit, OrderType.MIT };
        private readonly List<OrderType> decoTargetTypes = new List<OrderType> { OrderType.Limit };

        private enum DecorKind { STOP, TARGET, OTHER }
        private class DecorInfo
        {
            public DecorKind Kind;
            public string Text;
        }

        private readonly ConcurrentDictionary<string, int> decoQtyByKey = new ConcurrentDictionary<string, int>();
        private readonly ConcurrentDictionary<double, DecorInfo> decoToRender = new ConcurrentDictionary<double, DecorInfo>();
        private readonly object _decoLock = new object();

        private SimpleFont decoFont;
        private TextFormat decoTextFormat;
        private float decoSampleTextWidth;
        private const string DecoSampleText = "XXXXXXXX XXX XXXX";
        #endregion

        #region Conjuntos auxiliares
        private static readonly HashSet<OrderType> StopOrderTypesSet = new HashSet<OrderType>
        {
            OrderType.StopMarket,
            OrderType.StopLimit,
            OrderType.MIT
        };
        #endregion

        #region Propriedades ATR (novo toggle auto/fixo)
        [Display(Name = "ATR Auto (usa TF do gráfico)", Order = 8, GroupName = "ATR")]
        public bool AtrAuto { get; set; } = true;

        [Display(Name = "ATR Fixed TF (minutos)", Order = 12, GroupName = "ATR")]
        public int AtrFixedMinutes { get; set; } = 60;

        [Display(Name = "ATR Fixed Period", Order = 13, GroupName = "ATR")]
        public int AtrFixedPeriod { get; set; } = 14;

        [Display(Name = "ATR Fixed Multiplier", Order = 14, GroupName = "ATR")]
        public double AtrFixedMultiplier { get; set; } = 1.0;
        #endregion

        private int GetChartKey()
        {
            try { return ChartControl != null ? ChartControl.GetHashCode() : 0; }
            catch { return 0; }
        }

        #region Propriedades
        [Display(Name = "Enable diagnostic logging", Order = 1, GroupName = "Debug")]
        public bool EnableDiagnosticLogging { get; set; }

        [Display(Name = "Buy hotkey", Order = 1, GroupName = "Hotkeys")]
        public DesiredKey BuyKey { get => buyKey; set { buyKey = value; MapDesiredKeys(); SavePrefs(); } }

        [Display(Name = "Sell hotkey", Order = 2, GroupName = "Hotkeys")]
        public DesiredKey SellKey { get => sellKey; set { sellKey = value; MapDesiredKeys(); SavePrefs(); } }

        [Display(Name = "Stop order type", Order = 1, GroupName = "Order management")]
        public StopOrderTypes StopOrderType
        {
            get => stopOrderType;
            set { stopOrderType = value; orderType = (stopOrderType == StopOrderTypes.StopLimit) ? OrderType.StopLimit : OrderType.StopMarket; }
        }

        [Display(Name = "ATR Period (auto mode)", Order = 10, GroupName = "ATR")]
        public int AtrPeriod { get => atrPeriod; set => atrPeriod = Math.Max(1, value); }

        [Display(Name = "ATR Multiplier (auto mode)", Order = 11, GroupName = "ATR")]
        public double AtrMultiplier { get => atrMultiplier; set => atrMultiplier = Math.Max(0.0, value); }

        [Display(Name = "BreakEven ticks", Order = 20, GroupName = "BE", Description = "Ticks a favor para puxar o stop para o breakeven.")]
        public int BreakEvenTicks { get; set; } = 10;

        [Display(Name = "Min favor factor (ex: 2 => 2x BE ticks)", Order = 21, GroupName = "BE")]
        public double MinFavorFactor { get; set; } = 2.0;

        [Display(Name = "Overlay EndDay", Order = 100, GroupName = "EndDay Overlay")]
        public bool EnableOverlayOnEndDay { get; set; } = true;

        [Display(Name = "Overlay Opacity", Order = 101, GroupName = "EndDay Overlay")]
        public double OverlayOpacity { get; set; } = 0.85;

        [Display(Name = "Overlay Duration (s)", Order = 102, GroupName = "EndDay Overlay")]
        public int OverlayDurationSeconds { get; set; } = 90;

        [Display(Name = "Overlay Message", Order = 103, GroupName = "EndDay Overlay")]
        public string OverlayMessage { get; set; } = "Atenção: horário limite atingido. Envio de ordens bloqueado.";

        // RISK params (português)
        [Display(Name = "Ativar Risk", Order = 200, GroupName = "Risk")]
        public bool AtivarRisk { get; set; } = true;

        [Display(Name = "Limite perda diária (USD)", Order = 201, GroupName = "Risk")]
        public double LimitePerdaUSD { get; set; } = 500.0;

        [Display(Name = "Limite trades diário", Order = 202, GroupName = "Risk")]
        public int LimiteTradesDia { get; set; } = 10;

        [Display(Name = "Limite contratos diário", Order = 203, GroupName = "Risk")]
        public int LimiteContratosDia { get; set; } = 50;

        [Display(Name = "Limite lucro diário (USD)", Order = 204, GroupName = "Risk")]
        public double LimiteLucroUSD { get; set; } = 1000.0;

        [Display(Name = "Bloquear ao atingir lucro", Order = 205, GroupName = "Risk")]
        public bool BloquearAoAtingirLucro { get; set; } = false;

        [Display(Name = "Escopo Risk", Order = 206, GroupName = "Risk")]
        public SRiskScope EscopoRisk { get; set; } = SRiskScope.EsteGrafico;

        [Display(Name = "Aviso em % do limite", Order = 207, GroupName = "Risk")]
        public double PercentualAviso { get; set; } = 0.8;

        [Display(Name = "Duração overlay Risk (s)", Order = 208, GroupName = "Risk")]
        public int RiskOverlaySeconds { get; set; } = 90;

        [Display(Name = "Msg overlay risco", Order = 209, GroupName = "Risk")]
        public string RiskOverlayMessage { get; set; } = "Atenção: limite diário atingido.";

        [Display(Name = "Msg overlay lucro", Order = 210, GroupName = "Risk")]
        public string RiskOverlayProfitMessage { get; set; } = "Limite de lucro diário atingido.";

        // Decorator display
        [Display(Name = "Symbol (decorator)", GroupName = "Order Decorator", Order = 300)]
        public string DecorSymbol { get; set; } = "$";

        [Display(Name = "Show ticks", GroupName = "Order Decorator", Order = 301)]
        public bool DecorDisplayTicks { get; set; } = true;

        [Display(Name = "Show points", GroupName = "Order Decorator", Order = 302)]
        public bool DecorDisplayPoints { get; set; } = true;

        [Display(Name = "Show currency", GroupName = "Order Decorator", Order = 303)]
        public bool DecorDisplayCurrency { get; set; } = true;

        [Display(Name = "Show % account", GroupName = "Order Decorator", Order = 304)]
        public bool DecorDisplayPercent { get; set; } = true;

        [Display(Name = "Decorator Gap (px)", GroupName = "Order Decorator", Order = 305)]
        public int DecorFlexGapWidth { get; set; } = 90;

        [Display(Name = "Force decorations (ignore main toggle)", GroupName = "Order Decorator", Order = 306)]
        public bool ForceDecorationsOverride { get; set; } = false;

        [XmlIgnore]
        [Display(Name = "Stop Fill Color", GroupName = "Order Decorator Colors", Order = 310)]
        public Brush DecorStopFillBrush { get; set; }

        [Browsable(false)]
        public string DecorStopFillBrushSerializable
        {
            get => Serialize.BrushToString(DecorStopFillBrush);
            set => DecorStopFillBrush = Serialize.StringToBrush(value);
        }

        [XmlIgnore]
        [Display(Name = "Target Fill Color", GroupName = "Order Decorator Colors", Order = 311)]
        public Brush DecorTargetFillBrush { get; set; }

        [Browsable(false)]
        public string DecorTargetFillBrushSerializable
        {
            get => Serialize.BrushToString(DecorTargetFillBrush);
            set => DecorTargetFillBrush = Serialize.StringToBrush(value);
        }

        [XmlIgnore]
        [Display(Name = "Outline Color", GroupName = "Order Decorator Colors", Order = 312)]
        public Brush DecorOutlineBrush { get; set; }

        [Browsable(false)]
        public string DecorOutlineBrushSerializable
        {
            get => Serialize.BrushToString(DecorOutlineBrush);
            set => DecorOutlineBrush = Serialize.StringToBrush(value);
        }

        [XmlIgnore]
        [Display(Name = "Text Color", GroupName = "Order Decorator Colors", Order = 313)]
        public Brush DecorTextBrush { get; set; }

        [Browsable(false)]
        public string DecorTextBrushSerializable
        {
            get => Serialize.BrushToString(DecorTextBrush);
            set => DecorTextBrush = Serialize.StringToBrush(value);
        }
        #endregion

        #region Lifecycle
        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Name = "SmartBoletaIndicator";
                Description = "Hawk - Smart Panel";
                Calculate = Calculate.OnPriceChange; // manter, mas ATR só recalcula em fechamento de barra
                IsOverlay = true;
                DrawOnPricePanel = true;
                DisplayInDataBox = false;
                IsSuspendedWhileInactive = true;

                AtrPeriod = 14;
                AtrMultiplier = 1.0;
                AtrAuto = true;
                AtrFixedMinutes = 60;
                AtrFixedPeriod = 14;
                AtrFixedMultiplier = 1.0;

                EnableDiagnosticLogging = false;
                BreakEvenTicks = 10;
                MinFavorFactor = 2.0;
                ScanIntervalSeconds = 3;

                // Decorator defaults
                DecorSymbol = "$";
                DecorDisplayTicks = true;
                DecorDisplayPoints = true;
                DecorDisplayCurrency = true;
                DecorDisplayPercent = true;
                DecorFlexGapWidth = 90;

                var stopGradient = new LinearGradientBrush
                {
                    StartPoint = new Point(0, 0),
                    EndPoint = new Point(0, 1)
                };
                stopGradient.GradientStops.Add(new GradientStop(Color.FromRgb(130, 130, 130), 0.0));
                stopGradient.GradientStops.Add(new GradientStop(Color.FromRgb(90, 90, 90), 1.0));
                DecorStopFillBrush = stopGradient;

                DecorTargetFillBrush = Brushes.DarkGoldenrod;
                DecorOutlineBrush = Brushes.DimGray;
                DecorTextBrush = Brushes.White;
            }
            else if (State == State.Configure)
            {
                // Série secundária para ATR fixo (minutos)
                try
                {
                    int mins = Math.Max(1, AtrFixedMinutes);
                    AddDataSeries(BarsPeriodType.Minute, mins);
                }
                catch { }
            }
            else if (State == State.DataLoaded)
            {
                int chartKey = GetChartKey();
                if (chartKey != 0)
                {
                    if (ActivePerChart.TryGetValue(chartKey, out var wr) && wr.TryGetTarget(out var existing) && existing != null && existing != this)
                    {
                        SafePrint("Já existe boleta ativa neste chart; não criarei outra.");
                        return;
                    }
                    ActivePerChart[chartKey] = new WeakReference<SmartBoletaIndicator>(this);

                    if (BoletaIdPerChart.TryGetValue(chartKey, out var existingId) && !string.IsNullOrEmpty(existingId))
                        BoletaId = existingId;
                    else
                    {
                        if (string.IsNullOrEmpty(BoletaId))
                            BoletaId = $"B{Interlocked.Increment(ref BoletaCounter):D2}";
                        BoletaIdPerChart[chartKey] = BoletaId;
                    }
                }
                else if (string.IsNullOrEmpty(BoletaId))
                    BoletaId = $"B{Interlocked.Increment(ref BoletaCounter):D2}";

                MapDesiredKeys();
                orderType = (stopOrderType == StopOrderTypes.StopLimit) ? OrderType.StopLimit : OrderType.StopMarket;

                overlayController = new EndDayOverlayController(this);

                if (ChartControl != null)
                    ChartControl.Dispatcher.InvokeAsync(HookChartTraderAndInsert, DispatcherPriority.Background);

                StartAttachTimer();
                SafePrint($"DataLoaded: attach timer iniciado. BoletaId={BoletaId}");

                SubscribeExecutions();
                SubscribeDecoratorAccountEvents();
                _riskDay = DateTime.Now.Date;

                // Tags para desenho ATR
                string uid = Guid.NewGuid().ToString("N");
                _atrLineTag = $"ATR_LINE_{uid}";
                _atrTextTag1 = $"ATR_TEXT1_{uid}";
                _atrTextTag2 = $"ATR_TEXT2_{uid}";

                LoadPrefs(); // restaura preferências salvas
                ComputeOrderDecorations();
                ForceRefreshDecorations();
                StartDecoTimer();
            }
            else if (State == State.Realtime)
            {
                ComputeOrderDecorations();
                ForceRefreshDecorations();
            }
            else if (State == State.Terminated)
            {
                SafePrint("Terminated: cleaning up.");
                StopAttachTimer();
                StopDecoTimer();
                RemoveEmbedded();
                UnregisterChartHandlers();
                overlayController?.DisposeOverlay();
                UnsubscribeExecutions();
                UnsubscribeDecoratorAccountEvents();
                UnwireAccountSelector();

                SavePrefs(); // garantir persistência ao sair

                int chartKey = GetChartKey();
                if (chartKey != 0 && ActivePerChart.ContainsKey(chartKey))
                    ActivePerChart.Remove(chartKey);

                ClearAtrDraws();
                ClearDecorations();
            }
        }
        #endregion

        #region Persistência leve
        internal void SavePrefs() // internal para permitir chamadas do controle
        {
            try
            {
                if (string.IsNullOrEmpty(BoletaId) || embeddedControl == null) return;
                var sp = new SavedPrefs
                {
                    Qty = embeddedControl.GetQty(),
                    StopFinancial = embeddedControl.GetStopFinancial(),
                    AtrOn = embeddedControl.IsAtrEnabled(),
                    BeOn = embeddedControl.IsBeEnabled(),
                    OnClickOn = embeddedControl.IsOnClickEnabled(),
                    RiskOn = _riskOn,
                    BuyKey = buyKey,
                    SellKey = sellKey,
                    EndDayTime = EndDayTime,
                    EndDayScope = EndDayScope,
                    AtrAuto = AtrAuto,
                    AtrFixedMinutes = AtrFixedMinutes,
                    AtrFixedPeriod = AtrFixedPeriod,
                    AtrFixedMultiplier = AtrFixedMultiplier
                };
                PrefsById[BoletaId] = sp;
            }
            catch (Exception ex) { SafePrint("SavePrefs ex: " + ex.Message); }
        }

        private void LoadPrefs()
        {
            try
            {
                if (string.IsNullOrEmpty(BoletaId) || embeddedControl == null) return;
                if (!PrefsById.TryGetValue(BoletaId, out var sp)) return;

                // Hotkeys
                buyKey = sp.BuyKey;
                sellKey = sp.SellKey;
                MapDesiredKeys();

                // EndDay
                EndDayTime = sp.EndDayTime;
                EndDayScope = sp.EndDayScope;
                embeddedControl.SetEndDayLabel(EndDayTime, EndDayScope);

                // Qty
                if (sp.Qty > 0) embeddedControl.SetQty(sp.Qty);

                // Stop$
                if (sp.StopFinancial > 0) embeddedControl.SetStopFinancial(sp.StopFinancial);

                // Risk toggle
                _riskOn = sp.RiskOn;
                embeddedControl.SetRiskToggleVisual(_riskOn);

                // ATR config
                AtrAuto = sp.AtrAuto;
                AtrFixedMinutes = Math.Max(1, sp.AtrFixedMinutes);
                AtrFixedPeriod = Math.Max(1, sp.AtrFixedPeriod);
                AtrFixedMultiplier = Math.Max(0.0, sp.AtrFixedMultiplier);

                // BE
                embeddedControl.SetBeState(sp.BeOn);
                _beActive = sp.BeOn;

                // ATR ON?
                if (sp.AtrOn)
                {
                    bool ok = ApplyAtrSizingWithValidationProxy(_lastAtrTicks, _lastAtrDollarPerContract, true);
                    if (ok) embeddedControl.SetAtrState(true);
                }

                // OnClick
                embeddedControl.SetOnClickState(sp.OnClickOn);
                SetTradingFromChartEnabled(sp.OnClickOn);

                embeddedControl.UpdateBulletsAfterStateChange();
            }
            catch (Exception ex) { SafePrint("LoadPrefs ex: " + ex.Message); }
        }
        #endregion

        #region Deco timer
        private void StartDecoTimer()
        {
            try
            {
                if (decoTimer != null) return;
                decoTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(2) };
                decoTimer.Tick += (s, e) =>
                {
                    try
                    {
                        ComputeOrderDecorations();
                        ForceRefreshDecorations();
                    }
                    catch (Exception ex) { SafePrint("DecoTimer ex: " + ex.Message); }
                };
                decoTimer.Start();
                SafePrint("DecoTimer started (2s).");
            }
            catch (Exception ex) { SafePrint("StartDecoTimer ex: " + ex.Message); }
        }

        private void StopDecoTimer()
        {
            try
            {
                if (decoTimer != null)
                {
                    decoTimer.Stop();
                    decoTimer = null;
                }
            }
            catch { }
        }
        #endregion

        #region Logging
        public void SafePrint(string message)
        {
            try
            {
                Print($"[SmartBoleta][{BoletaId ?? "B??"}] {DateTime.Now:HH:mm:ss.fff} - {message}");
                if (!EnableDiagnosticLogging) return;

                string line = $"[SmartBoleta][{BoletaId ?? "B??"}] {DateTime.Now:yyyy-MM-dd HH:mm:ss.fff} - {message}";
                Directory.CreateDirectory(IOPath.GetDirectoryName(LogPath));
                File.AppendAllText(LogPath, line + Environment.NewLine);
            }
            catch { }
        }
        #endregion

        #region Qty sync
        public void SyncQtyToChartTrader(int qty)
        {
            try
            {
                if (ChartControl == null) return;
                if (qty < 0) qty = 0;

                ChartControl.Dispatcher.BeginInvoke(new Action(() =>
                {
                    try
                    {
                        var hostWin = FindAncestorWindow(ChartControl);
                        if (hostWin == null) return;

                        var qtySelector = hostWin.FindFirst("ChartTraderControlQuantitySelector") as QuantityUpDown;
                        if (qtySelector == null)
                        {
                            SafePrint("Qty sync skipped: Quantity selector not found.");
                            return;
                        }

                        qtySelector.Value = qty;
                        SafePrint($"Qty sync to ChartTrader: {qty}");
                    }
                    catch (Exception ex) { SafePrint("Qty sync error: " + ex.Message); }
                }));
            }
            catch { }
        }
        #endregion

        #region PnL helper (adapter)
        private Account FindAncestorAccount()
        {
            var sim = Account.All.FirstOrDefault(a => a != null && a.Name != null && a.Name.Equals("Sim101", StringComparison.OrdinalIgnoreCase));
            if (sim != null) return sim;
            return Account.All.FirstOrDefault();
        }

        private Window FindAncestorWindow(DependencyObject start)
        {
            try
            {
                DependencyObject current = start;
                while (current != null)
                {
                    if (current is Window w) return w;
                    current = VisualTreeHelper.GetParent(current);
                }
            }
            catch { }
            return null;
        }

        private Account GetSelectedAccount()
        {
            try
            {
                if (accountSelector != null && accountSelector.SelectedAccount != null)
                {
                    selectedAccountCached = accountSelector.SelectedAccount;
                    return selectedAccountCached;
                }

                var hostWin = FindAncestorWindow(ChartControl);
                var accSel = hostWin?.FindFirst("ChartTraderControlAccountSelector") as AccountSelector;
                if (accSel?.SelectedAccount != null)
                {
                    selectedAccountCached = accSel.SelectedAccount;
                    return selectedAccountCached;
                }
            }
            catch { }

            if (selectedAccountCached != null) return selectedAccountCached;

            var fallback = FindAncestorAccount();
            selectedAccountCached = fallback;
            SafePrint($"GetSelectedAccount fallback -> {(fallback?.Name ?? "null")}");
            return fallback;
        }

        private double? TryGetAccountValue(Account acc, AccountItem item)
        {
            return AccountValueProvider.TryGetAccountValueUsd(acc, item, SafePrint);
        }

        private void UpdatePnlDisplay()
        {
            try
            {
                Account acc = GetSelectedAccount();
                double? realized = AccountValueProvider.TryGetRealizedPnlUsd(acc, SafePrint);
                SafePrint($"PnL check: account={(acc?.Name ?? "null")} realized={(realized.HasValue ? realized.Value.ToString("N2") : "null")}");

                ChartControl?.Dispatcher?.BeginInvoke(new Action(() =>
                {
                    embeddedControl?.SetPnl(realized);
                }));
            }
            catch (Exception ex) { SafePrint("UpdatePnlDisplay ex: " + ex.Message); }
        }
        #endregion

        #region Attach / Insert UI
        private void StartAttachTimer()
        {
            if (attachTimer != null) return;
            attachTimer = new DispatcherTimer { Interval = TimeSpan.FromMilliseconds(AttachPollMs) };
            attachTimer.Tick += (s, e) =>
            {
                try { HookChartTraderAndInsert(); } catch (Exception ex) { SafePrint("attachTimer tick ex: " + ex.Message); }
            };
            attachTimer.Start();
        }

        private void StopAttachTimer()
        {
            try { if (attachTimer == null) return; attachTimer.Stop(); attachTimer = null; } catch { }
        }

        private void HookChartTraderAndInsert()
        {
            try
            {
                if (ChartControl == null) { SafePrint("Hook: ChartControl null"); return; }

                chartWindow = Window.GetWindow(ChartControl.Parent) as Gui.Chart.Chart;
                if (chartWindow == null) { SafePrint("Hook: chartWindow null"); return; }

                try { chartTrader = chartWindow.FindFirst("ChartWindowChartTraderControl") as Gui.Chart.ChartTrader; } catch { }
                if (chartTrader == null) chartTrader = FindVisualChildren<Gui.Chart.ChartTrader>(chartWindow).FirstOrDefault();

                var content = chartTrader?.Content as DependencyObject;
                if (content != null)
                    chartTraderGrid = content as Grid ?? FindVisualChildren<Grid>(content).FirstOrDefault();

                WireAccountSelector(); // conecta ao selector de conta

                if (!TabSelected()) { RegisterTabHandler(); SafePrint("Hook: tab not selected - waiting"); return; }

                if (!panelActive) InsertEmbedded();
                else
                {
                    UpdateEmbeddedForSelectedTab();
                    try { RefreshPositionAndOrders(); } catch { }
                }
            }
            catch (Exception ex) { SafePrint("HookChartTraderAndInsert ex: " + ex.Message); }
        }

        private void WireAccountSelector()
        {
            try
            {
                var hostWin = chartWindow ?? FindAncestorWindow(ChartControl);
                var sel = hostWin?.FindFirst("ChartTraderControlAccountSelector") as AccountSelector;
                if (sel == null) return;

                if (accountSelector == sel) return;

                UnwireAccountSelector();

                accountSelector = sel;
                accountSelector.SelectionChanged += AccountSelector_SelectionChanged;
                selectedAccountCached = accountSelector.SelectedAccount;
                SafePrint("Account selector wired.");
            }
            catch (Exception ex)
            {
                SafePrint("WireAccountSelector ex: " + ex.Message);
            }
        }

        private void UnwireAccountSelector()
        {
            try
            {
                if (accountSelector != null)
                {
                    accountSelector.SelectionChanged -= AccountSelector_SelectionChanged;
                    accountSelector = null;
                }
            }
            catch { }
        }

        private void AccountSelector_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            try
            {
                selectedAccountCached = accountSelector?.SelectedAccount;
                SafePrint($"Account changed -> {selectedAccountCached?.Name ?? "null"}");
                UpdatePnlDisplay();
                RefreshPositionAndOrders();
                EvaluateRisk(false);
                ComputeOrderDecorations();
            }
            catch (Exception ex)
            {
                SafePrint("AccountSelector_SelectionChanged ex: " + ex.Message);
            }
        }

        private bool TabSelected()
        {
            try
            {
                if (ChartControl == null || chartWindow == null || chartWindow.MainTabControl == null) return false;
                foreach (TabItem tab in chartWindow.MainTabControl.Items)
                    if ((tab.Content as Gui.Chart.ChartTab)?.ChartControl == ChartControl && tab == chartWindow.MainTabControl.SelectedItem)
                        return true;
            }
            catch { }
            return false;
        }

        private void RegisterTabHandler()
        {
            try
            {
                if (chartWindow?.MainTabControl != null && tabHandler == null)
                {
                    tabHandler = (s, e) =>
                    {
                        try
                        {
                            if (TabSelected())
                            {
                                WireAccountSelector();
                                if (!panelActive) InsertEmbedded();
                                else { UpdateEmbeddedForSelectedTab(); try { RefreshPositionAndOrders(); } catch { } }
                            }
                            else
                            {
                                if (panelActive) RemoveEmbedded();
                            }
                        }
                        catch (Exception ex) { SafePrint("TabHandler ex: " + ex.Message); }
                    };
                    chartWindow.MainTabControl.SelectionChanged += tabHandler;
                }
            }
            catch (Exception ex) { SafePrint("RegisterTabHandler ex: " + ex.Message); }
        }

        private void InsertEmbedded()
        {
            try
            {
                embeddedControl = new SmartBoletaEmbeddedControl(this);
                embeddedControl.SetBoletaId(BoletaId);

                var outer = new Border
                {
                    Background = Brushes.Transparent,
                    BorderBrush = new SolidColorBrush(Color.FromArgb(140, 72, 72, 72)),
                    BorderThickness = new Thickness(1),
                    SnapsToDevicePixels = true,
                    VerticalAlignment = VerticalAlignment.Top,
                    MaxHeight = EmbedHeightPx + 6,
                    Margin = new Thickness(0, 0, 0, 4)
                };

                var inner = new Border
                {
                    Background = new LinearGradientBrush(Color.FromArgb(128, 24, 24, 24), Color.FromArgb(128, 48, 48, 48), 90),
                    BorderBrush = new SolidColorBrush(Color.FromRgb(170, 120, 60)),
                    BorderThickness = new Thickness(1),
                    SnapsToDevicePixels = true,
                    Margin = new Thickness(3)
                };

                inner.Child = embeddedControl;
                outer.Child = inner;
                embeddedWrapper = outer;

                if (chartTraderGrid != null)
                {
                    addedRow = new RowDefinition { Height = GridLength.Auto };
                    int idx = chartTraderGrid.RowDefinitions.Count;
                    chartTraderGrid.RowDefinitions.Add(addedRow);
                    Grid.SetRow(embeddedWrapper, idx);
                    chartTraderGrid.Children.Add(embeddedWrapper);
                }
                else
                {
                    var parent = ChartControl.Parent as Panel;
                    if (parent != null) parent.Children.Add(embeddedWrapper);
                }

                panelActive = true;
                SafePrint($"InsertEmbedded: UI inserida. BoletaId={BoletaId}");
                RegisterTabHandler();
                UpdateEmbeddedForSelectedTab();
                try { RefreshPositionAndOrders(); } catch { }
                try { if (attachTimer != null) { attachTimer.Stop(); attachTimer = null; SafePrint("attach timer parado após attach."); } } catch { }
            }
            catch (Exception ex) { SafePrint("InsertEmbedded ex: " + ex.Message); }
        }

        private void RemoveEmbedded()
        {
            try
            {
                if (chartWindow?.MainTabControl != null && tabHandler != null)
                {
                    try { chartWindow.MainTabControl.SelectionChanged -= tabHandler; } catch { }
                    tabHandler = null;
                }

                if (chartTraderGrid != null && embeddedWrapper != null)
                {
                    try { chartTraderGrid.Children.Remove(embeddedWrapper); } catch { }
                    try { if (addedRow != null) chartTraderGrid.RowDefinitions.Remove(addedRow); } catch { }
                }
                else if (embeddedWrapper != null)
                {
                    var parent = embeddedWrapper.Parent as Panel;
                    if (parent != null) parent.Children.Remove(embeddedWrapper);
                    else if (embeddedWrapper.Parent is ContentControl cc) cc.Content = null;
                }

                embeddedWrapper = null;
                addedRow = null;
                panelActive = false;
                SafePrint("RemoveEmbedded: UI removida (defensivo).");
            }
            catch (Exception ex) { SafePrint("RemoveEmbedded ex: " + ex.Message); }
        }

        private void UpdateEmbeddedForSelectedTab()
        {
            try
            {
                if (chartWindow == null || embeddedControl == null) return;
                var selected = chartWindow.MainTabControl?.SelectedItem as TabItem;
                if (selected == null) return;
                var chartTab = selected.Content as Gui.Chart.ChartTab;
                if (chartTab == null) return;
                var cc = chartTab.ChartControl;
                if (cc == null) return;

                embeddedControl.UpdateForChart(cc);
                embeddedControl.SetEndDayLabel(EndDayTime, EndDayScope);
                embeddedControl.UpdateBulletsAfterStateChange();
            }
            catch (Exception ex) { SafePrint("UpdateEmbeddedForSelectedTab ex: " + ex.Message); }
        }
        #endregion

        #region EndDay dialog
        public void OpenEndDayDialog()
        {
            try
            {
                SafePrint("OpenEndDayDialog: start");
                var ownerWin = chartWindow ?? FindAncestorWindow(ChartControl) as Gui.Chart.Chart;

                var dlg = new Window()
                {
                    Owner = ownerWin,
                    WindowStartupLocation = WindowStartupLocation.CenterOwner,
                    SizeToContent = SizeToContent.WidthAndHeight,
                    ResizeMode = ResizeMode.NoResize,
                    WindowStyle = WindowStyle.ToolWindow,
                    Title = "Configure EndDay",
                    ShowInTaskbar = false,
                    Background = new LinearGradientBrush(Color.FromRgb(30, 30, 30), Color.FromRgb(50, 50, 50), 90),
                    Foreground = Brushes.LightGray
                };

                var panel = new StackPanel { Margin = new Thickness(8) };
                panel.Children.Add(new TextBlock { Text = "End of day time (HH:mm):", Margin = new Thickness(0, 0, 0, 4), Foreground = Brushes.LightGray });

                var timeInput = new TextBox
                {
                    Width = 160,
                    Height = 26,
                    FontSize = 14,
                    Text = (this.EndDayTime.HasValue) ? this.EndDayTime.Value.ToString(@"hh\:mm") : "",
                    Background = new SolidColorBrush(Color.FromRgb(22, 22, 22)),
                    Foreground = Brushes.White
                };

                timeInput.PreviewTextInput += (s, e) =>
                {
                    if (e.Text.All(c => char.IsDigit(c) || c == ':')) e.Handled = false;
                    else e.Handled = true;
                };

                panel.Children.Add(timeInput);

                panel.Children.Add(new TextBlock { Text = "Scope:", Margin = new Thickness(0, 8, 0, 4), Foreground = Brushes.LightGray });

                var rbThis = new RadioButton { Content = "This chart only", IsChecked = (this.EndDayScope == SBEndDayScope.ThisChartOnly) || (!this.EndDayTime.HasValue), Foreground = Brushes.LightGray };
                var rbAll = new RadioButton { Content = "All NinjaTrader", IsChecked = (this.EndDayScope == SBEndDayScope.AllNinjaTrader), Foreground = Brushes.LightGray };

                panel.Children.Add(rbThis);
                panel.Children.Add(rbAll);

                var buttons = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Right, Margin = new Thickness(0, 8, 0, 0) };
                var ok = new Button { Content = "OK", Width = 80, Margin = new Thickness(0, 0, 6, 0), Background = new SolidColorBrush(Color.FromRgb(40, 40, 40)), Foreground = Brushes.White };
                var cancel = new Button { Content = "Cancel", Width = 80, Background = new SolidColorBrush(Color.FromRgb(60, 60, 60)), Foreground = Brushes.White };

                ok.Click += (s, e) =>
                {
                    try
                    {
                        string txt = timeInput.Text?.Trim();
                        if (TimeSpan.TryParseExact(txt, @"h\:mm", CultureInfo.CurrentCulture, out TimeSpan ts) ||
                            TimeSpan.TryParseExact(txt, @"hh\:mm", CultureInfo.CurrentCulture, out ts) ||
                            TimeSpan.TryParse(txt, out ts))
                            this.EndDayTime = ts;
                        else
                            this.EndDayTime = null;

                        this.EndDayScope = (rbAll.IsChecked == true) ? SBEndDayScope.AllNinjaTrader : SBEndDayScope.ThisChartOnly;
                        embeddedControl?.SetEndDayLabel(this.EndDayTime, this.EndDayScope);
                        embeddedControl?.UpdateBulletsAfterStateChange();
                        SavePrefs();
                    }
                    catch (Exception ex) { SafePrint("EndDay OK parse error: " + ex.Message); }

                    try { dlg.Dispatcher.BeginInvoke(new Action(() => { dlg.DialogResult = true; dlg.Close(); })); } catch { try { dlg.Close(); } catch { } }
                };

                cancel.Click += (s, e) => { try { dlg.DialogResult = false; dlg.Close(); } catch { } };
                buttons.Children.Add(ok); buttons.Children.Add(cancel);

                panel.Children.Add(buttons);
                dlg.Content = panel;

                dlg.ShowDialog();
            }
            catch (Exception ex)
            {
                SafePrint("OpenEndDayDialog error: " + ex.Message);
            }
        }
        #endregion

        #region OnBarUpdate e checks (ATR agora só em fechamento de barra)
        protected override void OnBarUpdate()
        {
            try
            {
                // Recalcula ATR somente no fechamento da barra (IsFirstTickOfBar em Calculate.OnPriceChange)
                if (!IsFirstTickOfBar) return;

                if (BarsInProgress == 0)
                {
                    // Série principal (auto ou apenas para desenhar/estado)
                    if (AtrAuto)
                    {
                        ComputeAtrPrimaryAndApply();
                    }
                    // mesmo em modo fixo, aqui pode rodar outras verificações, mas ATR ficará a cargo do BIP1
                }
                else if (BarsInProgress == 1)
                {
                    // Série secundária fixa (minutos escolhidos)
                    if (!AtrAuto)
                    {
                        ComputeAtrFixedAndApply();
                    }
                }

                // Rotinas comuns (só na primária para evitar duplicar):
                if (BarsInProgress == 0)
                {
                    EnsureRiskResetDaily();
                    EvaluateRisk(false);

                    var now = DateTime.UtcNow;
                    if ((now - _lastScanUtc).TotalSeconds >= Math.Max(1, ScanIntervalSeconds))
                    {
                        _lastScanUtc = now;
                        UpdatePnlDisplay();
                        try { RefreshPositionAndOrders(); } catch (Exception ex) { SafePrint("UpdateEntry/Orders ex: " + ex.Message); }
                        ComputeOrderDecorations();
                    }

                    // Mini BE logic
                    if (IsFlat())
                    {
                        CleanupFlatOrders(GetSelectedAccount());
                        if (_beFireRequest || _beActive)
                            SafePrint("Position flat -> BE reset");
                        _beFireRequest = false;
                        _beActive = false;
                        embeddedControl?.ForceBeOff();
                        return;
                    }
                    else
                    {
                        _flatCleanupDone = false; // voltou a ter posição
                    }

                    if (_beFireRequest)
                    {
                        bool ok = TryApplyBreakEvenOneShot();
                        _beFireRequest = false;
                        if (ok)
                        {
                            _beActive = true;
                            embeddedControl?.ForceBeOn();
                        }
                        else
                        {
                            _beActive = false;
                            embeddedControl?.ForceBeOff();
                        }
                        SavePrefs();
                    }
                }
            }
            catch (Exception ex) { SafePrint("OnBarUpdate ATR/BE ex: " + ex.Message); }
        }

        private void ComputeAtrPrimaryAndApply()
        {
            if (Bars == null || CurrentBar < 1) { ClearAtrDraws(); return; }

            // TR e ATR no fechamento da barra principal
            double high = Bars.GetHigh(CurrentBar);
            double low = Bars.GetLow(CurrentBar);
            double prevClose = Bars.GetClose(CurrentBar - 1);
            double tr = Math.Max(high - low, Math.Max(Math.Abs(high - prevClose), Math.Abs(low - prevClose)));

            trQueue.Enqueue(tr);
            trSum += tr;
            if (trQueue.Count > atrPeriod) trSum -= trQueue.Dequeue();

            double currentAtr = trQueue.Count > 0 ? trSum / trQueue.Count : 0.0;
            double tickSize = Bars.Instrument?.MasterInstrument?.TickSize ?? 1.0;
            int atrTicks = (tickSize > 0 && currentAtr > 0) ? (int)Math.Round((currentAtr * atrMultiplier) / tickSize) : 0;

            double tickValue = 0.0;
            try
            {
                var mi = Instrument?.MasterInstrument;
                tickValue = (mi?.TickSize ?? 0) * (mi?.PointValue ?? 0);
            }
            catch { }

            double atrDollarPerContract = atrTicks * tickValue;

            ApplyAtrValues(atrTicks, atrDollarPerContract, tickSize);
        }

        private void ComputeAtrFixedAndApply()
        {
            if (BarsArray.Length < 2) return;
            var series = BarsArray[1];
            if (CurrentBars[1] < 1) { return; }

            double high = series.GetHigh(CurrentBars[1]);
            double low = series.GetLow(CurrentBars[1]);
            double prevClose = series.GetClose(CurrentBars[1] - 1);
            double tr = Math.Max(high - low, Math.Max(Math.Abs(high - prevClose), Math.Abs(low - prevClose)));

            trQueueFixed.Enqueue(tr);
            trSumFixed += tr;
            if (trQueueFixed.Count > AtrFixedPeriod) trSumFixed -= trQueueFixed.Dequeue();

            double currentAtr = trQueueFixed.Count > 0 ? trSumFixed / trQueueFixed.Count : 0.0;
            double tickSize = Instrument?.MasterInstrument?.TickSize ?? 1.0;
            int atrTicks = (tickSize > 0 && currentAtr > 0) ? (int)Math.Round((currentAtr * AtrFixedMultiplier) / tickSize) : 0;

            double tickValue = 0.0;
            try
            {
                var mi = Instrument?.MasterInstrument;
                tickValue = (mi?.TickSize ?? 0) * (mi?.PointValue ?? 0);
            }
            catch { }

            double atrDollarPerContract = atrTicks * tickValue;

            ApplyAtrValues(atrTicks, atrDollarPerContract, tickSize);
        }

        private void ApplyAtrValues(int atrTicks, double atrDollarPerContract, double tickSize)
        {
            _lastAtrTicks = atrTicks;
            _lastAtrDollarPerContract = atrDollarPerContract;

            try { ChartControl?.Dispatcher?.BeginInvoke(new Action(() => embeddedControl?.SetAtrValue(atrTicks, atrDollarPerContract))); } catch { }

            try
            {
                if (embeddedControl != null && embeddedControl.IsAtrEnabled())
                    ApplyAtrSizing(atrTicks, atrDollarPerContract);
            }
            catch (Exception ex) { SafePrint("ATR sizing ex: " + ex.Message); }

            // Fail-safe: se ATR ON e stop financeiro inválido, desligar ATR e liberar qty
            if (embeddedControl != null && embeddedControl.IsAtrEnabled())
            {
                double stopFinancial = embeddedControl.GetStopFinancial();
                if (stopFinancial <= 0)
                {
                    embeddedControl.ForceAtrOffAndEnableQty();
                    ShowTransientPopup("ATR desligado: defina Stop ($) para usar ATR.");
                    SafePrint("ATR auto-off: Stop($) inválido durante ATR ON.");
                    SavePrefs();
                }
            }

            // Desenho da linha/legenda ATR no gráfico (só se houver posição)
            DrawAtrVisuals(atrTicks, tickSize);
        }
        #endregion

        #region Helpers (posição/ordens/risk/BE)
        private (bool hasPos, double avgPrice, string ticker) GetOpenPositionInfo(bool verbose = true)
        {
            try
            {
                string chartInst = Instrument?.FullName ?? "(null)";
                string chartMI = Instrument?.MasterInstrument?.Name ?? "(null)";

                if (verbose) SafePrint($"GetOpenPositionInfo: chartInst={chartInst} chartMI={chartMI}");

                foreach (var acc in Account.All)
                {
                    try
                    {
                        var positionsProp = acc.GetType().GetProperty("Positions");
                        if (positionsProp != null)
                        {
                            var posColl = positionsProp.GetValue(acc) as System.Collections.IEnumerable;
                            if (posColl != null)
                            {
                                foreach (var px in posColl)
                                {
                                    try
                                    {
                                        var pInstProp = px.GetType().GetProperty("Instrument");
                                        var qtyProp = px.GetType().GetProperty("Quantity");
                                        var avgProp = px.GetType().GetProperty("AveragePrice");
                                        var pInst = pInstProp?.GetValue(px) as NinjaTrader.Cbi.Instrument;
                                        int qty = qtyProp != null ? Convert.ToInt32(qtyProp.GetValue(px)) : 0;
                                        double avg = avgProp != null ? Convert.ToDouble(avgProp.GetValue(px)) : 0.0;

                                        if (pInst != null && qty != 0)
                                        {
                                            string pFull = pInst.FullName;
                                            string pMI = pInst.MasterInstrument?.Name ?? "";
                                            bool match = (pFull == chartInst) || (!string.IsNullOrEmpty(pMI) && pMI == chartMI);
                                            if (match)
                                            {
                                                if (verbose) SafePrint($"Found position in acc={acc.Name} inst={pFull} qty={qty} avg={avg}");
                                                return (true, avg, pFull);
                                            }
                                        }
                                    }
                                    catch { }
                                }
                            }
                        }
                    }
                    catch { }
                }
            }
            catch (Exception ex) { if (verbose) SafePrint("GetOpenPositionInfo ex: " + ex.Message); }
            if (verbose) SafePrint("GetOpenPositionInfo: no position found.");
            return (false, 0.0, "");
        }

        private (double? chartStop, double? chartExit) GetChartStopAndExit(bool verbose = true)
        {
            double? foundStop = null;
            double? foundExit = null;
            string chartInst = Instrument?.FullName ?? "(null)";
            string chartMI = Instrument?.MasterInstrument?.Name ?? "(null)";
            int inspected = 0;

            try
            {
                foreach (var acc in Account.All)
                {
                    try
                    {
                        IEnumerable<object> orders = null;
                        var ordersProp = acc.GetType().GetProperty("Orders") ?? acc.GetType().GetProperty("WorkingOrders") ?? acc.GetType().GetProperty("OrdersCollection");
                        if (ordersProp != null)
                        {
                            var oCol = ordersProp.GetValue(acc);
                            if (oCol is System.Collections.IEnumerable ie) orders = ie.Cast<object>();
                        }
                        else
                        {
                            var method = acc.GetType().GetMethod("GetOrders", Type.EmptyTypes);
                            if (method != null)
                            {
                                var oCol = method.Invoke(acc, null);
                                if (oCol is System.Collections.IEnumerable ie2) orders = ie2.Cast<object>();
                            }
                        }

                        if (orders == null) continue;

                        foreach (var ordObj in orders)
                        {
                            inspected++;
                            var ord = ordObj as Order;
                            if (ord == null) continue;
                            try
                            {
                                string stateName = ord.OrderState.ToString();

                                bool isActive = false;
                                if (string.IsNullOrEmpty(stateName))
                                    isActive = true;
                                else
                                {
                                    var s = stateName.ToLower();
                                    if (s.Contains("work") || s.Contains("accept") || s.Contains("submit"))
                                        isActive = true;
                                }
                                if (!isActive) continue;

                                var ordInst = ord.Instrument;
                                if (ordInst == null || Instrument == null) continue;
                                string oFull = ordInst.FullName;
                                string oMI = ordInst.MasterInstrument?.Name ?? "";
                                bool match = (oFull == chartInst) || (!string.IsNullOrEmpty(oMI) && oMI == chartMI);
                                if (!match) continue;

                                string orderTypeName = ord.OrderType.ToString();
                                double? price = null;
                                var candNames = new[] { "StopPrice", "LimitPrice", "Price", "AuxPrice", "TriggerPrice", "Limit", "Stop", "AvgFillPrice" };
                                foreach (var n in candNames)
                                {
                                    var pInfo = ord.GetType().GetProperty(n);
                                    if (pInfo != null)
                                    {
                                        try
                                        {
                                            var pv = pInfo.GetValue(ord);
                                            if (pv != null)
                                            {
                                                double d = Convert.ToDouble(pv);
                                                if (!double.IsNaN(d) && !double.IsInfinity(d) && Math.Abs(d) > double.Epsilon)
                                                {
                                                    price = d;
                                                    break;
                                                }
                                            }
                                        }
                                        catch { }
                                    }
                                }

                                if (verbose) SafePrint($"Order inspected: acc={ord.Account?.Name} inst={oFull} type={orderTypeName} state={stateName} price={(price.HasValue ? price.Value.ToString("N2") : "null")}");

                                if (!string.IsNullOrEmpty(orderTypeName))
                                {
                                    var lower = orderTypeName.ToLower();
                                    if (lower.Contains("stop"))
                                    {
                                        if (!foundStop.HasValue && price.HasValue) foundStop = price.Value;
                                    }
                                    else if (lower.Contains("limit"))
                                    {
                                        if (!foundExit.HasValue && price.HasValue) foundExit = price.Value;
                                    }
                                    else
                                    {
                                        if (!foundExit.HasValue && price.HasValue) foundExit = price.Value;
                                    }

                                    if (foundStop.HasValue && foundExit.HasValue)
                                        return (foundStop, foundExit);
                                }
                                else
                                {
                                    if (!foundExit.HasValue && price.HasValue) foundExit = price.Value;
                                }
                            }
                            catch (Exception exOrd) { if (verbose) SafePrint("Order inspect ex: " + exOrd.Message); }
                        }
                    }
                    catch { }
                }
            }
            catch { }

            if (verbose) SafePrint($"GetChartStopAndExit: inspected={inspected} stop={(foundStop.HasValue ? foundStop.Value.ToString("N2") : "null")} exit={(foundExit.HasValue ? foundExit.Value.ToString("N2") : "null")}");
            return (foundStop, foundExit);
        }

        private void RefreshPositionAndOrders()
        {
            (bool hasPos, double avgPrice, string ticker) posInfo = (false, 0.0, "");
            (double? chartStop, double? chartExit) chartOrders = (null, null);

            try
            {
                posInfo = GetOpenPositionInfo();
                chartOrders = GetChartStopAndExit();

                ChartControl?.Dispatcher?.BeginInvoke(new Action(() =>
                {
                    if (embeddedControl != null)
                    {
                        if (posInfo.hasPos)
                            embeddedControl.SetEntryFromPosition(posInfo.ticker, posInfo.avgPrice);
                        else
                            embeddedControl.ClearEntry();

                        if (chartOrders.chartStop.HasValue)
                            embeddedControl.SetChartStop(chartOrders.chartStop.Value);
                        else
                            embeddedControl.ClearChartStop();

                        if (chartOrders.chartExit.HasValue)
                            embeddedControl.SetExitFromOrder(chartOrders.chartExit.Value);
                        else
                            embeddedControl.ClearExit();

                        embeddedControl.UpdateBulletsAfterStateChange();
                    }
                }));
            }
            catch (Exception ex) { SafePrint("RefreshPositionAndOrders ex: " + ex.Message); }
        }

        private void ApplyAtrSizing(int atrTicks, double atrDollarPerContract)
        {
            ApplyAtrSizingWithValidation(atrTicks, atrDollarPerContract, fromToggle: false);
        }

        private bool ApplyAtrSizingWithValidation(int atrTicks, double atrDollarPerContract, bool fromToggle)
        {
            try
            {
                embeddedControl?.SetQtyButtonsEnabled(false);

                double stopFinancial = embeddedControl?.GetStopFinancial() ?? 0.0;
                if (stopFinancial <= 0)
                {
                    embeddedControl?.SetLastOrderInfo("Stop ($) não definido");
                    ShowTransientPopup("Defina o Stop ($) para usar ATR.");
                    if (fromToggle) embeddedControl?.ForceAtrOffAndEnableQty();
                    else embeddedControl?.SetQtyButtonsEnabled(true);
                    return false;
                }

                if (atrTicks <= 0 || atrDollarPerContract <= 0)
                {
                    embeddedControl?.SetLastOrderInfo("ATR inválido");
                    ShowTransientPopup("ATR inválido para sizing.");
                    if (fromToggle) embeddedControl?.ForceAtrOffAndEnableQty();
                    else embeddedControl?.SetQtyButtonsEnabled(true);
                    return false;
                }

                double allowedContracts = Math.Floor(stopFinancial / atrDollarPerContract);
                int qty = (int)Math.Max(1, allowedContracts); // mínimo 1
                bool wasCappedToMin = allowedContracts < 1;

                embeddedControl?.SetQty(qty);
                if (wasCappedToMin)
                    embeddedControl?.SetLastOrderInfo($"ATR {atrTicks} ticks -> Qty min 1 (stop <$ por 1C)");
                else
                    embeddedControl?.SetLastOrderInfo($"ATR {atrTicks} ticks -> Qty {qty}");

                SavePrefs();
                return true;
            }
            catch (Exception ex)
            {
                SafePrint("ApplyAtrSizingWithValidation error: " + ex.Message);
                if (fromToggle) embeddedControl?.ForceAtrOffAndEnableQty();
                else embeddedControl?.SetQtyButtonsEnabled(true);
                return false;
            }
        }

        // Expostos ao controle para uso no toggle ATR
        public int LastAtrTicks() => _lastAtrTicks;
        public double LastAtrDollarPerContract() => _lastAtrDollarPerContract;
        public bool ApplyAtrSizingWithValidationProxy(int atrTicks, double atrDollarPerContract, bool fromToggle)
        {
            return ApplyAtrSizingWithValidation(atrTicks, atrDollarPerContract, fromToggle);
        }

        private bool IsFlat()
        {
            var acc = ResolveAccountWithPosition();
            var pos = GetPositionForInstrument(acc, Instrument);
            return pos == null || pos.Quantity == 0;
        }

        private Account ResolveAccountWithPosition()
        {
            var selected = GetSelectedAccount();
            if (selected != null)
            {
                var posSel = GetPositionForInstrument(selected, Instrument);
                if (posSel != null && posSel.Quantity != 0)
                {
                    SafePrint($"Conta selecionada com posição: {selected.Name}");
                    return selected;
                }
            }

            foreach (var acc in Account.All)
            {
                var p = GetPositionForInstrument(acc, Instrument);
                if (p != null && p.Quantity != 0)
                {
                    SafePrint($"Conta com posição encontrada: {acc.Name}");
                    return acc;
                }
            }

            var sim = Account.All.FirstOrDefault(a => a.Name != null && a.Name.Equals("Sim101", StringComparison.OrdinalIgnoreCase));
            if (sim != null)
            {
                SafePrint("Fallback para Sim101");
                return sim;
            }

            var first = Account.All.FirstOrDefault(a => a != null && a.Name != null) ?? Account.All.FirstOrDefault();
            if (first != null) SafePrint($"Fallback para primeira conta: {first.Name}");
            return first;
        }

        private Position GetPositionForInstrument(Account acc, Instrument inst)
        {
            if (acc == null || inst == null) return null;
            try
            {
                foreach (var p in acc.Positions)
                {
                    if (p.Instrument != null &&
                        (p.Instrument.FullName == inst.FullName || p.Instrument.MasterInstrument?.Name == inst.MasterInstrument?.Name))
                    {
                        return p;
                    }
                }
            }
            catch { }
            return null;
        }

        private void CancelAllStops(Account acc, Instrument inst)
        {
            try
            {
                var orders = acc?.Orders;
                if (orders == null) return;

                var toCancel = new List<Order>();
                foreach (var o in orders)
                {
                    if (o == null) continue;
                    if (!IsActive(o.OrderState)) continue;
                    var oi = o.Instrument;
                    if (oi == null) continue;
                    bool match = (oi.FullName == inst.FullName) || (oi.MasterInstrument?.Name == inst.MasterInstrument?.Name);
                    if (!match) continue;

                    var typeStr = o.OrderType.ToString().ToLowerInvariant();
                    if (typeStr.Contains("stop"))
                        toCancel.Add(o);
                }

                foreach (var c in toCancel)
                {
                    acc.Cancel(new[] { c });
                }

                SafePrint($"CancelAllStops: cancelados {toCancel.Count} stops. acc={acc?.Name}");
            }
            catch (Exception ex)
            {
                SafePrint("CancelAllStops ex: " + ex.Message);
            }
        }

        private bool IsActive(OrderState s)
        {
            return s == OrderState.Working || s == OrderState.Accepted || s == OrderState.Submitted || s == OrderState.PartFilled;
        }

        // Cancela todas as ordens ativas do instrumento (stop/target/etc)
        private int CancelAllActiveOrdersForInstrument(Account acc, Instrument inst)
        {
            int canceled = 0;
            try
            {
                var orders = acc?.Orders;
                if (orders == null) return 0;

                var toCancel = new List<Order>();
                foreach (var o in orders)
                {
                    if (o == null) continue;
                    if (!IsActive(o.OrderState)) continue;
                    var oi = o.Instrument;
                    if (oi == null) continue;
                    bool match = (oi.FullName == inst.FullName) || (oi.MasterInstrument?.Name == inst.MasterInstrument?.Name);
                    if (!match) continue;
                    toCancel.Add(o);
                }

                if (toCancel.Count > 0)
                {
                    acc.Cancel(toCancel.ToArray());
                    canceled = toCancel.Count;
                }
            }
            catch (Exception ex) { SafePrint("CancelAllActiveOrdersForInstrument ex: " + ex.Message); }
            return canceled;
        }

        // Novo helper: se flat, remove ordens ativas do instrumento
        private void CleanupFlatOrders(Account acc)
        {
            try
            {
                if (acc == null || Instrument == null) return;
                var pos = GetPositionForInstrument(acc, Instrument);
                if (pos != null && pos.Quantity != 0)
                {
                    _flatCleanupDone = false;
                    return;
                }

                if (_flatCleanupDone) return; // evita repetição
                int canceled = CancelAllActiveOrdersForInstrument(acc, Instrument);
                if (canceled > 0) SafePrint($"Flat cleanup: canceladas {canceled} ordens ativas pós-flat.");
                _flatCleanupDone = true;
            }
            catch (Exception ex) { SafePrint("CleanupFlatOrders ex: " + ex.Message); }
        }

        // Ajusta stop existente (mantido para outros usos; não chamado no novo BE)
        private bool AdjustStopOrdersForPosition(Account acc, Position pos, double bePrice, int qtyAbs, bool isShort)
        {
            bool changed = false;
            try
            {
                if (acc == null || pos == null || Instrument == null) return false;
                var orders = acc.Orders;
                if (orders == null) return false;

                foreach (var o in orders)
                {
                    if (o == null) continue;
                    if (!IsActive(o.OrderState)) continue;

                    var oi = o.Instrument;
                    if (oi == null) continue;
                    bool match = (oi.FullName == Instrument.FullName) || (oi.MasterInstrument?.Name == Instrument.MasterInstrument?.Name);
                    if (!match) continue;

                    if (!StopOrderTypesSet.Contains(o.OrderType)) continue;

                    if (pos.MarketPosition == MarketPosition.Long && !o.IsShort) continue;
                    if (pos.MarketPosition == MarketPosition.Short && !o.IsLong) continue;

                    try
                    {
                        bool ok = OrderChanger.TryChangeStopPrice(acc, o, bePrice, SafePrint);
                        if (ok)
                        {
                            changed = true;
                            SafePrint($"AdjustStopOrdersForPosition: changed stop -> {bePrice:F2} (id={o.OrderId})");
                        }
                        else
                        {
                            SafePrint($"AdjustStopOrdersForPosition: não achou overload Change compatível para id={o.OrderId}");
                        }
                    }
                    catch (Exception exChange)
                    {
                        SafePrint("AdjustStopOrdersForPosition change ex: " + exChange.Message);
                    }
                }
            }
            catch (Exception ex)
            {
                SafePrint("AdjustStopOrdersForPosition ex: " + ex.Message);
            }
            return changed;
        }

        // BE: cancela OU (stop+target) e recria o stop no preço de BE
        private bool TryApplyBreakEvenOneShot()
        {
            try
            {
                if (IsFlat())
                {
                    SafePrint("BE ignorado: posição flat.");
                    return false;
                }

                var acc = ResolveAccountWithPosition();
                if (acc == null)
                {
                    SafePrint("BE falhou: account null.");
                    return false;
                }

                var pos = GetPositionForInstrument(acc, Instrument);
                if (pos == null || pos.Quantity == 0)
                {
                    SafePrint($"BE ignorado: posição não encontrada na conta {acc.Name}. Instrumento={Instrument?.FullName}");
                    LogAllPositions();
                    return false;
                }

                int qtyAbs = Math.Abs(pos.Quantity);
                bool isShort = pos.MarketPosition == MarketPosition.Short;
                double avg = pos.AveragePrice;
                double last = Close[0];
                double tickSize = Instrument?.MasterInstrument?.TickSize ?? 0.0;
                if (tickSize <= 0)
                {
                    SafePrint("BE falhou: tickSize <= 0.");
                    return false;
                }

                double favorTicks = isShort
                    ? (avg - last) / tickSize
                    : (last - avg) / tickSize;

                double favorTicksInt = Math.Floor(favorTicks);
                int beTicks = Math.Max(0, BreakEvenTicks);
                double minFavor = beTicks * Math.Max(1.0, MinFavorFactor);

                SafePrint($"BE start: dir={(isShort ? "Short" : "Long")} avg={avg:F2} last={last:F2} favorTicks={favorTicksInt} minFavor={minFavor} qty={qtyAbs} acc={acc.Name}");

                if (favorTicksInt < minFavor)
                {
                    SafePrint("BE falhou: ticks insuficientes.");
                    ShowTransientPopup("Break-even: ticks insuficientes.");
                    return false;
                }

                double bePrice = isShort
                    ? avg - beTicks * tickSize
                    : avg + beTicks * tickSize;

                // Cancelar todas as ordens ativas (stop/target) antes de recriar o stop BE
                int canceled = CancelAllActiveOrdersForInstrument(acc, Instrument);
                SafePrint($"BE: canceladas {canceled} ordens ativas (stop/target) antes de recriar o stop BE.");

                // Cria novo stop no preço de BE, com a quantidade total da posição
                OrderAction action = isShort ? OrderAction.BuyToCover : OrderAction.Sell;
                var newStop = acc.CreateOrder(
                    Instrument,
                    action,
                    OrderType.StopMarket,
                    OrderEntry.Manual,
                    TimeInForce.Day,
                    qtyAbs,
                    0.0,
                    bePrice,
                    "",
                    "BE_Stop",
                    DateTime.MaxValue,
                    null);

                acc.Submit(new[] { newStop });
                SafePrint($"BE OK (novo stop): stop @ {bePrice:F2} qty={qtyAbs} action={action} acc={acc.Name}");
                ShowTransientPopup($"Break-even aplicado: stop @ {bePrice:F2}");
                SavePrefs();

                return true;
            }
            catch (Exception ex)
            {
                SafePrint("BE exception: " + ex.Message);
                ShowTransientPopup("Break-even falhou: " + ex.Message);
                return false;
            }
        }

        private void LogAllPositions()
        {
            try
            {
                SafePrint("== POSIÇÕES POR CONTA ==");
                foreach (var acc in Account.All)
                {
                    foreach (var p in acc.Positions)
                    {
                        SafePrint($"acc={acc.Name} inst={p?.Instrument?.FullName} qty={p?.Quantity} avg={p?.AveragePrice} mp={p?.MarketPosition}");
                    }
                }
            }
            catch (Exception ex) { SafePrint("LogAllPositions ex: " + ex.Message); }
        }

        #region Risk
        private void SubscribeExecutions()
        {
            try
            {
                foreach (var acc in Account.All)
                {
                    acc.ExecutionUpdate -= OnExecutionUpdate;
                    acc.ExecutionUpdate += OnExecutionUpdate;
                }
            }
            catch (Exception ex) { SafePrint("SubscribeExecutions ex: " + ex.Message); }
        }

        private void UnsubscribeExecutions()
        {
            try
            {
                foreach (var acc in Account.All)
                {
                    acc.ExecutionUpdate -= OnExecutionUpdate;
                }
            }
            catch { }
        }

        private void OnExecutionUpdate(object sender, ExecutionEventArgs e)
        {
            try
            {
                if (e == null || e.Execution == null) return;
                var exec = e.Execution;

                var ord = exec.Order;
                if (ord == null) return;
                var state = ord.OrderState;
                if (state != OrderState.Filled && state != OrderState.PartFilled) return;

                if (EscopoRisk == SRiskScope.EsteGrafico && Instrument != null)
                {
                    var exInst = exec.Instrument;
                    if (exInst == null) return;
                    bool match = (exInst.FullName == Instrument.FullName) ||
                                 (exInst.MasterInstrument?.Name == Instrument.MasterInstrument?.Name);
                    if (!match) return;
                }

                EnsureRiskResetDaily();

                _riskTrades += 1;
                _riskContracts += Math.Abs(exec.Quantity);

                SafePrint($"Exec contabilizada para Risk: trades={_riskTrades} contratos={_riskContracts} qtyExec={exec.Quantity}");

                // Limpeza pós-flat imediatamente após execução
                CleanupFlatOrders(exec.Account);

                EvaluateRisk(true);
                ComputeOrderDecorations();
            }
            catch (Exception ex)
            {
                SafePrint("OnExecutionUpdate Risk ex: " + ex.Message);
            }
        }

        private void EnsureRiskResetDaily()
        {
            var today = DateTime.Now.Date;
            if (_riskDay != today)
            {
                _riskDay = today;
                _riskTrades = 0;
                _riskContracts = 0;
                _warnedLoss = _warnedTrades = _warnedContracts = _warnedProfit = false;
                _riskBlocked = false;
                _riskBlockedUntil = DateTime.MinValue;
                _mainToggleLockedByRisk = false;
                _riskOverlayShown = false;
                embeddedControl?.SetRiskState(RiskState.Ok, _riskOn, "");
                SafePrint("Risk: reset diário.");
            }
        }

        private DateTime NextMidnight()
        {
            var dt = DateTime.Now;
            var next = dt.Date.AddDays(1);
            return next;
        }

        internal bool IsRiskBlocked()
        {
            return _riskBlocked && DateTime.Now < _riskBlockedUntil;
        }

        internal void NotifyRiskToggle(bool enabled)
        {
            _riskOn = enabled;
            SafePrint("Risk toggle: " + enabled);
            EvaluateRisk(false);
            SavePrefs();
        }

        private void EvaluateRisk(bool fromExec)
        {
            try
            {
                EnsureRiskResetDaily();

                if (!AtivarRisk)
                {
                    embeddedControl?.SetRiskState(RiskState.Off, false, "");
                    _riskBlocked = false;
                    _mainToggleLockedByRisk = false;
                    return;
                }

                if (!_riskOn)
                {
                    embeddedControl?.SetRiskState(RiskState.Off, false, "");
                    _riskBlocked = false;
                    _mainToggleLockedByRisk = false;
                    return;
                }

                double pnl = 0.0;
                var acc = GetSelectedAccount();
                var pVal = AccountValueProvider.TryGetRealizedPnlUsd(acc, SafePrint);
                pnl = pVal ?? 0.0;

                bool breachLoss = false, breachTrades = false, breachContracts = false, breachProfit = false;
                bool warn = false;

                if (LimitePerdaUSD > 0 && (-pnl) >= LimitePerdaUSD)
                    breachLoss = true;
                else if (LimitePerdaUSD > 0 && (-pnl) >= PercentualAviso * LimitePerdaUSD)
                    warn = true;

                if (LimiteTradesDia > 0 && _riskTrades >= LimiteTradesDia)
                    breachTrades = true;
                else if (LimiteTradesDia > 0 && _riskTrades >= (int)Math.Floor(PercentualAviso * LimiteTradesDia))
                    warn = true;

                if (LimiteContratosDia > 0 && _riskContracts >= LimiteContratosDia)
                    breachContracts = true;
                else if (LimiteContratosDia > 0 && _riskContracts >= (int)Math.Floor(PercentualAviso * LimiteContratosDia))
                    warn = true;

                if (LimiteLucroUSD > 0 && pnl >= LimiteLucroUSD)
                    breachProfit = true;
                else if (LimiteLucroUSD > 0 && pnl >= PercentualAviso * LimiteLucroUSD)
                    warn = true;

                if (breachLoss || breachTrades || breachContracts)
                {
                    TriggerRiskBlock("Limite diário atingido.", RiskOverlayMessage, true);
                    return;
                }

                if (breachProfit)
                {
                    if (BloquearAoAtingirLucro)
                    {
                        TriggerRiskBlock("Limite de lucro diário atingido.", RiskOverlayProfitMessage, true);
                    }
                    else
                    {
                        if (!_warnedProfit)
                        {
                            ShowTransientPopup("Limite de lucro diário atingido.");
                            _warnedProfit = true;
                        }
                        embeddedControl?.SetRiskState(RiskState.Pre, true, "pré-limite");
                    }
                    return;
                }

                if (warn)
                {
                    if (!_warnedLoss && LimitePerdaUSD > 0 && (-pnl) >= PercentualAviso * LimitePerdaUSD)
                    {
                        ShowTransientPopup("Atenção: próximo do limite de perda diário.");
                        _warnedLoss = true;
                    }
                    if (!_warnedTrades && LimiteTradesDia > 0 && _riskTrades >= (int)Math.Floor(PercentualAviso * LimiteTradesDia))
                    {
                        ShowTransientPopup("Atenção: próximo do limite de trades diário.");
                        _warnedTrades = true;
                    }
                    if (!_warnedContracts && LimiteContratosDia > 0 && _riskContracts >= (int)Math.Floor(PercentualAviso * LimiteContratosDia))
                    {
                        ShowTransientPopup("Atenção: próximo do limite de contratos diário.");
                        _warnedContracts = true;
                    }
                    embeddedControl?.SetRiskState(RiskState.Pre, true, "pré-limite");
                    return;
                }

                // OK
                embeddedControl?.SetRiskState(RiskState.Ok, true, "");
                _warnedLoss = _warnedTrades = _warnedContracts = _warnedProfit = false;
                _riskBlocked = false;
                _mainToggleLockedByRisk = false;
            }
            catch (Exception ex)
            {
                SafePrint("EvaluateRisk ex: " + ex.Message);
            }
        }

        private void TriggerRiskBlock(string logMsg, string overlayMsg, bool lockMain)
        {
            _riskBlocked = true;
            _riskBlockedUntil = NextMidnight();
            _mainToggleLockedByRisk = lockMain;
            SafePrint("RISK BLOQUEADO: " + logMsg + $" até {_riskBlockedUntil:HH:mm}");

            SetTradingFromChartEnabled(false);
            embeddedControl?.SetRiskState(RiskState.Blocked, false, "bloqueado");
            embeddedControl?.ForceMainToggleBlocked();

            if (!_riskOverlayShown)
            {
                overlayController?.EnsureOverlayShown(OverlayOpacity, RiskOverlaySeconds > 0 ? RiskOverlaySeconds : 90, overlayMsg);
                _riskOverlayShown = true;
            }
        }
        #endregion
        #endregion

        #region TradingFromChart integration
        private void MapDesiredKeys()
        {
            switch (buyKey)
            {
                case DesiredKey.LeftShift: kbuyKey = Key.LeftShift; break;
                case DesiredKey.LeftAlt: kbuyKey = Key.LeftAlt; break;
                case DesiredKey.RightAlt: kbuyKey = Key.RightAlt; break;
                case DesiredKey.RightShift: kbuyKey = Key.RightShift; break;
                default: kbuyKey = Key.LeftShift; break;
            }

            switch (sellKey)
            {
                case DesiredKey.LeftShift: ksellKey = Key.LeftShift; break;
                case DesiredKey.LeftAlt: ksellKey = Key.LeftAlt; break;
                case DesiredKey.RightAlt: ksellKey = Key.RightAlt; break;
                case DesiredKey.RightShift: ksellKey = Key.RightShift; break;
                default: ksellKey = Key.LeftAlt; break;
            }

            embeddedControl?.SetHotkeyMapping(buyKey.ToString(), sellKey.ToString());
        }

        public void RegisterChartHandlers()
        {
            try
            {
                if (ChartControl != null) ChartControl.MouseLeftButtonDown += LeftMouseDown;
                if (ChartPanel != null)
                {
                    ChartPanel.PreviewKeyDown += ChartPanel_PreviewKeyDown;
                    ChartPanel.PreviewKeyUp += ChartPanel_PreviewKeyUp;
                }
            }
            catch (Exception ex) { SafePrint("RegisterChartHandlers ex: " + ex.Message); }
        }

        public void UnregisterChartHandlers()
        {
            try
            {
                if (ChartControl != null) ChartControl.MouseLeftButtonDown -= LeftMouseDown;
                if (ChartPanel != null)
                {
                    ChartPanel.PreviewKeyDown -= ChartPanel_PreviewKeyDown;
                    ChartPanel.PreviewKeyUp -= ChartPanel_PreviewKeyUp;
                }
            }
            catch (Exception ex) { SafePrint("UnregisterChartHandlers ex: " + ex.Message); }
        }

        private void ChartPanel_PreviewKeyDown(object sender, KeyEventArgs e)
        {
            if (Keyboard.IsKeyDown(kbuyKey)) buyButton = true;
            if (Keyboard.IsKeyDown(ksellKey)) sellButton = true;
            embeddedControl?.SetHotkeyPressed(buyButton, sellButton);
        }

        private void ChartPanel_PreviewKeyUp(object sender, KeyEventArgs e)
        {
            if (Keyboard.IsKeyUp(kbuyKey)) buyButton = false;
            if (Keyboard.IsKeyUp(ksellKey)) sellButton = false;
            embeddedControl?.SetHotkeyPressed(buyButton, sellButton);
        }

        protected void LeftMouseDown(object sender, MouseButtonEventArgs e)
        {
            if (IsRiskBlocked())
            {
                embeddedControl?.SetLastOrderInfo("Bloqueado por RISK até 00:00.");
                e.Handled = true;
                return;
            }

            if (EndDayTime.HasValue && DateTime.Now.TimeOfDay >= EndDayTime.Value)
            {
                embeddedControl?.SetLastOrderInfo("Bloqueado: horário limite atingido");
                SafePrint("Envio bloqueado por EndDay.");
                if (EnableOverlayOnEndDay) overlayController?.EnsureOverlayShown(OverlayOpacity, OverlayDurationSeconds, OverlayMessage);
                e.Handled = true;
                return;
            }

            if ((buyButton == true || sellButton == true) && tradingFromChart == true)
            {
                TriggerCustomEvent(o =>
                {
                    try
                    {
                        if (MyChartScale == null)
                        {
                            embeddedControl?.SetLastOrderInfo("Clique inválido (escala indisponível).");
                            return;
                        }

                        int Y = ChartingExtensions.ConvertToVerticalPixels(e.GetPosition(ChartControl as IInputElement).Y, ChartControl.PresentationSource);
                        double priceClicked = MyChartScale.GetValueByY(Y);

                        if (double.IsNaN(priceClicked) || double.IsInfinity(priceClicked))
                        {
                            embeddedControl?.SetLastOrderInfo("Preço inválido no clique.");
                            return;
                        }

                        myQuantity = embeddedControl?.GetQty() ?? 1;

                        var hostWin = FindAncestorWindow(ChartControl);
                        if (hostWin != null)
                        {
                            var quantitySelector = hostWin.FindFirst("ChartTraderControlQuantitySelector") as QuantityUpDown;
                            if (quantitySelector != null) myQuantity = quantitySelector.Value;

                            var accountSelectorLocal = hostWin.FindFirst("ChartTraderControlAccountSelector") as AccountSelector;
                            if (accountSelectorLocal != null) myAccount = accountSelectorLocal.SelectedAccount;
                            else myAccount = FindAncestorAccount();

                            var atmSelector = hostWin.FindFirst("ChartTraderControlATMStrategySelector") as NinjaTrader.Gui.NinjaScript.AtmStrategy.AtmStrategySelector;

                            if (buyButton == true)
                            {
                                if (priceClicked > Close[0])
                                    myOrder = myAccount?.CreateOrder(Instrument, OrderAction.Buy, orderType, OrderEntry.Manual, TimeInForce.Day, myQuantity, priceClicked, priceClicked, "", "Entry", DateTime.MaxValue, null);
                                else
                                    myOrder = myAccount?.CreateOrder(Instrument, OrderAction.Buy, OrderType.Limit, OrderEntry.Manual, TimeInForce.Day, myQuantity, priceClicked, 0, "", "Entry", DateTime.MaxValue, null);
                            }

                            if (sellButton == true)
                            {
                                if (priceClicked < Close[0])
                                    myOrder = myAccount?.CreateOrder(Instrument, OrderAction.Sell, orderType, OrderEntry.Manual, TimeInForce.Day, myQuantity, priceClicked, priceClicked, "", "Entry", DateTime.MaxValue, null);
                                else
                                    myOrder = myAccount?.CreateOrder(Instrument, OrderAction.Sell, OrderType.Limit, OrderEntry.Manual, TimeInForce.Day, myQuantity, priceClicked, 0, "", "Entry", DateTime.MaxValue, null);
                            }

                            if (myAccount == null)
                            {
                                embeddedControl?.SetLastOrderInfo("Conta não definida.");
                                return;
                            }

                            if (myQuantity <= 0)
                            {
                                embeddedControl?.SetLastOrderInfo("Quantidade inválida.");
                                return;
                            }

                            if (myOrder == null)
                            {
                                embeddedControl?.SetLastOrderInfo("Falha ao criar ordem.");
                                return;
                            }

                            if (atmSelector?.SelectedAtmStrategy != null)
                                NinjaTrader.NinjaScript.AtmStrategy.StartAtmStrategy(atmSelector.SelectedAtmStrategy, myOrder);
                        }

                        myAccount?.Submit(new[] { myOrder });

                        embeddedControl?.SetLastOrderInfo(myOrder?.ToString() ?? "Order submitted");
                        SafePrint($"OnClick: order qty={myQuantity} price={priceClicked}");
                    }
                    catch (Exception ex2)
                    {
                        SafePrint("LeftMouseDown OnClick error: " + ex2.Message);
                        embeddedControl?.SetLastOrderInfo("Erro ao enviar ordem: " + ex2.Message);
                    }
                }, null);

                e.Handled = true;
            }
        }

        public void SetTradingFromChartEnabled(bool enabled)
        {
            tradingFromChart = enabled;
            if (enabled) RegisterChartHandlers(); else UnregisterChartHandlers();
            SafePrint("SetTradingFromChartEnabled: " + enabled);
        }

        internal void NotifyMainToggle(bool enabled)
        {
            _mainEnabled = enabled;
            SafePrint($"Main toggle notify: {_mainEnabled}");
            if (_mainEnabled || ForceDecorationsOverride)
                ComputeOrderDecorations();
            else
                ClearDecorations();
        }

        protected override void OnRender(ChartControl chartControl, ChartScale chartScale)
        {
            base.OnRender(chartControl, chartScale);
            MyChartScale = chartScale;
            RenderOrderDecorations(chartControl, chartScale);
        }
        #endregion

        #region Visual helpers
        private static IEnumerable<T> FindVisualChildren<T>(DependencyObject depObj) where T : DependencyObject
        {
            if (depObj == null) yield break;
            for (int i = 0; i < VisualTreeHelper.GetChildrenCount(depObj); i++)
            {
                var child = VisualTreeHelper.GetChild(depObj, i);
                if (child is T t) yield return t;
                foreach (var c in FindVisualChildren<T>(child)) yield return c;
            }
        }
        #endregion

        #region Popups auxiliares
        public void ShowTransientPopup(string message, int seconds = 3)
        {
            try
            {
                void Show()
                {
                    try
                    {
                        var owner = Window.GetWindow(ChartControl);
                        var popup = new Window
                        {
                            Owner = owner,
                            WindowStyle = WindowStyle.None,
                            AllowsTransparency = true,
                            Background = Brushes.Transparent,
                            ShowInTaskbar = false,
                            ResizeMode = ResizeMode.NoResize,
                            Topmost = true,
                            SizeToContent = SizeToContent.WidthAndHeight
                        };

                        var border = new Border
                        {
                            Background = new SolidColorBrush(Color.FromArgb(220, 30, 30, 30)),
                            BorderBrush = new SolidColorBrush(Color.FromRgb(170, 120, 60)),
                            BorderThickness = new Thickness(1),
                            CornerRadius = new CornerRadius(6),
                            Padding = new Thickness(10),
                            Child = new TextBlock
                            {
                                Text = message ?? "",
                                Foreground = Brushes.White,
                                FontSize = 12,
                                TextWrapping = TextWrapping.Wrap
                            }
                        };

                        popup.Content = border;

                        if (owner != null)
                        {
                            popup.WindowStartupLocation = WindowStartupLocation.Manual;
                            popup.Left = owner.Left + owner.Width / 2 - 160;
                            popup.Top = owner.Top + owner.Height / 2 - 40;
                        }
                        else
                            popup.WindowStartupLocation = WindowStartupLocation.CenterScreen;

                        popup.Show();

                        var t = new DispatcherTimer { Interval = TimeSpan.FromSeconds(Math.Max(1, seconds)) };
                        t.Tick += (s, e) =>
                        {
                            try { t.Stop(); } catch { }
                            try { popup.Close(); } catch { }
                        };
                        t.Start();
                    }
                    catch { }
                }

                if (ChartControl?.Dispatcher != null)
                    ChartControl.Dispatcher.BeginInvoke((Action)(() => Show()));
                else
                    Dispatcher.CurrentDispatcher.BeginInvoke((Action)(() => Show()));
            }
            catch { }
        }
        #endregion

        #region BE toggle notifications
        internal void NotifyBeToggle(bool enabled)
        {
            if (!enabled)
            {
                _beFireRequest = false;
                _beActive = false;
            }
            else
            {
                _beFireRequest = true; // evento one-shot
            }
            SavePrefs();
        }

        internal void NotifyStopChanged()
        {
            try
            {
                if (embeddedControl == null) return;
                if (embeddedControl.IsAtrEnabled())
                {
                    double stopFinancial = embeddedControl.GetStopFinancial();
                    if (stopFinancial <= 0)
                    {
                        embeddedControl.ForceAtrOffAndEnableQty();
                        ShowTransientPopup("ATR desligado: defina Stop ($) para usar ATR.");
                        SafePrint("ATR auto-off (NotifyStopChanged): Stop($) inválido.");
                        SavePrefs();
                        return;
                    }

                    // Se temos ATR válido, tenta recalc com últimos valores conhecidos
                    if (_lastAtrTicks > 0 && _lastAtrDollarPerContract > 0)
                    {
                        bool ok = ApplyAtrSizingWithValidationProxy(_lastAtrTicks, _lastAtrDollarPerContract, false);
                        if (!ok)
                        {
                            embeddedControl.ForceAtrOffAndEnableQty();
                            ShowTransientPopup("ATR desligado: não foi possível recalcular sizing.");
                        }
                        SavePrefs();
                    }
                }
                else
                {
                    SavePrefs();
                }
            }
            catch (Exception ex)
            {
                SafePrint("NotifyStopChanged ex: " + ex.Message);
            }
        }
        #endregion

        #region Desenho ATR (linha + legendas)
        private int GetLeftBarsAgo()
        {
            try
            {
                if (ChartBars != null)
                {
                    int from = ChartBars.FromIndex;
                    if (from >= 0 && from <= CurrentBar)
                        return CurrentBar - from;
                }
            }
            catch { }
            return 0; // fallback: candle atual
        }

        private void DrawAtrVisuals(int atrTicks, double tickSize)
        {
            try
            {
                if (Instrument == null || atrTicks <= 0)
                {
                    ClearAtrDraws();
                    return;
                }

                var acc = ResolveAccountWithPosition();
                var pos = GetPositionForInstrument(acc, Instrument);
                if (pos == null || pos.Quantity == 0)
                {
                    ClearAtrDraws();
                    return;
                }

                double entry = pos.AveragePrice;
                bool isShort = pos.MarketPosition == MarketPosition.Short;
                double stopPrice = isShort
                    ? entry + atrTicks * tickSize
                    : entry - atrTicks * tickSize;

                ClearAtrDraws();

                var lineBrush = new SolidColorBrush(Color.FromArgb(110, 200, 200, 200));
                lineBrush.Freeze();
                NinjaTrader.NinjaScript.DrawingTools.Draw.HorizontalLine(this, _atrLineTag, stopPrice, lineBrush);

                int barsAgoLeft = GetLeftBarsAgo();
                double tick = Instrument?.MasterInstrument?.TickSize ?? 1.0;
                double yAbove = stopPrice + tick * AtrLabelOffsetTicks;
                double yBelow = stopPrice - tick * AtrLabelOffsetTicks;

                NinjaTrader.NinjaScript.DrawingTools.Draw.Text(
                    this,
                    _atrTextTag1,
                    false,
                    "● ATR ON",
                    barsAgoLeft,
                    yAbove,
                    0,
                    Brushes.DarkGoldenrod,
                    new SimpleFont("Montserrat", 10),
                    TextAlignment.Left,
                    Brushes.Transparent,
                    Brushes.Transparent,
                    0);

                NinjaTrader.NinjaScript.DrawingTools.Draw.Text(
                    this,
                    _atrTextTag2,
                    false,
                    "Sugestão Stop",
                    barsAgoLeft,
                    yBelow,
                    0,
                    Brushes.DarkGoldenrod,
                    new SimpleFont("Montserrat", 8),
                    TextAlignment.Left,
                    Brushes.Transparent,
                    Brushes.Transparent,
                    0);
            }
            catch (Exception ex)
            {
                SafePrint("DrawAtrVisuals ex: " + ex.Message);
            }
        }

        private void ClearAtrDraws()
        {
            try
            {
                RemoveDrawObject(_atrLineTag);
                RemoveDrawObject(_atrTextTag1);
                RemoveDrawObject(_atrTextTag2);
            }
            catch { }
        }
        #endregion

        #region Order Decorator integration
        private void SubscribeDecoratorAccountEvents()
        {
            try
            {
                lock (Account.All)
                {
                    foreach (var acc in Account.All)
                    {
                        acc.OrderUpdate -= OnOrderUpdateDecorator;
                        acc.OrderUpdate += OnOrderUpdateDecorator;

                        acc.ExecutionUpdate -= OnExecutionUpdateDecorator;
                        acc.ExecutionUpdate += OnExecutionUpdateDecorator;

                        acc.PositionUpdate -= OnPositionUpdateDecorator;
                        acc.PositionUpdate += OnPositionUpdateDecorator;

                        acc.AccountItemUpdate -= OnAccountItemUpdateDecorator;
                        acc.AccountItemUpdate += OnAccountItemUpdateDecorator;
                    }
                }
            }
            catch (Exception ex) { SafePrint("SubscribeDecoratorAccountEvents ex: " + ex.Message); }
        }

        private void UnsubscribeDecoratorAccountEvents()
        {
            try
            {
                lock (Account.All)
                {
                    foreach (var acc in Account.All)
                    {
                        acc.OrderUpdate -= OnOrderUpdateDecorator;
                        acc.ExecutionUpdate -= OnExecutionUpdateDecorator;
                        acc.PositionUpdate -= OnPositionUpdateDecorator;
                        acc.AccountItemUpdate -= OnAccountItemUpdateDecorator;
                    }
                }
            }
            catch { }
        }

        private void OnOrderUpdateDecorator(object sender, OrderEventArgs e)
        {
            try
            {
                if (e?.Order == null) return;
                var st = e.OrderState;
                if (st != OrderState.Accepted && st != OrderState.Working && st != OrderState.PartFilled && st != OrderState.Filled) return;
                ComputeOrderDecorations();
            }
            catch (Exception ex) { SafePrint("OnOrderUpdateDecorator ex: " + ex.Message); }
        }

        private void OnExecutionUpdateDecorator(object sender, ExecutionEventArgs e)
        {
            try
            {
                if (e?.Execution == null) return;
                ComputeOrderDecorations();
            }
            catch (Exception ex) { SafePrint("OnExecutionUpdateDecorator ex: " + ex.Message); }
        }

        private void OnPositionUpdateDecorator(object sender, PositionEventArgs e)
        {
            try
            {
                if (e?.Position == null) return;
                // Se ficou flat, limpa ordens pendentes do instrumento
                if (e.Position.Instrument != null &&
                    Instrument != null &&
                    (e.Position.Instrument.FullName == Instrument.FullName ||
                     e.Position.Instrument.MasterInstrument?.Name == Instrument.MasterInstrument?.Name) &&
                    e.Position.Quantity == 0)
                {
                    CleanupFlatOrders(e.Position.Account);
                }
                ComputeOrderDecorations();
            }
            catch (Exception ex) { SafePrint("OnPositionUpdateDecorator ex: " + ex.Message); }
        }

        private void OnAccountItemUpdateDecorator(object sender, AccountItemEventArgs e)
        {
            try
            {
                if (e.AccountItem != AccountItem.UnrealizedProfitLoss) return;
                ComputeOrderDecorations();
            }
            catch (Exception ex) { SafePrint("OnAccountItemUpdateDecorator ex: " + ex.Message); }
        }

        private void ComputeOrderDecorations()
        {
            lock (_decoLock)
            {
                decoQtyByKey.Clear();
                decoToRender.Clear();

                if (State == State.Historical) return;
                if (ChartControl == null || Instrument == null) return;

                Account sel = null;
                try
                {
                    sel = GetSelectedAccount();
                    if (sel == null)
                        sel = ResolveAccountWithPosition();
                    if (sel == null && selectedAccountCached != null)
                        sel = selectedAccountCached;
                    if (sel == null && Account.All.Count > 0)
                        sel = Account.All.FirstOrDefault();
                }
                catch { }

                if (sel == null)
                {
                    SafePrint("ComputeOrderDecorations: nenhuma conta resolvida (fallback falhou).");
                    return;
                }

                int posCount = 0;
                int ordCount = 0;
                int renderCount = 0;

                foreach (var pos in sel.Positions)
                {
                    if (pos.Instrument != Instrument) continue;
                    if (pos.MarketPosition == MarketPosition.Flat) continue;
                    posCount++;

                    double entryPrice = pos.AveragePrice;

                    foreach (var order in sel.Orders)
                    {
                        if (order == null) continue;
                        if (order.Instrument != Instrument) continue;

                        if (order.OrderState != OrderState.Accepted &&
                            order.OrderState != OrderState.Working &&
                            order.OrderState != OrderState.PartFilled) continue;

                        if (pos.MarketPosition == MarketPosition.Long && order.IsLong) continue;
                        if (pos.MarketPosition == MarketPosition.Short && order.IsShort) continue;

                        double ordPrice = GetOrderPriceForDeco(order);
                        if (ordPrice <= 0) continue;

                        var kind = GetDecorKind(order.OrderType);
                        if (kind == DecorKind.OTHER) continue;

                        ordCount++;

                        string key = ordPrice.ToString("G17") + kind.ToString();
                        int aggQty = decoQtyByKey.AddOrUpdate(key, order.Quantity, (_, old) => old + order.Quantity);

                        double priceDiff = (pos.MarketPosition == MarketPosition.Long) ? (ordPrice - entryPrice) : (entryPrice - ordPrice);
                        double tickSize = TickSize;
                        if (tickSize <= 0) continue;

                        int ticks = (int)Math.Round(priceDiff / tickSize);
                        double points = priceDiff * aggQty;
                        double currencyValue = priceDiff * (Instrument?.MasterInstrument?.PointValue ?? 1.0) * aggQty;

                        double accCash = 0.0;
                        try { accCash = sel.GetAccountItem(AccountItem.CashValue, Currency.UsDollar).Value; } catch { }

                        string text = $"{(kind == DecorKind.STOP ? "STOP" : "TARGET")} ({aggQty})";
                        text += DecorDisplayTicks ? $"  :  {((kind == DecorKind.STOP && ticks > 0) ? "+" : "")}{ticks} T" : "";
                        text += DecorDisplayPoints ? $"  :  {((kind == DecorKind.STOP && points > 0) ? "+" : "")}{points:F2} P" : "";
                        text += DecorDisplayCurrency ? $"  :  {DecorSymbol} {currencyValue:N2}" : "";
                        if (DecorDisplayPercent && accCash > 0)
                            text += $"  :  {(currencyValue / accCash):P2}";

                        var item = new DecorInfo { Kind = kind, Text = text };
                        decoToRender.AddOrUpdate(ordPrice, item, (_, __) => item);
                        renderCount++;
                    }
                }

                SafePrint($"ComputeOrderDecorations: main={_mainEnabled} override={ForceDecorationsOverride} acc={sel.Name} posCount={posCount} ordCount={ordCount} render={renderCount}");
            }
            ForceRefreshDecorations();
        }

        private void ClearDecorations()
        {
            lock (_decoLock)
            {
                decoQtyByKey.Clear();
                decoToRender.Clear();
            }
            ForceRefreshDecorations();
        }

        private DecorKind GetDecorKind(OrderType ot)
        {
            if (decoStopTypes.Contains(ot)) return DecorKind.STOP;
            if (decoTargetTypes.Contains(ot)) return DecorKind.TARGET;
            return DecorKind.OTHER;
        }

        private double GetOrderPriceForDeco(Order o)
        {
            if (o == null) return 0;
            if (decoStopTypes.Contains(o.OrderType)) return o.StopPrice;
            if (decoTargetTypes.Contains(o.OrderType)) return o.LimitPrice;
            return 0;
        }

        private SharpDX.Direct2D1.SolidColorBrush ToDxSolidBrush(Brush brush)
        {
            var scb = brush as SolidColorBrush ?? Brushes.White as SolidColorBrush;
            var c = scb.Color;
            return new SharpDX.Direct2D1.SolidColorBrush(
                RenderTarget,
                new Color4(c.ScR, c.ScG, c.ScB, c.ScA));
        }

        private SharpDX.Direct2D1.Brush ToDxFillBrush(Brush brush, SharpDX.RectangleF rect)
        {
            if (brush is LinearGradientBrush lg && lg.GradientStops != null && lg.GradientStops.Count > 0)
            {
                var stops = lg.GradientStops.Select(gs =>
                    new SharpDX.Direct2D1.GradientStop
                    {
                        Color = new Color4(gs.Color.ScR, gs.Color.ScG, gs.Color.ScB, gs.Color.ScA),
                        Position = (float)gs.Offset
                    }).ToArray();

                using (var stopCollection = new SharpDX.Direct2D1.GradientStopCollection(RenderTarget, stops, SharpDX.Direct2D1.ExtendMode.Clamp))
                {
                    var props = new SharpDX.Direct2D1.LinearGradientBrushProperties
                    {
                        StartPoint = new Vector2(rect.Left, rect.Top),
                        EndPoint = new Vector2(rect.Left, rect.Top + rect.Height)
                    };
                    return new SharpDX.Direct2D1.LinearGradientBrush(RenderTarget, props, null, stopCollection);
                }
            }
            return ToDxSolidBrush(brush);
        }

        private void RenderOrderDecorations(ChartControl chartControl, ChartScale chartScale)
        {
            if (State == State.Historical) return;
            if (decoToRender.IsEmpty) return;
            if (ChartPanel == null) return;

            if (chartControl.Properties.LabelFont != decoFont)
            {
                decoFont = chartControl.Properties.LabelFont;
                decoTextFormat = decoFont.ToDirectWriteTextFormat();
                decoSampleTextWidth = MeasureTextWidth(decoFont, DecoSampleText);
            }

            try
            {
                using (var borderDx = ToDxSolidBrush(DecorOutlineBrush))
                using (var textDx = ToDxSolidBrush(DecorTextBrush))
                {
                    double barPct = chartControl.OwnerChart?.ChartTrader?.Properties?.OrderDisplayBarLength ?? 0;
                    double barPx = ChartPanel.W * (barPct / 100.0);

                    foreach (var kvp in decoToRender)
                    {
                        double price = kvp.Key;
                        DecorInfo info = kvp.Value;

                        var layout = new SharpDX.DirectWrite.TextLayout(
                            NinjaTrader.Core.Globals.DirectWriteFactory,
                            info.Text,
                            decoTextFormat,
                            ChartPanel.X + ChartPanel.W,
                            decoTextFormat.FontSize);

                        float tw = layout.Metrics.Width;
                        float th = layout.Metrics.Height;

                        float x = (float)(ChartPanel.W - (barPx + tw + decoSampleTextWidth + DecorFlexGapWidth));
                        int yPx = chartScale.GetYByValue(price);
                        float y = yPx - ((th + 7) / 2);

                        var start = new SharpDX.Vector2(x, y);
                        var textPos = new SharpDX.Vector2(start.X + 4, start.Y + 3);
                        var lineStart = new SharpDX.Vector2(start.X + tw + 9, yPx);
                        var lineEnd = new SharpDX.Vector2(ChartPanel.W, yPx);

                        var rect = new SharpDX.RectangleF(start.X, start.Y, tw + 8, th + 6);

                        using (var fillDx = ToDxFillBrush(info.Kind == DecorKind.STOP ? DecorStopFillBrush : DecorTargetFillBrush, rect))
                        {
                            RenderTarget.FillRectangle(rect, fillDx);
                        }

                        RenderTarget.DrawRectangle(rect, borderDx, 1f);
                        RenderTarget.DrawLine(lineStart, lineEnd, borderDx);

                        RenderTarget.DrawTextLayout(textPos, layout, textDx, SharpDX.Direct2D1.DrawTextOptions.NoSnap);
                        layout.Dispose();
                    }
                }
            }
            catch (Exception ex)
            {
                SafePrint("RenderOrderDecorations ex: " + ex.Message);
            }
        }

        private float MeasureTextWidth(SimpleFont font, string text)
        {
            var tf = font.ToDirectWriteTextFormat();
            using (var tl = new SharpDX.DirectWrite.TextLayout(
                NinjaTrader.Core.Globals.DirectWriteFactory,
                text,
                tf,
                ChartPanel.X + ChartPanel.W,
                tf.FontSize))
            {
                return tl.Metrics.Width;
            }
        }

        private void ForceRefreshDecorations()
        {
            try { ChartControl?.InvalidateVisual(); } catch { }
        }

        private static Brush CreateDefaultStopGradient()
        {
            var stopGradient = new LinearGradientBrush
            {
                StartPoint = new Point(0, 0),
                EndPoint = new Point(0, 1)
            };
            stopGradient.GradientStops.Add(new GradientStop(Color.FromRgb(130, 130, 130), 0.0));
            stopGradient.GradientStops.Add(new GradientStop(Color.FromRgb(90, 90, 90), 1.0));
            return stopGradient;
        }
        #endregion
    }

    internal class EndDayOverlayController
    {
        private readonly SmartBoletaIndicator _parent;
        private Window _overlay;
        private Window _host;
        private DispatcherTimer _fallbackTimer;

        public EndDayOverlayController(SmartBoletaIndicator parent)
        {
            _parent = parent;
        }

        public void ShowOverlay(TimeSpan triggerTime, double opacity, int durationSeconds, string message)
        {
            EnsureOverlayShown(opacity, durationSeconds, message);
        }

        public void EnsureOverlayShown(double opacity, int durationSeconds, string message)
        {
            try
            {
                RunOnUi(() =>
                {
                    try
                    {
                        _host = Window.GetWindow(_parent.ChartControl);
                        if (_host == null) { _parent.SafePrint("Overlay: host window null."); return; }

                        if (_overlay == null)
                        {
                            CreateOverlay(opacity, message);
                            AttachHostEvents();
                        }
                        ScheduleFallback(durationSeconds);
                    }
                    catch (Exception ex) { _parent.SafePrint("Overlay EnsureOverlayShown ex: " + ex.Message); }
                });
            }
            catch { }
        }

        public void DisposeOverlay()
        {
            RunOnUi(() =>
            {
                CancelFallback();
                RemoveOverlay();
            });
        }

        private void CreateOverlay(double opacity, string message)
        {
            try
            {
                _overlay = new Window
                {
                    Owner = _host,
                    WindowStyle = WindowStyle.None,
                    AllowsTransparency = true,
                    Background = new SolidColorBrush(Color.FromArgb((byte)(Math.Max(0, Math.Min(1.0, opacity)) * 255), 0, 0, 0)),
                    ShowInTaskbar = false,
                    ResizeMode = ResizeMode.NoResize,
                    Topmost = true,
                    Width = _host.ActualWidth,
                    Height = _host.ActualHeight,
                    Left = _host.Left,
                    Top = _host.Top,
                    ShowActivated = false
                };

                var grid = new Grid
                {
                    Background = new SolidColorBrush(Color.FromArgb((byte)(Math.Max(0, Math.Min(1.0, opacity)) * 255), 0, 0, 0)),
                    IsHitTestVisible = true
                };

                var inner = new StackPanel
                {
                    VerticalAlignment = VerticalAlignment.Center,
                    HorizontalAlignment = HorizontalAlignment.Center,
                    Orientation = Orientation.Vertical,
                    Margin = new Thickness(40)
                };

                var title = new TextBlock
                {
                    Text = "Atenção, trader — Janela de bloqueio ativa!",
                    Foreground = Brushes.White,
                    FontSize = 18,
                    FontWeight = FontWeights.Bold,
                    TextAlignment = TextAlignment.Center,
                    Margin = new Thickness(8)
                };

                var spacer = new Border { Height = 30, Background = Brushes.Transparent };

                var subtitle = new TextBlock
                {
                    Text = string.IsNullOrWhiteSpace(message) ? "Envio de ordens bloqueado neste horário." : message,
                    Foreground = Brushes.White,
                    FontSize = 13,
                    TextAlignment = TextAlignment.Center,
                    Margin = new Thickness(6)
                };

                inner.Children.Add(title);
                inner.Children.Add(spacer);
                inner.Children.Add(subtitle);

                grid.Children.Add(inner);
                var rect = new WpfRectangle { Fill = Brushes.Transparent, HorizontalAlignment = HorizontalAlignment.Stretch, VerticalAlignment = VerticalAlignment.Stretch, IsHitTestVisible = true };
                grid.Children.Add(rect);

                _overlay.PreviewKeyDown += (s, e) => e.Handled = true;
                _overlay.PreviewKeyUp += (s, e) => e.Handled = true;
                _overlay.MouseDown += (s, e) => e.Handled = true;
                _overlay.MouseUp += (s, e) => e.Handled = true;

                _overlay.Content = grid;
                _overlay.Show();

                _parent.SafePrint("Overlay: exibido.");
            }
            catch (Exception ex)
            {
                _parent.SafePrint("Overlay CreateOverlay ex: " + ex.Message);
            }
        }

        private void RemoveOverlay()
        {
            try
            {
                if (_overlay != null)
                {
                    try
                    {
                        if (_host != null)
                        {
                            _host.LocationChanged -= HostWindow_PositionOrSizeChanged;
                            _host.SizeChanged -= HostWindow_PositionOrSizeChanged;
                        }
                    }
                    catch { }

                    var w = _overlay;
                    _overlay = null;
                    try { w.Close(); } catch { }
                    _parent.SafePrint("Overlay: removido.");
                }
            }
            catch (Exception ex) { _parent.SafePrint("Overlay RemoveOverlay ex: " + ex.Message); }
        }

        private void AttachHostEvents()
        {
            try
            {
                if (_host != null)
                {
                    _host.LocationChanged += HostWindow_PositionOrSizeChanged;
                    _host.SizeChanged += HostWindow_PositionOrSizeChanged;
                }
            }
            catch (Exception ex) { _parent.SafePrint("Overlay AttachHostEvents ex: " + ex.Message); }
        }

        private void HostWindow_PositionOrSizeChanged(object sender, EventArgs e)
        {
            try
            {
                if (_overlay == null || _host == null) return;
                _overlay.Left = _host.Left;
                _overlay.Top = _host.Top;
                _overlay.Width = _host.ActualWidth;
                _overlay.Height = _host.ActualHeight;
            }
            catch (Exception ex) { _parent.SafePrint("Overlay HostWindow_PositionOrSizeChanged ex: " + ex.Message); }
        }

        private void ScheduleFallback(int seconds)
        {
            try
            {
                CancelFallback();
                if (seconds <= 0) return;
                _fallbackTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(seconds) };
                _fallbackTimer.Tick += (s, e) =>
                {
                    CancelFallback();
                    RemoveOverlay();
                };
                _fallbackTimer.Start();
            }
            catch (Exception ex) { _parent.SafePrint("Overlay ScheduleFallback ex: " + ex.Message); }
        }

        private void CancelFallback()
        {
            try
            {
                if (_fallbackTimer != null)
                {
                    _fallbackTimer.Stop();
                    _fallbackTimer = null;
                }
            }
            catch { }
        }

        private void RunOnUi(Action action)
        {
            try
            {
                if (_parent.ChartControl != null && _parent.ChartControl.Dispatcher != null)
                    _parent.ChartControl.Dispatcher.BeginInvoke(action);
                else
                    Dispatcher.CurrentDispatcher.BeginInvoke(action);
            }
            catch (Exception ex)
            {
                _parent.SafePrint("Overlay RunOnUi ex: " + ex.Message);
            }
        }
    }

    // --- SmartBoletaEmbeddedControl (completo) ---
    public class SmartBoletaEmbeddedControl : Grid
    {
        private readonly SmartBoletaIndicator _parent;

        private const double CompactTextBoxHeight = 16.0;
        private const double CompactFontSize = 10.0;
        private const double RowSpacing = 0.5; // reduzido para ganhar altura

        private readonly Brush BronzeBrush = new SolidColorBrush(Color.FromRgb(170, 120, 60));
        private readonly Brush GraphiteBrush = new SolidColorBrush(Color.FromRgb(72, 72, 72));
        private readonly Brush LightGrayBrush = Brushes.LightGray;
        private readonly Brush InactiveBulletBrush = new SolidColorBrush(Color.FromRgb(150, 150, 150));
        private readonly Brush MainOnBrush = new SolidColorBrush(Color.FromRgb(60, 200, 120));
        private readonly Brush PreLimitBrush = Brushes.Gold;
        private readonly Brush BlockBrush = Brushes.IndianRed;

        private readonly Brush PnlPositiveBrush = Brushes.LightGreen;
        private readonly Brush PnlNegativeBrush = Brushes.IndianRed;

        private TextBlock _titleCenter;
        private WpfEllipse _mainStateBullet;
        private TextBlock _tbMainToggle;

        private TextBlock _txtEntry;

        private WpfEllipse _bulletBe;
        private TextBlock _beStateText;

        private WpfEllipse _bulletQty;
        private TextBlock _txtQty;
        private TextBlock _tbMinus;
        private TextBlock _tbPlus;

        private WpfEllipse _bulletStopFinancial;
        private TextBlock _txtStop;
        private TextBlock _tbStopEdit;

        private WpfEllipse _bulletAtr;
        private TextBlock _tbAtrToggle;
        private TextBlock _atrValueText;

        private WpfEllipse _bulletPnlDia;
        private TextBlock _pnlDiaText;

        private WpfEllipse _bulletRisk;
        private TextBlock _tbRiskToggle;
        private TextBlock _tbRiskStatus;

        private TextBlock _txtChartStop;
        private TextBlock _txtExit;

        private WpfEllipse _bulletEndDay;
        private TextBlock _tbEndDayValue;
        private TextBlock _tbEndDayEdit;

        private WpfEllipse _bulletOnClick;
        private TextBlock _tbOnClickToggle;

        private TextBlock _tbBoletaId;

        // Hotkeys info
        private TextBlock _tbHotkeyInfo;
        private TextBlock _tbHotkeyPressed;

        private int _qty = 1;
        private bool _beEnabled = false;
        private bool _mainEnabled = false;
        private bool _onClickEnabled = false;

        private bool _qtyButtonsEnabled = true;

        public SmartBoletaEmbeddedControl(SmartBoletaIndicator parent)
        {
            _parent = parent;
            BuildUi();
            SizeChanged += SmartBoletaEmbeddedControl_SizeChanged;
        }

        private WpfEllipse CreateBullet(double size = 8) => new WpfEllipse { Width = size, Height = size, Fill = InactiveBulletBrush, Margin = new Thickness(0, 0, 6, 0), VerticalAlignment = VerticalAlignment.Center };
        private StackPanel CreateLabelWithBulletLeft(string labelText, out WpfEllipse bullet)
        {
            bullet = CreateBullet();
            var lbl = new TextBlock { Text = labelText, Foreground = LightGrayBrush, FontSize = CompactFontSize, VerticalAlignment = VerticalAlignment.Center, Cursor = Cursors.Hand };
            var stack = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Left };
            stack.Children.Add(bullet);
            stack.Children.Add(lbl);
            return stack;
        }
        private bool IsMainEnabled() => _mainEnabled;
        public bool IsBeEnabled() => _beEnabled;
        public bool IsAtrEnabled() { try { return _tbAtrToggle != null && _tbAtrToggle.Text == "On"; } catch { return false; } }
        public bool IsOnClickEnabled() => _onClickEnabled;

        public void SetBoletaId(string id)
        {
            if (_tbBoletaId != null)
                _tbBoletaId.Text = string.IsNullOrWhiteSpace(id) ? "" : id;
        }

        private void BuildUi()
        {
            Background = Brushes.Transparent;
            Margin = new Thickness(6);

            // ScrollViewer para garantir visibilidade do rodapé em telas menores/altura limitada
            var scroller = new ScrollViewer
            {
                VerticalScrollBarVisibility = ScrollBarVisibility.Auto,
                HorizontalScrollBarVisibility = ScrollBarVisibility.Disabled,
                Margin = new Thickness(0),
                Padding = new Thickness(0)
            };

            var main = new StackPanel { Orientation = Orientation.Vertical, Margin = new Thickness(2) };

            var header = new Grid { Margin = new Thickness(0, 0, 0, 4) };
            header.ColumnDefinitions.Add(new ColumnDefinition { Width = GridLength.Auto });
            header.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
            header.ColumnDefinitions.Add(new ColumnDefinition { Width = GridLength.Auto });

            var iconHolder = new Grid { Width = 18, Height = 18, Margin = new Thickness(0, 0, 4, 0) };
            var outer = new WpfEllipse { Width = 18, Height = 18, Stroke = new SolidColorBrush(Color.FromRgb(58, 58, 58)), StrokeThickness = 1.0, Fill = Brushes.Transparent };

            var radial = new RadialGradientBrush { GradientOrigin = new Point(0.35, 0.25), Center = new Point(0.35, 0.25), RadiusX = 0.8, RadiusY = 0.8 };
            radial.GradientStops.Add(new GradientStop(Color.FromRgb(170, 120, 60), 0.0));
            radial.GradientStops.Add(new GradientStop(Color.FromRgb(130, 80, 35), 0.9));
            var bronzeCircle = new WpfEllipse { Width = 14, Height = 14, Fill = radial, HorizontalAlignment = HorizontalAlignment.Center, VerticalAlignment = VerticalAlignment.Center };

            var star = new System.Windows.Shapes.Path
            {
                Fill = Brushes.Black,
                Data = Geometry.Parse("M7 0 L8.6 4.2 L13 4.2 L9.1 6.5 L10.6 10.7 L7 8.3 L3.4 10.7 L4.9 6.5 L1 4.2 L5.4 4.2 Z"),
                Width = 9,
                Height = 9,
                Stretch = Stretch.Uniform,
                HorizontalAlignment = HorizontalAlignment.Center,
                VerticalAlignment = VerticalAlignment.Center
            };

            iconHolder.Children.Add(outer); iconHolder.Children.Add(bronzeCircle); iconHolder.Children.Add(star);

            _titleCenter = new TextBlock { VerticalAlignment = VerticalAlignment.Center, HorizontalAlignment = HorizontalAlignment.Left };
            var runHawk = new Run("Hawk - ") { Foreground = BronzeBrush, FontWeight = FontWeights.SemiBold };
            var runSmartPanel = new Run("Smart Panel") { Foreground = GraphiteBrush, FontWeight = FontWeights.SemiBold };
            _titleCenter.Inlines.Add(runHawk); _titleCenter.Inlines.Add(runSmartPanel);
            _titleCenter.FontSize = CompactFontSize + 4;

            var leftHeaderPanel = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Left };
            leftHeaderPanel.Children.Add(iconHolder); leftHeaderPanel.Children.Add(_titleCenter);
            header.Children.Add(leftHeaderPanel); Grid.SetColumn(leftHeaderPanel, 0);

            var rightHeader = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Right, VerticalAlignment = VerticalAlignment.Center };
            _mainStateBullet = CreateBullet(14);
            _mainStateBullet.Fill = InactiveBulletBrush;
            _tbMainToggle = new TextBlock { Text = "Off", Width = 40, TextAlignment = TextAlignment.Center, Cursor = Cursors.Hand, Foreground = Brushes.Gray, VerticalAlignment = VerticalAlignment.Center, Margin = new Thickness(6, 0, 0, 0) };
            _tbMainToggle.MouseLeftButtonUp += (s, e) => ToggleMain();

            rightHeader.Children.Add(_mainStateBullet);
            rightHeader.Children.Add(_tbMainToggle);

            header.Children.Add(rightHeader); Grid.SetColumn(rightHeader, 2);

            main.Children.Add(header);

            // Hotkeys info
            var hkGrid = new Grid { Margin = new Thickness(0, 0, 0, 2) };
            hkGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
            hkGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });

            _tbHotkeyInfo = new TextBlock { Text = "Keys: Buy=LeftShift | Sell=LeftAlt", Foreground = LightGrayBrush, FontSize = CompactFontSize, HorizontalAlignment = HorizontalAlignment.Left };
            _tbHotkeyPressed = new TextBlock { Text = "", Foreground = BronzeBrush, FontSize = CompactFontSize, HorizontalAlignment = HorizontalAlignment.Right };

            hkGrid.Children.Add(_tbHotkeyInfo);
            Grid.SetColumn(_tbHotkeyInfo, 0);
            hkGrid.Children.Add(_tbHotkeyPressed);
            Grid.SetColumn(_tbHotkeyPressed, 1);

            main.Children.Add(hkGrid);

            var threeCol = new Grid { Margin = new Thickness(0, 0, 0, 4) };
            threeCol.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
            threeCol.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Auto) });
            threeCol.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });

            var valueMargin = new Thickness(0, RowSpacing, 0, 0);

            var entryCol = new StackPanel { Orientation = Orientation.Vertical, HorizontalAlignment = HorizontalAlignment.Left };
            entryCol.Children.Add(new TextBlock { Text = "Entry", Foreground = LightGrayBrush, FontSize = CompactFontSize, Margin = new Thickness(0, 0, 0, RowSpacing) });
            _txtEntry = new TextBlock { Text = "-", Foreground = Brushes.White, FontSize = CompactFontSize, Margin = valueMargin, HorizontalAlignment = HorizontalAlignment.Left };
            entryCol.Children.Add(_txtEntry);
            Grid.SetColumn(entryCol, 0);
            threeCol.Children.Add(entryCol);

            var centerCol = new StackPanel { Orientation = Orientation.Vertical, HorizontalAlignment = HorizontalAlignment.Center };
            centerCol.Children.Add(new TextBlock { Text = "Stop", Foreground = LightGrayBrush, FontSize = CompactFontSize, TextAlignment = TextAlignment.Center, Margin = new Thickness(0, 0, 0, RowSpacing) });
            _txtChartStop = new TextBlock { Text = "-", Foreground = Brushes.White, FontSize = CompactFontSize, Margin = valueMargin, TextAlignment = TextAlignment.Center };
            centerCol.Children.Add(_txtChartStop);
            Grid.SetColumn(centerCol, 1);
            threeCol.Children.Add(centerCol);

            var exitCol = new StackPanel { Orientation = Orientation.Vertical, HorizontalAlignment = HorizontalAlignment.Right };
            exitCol.Children.Add(new TextBlock { Text = "Exit", Foreground = LightGrayBrush, FontSize = CompactFontSize, TextAlignment = TextAlignment.Right, Margin = new Thickness(0, 0, 0, RowSpacing) });
            _txtExit = new TextBlock { Text = "-", Foreground = Brushes.White, FontSize = CompactFontSize, Margin = valueMargin, TextAlignment = TextAlignment.Right };
            exitCol.Children.Add(_txtExit);
            Grid.SetColumn(exitCol, 2);
            threeCol.Children.Add(exitCol);

            main.Children.Add(threeCol);

            var beRow = CreateLabelWithBulletLeft("BE", out _bulletBe);
            if (beRow.Children.Count > 1 && beRow.Children[1] is TextBlock beLabel) beLabel.Cursor = Cursors.Arrow;
            main.Children.Add(beRow);

            _beStateText = new TextBlock { Text = "Off", FontSize = CompactFontSize, Foreground = Brushes.Gray, HorizontalAlignment = HorizontalAlignment.Center, Margin = new Thickness(0, RowSpacing, 0, RowSpacing * 2) };
            _beStateText.MouseLeftButtonUp += (s, e) => { if (!IsMainEnabled()) return; ToggleBE(); };
            _beStateText.ToolTip = "Break-even one-shot: puxa stop para BE quando ticks favoráveis suficientes.";
            main.Children.Add(_beStateText);

            var qtyRow = CreateLabelWithBulletLeft("Qty", out _bulletQty);
            main.Children.Add(qtyRow);

            var qtyInline = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, RowSpacing, 0, RowSpacing * 2.5), HorizontalAlignment = HorizontalAlignment.Center };
            _tbMinus = new TextBlock { Text = "-", Width = 28, Height = CompactTextBoxHeight, TextAlignment = TextAlignment.Center, Cursor = Cursors.Hand, Foreground = Brushes.Gray, VerticalAlignment = VerticalAlignment.Center };
            _tbMinus.MouseLeftButtonDown += (s, e) => { if (!IsMainEnabled() || !_qtyButtonsEnabled) return; _tbMinus.Foreground = BronzeBrush; };
            _tbMinus.MouseLeftButtonUp += (s, e) =>
            {
                if (!IsMainEnabled() || !_qtyButtonsEnabled) { _tbMinus.Foreground = Brushes.Gray; return; }
                if (_qty > 1) _qty--;
                _txtQty.Text = _qty.ToString();
                _tbMinus.Foreground = Brushes.Gray;
                UpdateBulletsAfterStateChange();
                _parent.SyncQtyToChartTrader(_qty);
                _parent.SafePrint($"Qty set to {_qty}");
                _parent.SavePrefs();
            };
            _tbMinus.MouseLeave += (s, e) => _tbMinus.Foreground = Brushes.Gray;

            _txtQty = new TextBlock { Text = _qty.ToString(), Width = 36, TextAlignment = TextAlignment.Center, Background = Brushes.Black, Foreground = Brushes.White, VerticalAlignment = VerticalAlignment.Center, Margin = new Thickness(6, 0, 6, 0), FontSize = CompactFontSize };

            _tbPlus = new TextBlock { Text = "+", Width = 28, Height = CompactTextBoxHeight, TextAlignment = TextAlignment.Center, Cursor = Cursors.Hand, Foreground = Brushes.Gray, VerticalAlignment = VerticalAlignment.Center };
            _tbPlus.MouseLeftButtonDown += (s, e) => { if (!IsMainEnabled() || !_qtyButtonsEnabled) return; _tbPlus.Foreground = BronzeBrush; };
            _tbPlus.MouseLeftButtonUp += (s, e) =>
            {
                if (!IsMainEnabled() || !_qtyButtonsEnabled) { _tbPlus.Foreground = Brushes.Gray; return; }
                _qty++;
                _txtQty.Text = _qty.ToString();
                _tbPlus.Foreground = Brushes.Gray;
                UpdateBulletsAfterStateChange();
                _parent.SyncQtyToChartTrader(_qty);
                _parent.SafePrint($"Qty set to {_qty}");
                _parent.SavePrefs();
            };
            _tbPlus.MouseLeave += (s, e) => _tbPlus.Foreground = Brushes.Gray;

            qtyInline.Children.Add(_tbMinus); qtyInline.Children.Add(_txtQty); qtyInline.Children.Add(_tbPlus);
            main.Children.Add(qtyInline);

            var stopLabelRow = CreateLabelWithBulletLeft("Stop ($)", out _bulletStopFinancial);
            main.Children.Add(stopLabelRow);

            _txtStop = new TextBlock
            {
                Text = "-",
                FontSize = CompactFontSize,
                Foreground = Brushes.White,
                Background = Brushes.Transparent,
                Margin = new Thickness(0, RowSpacing, 0, 0),
                Padding = new Thickness(4, 1, 4, 1),
                HorizontalAlignment = HorizontalAlignment.Center,
                ToolTip = "Stop ($): obrigatório para ATR e BE."
            };

            var financialStopRow = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Center, Margin = new Thickness(0, RowSpacing, 0, RowSpacing * 2.5) };
            financialStopRow.Children.Add(_txtStop);

            _tbStopEdit = new TextBlock { Text = "Edit", Width = 34, FontSize = CompactFontSize, TextAlignment = TextAlignment.Center, Cursor = Cursors.Hand, Foreground = Brushes.Gray, Background = Brushes.Transparent, VerticalAlignment = VerticalAlignment.Center, Margin = new Thickness(6, 0, 0, 0), ToolTip = "Editar Stop ($)." };
            _tbStopEdit.MouseLeftButtonDown += (s, e) => { if (!IsMainEnabled()) return; _tbStopEdit.Foreground = BronzeBrush; };
            _tbStopEdit.MouseLeftButtonUp += (s, e) =>
            {
                if (!IsMainEnabled()) { _tbStopEdit.Foreground = Brushes.Gray; return; }
                _tbStopEdit.Foreground = Brushes.Gray;
                _parent.SafePrint("Stop/Edit clicked (financial stop)");
                OpenStopInputDialog();
                _parent.NotifyStopChanged();
            };
            _tbStopEdit.MouseEnter += (s, e) => _tbStopEdit.Foreground = BronzeBrush;
            _tbStopEdit.MouseLeave += (s, e) => _tbStopEdit.Foreground = Brushes.Gray;

            financialStopRow.Children.Add(_tbStopEdit);
            main.Children.Add(financialStopRow);

            var atrRow = CreateLabelWithBulletLeft("ATR", out _bulletAtr);
            main.Children.Add(atrRow);

            _tbAtrToggle = new TextBlock { Text = "Off", FontSize = CompactFontSize, Foreground = Brushes.Gray, Cursor = Cursors.Hand, Width = 36, TextAlignment = TextAlignment.Center, Margin = new Thickness(0, RowSpacing, 0, RowSpacing * 2), HorizontalAlignment = HorizontalAlignment.Center, ToolTip = "ATR: calcula qty pelo Stop($) e ATR. Requer Stop($) válido." };
            _tbAtrToggle.MouseLeftButtonUp += (s, e) => { if (!IsMainEnabled()) return; ToggleAtr(); };
            main.Children.Add(_tbAtrToggle);

            _atrValueText = new TextBlock { Text = "-", Foreground = LightGrayBrush, FontSize = CompactFontSize, Margin = new Thickness(0, RowSpacing, 0, RowSpacing * 2.5), HorizontalAlignment = HorizontalAlignment.Center, ToolTip = "Ticks e $/contrato calculados pelo ATR." };
            main.Children.Add(_atrValueText);

            var pnlRiskRow = new Grid { Margin = new Thickness(0, RowSpacing, 0, RowSpacing * 2) };
            pnlRiskRow.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
            pnlRiskRow.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });

            var pnlBlock = new StackPanel { Orientation = Orientation.Vertical, HorizontalAlignment = HorizontalAlignment.Left };
            var pnlLabelRow = CreateLabelWithBulletLeft("PNL dia", out _bulletPnlDia);
            pnlLabelRow.Margin = new Thickness(0, 0, 0, 2);
            pnlBlock.Children.Add(pnlLabelRow);
            _pnlDiaText = new TextBlock
            {
                Text = "-",
                Foreground = LightGrayBrush,
                FontSize = CompactFontSize,
                Margin = new Thickness(14, 0, 0, RowSpacing * 2),
                HorizontalAlignment = HorizontalAlignment.Left,
                ToolTip = "P/L realizado do dia (conta selecionada)."
            };
            pnlBlock.Children.Add(_pnlDiaText);
            pnlRiskRow.Children.Add(pnlBlock);
            Grid.SetColumn(pnlBlock, 0);

            var riskPanel = new StackPanel { Orientation = Orientation.Vertical, HorizontalAlignment = HorizontalAlignment.Right };
            var riskLabelStack = CreateLabelWithBulletLeft("Risk", out _bulletRisk);
            riskLabelStack.HorizontalAlignment = HorizontalAlignment.Right;
            riskPanel.Children.Add(riskLabelStack);

            var riskToggleStack = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Right };
            _tbRiskToggle = new TextBlock { Text = "Off", FontSize = CompactFontSize, Foreground = Brushes.Gray, Cursor = Cursors.Hand, Width = 40, TextAlignment = TextAlignment.Center, VerticalAlignment = VerticalAlignment.Center, ToolTip = "Risk: bloqueia envios ao atingir limites diários." };
            _tbRiskStatus = new TextBlock { Text = "", FontSize = CompactFontSize - 1, Foreground = Brushes.Gray, Margin = new Thickness(4, 0, 0, 0), VerticalAlignment = VerticalAlignment.Center, ToolTip = "Estado atual do Risk." };
            _tbRiskToggle.MouseLeftButtonUp += (s, e) => { if (!IsMainEnabled()) return; ToggleRisk(); };
            riskToggleStack.Children.Add(_tbRiskToggle);
            riskToggleStack.Children.Add(_tbRiskStatus);

            riskPanel.Children.Add(riskToggleStack);

            pnlRiskRow.Children.Add(riskPanel);
            Grid.SetColumn(riskPanel, 1);

            main.Children.Add(pnlRiskRow);

            var bottomRow = new Grid { Margin = new Thickness(0, RowSpacing, 0, RowSpacing * 1.5) };
            bottomRow.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
            bottomRow.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
            bottomRow.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });

            var onClickLabelStack = CreateLabelWithBulletLeft("OnClick", out _bulletOnClick);
            if (onClickLabelStack.Children.Count > 1 && onClickLabelStack.Children[1] is TextBlock ocLabel) ocLabel.Cursor = Cursors.Arrow;
            onClickLabelStack.HorizontalAlignment = HorizontalAlignment.Left;
            bottomRow.Children.Add(onClickLabelStack);
            Grid.SetColumn(onClickLabelStack, 0);

            var onClickCenter = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Center, VerticalAlignment = VerticalAlignment.Center };
            _tbOnClickToggle = new TextBlock { Text = "Off", FontSize = CompactFontSize, Foreground = Brushes.Gray, Cursor = Cursors.Hand, Width = 40, TextAlignment = TextAlignment.Center, VerticalAlignment = VerticalAlignment.Center, ToolTip = "OnClick: envia ordens pelo clique no gráfico usando hotkeys." };
            _tbOnClickToggle.MouseLeftButtonUp += (s, e) => { if (!IsMainEnabled()) return; ToggleOnClick(); };
            onClickCenter.Children.Add(_tbOnClickToggle);
            bottomRow.Children.Add(onClickCenter);
            Grid.SetColumn(onClickCenter, 1);

            var endDayRight = new StackPanel { Orientation = Orientation.Vertical, HorizontalAlignment = HorizontalAlignment.Right };
            var endDayLabelWithBullet = CreateLabelWithBulletLeft("EndDay", out _bulletEndDay);
            endDayLabelWithBullet.HorizontalAlignment = HorizontalAlignment.Right;
            endDayRight.Children.Add(endDayLabelWithBullet);

            var endRow = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Right };
            _tbEndDayValue = new TextBlock { Text = "-", Foreground = Brushes.Gray, FontSize = CompactFontSize, VerticalAlignment = VerticalAlignment.Center, Margin = new Thickness(4, 0, 6, 0) };
            _tbEndDayEdit = new TextBlock { Text = "Edit", Foreground = Brushes.Gray, FontSize = CompactFontSize, Cursor = Cursors.Hand, VerticalAlignment = VerticalAlignment.Center, ToolTip = "Editar horário/endereço EndDay." };
            _tbEndDayEdit.MouseLeftButtonDown += (s, e) => { if (!IsMainEnabled()) return; _tbEndDayEdit.Foreground = BronzeBrush; };
            _tbEndDayEdit.MouseLeftButtonUp += (s, e) =>
            {
                if (!IsMainEnabled()) { _tbEndDayEdit.Foreground = Brushes.Gray; return; }
                _tbEndDayEdit.Foreground = Brushes.Gray;
                _parent.OpenEndDayDialog();
            };
            _tbEndDayEdit.MouseEnter += (s, e) => _tbEndDayEdit.Foreground = BronzeBrush;
            _tbEndDayEdit.MouseLeave += (s, e) => _tbEndDayEdit.Foreground = Brushes.Gray;

            endRow.Children.Add(_tbEndDayValue); endRow.Children.Add(_tbEndDayEdit);
            endDayRight.Children.Add(endRow);

            bottomRow.Children.Add(endDayRight);
            Grid.SetColumn(endDayRight, 2);

            main.Children.Add(bottomRow);

            var footerGrid = new Grid { Margin = new Thickness(0, 1, 0, 0) };
            footerGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = GridLength.Auto });
            footerGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
            footerGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = GridLength.Auto });

            _tbBoletaId = new TextBlock
            {
                Text = "",
                Foreground = BronzeBrush,
                FontSize = CompactFontSize - 1,
                HorizontalAlignment = HorizontalAlignment.Left,
                Margin = new Thickness(0, 0, 8, 0)
            };
            footerGrid.Children.Add(_tbBoletaId);
            Grid.SetColumn(_tbBoletaId, 0);

            var footerNote = new TextBlock
            {
                Text = "-Produto oficial Dashflix-",
                Foreground = BronzeBrush,
                FontSize = CompactFontSize,
                HorizontalAlignment = HorizontalAlignment.Center
            };
            footerGrid.Children.Add(footerNote);
            Grid.SetColumn(footerNote, 1);

            main.Children.Add(footerGrid);

            scroller.Content = main;
            Children.Add(scroller);

            SetEndDayLabel(_parent.EndDayTime, _parent.EndDayScope);
            UpdateBulletsAfterStateChange();
        }

        private void ToggleMain()
        {
            if (_parent.IsRiskBlocked())
            {
                _parent.ShowTransientPopup("Bloqueado por RISK até 00:00.");
                return;
            }

            _mainEnabled = !_mainEnabled;
            _tbMainToggle.Text = _mainEnabled ? "On" : "Off";
            _tbMainToggle.Foreground = _mainEnabled ? BronzeBrush : Brushes.Gray;
            _mainStateBullet.Fill = _mainEnabled ? MainOnBrush : InactiveBulletBrush;
            _parent.SafePrint($"Main toggled {(_mainEnabled ? "On" : "Off")}");
            _parent.NotifyMainToggle(_mainEnabled);

            if (!_mainEnabled)
            {
                ResetAllToDefaults();
                _parent.SetTradingFromChartEnabled(false);
            }

            UpdateBulletsAfterStateChange();
        }

        public void ForceMainToggleBlocked()
        {
            try
            {
                _mainEnabled = false;
                _tbMainToggle.Text = "Off";
                _tbMainToggle.Foreground = BlockBrush;
                _mainStateBullet.Fill = BlockBrush;
                _parent.SetTradingFromChartEnabled(false);
                _parent.NotifyMainToggle(false);
            }
            catch { }
        }

        private void ResetAllToDefaults()
        {
            try
            {
                _beEnabled = false;
                _bulletBe.Fill = InactiveBulletBrush;
                _beStateText.Text = "Off"; _beStateText.Foreground = Brushes.Gray;

                _qty = 1;
                _txtQty.Text = "1";
                _parent.SyncQtyToChartTrader(_qty);

                _txtStop.Text = "-"; _txtStop.Foreground = Brushes.White;

                _tbAtrToggle.Text = "Off"; _tbAtrToggle.Foreground = Brushes.Gray;
                _atrValueText.Text = "-";

                _onClickEnabled = false;
                _tbOnClickToggle.Text = "Off"; _tbOnClickToggle.Foreground = Brushes.Gray;
                _bulletOnClick.Fill = InactiveBulletBrush;

                _tbRiskToggle.Text = "Off";
                _tbRiskToggle.Foreground = Brushes.Gray;
                _tbRiskStatus.Text = "";
                _bulletRisk.Fill = InactiveBulletBrush;

                _tbHotkeyPressed.Text = "";

                SetQtyButtonsEnabled(true);
            }
            catch { }
        }

        private void ToggleBE()
        {
            _beEnabled = !_beEnabled;
            _bulletBe.Fill = _beEnabled ? BronzeBrush : InactiveBulletBrush;
            _beStateText.Text = _beEnabled ? "On" : "Off"; _beStateText.Foreground = _beEnabled ? BronzeBrush : Brushes.Gray;
            _parent.SafePrint($"BE toggled {(_beEnabled ? "On" : "Off")}");
            _parent.NotifyBeToggle(_beEnabled);
            UpdateBulletsAfterStateChange();
        }

        private void ToggleOnClick()
        {
            if (_parent.IsRiskBlocked())
            {
                _parent.ShowTransientPopup("Bloqueado por RISK até 00:00.");
                return;
            }

            _onClickEnabled = !_onClickEnabled;
            _tbOnClickToggle.Text = _onClickEnabled ? "On" : "Off";
            _tbOnClickToggle.Foreground = _onClickEnabled ? BronzeBrush : Brushes.Gray;
            _bulletOnClick.Fill = _onClickEnabled ? BronzeBrush : InactiveBulletBrush;
            _parent.SetTradingFromChartEnabled(_onClickEnabled);
            _parent.SafePrint($"OnClick toggled {(_onClickEnabled ? "On" : "Off")}");
            UpdateBulletsAfterStateChange();
        }

        private void ToggleAtr()
        {
            if (_parent.IsRiskBlocked())
            {
                _parent.ShowTransientPopup("Bloqueado por RISK até 00:00.");
                return;
            }

            bool turningOn = _tbAtrToggle.Text != "On";
            if (turningOn)
            {
                bool ok = _parent.ApplyAtrSizingWithValidationProxy(_parent.LastAtrTicks(), _parent.LastAtrDollarPerContract(), true);
                if (!ok) return;
                _tbAtrToggle.Text = "On";
                _tbAtrToggle.Foreground = BronzeBrush;
                SetQtyButtonsEnabled(false);
            }
            else
            {
                _tbAtrToggle.Text = "Off";
                _tbAtrToggle.Foreground = Brushes.Gray;
                SetQtyButtonsEnabled(true);
                _parent.SafePrint("ATR toggled Off");
            }

            UpdateBulletsAfterStateChange();
        }

        public void ForceAtrOffAndEnableQty()
        {
            try
            {
                _tbAtrToggle.Text = "Off";
                _tbAtrToggle.Foreground = Brushes.Gray;
                SetQtyButtonsEnabled(true);
                UpdateBulletsAfterStateChange();
                _parent.SafePrint("ATR forced Off (validation).");
            }
            catch { }
        }

        private void ToggleRisk()
        {
            if (_parent.IsRiskBlocked())
            {
                _parent.ShowTransientPopup("Bloqueado por RISK até 00:00.");
                return;
            }
            bool turningOn = _tbRiskToggle.Text != "On";
            _tbRiskToggle.Text = turningOn ? "On" : "Off";
            _parent.NotifyRiskToggle(turningOn);
        }

        public void UpdateBulletsAfterStateChange()
        {
            try
            {
                _bulletBe.Fill = _beEnabled ? BronzeBrush : InactiveBulletBrush;
                _bulletQty.Fill = (_txtQty != null && int.TryParse(_txtQty.Text, out int q) && q > 0) ? BronzeBrush : InactiveBulletBrush;
                _bulletStopFinancial.Fill = (_txtStop != null && _txtStop.Text != "-" ? BronzeBrush : InactiveBulletBrush);
                _bulletAtr.Fill = (_tbAtrToggle != null && _tbAtrToggle.Text == "On" ? BronzeBrush : InactiveBulletBrush);

                _bulletPnlDia.Fill = (_pnlDiaText != null && _pnlDiaText.Text != "-") ? BronzeBrush : InactiveBulletBrush;

                _bulletEndDay.Fill = (_parent.EndDayTime.HasValue ? BronzeBrush : InactiveBulletBrush);
                _bulletOnClick.Fill = (_onClickEnabled ? BronzeBrush : InactiveBulletBrush);

                _tbAtrToggle.Foreground = (_tbAtrToggle.Text == "On") ? BronzeBrush : Brushes.Gray;
                _tbOnClickToggle.Foreground = (_onClickEnabled ? BronzeBrush : Brushes.Gray);
            }
            catch { }
        }

        public void SetEntryFromPosition(string ticker, double avgPrice)
        {
            try
            {
                _txtEntry.Text = avgPrice.ToString("N2", CultureInfo.CurrentCulture);
                _txtEntry.Foreground = BronzeBrush;
            }
            catch { }
        }

        public void ClearEntry()
        {
            try
            {
                _txtEntry.Text = "-";
                _txtEntry.Foreground = Brushes.White;
            }
            catch { }
        }

        public void SetChartStop(double price)
        {
            try
            {
                _txtChartStop.Text = price.ToString("N2", CultureInfo.CurrentCulture);
                _txtChartStop.Foreground = BronzeBrush;
            }
            catch { }
        }

        public void ClearChartStop()
        {
            try
            {
                _txtChartStop.Text = "-";
                _txtChartStop.Foreground = Brushes.White;
            }
            catch { }
        }

        public void SetExitFromOrder(double price)
        {
            try
            {
                _txtExit.Text = price.ToString("N2", CultureInfo.CurrentCulture);
                _txtExit.Foreground = BronzeBrush;
            }
            catch { }
        }

        public void ClearExit()
        {
            try
            {
                _txtExit.Text = "-";
                _txtExit.Foreground = Brushes.White;
            }
            catch { }
        }

        public void SetAtrValue(int ticks, double dollarsPerContract)
        {
            try
            {
                if (ticks > 0)
                {
                    var enUs = CultureInfo.GetCultureInfo("en-US");
                    string money = dollarsPerContract > 0
                        ? dollarsPerContract.ToString("C2", enUs)
                        : "-";
                    _atrValueText.Text = $"{ticks} ticks / {money} (1C)";
                }
                else
                {
                    _atrValueText.Text = "-";
                }
            }
            catch { }
        }

        public int GetQty() => _qty;

        public void SetLastOrderInfo(string info)
        {
            try
            {
                _pnlDiaText.Text = info ?? "-";
            }
            catch { }
        }

        public void SetQty(int q)
        {
            try
            {
                _qty = Math.Max(0, q);
                _txtQty.Text = _qty.ToString();
                UpdateBulletsAfterStateChange();
                _parent.SyncQtyToChartTrader(_qty);
            }
            catch { }
        }

        public double GetStopFinancial()
        {
            try
            {
                if (_txtStop == null) return 0.0;
                string s = _txtStop.Text?.Trim() ?? "";
                if (string.IsNullOrEmpty(s) || s == "-") return 0.0;
                if (double.TryParse(s, NumberStyles.Any, CultureInfo.CurrentCulture, out double v))
                    return Math.Max(0.0, v);
                if (double.TryParse(s, NumberStyles.Any, CultureInfo.InvariantCulture, out v))
                    return Math.Max(0.0, v);
                return 0.0;
            }
            catch { return 0.0; }
        }

        public void SetStopFinancial(double value)
        {
            try
            {
                if (value > 0)
                {
                    _txtStop.Text = value.ToString("N2", CultureInfo.CurrentCulture);
                    _txtStop.Foreground = BronzeBrush;
                }
            }
            catch { }
        }

        public void SetPnl(double? pnl)
        {
            try
            {
                if (pnl.HasValue)
                {
                    _pnlDiaText.Text = pnl.Value.ToString("N2", CultureInfo.CurrentCulture);
                    _pnlDiaText.Foreground = pnl.Value >= 0 ? PnlPositiveBrush : PnlNegativeBrush;
                }
                else
                {
                    _pnlDiaText.Text = "-";
                    _pnlDiaText.Foreground = LightGrayBrush;
                }
                UpdateBulletsAfterStateChange();
            }
            catch { }
        }

        public void ForceBeOff()
        {
            try
            {
                Action doUi = () =>
                {
                    _beEnabled = false;
                    _bulletBe.Fill = InactiveBulletBrush;
                    _beStateText.Text = "Off";
                    _beStateText.Foreground = Brushes.Gray;
                    UpdateBulletsAfterStateChange();
                    _parent.SafePrint("BE forced Off");
                };

                if (Dispatcher.CheckAccess())
                    doUi();
                else
                    Dispatcher.BeginInvoke(doUi);
            }
            catch { }
        }

        public void ForceBeOn()
        {
            try
            {
                Action doUi = () =>
                {
                    _beEnabled = true;
                    _bulletBe.Fill = BronzeBrush;
                    _beStateText.Text = "On";
                    _beStateText.Foreground = BronzeBrush;
                    UpdateBulletsAfterStateChange();
                    _parent.SafePrint("BE forced On");
                };

                if (Dispatcher.CheckAccess())
                    doUi();
                else
                    Dispatcher.BeginInvoke(doUi);
            }
            catch { }
        }

        public void SetQtyButtonsEnabled(bool enabled)
        {
            _qtyButtonsEnabled = enabled;
            if (_tbMinus != null) _tbMinus.IsEnabled = enabled;
            if (_tbPlus != null) _tbPlus.IsEnabled = enabled;
            _tbMinus.Opacity = enabled ? 1.0 : 0.4;
            _tbPlus.Opacity = enabled ? 1.0 : 0.4;
        }

        private void OpenStopInputDialog()
        {
            try
            {
                _parent.SafePrint("OpenStopInputDialog: start");

                var ownerWin = Window.GetWindow(this);

                var dlg = new Window()
                {
                    Owner = ownerWin,
                    WindowStartupLocation = WindowStartupLocation.CenterOwner,
                    SizeToContent = SizeToContent.WidthAndHeight,
                    ResizeMode = ResizeMode.NoResize,
                    WindowStyle = WindowStyle.ToolWindow,
                    Title = "Enter Stop ($)",
                    ShowInTaskbar = false,
                    Background = new LinearGradientBrush(Color.FromRgb(30, 30, 30), Color.FromRgb(50, 50, 50), 90),
                    Foreground = Brushes.LightGray
                };

                var panel = new StackPanel { Margin = new Thickness(8) };
                panel.Children.Add(new TextBlock { Text = "Stop ($):", Margin = new Thickness(0, 0, 0, 4), Foreground = Brushes.LightGray });

                var input = new TextBox
                {
                    Width = 240,
                    Height = 28,
                    FontSize = 14,
                    Text = (_txtStop.Text == "-" ? "" : _txtStop.Text),
                    HorizontalAlignment = HorizontalAlignment.Stretch,
                    Background = new SolidColorBrush(Color.FromRgb(22, 22, 22)),
                    Foreground = Brushes.White,
                    CaretBrush = Brushes.White
                };

                input.PreviewTextInput += (s, e) =>
                {
                    var decimalSep = CultureInfo.CurrentCulture.NumberFormat.NumberDecimalSeparator;
                    var groupSep = CultureInfo.CurrentCulture.NumberFormat.NumberGroupSeparator;
                    string text = e.Text;
                    if (text.All(c => Char.IsDigit(c)) || text == decimalSep || text == groupSep) e.Handled = false;
                    else e.Handled = true;
                };
                DataObject.AddPastingHandler(input, (s, e) =>
                {
                    if (e.DataObject.GetDataPresent(DataFormats.Text))
                    {
                        string pasted = e.DataObject.GetData(DataFormats.Text) as string;
                        if (!double.TryParse(pasted, NumberStyles.Number, CultureInfo.CurrentCulture, out _)) e.CancelCommand();
                    }
                    else e.CancelCommand();
                });

                var buttons = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Right, Margin = new Thickness(0, 8, 0, 0) };
                var ok = new Button { Content = "OK", Width = 80, Margin = new Thickness(0, 0, 6, 0), Background = new SolidColorBrush(Color.FromRgb(40, 40, 40)), Foreground = Brushes.White };
                var cancel = new Button { Content = "Cancel", Width = 80, Background = new SolidColorBrush(Color.FromRgb(60, 60, 60)), Foreground = Brushes.White };

                ok.Click += (s, e) =>
                {
                    try
                    {
                        string txt = input.Text?.Trim();
                        if (string.IsNullOrEmpty(txt))
                        {
                            _txtStop.Text = "-";
                            _txtStop.Foreground = Brushes.White;
                        }
                        else if (double.TryParse(txt, NumberStyles.Number, CultureInfo.CurrentCulture, out double v))
                        {
                            _txtStop.Text = v.ToString("N2", CultureInfo.CurrentCulture);
                            _txtStop.Foreground = BronzeBrush;
                        }
                        else if (double.TryParse(txt, NumberStyles.Number, CultureInfo.InvariantCulture, out v))
                        {
                            _txtStop.Text = v.ToString("N2", CultureInfo.CurrentCulture);
                            _txtStop.Foreground = BronzeBrush;
                        }
                        else
                        {
                            _txtStop.Text = "-";
                            _txtStop.Foreground = Brushes.White;
                        }
                    }
                    catch (Exception ex) { _parent.SafePrint("Stop OK parse error: " + ex.Message); }

                    try { dlg.Dispatcher.BeginInvoke(new Action(() => { dlg.DialogResult = true; dlg.Close(); })); } catch { try { dlg.Close(); } catch { } }

                    UpdateBulletsAfterStateChange();
                    _parent.SavePrefs();
                };

                cancel.Click += (s, e) => { try { dlg.DialogResult = false; dlg.Close(); } catch { } };

                buttons.Children.Add(ok); buttons.Children.Add(cancel);

                panel.Children.Add(input);
                panel.Children.Add(buttons);
                dlg.Content = panel;

                input.Loaded += (s, e) => { input.Focus(); input.SelectAll(); };

                dlg.ShowDialog();
                _parent.SafePrint("OpenStopInputDialog: dialog closed");
            }
            catch (Exception ex)
            {
                _parent.SafePrint("OpenStopInputDialog error: " + ex.Message);
            }
        }

        private void SmartBoletaEmbeddedControl_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            try
            {
                double w = e.NewSize.Width;
                _titleCenter.FontSize = (w < 320) ? CompactFontSize + 3 : CompactFontSize + 4;
            }
            catch { }
        }

        public void SetEndDayLabel(TimeSpan? t, SBEndDayScope scope)
        {
            try
            {
                if (t.HasValue)
                {
                    _tbEndDayValue.Text = $"{t.Value:hh\\:mm} ({(scope == SBEndDayScope.AllNinjaTrader ? "All" : "This")})";
                    _tbEndDayValue.Foreground = BronzeBrush;
                }
                else
                {
                    _tbEndDayValue.Text = "-";
                    _tbEndDayValue.Foreground = Brushes.Gray;
                }

                _tbEndDayValue.ToolTip = t.HasValue
                    ? $"EndDay: {t.Value:hh\\:mm} — escopo {(scope == SBEndDayScope.AllNinjaTrader ? "toda a plataforma" : "este gráfico")}."
                    : "Defina um horário para bloquear envios no fim do dia.";

                UpdateBulletsAfterStateChange();
            }
            catch { }
        }

        public void SetRiskState(RiskState state, bool enabled, string status)
        {
            try
            {
                Brush bullet = InactiveBulletBrush;
                Brush textColor = Brushes.Gray;
                string toggleText = enabled ? "On" : "Off";
                switch (state)
                {
                    case RiskState.Ok:
                        bullet = MainOnBrush; textColor = MainOnBrush; break;
                    case RiskState.Pre:
                        bullet = PreLimitBrush; textColor = PreLimitBrush; break;
                    case RiskState.Blocked:
                        bullet = BlockBrush; textColor = BlockBrush; toggleText = "Off"; break;
                    case RiskState.Off:
                    default:
                        bullet = InactiveBulletBrush; textColor = Brushes.Gray; break;
                }
                _bulletRisk.Fill = bullet;
                _tbRiskToggle.Text = toggleText;
                _tbRiskToggle.Foreground = textColor;
                _tbRiskStatus.Text = state switch
                {
                    RiskState.Ok => "OK",
                    RiskState.Pre => "PRE",
                    RiskState.Blocked => "BLOQ",
                    RiskState.Off => "OFF",
                    _ => status ?? ""
                };
                _tbRiskStatus.ToolTip = "Estado atual do Risk.";
            }
            catch { }
        }

        public void UpdateForChart(ChartControl chartControl)
        {
            try
            {
                string inst = chartControl?.Instrument?.FullName ?? "unknown";
            }
            catch (Exception ex) { _parent.SafePrint("Embedded UpdateForChart ex: " + ex.Message); }
        }

        public void SetHotkeyMapping(string buyKey, string sellKey)
        {
            try
            {
                _tbHotkeyInfo.Text = $"Keys: Buy={buyKey} | Sell={sellKey}";
            }
            catch { }
        }

        public void SetHotkeyPressed(bool buyPressed, bool sellPressed)
        {
            try
            {
                if (buyPressed && sellPressed)
                    _tbHotkeyPressed.Text = "BUY & SELL pressed";
                else if (buyPressed)
                    _tbHotkeyPressed.Text = "BUY pressed";
                else if (sellPressed)
                    _tbHotkeyPressed.Text = "SELL pressed";
                else
                    _tbHotkeyPressed.Text = "";

                _tbHotkeyPressed.Foreground = BronzeBrush;
            }
            catch { }
        }

        public void SetAtrState(bool on)
        {
            try
            {
                _tbAtrToggle.Text = on ? "On" : "Off";
                _tbAtrToggle.Foreground = on ? BronzeBrush : Brushes.Gray;
                SetQtyButtonsEnabled(!on);
            }
            catch { }
        }

        public void SetBeState(bool on)
        {
            try
            {
                _beEnabled = on;
                _bulletBe.Fill = on ? BronzeBrush : InactiveBulletBrush;
                _beStateText.Text = on ? "On" : "Off";
                _beStateText.Foreground = on ? BronzeBrush : Brushes.Gray;
            }
            catch { }
        }

        public void SetOnClickState(bool on)
        {
            try
            {
                _onClickEnabled = on;
                _tbOnClickToggle.Text = on ? "On" : "Off";
                _tbOnClickToggle.Foreground = on ? BronzeBrush : Brushes.Gray;
                _bulletOnClick.Fill = on ? BronzeBrush : InactiveBulletBrush;
            }
            catch { }
        }

        public void SetRiskToggleVisual(bool on)
        {
            try
            {
                _tbRiskToggle.Text = on ? "On" : "Off";
                _tbRiskToggle.Foreground = on ? BronzeBrush : Brushes.Gray;
            }
            catch { }
        }
    }

    public enum DesiredKey
    {
        LeftAlt,
        LeftShift,
        RightAlt,
        RightShift
    }

    public enum StopOrderTypes
    {
        StopLimit,
        StopMarket
    }

    public enum SBEndDayScope
    {
        ThisChartOnly,
        AllNinjaTrader
    }

    public enum SRiskScope
    {
        EsteGrafico,
        TodaPlataforma
    }

    public enum RiskState
    {
        Off,
        Ok,
        Pre,
        Blocked
    }

    /// <summary>
    /// Adapter para obter valores de conta via reflexão, com cache de método/prop por tipo.
    /// </summary>
    internal static class AccountValueProvider
    {
        private static readonly ConcurrentDictionary<string, Func<Account, AccountItem, double?>> _getterByType = new();
        private static readonly ConcurrentDictionary<string, Func<Account, double?>> _realizedGetterByType = new();

        public static double? TryGetAccountValueUsd(Account acc, AccountItem item, Action<string> log)
        {
            if (acc == null) return null;
            var key = acc.GetType().FullName + "|item";
            var getter = _getterByType.GetOrAdd(key, _ => BuildGetter(acc, log));
            try { return getter(acc, item); } catch { return null; }
        }

        public static double? TryGetRealizedPnlUsd(Account acc, Action<string> log)
        {
            if (acc == null) return null;
            var key = acc.GetType().FullName + "|realized";
            var getter = _realizedGetterByType.GetOrAdd(key, _ => BuildRealizedGetter(acc, log));
            try { return getter(acc); } catch { return null; }
        }

        private static Func<Account, AccountItem, double?> BuildGetter(Account acc, Action<string> log)
        {
            var t = acc.GetType();
            var m1 = t.GetMethod("GetAccountValue", new Type[] { typeof(AccountItem), typeof(Currency) });
            if (m1 != null) return (a, item) => ExtractNumber(m1.Invoke(a, new object[] { item, Currency.UsDollar }));
            var m2 = t.GetMethod("Get", new Type[] { typeof(AccountItem), typeof(Currency) });
            if (m2 != null) return (a, item) => ExtractNumber(m2.Invoke(a, new object[] { item, Currency.UsDollar }));
            var m3 = t.GetMethod("Get", new Type[] { typeof(AccountItem) });
            if (m3 != null) return (a, item) => ExtractNumber(m3.Invoke(a, new object[] { item }));
            log?.Invoke("AccountValueProvider: nenhum getter encontrado para " + t.FullName);
            return (a, item) => null;
        }

        private static Func<Account, double?> BuildRealizedGetter(Account acc, Action<string> log)
        {
            var t = acc.GetType();
            var p1 = t.GetProperty("RealizedProfitLoss");
            if (p1 != null) return a => ExtractNumber(p1.GetValue(a));
            var p2 = t.GetProperty("GrossRealizedProfitLoss");
            if (p2 != null) return a => ExtractNumber(p2.GetValue(a));
            var g = BuildGetter(acc, log);
            return a => g(a, AccountItem.RealizedProfitLoss);
        }

        private static double? ExtractNumber(object o)
        {
            if (o == null) return null;
            if (o is double d) return d;
            if (o is float f) return (double)f;
            if (o is decimal dec) return (double)dec;

            var prop = o.GetType().GetProperty("Value");
            if (prop != null)
            {
                try
                {
                    var val = prop.GetValue(o);
                    return ExtractNumber(val);
                }
                catch { }
            }
            return null;
        }
    }

    /// <summary>
    /// Adapter para mudar preço de stop via reflexão, com cache por tipo de conta.
    /// </summary>
    internal static class OrderChanger
    {
        private class Signature
        {
            public Type[] Sig;
            public Func<Account, Order, double, bool> Invoker;
            public Signature(Type[] sig, Func<Account, Order, double, bool> invoker)
            {
                Sig = sig; Invoker = invoker;
            }
        }

        private static readonly ConcurrentDictionary<string, Signature> _cachedSig = new();

        public static bool TryChangeStopPrice(Account acc, Order o, double bePrice, Action<string> log)
        {
            if (acc == null || o == null) return false;
            var key = acc.GetType().FullName ?? "unknown";
            var sig = _cachedSig.GetOrAdd(key, _ => BuildInvoker(acc, log));
            return sig.Invoker(acc, o, bePrice);
        }

        private static Signature BuildInvoker(Account acc, Action<string> log)
        {
            var t = acc.GetType();
            var attempts = new List<Type[]>
            {
                new[] { typeof(Order), typeof(int), typeof(double), typeof(double), typeof(string), typeof(string) },
                new[] { typeof(Order), typeof(int), typeof(double), typeof(double), typeof(string) },
                new[] { typeof(Order), typeof(int), typeof(double), typeof(double) }
            };

            foreach (var sig in attempts)
            {
                var mi = t.GetMethod("Change", sig);
                if (mi == null) continue;

                Func<Account, Order, double, bool> inv = (a, o, price) =>
                {
                    try
                    {
                        var args = BuildArgs(sig, o, price);
                        mi.Invoke(a, args);
                        return true;
                    }
                    catch (Exception ex)
                    {
                        log?.Invoke("OrderChanger invoke ex: " + ex.Message);
                        return false;
                    }
                };
                return new Signature(sig, inv);
            }

            log?.Invoke("OrderChanger: nenhum overload Change encontrado para " + t.FullName);
            return new Signature(Type.EmptyTypes, (a, o, p) => false);
        }

        private static object[] BuildArgs(Type[] sig, Order o, double price)
        {
            if (sig.Length == 6) return new object[] { o, o.Quantity, double.NaN, price, o.Oco, "BE_Stop" };
            if (sig.Length == 5) return new object[] { o, o.Quantity, double.NaN, price, o.Oco };
            if (sig.Length == 4) return new object[] { o, o.Quantity, double.NaN, price };
            return Array.Empty<object>();
        }
    }
}
