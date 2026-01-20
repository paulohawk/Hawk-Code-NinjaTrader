using System;
using NinjaTrader.Cbi;

namespace NinjaTrader.NinjaScript
{
    public static class HawkOrderDecoratorState
    {
        public static bool Enabled;

        public static MarketPosition Side;
        public static int Quantity;

        public static double EntryPrice;
        public static double StopPrice;
        public static double TargetPrice;

        public static DateTime LastUpdateUtc;

        public static void Clear()
        {
            Enabled = false;
            Side = MarketPosition.Flat;
            Quantity = 0;
            EntryPrice = 0;
            StopPrice = 0;
            TargetPrice = 0;
            LastUpdateUtc = Core.Globals.MinDate;
        }
    }
}
