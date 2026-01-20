using System;
using NinjaTrader.Cbi;

namespace NinjaTrader.NinjaScript
{
    public static class OrderLineDecoratorHub
    {
        public static bool Enabled;

        public static double EntryPrice;
        public static double StopPrice;
        public static double TargetPrice;

        public static int Quantity;
        public static MarketPosition Side;

        public static DateTime LastUpdateUtc;

        public static void Clear()
        {
            Enabled = false;
            EntryPrice = 0;
            StopPrice = 0;
            TargetPrice = 0;
            Quantity = 0;
            Side = MarketPosition.Flat;
            LastUpdateUtc = Core.Globals.MinDate;
        }
    }
}
