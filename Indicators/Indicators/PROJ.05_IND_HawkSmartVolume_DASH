#region Using declarations
using System;
                            using System.Collections;
                            using System.Collections.Generic;
                            using System.ComponentModel;
                            using System.ComponentModel.DataAnnotations;
                            using System.Diagnostics.CodeAnalysis;
                            using System.Windows;
                            using System.Reflection;
                            using System.Windows.Media;
                            using System.Xml.Serialization;
                            using NinjaTrader.Cbi;
                            using NinjaTrader.Data;
                            using NinjaTrader.Gui;
                            using NinjaTrader.Gui.Chart;
                            using NinjaTrader.Gui.Tools;
                            using NinjaTrader.NinjaScript.DrawingTools;
                            using NinjaTrader.NinjaScript.Indicators;
#endregion

// This namespace holds all indicators and is required. Do not change it.
namespace NinjaTrader.NinjaScript.Indicators
{
    /// <summary>
    /// Enter the description of your new custom indicator here
    /// </summary>
    public class BigTrades3Vol : Indicator
    {
        #region Variables 
		private int vol1 = 900;
		private int vol2 = 1500;
		private int vol3 = 2500;
		private int fix = 1; 
		Brush colorV1 = Brushes.RoyalBlue;
		Brush colorV2 = Brushes.DarkMagenta;
		Brush colorV3 = Brushes.Gold;
		Brush colorText = Brushes.DarkGray;
		Brush shadowcolor = Brushes.Red;
		int opacity = 1;
		private bool useAlerts = true;
		private bool useEllipse = true;
		private bool ShowTime = false;
		private string stringtoAlert = "Alert4.wav";
        #endregion

        /// <summary>
        /// This method is used to configure the indicator and is called once before any bar data is loaded.
        /// </summary>
		/// 
        private void Initialize()
        {                
            Calculate	= Calculate.OnBarClose;
			IsOverlay				= true;	
        }

        protected override void OnStateChange()
        {
            switch (State)
            {
                case State.SetDefaults:
                    Name = "BigTrades3Vol";
                    Description = "Marca con una elipse vols relevantes";
                    Initialize();
                    break;
             }
		if (State == State.Configure)
    	{
			AddDataSeries(BarsPeriodType.Second,1);
		}
        }
        /// <summary>
        /// Called on each bar update event (incoming tick)
        /// </summary>
       protected override void OnBarUpdate()
        {
					
	        if (CurrentBar < 2) return;
			if (BarsInProgress == 1)
			{			
				TimeSpan ts1 = Time[0] - new DateTime(1970,1,1,0,0,0);
			    TimeSpan ts2 = Time[1] - new DateTime(1970,1,1,0,0,0);

			   // int timeGap=(int)Time[0].Second-(int)Time[1].Second;
				int timeGap=(int)ts1.TotalSeconds-(int)ts2.TotalSeconds;

				if (Math.Abs(timeGap)<=fix)
				{
					if (Volume[0]>=vol3)
					{	
						if(useEllipse)	
					    	Draw.Ellipse(this,"ellipse"+CurrentBar, true, 3, High[0], -3, Low[0], colorV3, shadowcolor, opacity);
					    
						if(ShowTime)	
						{
							Draw.Text(this,"TFx"+CurrentBar, true, Convert.ToString(Time[0]),5, Median[0], 0,colorText, 
							new SimpleFont("Small Fonts", 9)/*new Font("Small Fonts", 7, FontStyle.Regular)*/, TextAlignment.Right,	Brushes.Transparent,Brushes.Transparent, 0);
						}
						else
						{
							Draw.Text(this,"TFx"+CurrentBar, true, Convert.ToString(Volume[0]), 5, Median[0], 0,colorText, 
							new SimpleFont("Small Fonts", 9)/*new Font("Small Fonts", 7, FontStyle.Regular)*/, TextAlignment.Right,Brushes.Transparent, Brushes.Transparent, 0);
						}
					}
					else
					if (Volume[0]>=vol2)
					{	
						if(useEllipse)	
					    	Draw.Ellipse(this,"ellipse"+CurrentBar, true, 3, High[0], -3, Low[0], colorV2, shadowcolor, opacity);
					    
						if(ShowTime)	
						{
							Draw.Text(this,"TFx"+CurrentBar, true, Convert.ToString(Time[0]),5, Median[0], 0,colorText, 
							new SimpleFont("Small Fonts", 9)/*new Font("Small Fonts", 7, FontStyle.Regular)*/, TextAlignment.Right,	Brushes.Transparent,Brushes.Transparent, 0);
						}
						else
						{
							Draw.Text(this,"TFx"+CurrentBar, true, Convert.ToString(Volume[0]), 5, Median[0], 0,colorText, 
							new SimpleFont("Small Fonts", 9)/*new Font("Small Fonts", 7, FontStyle.Regular)*/, TextAlignment.Right,Brushes.Transparent, Brushes.Transparent, 0);
						}
					}
					else 
					if (Volume[0]>=vol1)
					{	
						if(useEllipse)	
					    	Draw.Ellipse(this,"ellipse"+CurrentBar, true, 3, High[0], -3, Low[0], colorV1, shadowcolor, opacity);
					    
						if(ShowTime)	
						{
							Draw.Text(this,"TFx"+CurrentBar, true, Convert.ToString(Time[0]),5, Median[0], 0,colorText, 
							new SimpleFont("Small Fonts", 9)/*new Font("Small Fonts", 7, FontStyle.Regular)*/, TextAlignment.Right,	Brushes.Transparent,Brushes.Transparent, 0);
						}
						else
						{
							Draw.Text(this,"TFx"+CurrentBar, true, Convert.ToString(Volume[0]), 5, Median[0], 0,colorText, 
							new SimpleFont("Small Fonts", 9)/*new Font("Small Fonts", 7, FontStyle.Regular)*/, TextAlignment.Right,Brushes.Transparent, Brushes.Transparent, 0);
						}
					}
				}
			}
		}
	
		#region Properties	
		[NinjaScriptProperty]		
		[Display(Name = "1. Volumen 1 de la transacción", Description = "Volumen 1 de transacción", GroupName = "Parameters", Order = 1)]		public int Vol1
        {
            get { return vol1; }
            set { vol1 = Math.Max(1, value); }
        }
        
		[NinjaScriptProperty]		
		[Display(Name = "2. Volumen 2 de la transacción", Description = "Volumen 2 de transacción", GroupName = "Parameters", Order = 2)]		public int Vol2
        {
            get { return vol2; }
            set { vol2 = Math.Max(1, value); }
        }
		
		[NinjaScriptProperty]		
		[Display(Name = "3. Volumen 3 de la transacción", Description = "Volumen 3 de transacción", GroupName = "Parameters", Order = 3)]		public int Vol3
        {
            get { return vol3; }
            set { vol3 = Math.Max(1, value); }
        }
		[NinjaScriptProperty]        
		[Display(Name = "4. Momento", Description = "Momento durante el cual se realizó la transacción.", GroupName = "Parameters", Order = 4)]        public int Время
        {
            get { return fix; }
            set { fix = Math.Max(1, value); }
        }
		[NinjaScriptProperty]		
		[XmlIgnore()]
		[Display(Name = "5. Color de elipse 1", Description = "Color 1", GroupName = "Parameters", Order = 5)]		
		public Brush cV1
		{
			get{return colorV1;}
			set{colorV1 = value;}
		}
		
		[NinjaScriptProperty]		
		[XmlIgnore()]
		[Display(Name = "6. Color de elipse 2", Description = "Color 2", GroupName = "Parameters", Order = 6)]		
		public Brush cV2
		{
			get{return colorV2;}
			set{colorV2 = value;}
		}
		
		[NinjaScriptProperty]		
		[XmlIgnore()]
		[Display(Name = "7. Color de elipse 3", Description = "Color 3", GroupName = "Parameters", Order = 7)]		
		public Brush cV3
		{
			get{return colorV3;}
			set{colorV3 = value;}
		}
		
		
		// Serialize our Color object
		[Browsable(false)]
		public string ColorBrushSerialize1
		{
			get { return Serialize.BrushToString(colorV1); }
   			set { colorV1 = Serialize.StringToBrush(value); }
		}
		[Browsable(false)]
		public string ColorBrushSerialize2
		{
			get { return Serialize.BrushToString(colorV2); }
   			set { colorV2 = Serialize.StringToBrush(value); }
		}
		[Browsable(false)]
		public string ColorBrushSerialize3
		{
			get { return Serialize.BrushToString(colorV3); }
   			set { colorV3 = Serialize.StringToBrush(value); }
		}
		[NinjaScriptProperty]		
		[XmlIgnore()]
		[Display(Name = "4. Colores del texto", Description = "colores del texto", GroupName = "Parameters", Order = 8)]		
		public Brush ЦветТекста
		{
			get{return colorText;}
			set{colorText = value;}
		}
		[Browsable(false)]
		public string ColorTextBrushSerialize
		{
			get { return Serialize.BrushToString(ЦветТекста); }
   			set { ЦветТекста = Serialize.StringToBrush(value); }
		}
        [NinjaScriptProperty]        
		[XmlIgnore()]
		[Display(Name = "1. Exhibición comercial", Description = "Exhibición comercial", GroupName = "Parameters-Other", Order = 9)]        public bool Эллипс
        {
            get { return useEllipse; }
            set {useEllipse = value; }
        }	
        [NinjaScriptProperty]        
		[Display(Name = "2. Tiempo y volumen", Description = "Tiempo de visualización verdadero, volumen", GroupName = "Parameters-Other", Order = 10)]        public bool Значения_объёма
        {
            get { return ShowTime; }
            set {ShowTime = value; }
        }	
        [NinjaScriptProperty]       
		[Display(Name = "3. Señal de sonido", Description = "Señal de sonido", GroupName = "Parameters-Other", Order = 11)]        public bool Звуковой_сигнал
        {
            get { return useAlerts; }
            set {useAlerts = value; }
        }			
        [NinjaScriptProperty]        
		[Display(Name = "4. Archivo", Description = "Nombre del archivo de sonido", GroupName = "Parameters-Other", Order = 12)]        public string StringtoAlert
        {
            get { return stringtoAlert; }
            set {stringtoAlert = value; }
        }		
        #endregion
    }
}

#region NinjaScript generated code. Neither change nor remove.

namespace NinjaTrader.NinjaScript.Indicators
{
	public partial class Indicator : NinjaTrader.Gui.NinjaScript.IndicatorRenderBase
	{
		private BigTrades3Vol[] cacheBigTrades3Vol;
		public BigTrades3Vol BigTrades3Vol(int vol1, int vol2, int vol3, int время, Brush cV1, Brush cV2, Brush cV3, Brush цветТекста, bool эллипс, bool значения_объёма, bool звуковой_сигнал, string stringtoAlert)
		{
			return BigTrades3Vol(Input, vol1, vol2, vol3, время, cV1, cV2, cV3, цветТекста, эллипс, значения_объёма, звуковой_сигнал, stringtoAlert);
		}

		public BigTrades3Vol BigTrades3Vol(ISeries<double> input, int vol1, int vol2, int vol3, int время, Brush cV1, Brush cV2, Brush cV3, Brush цветТекста, bool эллипс, bool значения_объёма, bool звуковой_сигнал, string stringtoAlert)
		{
			if (cacheBigTrades3Vol != null)
				for (int idx = 0; idx < cacheBigTrades3Vol.Length; idx++)
					if (cacheBigTrades3Vol[idx] != null && cacheBigTrades3Vol[idx].Vol1 == vol1 && cacheBigTrades3Vol[idx].Vol2 == vol2 && cacheBigTrades3Vol[idx].Vol3 == vol3 && cacheBigTrades3Vol[idx].Время == время && cacheBigTrades3Vol[idx].cV1 == cV1 && cacheBigTrades3Vol[idx].cV2 == cV2 && cacheBigTrades3Vol[idx].cV3 == cV3 && cacheBigTrades3Vol[idx].ЦветТекста == цветТекста && cacheBigTrades3Vol[idx].Эллипс == эллипс && cacheBigTrades3Vol[idx].Значения_объёма == значения_объёма && cacheBigTrades3Vol[idx].Звуковой_сигнал == звуковой_сигнал && cacheBigTrades3Vol[idx].StringtoAlert == stringtoAlert && cacheBigTrades3Vol[idx].EqualsInput(input))
						return cacheBigTrades3Vol[idx];
			return CacheIndicator<BigTrades3Vol>(new BigTrades3Vol(){ Vol1 = vol1, Vol2 = vol2, Vol3 = vol3, Время = время, cV1 = cV1, cV2 = cV2, cV3 = cV3, ЦветТекста = цветТекста, Эллипс = эллипс, Значения_объёма = значения_объёма, Звуковой_сигнал = звуковой_сигнал, StringtoAlert = stringtoAlert }, input, ref cacheBigTrades3Vol);
		}
	}
}

namespace NinjaTrader.NinjaScript.MarketAnalyzerColumns
{
	public partial class MarketAnalyzerColumn : MarketAnalyzerColumnBase
	{
		public Indicators.BigTrades3Vol BigTrades3Vol(int vol1, int vol2, int vol3, int время, Brush cV1, Brush cV2, Brush cV3, Brush цветТекста, bool эллипс, bool значения_объёма, bool звуковой_сигнал, string stringtoAlert)
		{
			return indicator.BigTrades3Vol(Input, vol1, vol2, vol3, время, cV1, cV2, cV3, цветТекста, эллипс, значения_объёма, звуковой_сигнал, stringtoAlert);
		}

		public Indicators.BigTrades3Vol BigTrades3Vol(ISeries<double> input , int vol1, int vol2, int vol3, int время, Brush cV1, Brush cV2, Brush cV3, Brush цветТекста, bool эллипс, bool значения_объёма, bool звуковой_сигнал, string stringtoAlert)
		{
			return indicator.BigTrades3Vol(input, vol1, vol2, vol3, время, cV1, cV2, cV3, цветТекста, эллипс, значения_объёма, звуковой_сигнал, stringtoAlert);
		}
	}
}

namespace NinjaTrader.NinjaScript.Strategies
{
	public partial class Strategy : NinjaTrader.Gui.NinjaScript.StrategyRenderBase
	{
		public Indicators.BigTrades3Vol BigTrades3Vol(int vol1, int vol2, int vol3, int время, Brush cV1, Brush cV2, Brush cV3, Brush цветТекста, bool эллипс, bool значения_объёма, bool звуковой_сигнал, string stringtoAlert)
		{
			return indicator.BigTrades3Vol(Input, vol1, vol2, vol3, время, cV1, cV2, cV3, цветТекста, эллипс, значения_объёма, звуковой_сигнал, stringtoAlert);
		}

		public Indicators.BigTrades3Vol BigTrades3Vol(ISeries<double> input , int vol1, int vol2, int vol3, int время, Brush cV1, Brush cV2, Brush cV3, Brush цветТекста, bool эллипс, bool значения_объёма, bool звуковой_сигнал, string stringtoAlert)
		{
			return indicator.BigTrades3Vol(input, vol1, vol2, vol3, время, cV1, cV2, cV3, цветТекста, эллипс, значения_объёма, звуковой_сигнал, stringtoAlert);
		}
	}
}

#endregion
