#region Using declarations
using System;
using System.Collections.Generic;
using NinjaTrader.Data;
using NinjaTrader.NinjaScript.Indicators.Hawk.Volume;
#endregion

namespace NinjaTrader.NinjaScript.Indicators.Hawk.Volume.Engine
{
	public sealed class HawkVpSelection
	{
		public int ChartKey;
		public DateTime StartTime;
		public DateTime EndTime;
		public int StartBar0;
		public int EndBar0;
		public DateTime UpdatedUtc;
	}

	public static class HawkVpSelectionBus
	{
		private static readonly Dictionary<int, HawkVpSelection> _byChartKey = new Dictionary<int, HawkVpSelection>();
		private static readonly object _lock = new object();

		public static void Set(int chartKey, HawkVpSelection sel)
		{
			if (chartKey == 0 || sel == null)
				return;

			lock (_lock)
			{
				_byChartKey[chartKey] = sel;
			}
		}

		public static bool TryGet(int chartKey, out HawkVpSelection sel)
		{
			lock (_lock)
			{
				return _byChartKey.TryGetValue(chartKey, out sel);
			}
		}

		public static void Clear(int chartKey)
		{
			lock (_lock)
			{
				if (_byChartKey.ContainsKey(chartKey))
					_byChartKey.Remove(chartKey);
			}
		}
	}

	public sealed class HawkVpContext
	{
		public IList<Indicators.Hawk.Volume.HawkVolumeProfile.VolItem> VolItems;
		public IList<int> ListPtr;
		public IList<int> SessionStartList;
		public Bars Bars0;
		public Bars Bars1;
		public int Bars1LastValidIndex;
	}

	public sealed class HawkVpRegionResult
	{
		public int StartBar0;
		public int EndBar0;
		public int StartBar1;
		public int EndBar1;
		public Dictionary<double, Indicators.Hawk.Volume.HawkVolumeProfile.VolItem> ProfileByPrice;
	}

	public sealed class HawkVpResult
	{
		public List<HawkVpRegionResult> Regions = new List<HawkVpRegionResult>();
	}

	public static class HawkVpEngine
	{
		public static int Clamp(int value, int min, int max)
		{
			if (max < min)
				return min;
			return Math.Max(min, Math.Min(max, value));
		}

		public static int SafeGetPtr(IList<int> listPtr, int bar0Index, int fallback)
		{
			if (listPtr == null || listPtr.Count == 0)
				return fallback;
			if (bar0Index < 0 || bar0Index >= listPtr.Count)
				return fallback;
			return listPtr[bar0Index];
		}

		public static void NormalizeRange(ref int startBar0, ref int endBar0)
		{
			if (startBar0 > endBar0)
			{
				int tmp = startBar0;
				startBar0 = endBar0;
				endBar0 = tmp;
			}
		}

		public static bool IsRangeValid(int startBar0, int endBar0, int bars0Count)
		{
			if (bars0Count <= 0)
				return false;
			if (startBar0 < 0 || endBar0 < 0)
				return false;
			if (startBar0 >= bars0Count || endBar0 >= bars0Count)
				return false;
			return startBar0 <= endBar0;
		}

		private static int MapBar0ToBar1(HawkVpContext ctx, int bar0Index)
		{
			int fallback = Clamp(ctx.Bars1LastValidIndex, 0, Math.Max(0, (ctx.VolItems?.Count ?? 1) - 1));
			int ptr = SafeGetPtr(ctx.ListPtr, bar0Index, fallback);
			int mapped = ptr;
			if (mapped < 0)
				mapped = fallback;
			return Clamp(mapped, 0, fallback);
		}

		private static int GetRegionStartBar1(HawkVpContext ctx, int startBar0)
		{
			if (startBar0 <= 0 || ctx.ListPtr == null || ctx.ListPtr.Count == 0)
				return 1;
			int ptrIndex = Clamp(startBar0 - 1, 0, ctx.ListPtr.Count - 1);
			return Clamp(ctx.ListPtr[ptrIndex] + 2, 0, Math.Max(0, ctx.Bars1LastValidIndex));
		}

		private static int GetRegionEndBar1(HawkVpContext ctx, int endBar0)
		{
			if (ctx.Bars0 != null && endBar0 == (ctx.Bars0.Count - 1))
				return ctx.Bars1LastValidIndex;
			if (ctx.ListPtr == null || ctx.ListPtr.Count == 0)
				return 0;
			int safeEndBar0 = Clamp(endBar0, 0, ctx.ListPtr.Count - 1);
			int ptr = MapBar0ToBar1(ctx, safeEndBar0);
			int bars1Count = ctx.Bars1 != null ? ctx.Bars1.Count : 0;
			if ((bars1Count - 1) >= ptr + 1)
				return Clamp(ptr + 1, 0, ctx.Bars1LastValidIndex);
			return Clamp(ptr, 0, ctx.Bars1LastValidIndex);
		}

		public static List<(int startBar0, int endBar0)> BuildRegions(
			HawkVolumeProfileRegionFromType from,
			HawkVolumeProfileRegionToType to,
			int chartFromIndex,
			int chartToIndex,
			DateTime dateFrom,
			DateTime dateTo,
			Func<DateTime, int> mapTimeToBar0,
			IList<int> sessionStartsInWindow)
		{
			var regions = new List<(int startBar0, int endBar0)>();
			int safeFrom = Math.Max(0, chartFromIndex);
			int safeTo = Math.Max(0, chartToIndex);
			if (safeFrom > safeTo)
			{
				int tmp = safeFrom;
				safeFrom = safeTo;
				safeTo = tmp;
			}

			if (from == HawkVolumeProfileRegionFromType.Window && to == HawkVolumeProfileRegionToType.Window)
				regions.Add((safeFrom, safeTo));
			else if (from == HawkVolumeProfileRegionFromType.Date && to == HawkVolumeProfileRegionToType.Date && mapTimeToBar0 != null)
			{
				int mappedFrom = mapTimeToBar0(dateFrom);
				int mappedTo = mapTimeToBar0(dateTo);
				if (mappedFrom > mappedTo)
				{
					int tmp = mappedFrom;
					mappedFrom = mappedTo;
					mappedTo = tmp;
				}
				regions.Add((mappedFrom, mappedTo));
			}
			else if (from == HawkVolumeProfileRegionFromType.Daily && to == HawkVolumeProfileRegionToType.Daily)
			{
				if (sessionStartsInWindow != null && sessionStartsInWindow.Count > 0)
				{
					for (int i = 0; i < sessionStartsInWindow.Count; i++)
					{
						int start = sessionStartsInWindow[i];
						int end = (i + 1 < sessionStartsInWindow.Count) ? sessionStartsInWindow[i + 1] - 1 : safeTo;
						regions.Add((start, end));
					}
				}
			}
			else if (from == HawkVolumeProfileRegionFromType.Bar && to == HawkVolumeProfileRegionToType.Bar)
			{
				for (int i = safeFrom; i <= safeTo; i++)
					regions.Add((i, i));
			}
			else if (from == HawkVolumeProfileRegionFromType.All && to == HawkVolumeProfileRegionToType.Current)
				regions.Add((0, safeTo));
			else
				regions.Add((safeFrom, safeTo));

			return regions;
		}

		public static HawkVpResult CalculateProfiles(HawkVpContext ctx, List<(int startBar0, int endBar0)> regionsBar0)
		{
			var result = new HawkVpResult();
			if (ctx == null || ctx.Bars0 == null || ctx.Bars1 == null || ctx.Bars0.Count == 0 || ctx.VolItems == null || regionsBar0 == null)
				return result;

			int bars0Max = ctx.Bars0.Count - 1;
			int volItemsMax = Math.Max(0, ctx.VolItems.Count - 1);
			int bars1Max = Clamp(ctx.Bars1LastValidIndex, 0, volItemsMax);

			for (int r = 0; r < regionsBar0.Count; r++)
			{
				int startBar0 = Clamp(regionsBar0[r].startBar0, 0, bars0Max);
				int endBar0 = Clamp(regionsBar0[r].endBar0, 0, bars0Max);
				NormalizeRange(ref startBar0, ref endBar0);
				if (!IsRangeValid(startBar0, endBar0, ctx.Bars0.Count))
					continue;

				int startBar1 = GetRegionStartBar1(ctx, startBar0);
				int endBar1 = GetRegionEndBar1(ctx, endBar0);
				startBar1 = Math.Max(1, startBar1);
				endBar1 = Clamp(endBar1, 0, bars1Max);
				if (ctx.VolItems.Count <= endBar1)
					endBar1 = ctx.VolItems.Count - 1;
				if (startBar1 > endBar1)
					continue;

				var profile = new Dictionary<double, Indicators.Hawk.Volume.HawkVolumeProfile.VolItem>();
				for (int i = startBar1; i <= endBar1; i++)
				{
					double price = ctx.Bars1.GetClose(i - 1);
					Indicators.Hawk.Volume.HawkVolumeProfile.VolItem entry;
					if (!profile.TryGetValue(price, out entry))
					{
						entry = new Indicators.Hawk.Volume.HawkVolumeProfile.VolItem();
						profile.Add(price, entry);
					}
					entry.up += ctx.VolItems[i].up;
					entry.down += ctx.VolItems[i].down;
					entry.total += ctx.VolItems[i].total;
				}

				result.Regions.Add(new HawkVpRegionResult
				{
					StartBar0 = startBar0,
					EndBar0 = endBar0,
					StartBar1 = startBar1,
					EndBar1 = endBar1,
					ProfileByPrice = profile
				});
			}

			return result;
		}
	}
}
