# Hawk-Code-NinjaTrader

Projeto de desenvolvimento de indicador e automações personalizadas para NinjaTrader.

## Indicador entregue

### `HawkMidasMNQ_V13_Auditor`

Arquivo NinjaScript:

```text
Indicators/HawkMidasMNQ_V13_Auditor.cs
```

O indicador é um **auditor**, não uma estratégia executora. Ele replica a lógica HawkMidas MNQ V1.3 em um motor virtual interno, calculado em `Calculate.OnBarClose`, sem enviar ordens reais.

**Status:** indicador auditor em validação. Não considerar produção até bater trade a trade com o TradingView no recorte oficial de maio/2026. O merge na `main` depende da validação dos critérios de aceitação: compilação no NinjaTrader 8, ausência de ordens reais, reset diário BRT completo, contexto somente após 10:35 BRT, `context_ready`, timezone auditável, ZigZag compatível e reprodução da lista oficial V1.3.

Principais recursos:

- SuperTrend interno com ATR RMA, fator e interpretação Pine (`st_dir < 0` como contexto comprador).
- ZigZag interno equivalente ao conceito `pivothigh/pivotlow` com pernas 2/2 e confirmação atrasada.
- AVWAP/MIDAS ancorada em pivô ZigZag, estática por contexto V1.3.
- Regra de `bridge trade` antes de invalidar contexto em giro do SuperTrend.
- Motor virtual de entradas, stops, targets, EOD, travas diárias e calendário BRT.
- Plots, marcadores de pivôs/entradas/saídas e painel de estatísticas.
- Exportação CSV opcional da lista de trades virtuais.
- Logs de auditoria opcionais via janela Output do NinjaTrader, incluindo auditoria explícita de timezone.
- Reset diário BRT completo da estrutura operacional: pivôs, contexto, âncora, AVWAP e nível de entrada.
- Regra `context_ready` equivalente ao Pine, impedindo entrada normal no candle de criação do contexto.
- Filtro ZigZag por desvio percentual e substituição de pivô por extremo mais relevante antes da alternância.

## Instalação rápida no NinjaTrader 8

1. Copie `Indicators/HawkMidasMNQ_V13_Auditor.cs` para a pasta de indicadores do NinjaTrader 8, normalmente:

   ```text
   Documents\NinjaTrader 8\bin\Custom\Indicators\
   ```

2. No NinjaTrader 8, abra **New > NinjaScript Editor**.
3. Clique com o botão direito e selecione **Compile**.
4. Abra um gráfico de **MNQ 5 minutos**.
5. Adicione o indicador `HawkMidasMNQ_V13_Auditor`.
6. Para auditoria de maio/2026, mantenha `BlockedDatesCsv = 2026-05-25`.
7. Ative `EnableDebugLogs` para comparar eventos candle a candle contra o TradingView.
8. Ative `EnableCsvExport` e informe `CsvExportPath` se quiser gerar o CSV de trades.

## Parâmetros oficiais padrão V1.3

- ATR Length: `10`
- SuperTrend Factor: `3.0`
- ZigZag Legs: `2`
- ZigZag Reversal: `0.00001`
- Offset AVWAP: `0.25`
- Valor por ponto: `2.0 USD`
- Tick mínimo: `0.25`
- Contratos: `1`
- Stop: `25 pontos`
- Target: `100 pontos`
- Custo round-trip: `2.0 USD`
- Capital inicial visual: `1500.0 USD`
- Máximo de trades/dia: `2`
- Meta diária líquida: `198.0 USD`
- Stop diário líquido: `-104.0 USD`
- Timezone operacional: `E. South America Standard Time`
- SourceTimeZoneMode: `LocalMachine` (`Utc`, `AlreadyBrt` e `Exchange` também ficam documentados nos logs; `Exchange` mantém conversão de máquina local nesta fase)
- Janela BRT: `10:35` até `16:45`
- EOD BRT: `17:00`
- Datas bloqueadas: `2026-05-25`


## Ajustes visuais

O indicador permite configurar:

- exibição dos marcadores do ZigZag;
- tamanho dos marcadores do ZigZag;
- offset visual dos marcadores;
- cor dos pivôs de topo e fundo;
- cor do SuperTrend comprador e vendedor.

Por padrão, os marcadores do ZigZag são plotados apenas dentro da janela operacional BRT.

## Observações de conversão Pine → NinjaTrader

- A decisão operacional é feita após converter `Time[0]` para BRT; com `EnableDebugLogs = true`, cada candle registra `RAW Time[0]`, `Kind`, BRT convertido, `dateBrt`, hora BRT, timezone operacional e `SourceTimeZoneMode`.
- O indicador não usa `EnterLong`, `EnterShort`, `SetStopLoss`, `SetProfitTarget` ou qualquer API de ordens reais.
- O CSV só registra trades fechados, porque os campos exigem horário/preço/tipo de saída.
- A validação trade a trade de maio/2026 deve ser feita dentro do NinjaTrader 8 com a mesma base de candles usada no TradingView; este repositório não inclui dados históricos oficiais nem ambiente NinjaTrader para compilação local.
- O indicador permanece candidato de validação, não artefato de produção, até reproduzir: 27 trades, 12 targets, 14 stops, 1 EOD, 15 longs, 12 shorts e resultado líquido aproximado de US$ 1.630,61 no recorte oficial de maio/2026.

### `HawkMidasMNQ_V21_Auditor`

Arquivo NinjaScript:

```text
Indicators/HawkMidasMNQ_V21_Auditor.cs
```

A V2.1 é um **novo indicador auditor separado** da V1.3. Ela mantém o mesmo conceito operacional base — SuperTrend interno, ZigZag 2/2 interno, AVWAP/MIDAS ancorada, entrada virtual por `AVWAP[1] ± offset`, stop/target/EOD simulados e CSV de trades fechados — sem enviar ordens reais no NinjaTrader.

Diferença central da V2.1:

- `DynamicPivotAvwap = true` por padrão.
- Enquanto o SuperTrend permanecer comprado, um novo fundo ZigZag relevante pode substituir a âncora da AVWAP.
- Enquanto o SuperTrend permanecer vendido, um novo topo ZigZag relevante pode substituir a âncora da AVWAP.
- A atualização dinâmica roda **somente depois** das tentativas de entrada/bridge/saída do candle, preservando a prioridade do nível operacional antigo quando um pivô é confirmado no mesmo candle.

Parâmetros oficiais padrão V2.1 criados/mantidos:

- `AtrLength = 10`
- `SuperTrendFactor = 3.0`
- `ZigZagLegs = 2`
- `ZigZagReversal = 0.00001`
- `AvwapOffsetPoints = 0.25`
- `PointValueUsd = 2.0`
- `TickSizePoints = 0.25`
- `Contracts = 1`
- `StopPoints = 25.0`
- `TargetPoints = 100.0`
- `RoundTripCostUsd = 2.0`
- `InitialCapital = 1500.0`
- `MaxTradesPerDay = 2`
- `DailyProfitTargetUsd = 198.0`
- `DailyStopUsd = -104.0`
- `OneTradePerDirectionContext = false` para fidelidade ao Pine V2.1 original
- `DynamicPivotAvwap = true`
- `ResetZigZagDaily = true`
- `IntrabarMode = STOP_PRIMEIRO`
- `EntryCandleMode = STOP_MESMO_CANDLE_TARGET_PROXIMO`
- `OperationalTimeZoneId = E. South America Standard Time`
- `SourceTimeZoneMode = LocalMachine`
- `TradingStartBrt = 10:35`
- `LastEntryBrt = 16:45`
- `EodBrt = 17:00`
- `BlockedDatesCsv = 2026-01-01,2026-01-19,2026-02-16,2026-04-03,2026-05-25,2026-06-19,2026-07-03,2026-09-07,2026-11-26,2026-12-25`
- `EarlyCloseDatesCsv = 2026-11-27,2026-12-24`
- `EnableCsvExport`, `CsvExportPath`, `EnableDebugLogs`
- parâmetros visuais de marcadores ZigZag e cores de SuperTrend/ZigZag

Campos adicionais no CSV V2.1:

- `anchor_type`
- `dynamic_pivot_avwap`
- `dynamic_update_id`
- `dynamic_anchor_changed`
- `dynamic_anchor_time_brt`
- `dynamic_anchor_price`
- `source_time_raw`
- `source_time_brt`

Observações de conversão Pine → NinjaTrader V2.1:

- A AVWAP compradora usa `Low * Volume`; a AVWAP vendedora usa `High * Volume`.
- A entrada operacional usa exclusivamente `avwapSeries[1] ± AvwapOffsetPoints`; o nível visual usa a AVWAP do candle atual.
- `effective_offset` é gravado no CSV; longs devem aparecer com `+0.2500` e shorts com `-0.2500` quando o offset padrão é usado.
- Toda decisão operacional continua sendo feita depois da conversão de `Time[0]` para BRT; o horário bruto do NinjaTrader é usado apenas para auditoria/log.
- O arquivo V1.3 permanece separado e não deve ser alterado para validar a V2.1.
