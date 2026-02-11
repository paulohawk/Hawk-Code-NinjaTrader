# 📄 PAPER – Correção Cirúrgica do TradingDay em Replay

## 🎯 Objetivo

Restaurar o comportamento correto da estratégia em Replay de Mercado, corrigindo exclusivamente o cálculo de TradingDay, que atualmente está projetando datas futuras (ex: 2026-02-12) quando o replay está em 2026-02-09.

## 🚫 Proibido neste paper

- Não alterar lógica de conta live.
- Não alterar lógica de SessionIterator para ambiente real.
- Não mexer em overlay.
- Não mexer em AutoClose.
- Não refatorar nada além do necessário.

## 🔎 Diagnóstico Técnico

Atualmente:

```csharp
private DateTime GetReplayTradingDayOrFallback(DateTime fallbackReferenceTime)
{
    if (!IsReplayMode())
        return GetTradingDay(fallbackReferenceTime);

    DateTime replayNow = GetReplayNowOrFallback(fallbackReferenceTime);
    return GetTradingDay(replayNow);
}
```

### ❌ Problema

`GetTradingDay()` usa `SessionIterator`.

Em Replay, o `SessionIterator` pode:

- Considerar sessão CME
- Aplicar DST
- Projetar sessão ETH
- Avançar trading day

Resultado observado:

Replay em 09/02 → TradingDay retornando 12/02.

Isso quebra:

```csharp
plannedTradeDate.Date == tradingDay.Date
```

E impede o armamento do hedge.

## ✅ Correção Necessária (Replay isolado)

Replay não deve usar `SessionIterator`.

Replay deve usar exclusivamente:

```csharp
Times[0][0].Date
```

## 🔧 ALTERAÇÃO EXATA A SER FEITA

Substituir o método atual por:

```csharp
private DateTime GetReplayTradingDayOrFallback(DateTime fallbackReferenceTime)
{
    // Conta LIVE → mantém comportamento original
    if (!IsReplayMode())
        return GetTradingDay(fallbackReferenceTime);

    // Replay → usa exclusivamente a data do candle principal
    DateTime replayNow = GetReplayNowOrFallback(fallbackReferenceTime);
    return replayNow.Date;
}
```

## 🔐 GARANTIA DE ISOLAMENTO

Observe:

```csharp
if (!IsReplayMode())
    return GetTradingDay(fallbackReferenceTime);
```

Ou seja:

- Conta Live → continua usando SessionIterator.
- Replay → usa Date puro.
- Nenhuma função de live é alterada.
- Nenhuma lógica de bracket live é tocada.

## 🧠 Por Que Isso É Seguro?

Porque:

- Replay é um ambiente simulado.
- Replay não precisa respeitar sessão real.
- Replay precisa apenas alinhar entrada com o dia do candle.
- A conta live continua 100% dependente de SessionIterator.

## 🚨 O QUE NÃO DEVE SER ALTERADO

- ❌ Não alterar GetReplayNowOrFallback
- ❌ Não alterar GetTradingDay
- ❌ Não alterar AutoClose
- ❌ Não alterar Hedge lifecycle
- ❌ Não alterar Audit
- ❌ Não alterar Log

Somente o retorno do TradingDay em replay.

## 🎯 Resultado Esperado

Replay 09/02:

```text
TradingDay = 2026-02-09
```

Condição volta a funcionar:

```csharp
plannedTradeDate == tradingDay
```

Hedge arma normalmente.

Ordem volta a plotar.

## 📌 Diretriz Permanente a partir de agora

- Só mexer em lógica se houver bug funcional.
- Log não justifica alteração estrutural.
- Replay e Live devem sempre ter tratamento separado.
- Nunca tentar “unificar” comportamento de sessão entre Replay e Live.
