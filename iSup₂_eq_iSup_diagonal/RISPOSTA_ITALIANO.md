# Collegamento tra lo screenshot e le correzioni API

Lo screenshot e il testo citato raccontano in realtà **due aspetti distinti della stessa proposta di PR**:

1. lo screenshot mostra i problemi emersi durante il controllo della patch;
2. le due correzioni spiegano quale sia la formulazione Lean corretta dell’eventuale lemma su `sSup`.

## 1. Perché l’orientamento di `IsCofinalFor` è `t s`

In questa API la relazione d’ordine è già incorporata in `IsCofinalFor`. Informalmente,

```lean
IsCofinalFor t s
```

significa che ogni elemento di `t` è maggiorato da un opportuno elemento di `s`. È esattamente ciò che serve per ottenere

```lean
sSup t ≤ sSup s
```

tramite `sSup_le_sSup_of_isCofinalFor`.

L’altra disuguaglianza viene invece direttamente dall’inclusione:

```lean
hst : s ⊆ t
```

che, usando il nome presente in questa versione di Mathlib,

```lean
sSup_le_sSup hst
```

fornisce

```lean
sSup s ≤ sSup t.
```

Le due direzioni si chiudono quindi per antisimmetria:

```lean
theorem sSup_eq_sSup_of_subset_of_isCofinalFor
    [CompleteSemilatticeSup α] {s t : Set α}
    (hst : s ⊆ t) (hts : IsCofinalFor t s) : sSup s = sSup t := by
  apply le_antisymm
  · exact sSup_le_sSup hst
  · exact sSup_le_sSup_of_isCofinalFor hts
```

Questo chiarisce anche perché le due correzioni non sono cosmetiche:

- scrivere gli argomenti di `IsCofinalFor` nell’ordine opposto dimostrerebbe la disuguaglianza nella direzione sbagliata;
- `sSup_mono` non è il nome disponibile nell’API della versione usata dalla patch: qui il lemma è `sSup_le_sSup`.

## 2. Collegamento con gli errori mostrati nello screenshot

Il punto importante è distinguere gli errori **primari** da quelli **a cascata**.

- L’errore `Unknown identifier rw` non indica che manchi un import della tattica `rw`. È una conseguenza del fatto che la dichiarazione precedente non era stata elaborata correttamente, in particolare nell’area della generazione duale e del nome del teorema.
- L’avviso relativo al nome generato da `to_dual` si risolve scegliendo nomi simmetrici e prevedibili, cioè `iSup₂_eq_diagonal` e `iInf₂_eq_diagonal`.
- L’avviso sulla riga troppo lunga è soltanto stilistico e si risolve spezzando la dichiarazione di `ENNReal.iInf_add_iInf`.
- L’avviso sulla versione di Node.js appartiene alla manutenzione del workflow del repository e non alla correttezza matematica o Lean di questa PR; non va “risolto” modificando il lemma.

Le correzioni a `IsCofinalFor` e `sSup_le_sSup`, invece, riguardano la **forma corretta dell’API matematica**. Sono quindi collegate allo stesso lavoro, ma non sono la causa diretta di tutti i messaggi CI visibili nello screenshot.

## 3. Perché il lemma corretto non è necessariamente la scelta migliore per questa PR

Il lemma su `sSup` è naturale e corretto, ma il suo corpo combina soltanto due risultati già esistenti, ciascuno in una riga:

```text
s ⊆ t                 ⇒ sSup s ≤ sSup t
IsCofinalFor t s      ⇒ sSup t ≤ sSup s
                       ──────────────────
                       sSup s = sSup t
```

Al momento il solo uso concreto noto sarebbe il risultato sulla diagonale. Questo è debole rispetto al criterio iniziale della ricerca: un nuovo helper è più convincente quando semplifica **due o tre chiamanti già esistenti**.

Il lemma focalizzato sulla diagonale ha invece già tre riusi concreti:

- `ENat.iSup_add_iSup`;
- `ENNReal.iSup_add_iSup`;
- `ENNReal.iInf_add_iInf`, tramite il duale.

Perciò lo screenshot e le correzioni portano alla stessa raccomandazione pratica:

- correggere la patch e mantenere la PR attuale centrata su `iSup₂_eq_diagonal` / `iInf₂_eq_diagonal` e sui tre chiamanti;
- non aggiungere ora `sSup_eq_sSup_of_subset_of_isCofinalFor`, salvo trovare almeno un altro chiamante indipendente o ricevere dal reviewer la richiesta esplicita di organizzare l’API attorno a `IsCofinalFor`.

## Conclusione

La formulazione proposta nel testo è la versione Lean corretta del possibile helper su `sSup`. Tuttavia, proprio il contesto mostrato dallo screenshot rafforza l’idea di una PR più piccola e mirata: correggere i problemi di elaborazione, dualità e stile, presentare il lemma diagonale con tre riusi verificabili, e lasciare l’uguaglianza generale basata su `IsCofinalFor` a un eventuale seguito meglio motivato.