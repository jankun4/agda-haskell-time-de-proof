# The seven holy principles

Sanctum is built on one organising pattern: seven layers, each born from
the one before, from the void to harmony. This is the literal module and
dependency stack of the codebase — every layer imports only the layers
below it.

```
6  Harmony      finality · Testament · total contracts · capstone theorems
5  Life         validator sets · quorum certs · reconfiguration (growth)
4  Structure    blocks · Merkle trees · the append-only ledger
3  Connection   hash links · signed attestations binding author↔fact↔time
2  Distinction  identities · keys · signatures (telling author from forger)
1  Truth        the Fact — a digest witnessing a document exists
0  Void         the empty: ∅, the zero hash, the parent of genesis
```

| # | Principle | Agda | Haskell | Meaning in Sanctum |
|---|-----------|------|---------|--------------------|
| 0 | **Pustka / Void** | `P0_Void` | `Crypto.zeroHash` | The empty octet string and the zero hash from which genesis is born. Nothing yet *is*. |
| 1 | **Prawda, byt / Truth, Being** | `P1_Truth` | `Types.Fact` | The atomic being: a document *exists*, witnessed by its digest. Truth is decidable. |
| 2 | **Rozdzielenie / Distinction** | `P2_Distinction` | `Crypto` | To know a being is to distinguish it. Identities (keys) and signatures separate the true author from a forger. |
| 3 | **Połączenie / Connection** | `P3_Connection` | `Types.Attestation` | Beings are bound: a signature binds author ↔ fact ↔ time; a hash binds a block to its parent. |
| 4 | **Struktura / Structure** | `P4_Structure`, `Proofs.Append` | `Types`, `Ledger` | From bonds, form: the append-only chain and Merkle commitments. *Theorem: history is never rewritten.* |
| 5 | **Życie, bunt, opór / Life, Rebellion, Resistance** | `P5_Life`, `Proofs.Quorum` | `Consensus`, `Ledger.adoptValidatorSet` | The structure lives: it resists the Byzantine (quorum) and it grows (new hospitals join). *Theorem: quorum intersection.* |
| 6 | **Doskonałość, harmonia / Perfection, Harmony** | `P6_Harmony`, `Proofs.Time`, `Proofs.Totality` | `Ledger` (Testament), `Core.runContract` | All layers in accord: one agreed history, trustworthy time, total contracts, and the offline Testament. *Theorems: agreement, timestamp soundness, totality.* |

## Why this is more than decoration

Each principle is a real boundary:

- **0→1** Nothing becomes something: hashing turns the void into a witnessed fact.
- **1→2** A fact alone is anonymous; identity makes it *attributable*.
- **2→3** Identity alone is inert; a signature *connects* an author to a fact at a time.
- **3→4** Connections alone are a heap; hash-linking imposes *order and immutability*.
- **4→5** A structure alone is dead; consensus makes it *defend itself and grow*.
- **5→6** A living chain alone is internal; finality + the Testament make its truth *portable and total*.

The dependency graph is acyclic and matches the numbering: you can read the
system bottom-up and never need a concept before it is introduced.
