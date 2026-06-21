# Sanctum

> A minimal, Byzantine-fault-tolerant **trusted-timestamping ledger** for hospital
> networks, whose core theses are **machine-checked in Agda** and whose node runs
> in **Haskell**.

Hospitals sign a great many documents. What matters is not only *who* signed, but
that a signature **provably existed at a given time** — and that this proof holds
up even between hospitals that do **not trust each other**, and even for hospitals
that have **no connection to the outside world** beyond their local network.

Sanctum delivers that with:

- a **hash-linked, append-only ledger** replicated across hospital nodes;
- **BFT consensus** so that distrusting parties still agree on one history;
- **provably trustworthy time**: a block's timestamp is the *median* of its
  validators' clocks, and we prove that with a Byzantine minority the median is
  bounded by honest reality;
- **offline-verifiable proofs**: a hospital can hand anyone a self-contained
  certificate (`Testament`) proving "this document existed at this time", and the
  recipient verifies it **without contacting the network** — essential when a node
  is air-gapped;
- a **total smart-contract layer** (Cardano/EUTXO-flavoured validators) that needs
  **no gas and no fees**, because every contract is *proven to halt*;
- **dynamic membership**: new hospitals join over time through a quorum-authorised
  reconfiguration recorded on the ledger itself.

The non-negotiable theses live in [`agda/`](agda/) and are checked by Agda. The
running node lives in [`haskell/`](haskell/); its kernel is **generated from the
Agda** so that what runs is what was proven.

---

## The seven holy principles

The whole system is built on a single organising pattern — seven layers, each
born from the previous, from the void to harmony. This is not decoration: it is
the actual module/dependency stack of the codebase. See
[`docs/seven-principles.md`](docs/seven-principles.md).

| # | Principle (PL) | Principle (EN) | What it *is* in Sanctum |
|---|----------------|----------------|--------------------------|
| 0 | Pustka | Void | The empty: genesis from nothing, the zero hash, `⊥`. |
| 1 | Prawda, byt | Truth, Being | The atomic **Fact** — a hash that witnesses a document *exists*. |
| 2 | Rozdzielenie | Separation, Distinction | **Identity**: keys, hospitals, signatures — telling true author from forger. |
| 3 | Połączenie | Connection | **Links**: hash-chaining and signatures binding author ↔ fact ↔ time. |
| 4 | Struktura | Structure | The **ledger**: blocks, Merkle trees, the append-only log. |
| 5 | Życie, bunt, opór | Life, Rebellion, Resistance | **Consensus & growth**: BFT against the Byzantine, new nodes joining. |
| 6 | Doskonałość, harmonia | Perfection, Harmony | **Finality & contracts**: one agreed history, total validators, the capstone theorems. |

---

## What is proven (the theses)

| Thesis | Principle | Statement | File |
|--------|-----------|-----------|------|
| Append-only | 4 Structure | Extending a valid chain preserves all prior history; genesis is fixed. | [`Append.agda`](agda/src/Sanctum/Proofs/Append.agda) |
| Quorum intersection | 5 Life | Any two quorums of a `3f+1` validator set share an **honest** member ⇒ no two conflicting blocks finalise at one height (**Agreement**). | [`Quorum.agda`](agda/src/Sanctum/Proofs/Quorum.agda) |
| BFT time soundness | 6 Harmony | If `> f` of `2f+1` validator clocks lie in `[lo,hi]`, the agreed **median ∈ [lo,hi]** — the timestamp is bounded by honest reality. | [`Time.agda`](agda/src/Sanctum/Proofs/Time.agda) |
| Contract totality | 6 Harmony | The on-chain evaluator is **total** ⇒ every contract halts ⇒ **no gas is needed**. (The Agda termination checker accepting it *is* the proof.) | [`Totality.agda`](agda/src/Sanctum/Proofs/Totality.agda) |
| Reconfiguration safety | 5 Life | A new validator set is adopted only with a quorum certificate from the *previous* set ⇒ unbroken chain of authority from genesis. | [`Append.agda`](agda/src/Sanctum/Proofs/Append.agda) |

The cryptographic primitives (collision-resistant hashing, unforgeable signatures)
are modelled as an **abstract interface with stated assumptions** (postulates).
We prove the *protocol* correct on top of those assumptions — we do not re-prove
cryptography. See [`docs/threat-model.md`](docs/threat-model.md).

---

## Repository layout

```
agda/                     Agda library "sanctum" (proofs + extractable kernel)
  src/Sanctum/
    P0_Void.agda          0  the empty
    P1_Truth.agda         1  Facts (document commitments)
    P2_Distinction.agda   2  identities, keys, signatures (abstract crypto)
    P3_Connection.agda    3  hash links
    P4_Structure.agda     4  blocks, the ledger
    P5_Life.agda          5  validator sets, quorum certificates, reconfiguration
    P6_Harmony.agda       6  finality, the Testament (offline proof), contracts
    Kernel.agda           the total state-transition core (extracts to Haskell)
    Proofs/               the machine-checked theses
  Everything.agda         typecheck entry point
haskell/                  the node (Cabal project "sanctum-node")
  src/                    node shell: networking, storage, gossip, CLI glue
  app/Main.hs             node + demo executable
  gen/                    Haskell generated from agda/Kernel.agda (MAlonzo)
  test/
docs/                     architecture, principles, threat model, timestamping
scripts/                  check.sh (typecheck), extract.sh (Agda→Haskell)
```

## Build

```sh
scripts/check.sh      # type-check every Agda thesis  (needs: agda + agda-stdlib)
scripts/extract.sh    # generate haskell/gen/ from the Agda kernel
cd haskell && cabal build && cabal run sanctum-node -- demo
```

See [`docs/architecture.md`](docs/architecture.md) for the full picture and
[`docs/timestamping.md`](docs/timestamping.md) for *why* the time proof is
trustworthy without any external time authority.
