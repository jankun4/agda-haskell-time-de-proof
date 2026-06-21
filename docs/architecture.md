# Architecture

Sanctum is a **permissioned, Byzantine-fault-tolerant distributed ledger**
specialised for one job: proving that a signed document existed at a given
time, for a network of hospitals that do not fully trust one another and
are not all connected to the outside world.

## Components

```
                 ┌─────────────────────────────────────────────┐
                 │  agda/  — the verified core (source of truth) │
                 │   Proofs/*  the theses (quorum, time, append, │
                 │             totality)                         │
                 │   Kernel    total executable core ──┐         │
                 └─────────────────────────────────────┼─────────┘
                                                        │ scripts/extract.sh
                                                        │ (MAlonzo: Agda → Haskell)
                 ┌──────────────────────────────────────▼────────┐
                 │  haskell/ — the node                           │
                 │   Core       quorum rule · median · contracts  │ (mirror of Kernel)
                 │   Crypto     digest + signatures (swappable)    │
                 │   Types      Fact/Block/Chain/QC/Testament      │
                 │   Ledger     Merkle · append · Testament        │
                 │   Consensus  one BFT finalisation round         │
                 │   Node       hospital identities & attestations │
                 └────────────────────────────────────────────────┘
```

The **kernel** (the security-critical arithmetic: quorum threshold, median
time, total contract evaluation) is written in Agda, proved, and extracted
to Haskell. The **shell** (keys, networking, storage, CLI) is conventional
Haskell. `Sanctum.Core` is the hand-mirror of the kernel so the node builds
without the Agda toolchain; `scripts/extract.sh` produces the literal
generated version.

## Trust model in one line

> *No hospital trusts another's word; everyone trusts a quorum and trusts
> mathematics.*

A node accepts a block only if it carries a **quorum certificate** (≥ 2f+1
validator signatures). It accepts a *time* only as the **median** of the
quorum's clocks. It accepts a *contract result* only because the contract
is **provably total**. None of these require trusting any single party.

## Data flow: timestamping a document

1. A hospital hashes the document → a `Fact`, signs `author‖fact‖time`
   → an `Attestation` (Principle 3).
2. Attestations are gossiped and gathered by a block proposer into a block
   (Principle 4). The block's Merkle root commits to them.
3. Validators run a finalisation round (`Consensus.finalise`, Principle 5):
   each contributes a clock sample and a signature over the header. The
   header's `blockTime` is the **median** of the samples.
4. With ≥ 2f+1 signatures the block is final and appended. The chain is
   append-only (`Proofs.Append`).
5. Anyone can extract a **Testament** (Principle 6): the attestation, the
   header, the validator set, the quorum certificate, and a Merkle
   inclusion path. It proves "this document existed by `blockTime`".

## Partial connectivity (air-gapped sites)

Many hospitals have no route to the outside world. Two design choices make
this a non-issue:

- **The ledger is internal.** There is no dependency on any external clock,
  blockchain, or timestamping authority. Time comes from the validators'
  own quorum (see [timestamping.md](timestamping.md)).
- **Proofs are portable and offline-verifiable.** A `Testament` is
  self-contained. A site provisioned once with the (genesis-anchored)
  validator set can verify any Testament with **no network access** —
  `Ledger.verifyTestament` touches nothing but the bytes in front of it.
  A node that has been offline simply replays the block headers it missed
  when it reconnects; each is self-certifying via its quorum certificate.

## No gas, no fees

There is no gas metering and no fee market. The reason is structural, not
economic: the on-chain language is **total** — every program provably halts
(`Proofs.Totality`; the Agda termination checker *is* the proof). Gas exists
in other systems only to bound otherwise-unbounded execution and to price
it; with guaranteed termination and a permissioned (non-anonymous) validator
set, neither is needed. Resource fairness is handled administratively
(rate limits per hospital), not by a token.

## Adding nodes over time

See [reconfiguration](#reconfiguration). New hospitals join through an
on-ledger, quorum-authorised change of the validator set.

### Reconfiguration

The validator set is itself part of the replicated state, versioned by an
`epoch` recorded in every block header. To change it:

1. A proposal names the next `ValidatorSet` (e.g. current members + the new
   hospital), which must satisfy `n ≥ 3f+1`.
2. A **quorum of the current set** signs the proposal
   (`Ledger.adoptValidatorSet` checks ≥ 2f+1).
3. From the next epoch, blocks are finalised under the new set.

Because every set is adopted only by the previous set's quorum, authority
forms an unbroken lineage back to genesis — proved as
`Proofs.Append.Reconfiguration.authorised→lineage`. A light client tracks
this lineage from the header chain alone, so even an air-gapped verifier can
know *which* validator set to trust for a given epoch.

This also covers **leaving** (remove a member), **key rotation** (swap an
identity), and **changing the fault budget** `f` as the network grows.
