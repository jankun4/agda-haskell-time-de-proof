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
time, total contract evaluation) is written in Agda and proved.
`Sanctum.Core` is a faithful hand-mirror of that kernel, so the node builds
without the Agda toolchain; `scripts/extract.sh` produces the literal
MAlonzo-generated version and CI runs it. (The node currently links the
mirror, not the generated module — see [limitations.md](limitations.md) §1.)
The **shell** here is deliberately thin: `Node` provides hospital identities
and attestation construction only. Networking, gossip, and persistence are
**not implemented** — they are deployment concerns (see limitations §6).

## Trust model in one line

> *No hospital trusts another's word; everyone trusts a quorum and trusts
> mathematics.*

A node accepts a block only if it carries a **quorum certificate** of
**verified** signatures (≥ `n−f` distinct members; at `n = 3f+1` that is the
classic `2f+1`). The count is taken from signatures that actually verify,
never from a self-declared vector. It accepts a *time* only as the
**median** of the quorum's clocks. It accepts a *contract result* only
because the contract is **provably total**. None of these require trusting
any single party.

## Data flow: timestamping a document

1. A hospital hashes the document → a `Fact`, signs `author‖fact‖time`
   → an `Attestation` (Principle 3).
2. Attestations are disseminated (gossip layer is out of scope) and
   gathered by a block proposer into a block (Principle 4). The block's
   Merkle root commits to them.
3. Validators run a finalisation round (`Consensus.finalise`, Principle 5):
   each contributes a clock sample and a signature over the header. The
   header's `blockTime` is the **median** of the samples.
4. With ≥ `n−f` verified signatures the block is final and appended. The
   chain is append-only (`Proofs.Append`).
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
economic: the executed on-chain evaluator is **total** — `Kernel.runContract`
is accepted by Agda's termination checker, which *is* the proof that every
contract halts (`Proofs.Totality` separately proves a richer STLC total, as
headroom — it is not the executed language). Gas exists
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
2. A **quorum of the current set** *signs* a certificate that commits to
   exactly the proposed members and the target epoch.
   `Ledger.adoptValidatorSet` then checks: the target epoch is the
   successor; ≥ `n−f` *verified* current-member signatures over that exact
   certificate; a quorum of the current set persists into the new set (no
   wholesale handover); and the fault budget rises by at most one. This
   binding is what stops a stale or forged certificate from installing
   attacker validators.
3. From the next epoch, blocks are finalised under the new set.

Because every set is adopted only by the previous set's signed quorum,
authority forms an unbroken lineage back to genesis — proved abstractly as
`Proofs.Append.Reconfiguration.authorised→lineage`. A light client that
walks this lineage from the header chain (so an air-gapped verifier can know
*which* set to trust per epoch) is specified but **not yet implemented** —
see [limitations.md](limitations.md) and [threat-model.md](threat-model.md).

This also covers **leaving** (remove a member), **key rotation** (swap an
identity), and **changing the fault budget** `f` as the network grows.
