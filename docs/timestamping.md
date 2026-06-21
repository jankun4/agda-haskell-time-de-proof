# Trustworthy time without an authority

The core promise is: *a finalised document existed no later than time T*,
where T is trustworthy even though no single clock is trusted and there is
no external time source.

## The idea

A block's timestamp is **not** set by its proposer. It is the **median** of
the clock readings of the ≥ n−f validators that signed the block. Each
validator contributes its own clock as part of its vote
(`Consensus.Vote.voteClock`); the agreed `blockTime` is `medianTime` of
those samples (`Core.medianTime`, mirrored from `Kernel.medianTime`).

## Why the median is safe

Suppose more than `f` of the signers are honest (guaranteed when a quorum
of `n−f` signs and at most `f` are Byzantine), and the honest validators'
clocks all lie in some real interval `[lo, hi]` (they are roughly
synchronised — say within a few seconds). Then:

> **The median lies in `[lo, hi]`.**

This is the theorem `median-bound` in
[`Proofs/Time.agda`](../agda/src/Sanctum/Proofs/Time.agda), proved by a
counting argument:

- If the median were `> hi`, then every honest clock (`≤ hi`) would be
  strictly below it. That puts all `≥ f+1` honest samples in the "below"
  group, leaving the "at-or-above-median" group with `≤ f` members — but
  the median's defining property guarantees `≥ f+1` are at-or-above it.
  Contradiction (a pigeonhole clash, `quorum-clash`).
- Symmetrically the median cannot be `< lo`.

So a Byzantine minority can report `999999` or `0` all it likes; with the
honest majority bracketing the median, the agreed time cannot be dragged
outside honest reality. The demo shows exactly this: one validator reports
`999999`, the agreed time stays at `1002`.

## What a Testament proves, precisely

A verified `Testament` yields `provenTime = blockTime`. Combined with the
theorem above, the guarantee delivered to a third party is:

> The document was committed in a block whose time was agreed by a quorum;
> that time is bounded above by the latest honest clock among the signers.
> Therefore the document **existed by** `blockTime` according to time that
> no minority could forge.

Hash-linking gives the complementary lower bound (a block cannot precede its
parent), so a document's existence is sandwiched between its block's time
and that of any later block that refers to it.

## Consistency, not absolute time — read this carefully

The theorem bounds the median by the **honest validators' own clock
interval** `[lo,hi]`. It does **not** prove that `[lo,hi]` reflects true
wall-clock time. So the guarantee is a **consistency** property — *a
Byzantine minority cannot drag the timestamp outside the honest cluster* —
**not** an absolute-time **correctness** property.

Concretely, the **NTP attack**: if an adversary shifts the time source that
the honest validators share (a compromised LAN NTP server, a rogue DHCP-
supplied server, route manipulation), *all* honest clocks move together,
`[lo,hi]` shifts wholesale, and a document is finalised with a timestamp
hours off — and the proof still holds, because the honest nodes still agree.
The median resists a corrupted *minority of clocks*, never a corrupted
*shared clock source*. Mitigations (mandatory for any real deployment):

- validators must sit in **different hospitals / different NTP domains** —
  if they all share one LAN clock, the BFT time assumption collapses to a
  single point of failure;
- use **authenticated time** (NTS/GPS) and have validators **cross-check**:
  reject a round whose median deviates from one's own clock beyond a bound;
- treat a Testament's time as a **window `±` the honest clock spread**, not
  a point — that spread is the stated granularity of the guarantee.

## Other assumptions

- **`n ≥ 3f+1`** and **quorum `= n−f`.** Enforced when a validator set is
  adopted (`wellFormedVSet`) and when a block is finalised. With more than
  `f` Byzantine validators, neither agreement nor the time bound holds —
  fundamental to BFT, not a Sanctum limitation.
- **Positive evidence only.** A Testament proves *existence by* a time. The
  *absence* of a Testament proves nothing (it may have been censored).
- **Median-existence is tested, not yet proved**, and the bundled crypto is
  a demo — see [limitations.md](limitations.md) and
  [threat-model.md](threat-model.md).
