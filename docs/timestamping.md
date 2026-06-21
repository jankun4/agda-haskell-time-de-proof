# Trustworthy time without an authority

The core promise is: *a finalised document existed no later than time T*,
where T is trustworthy even though no single clock is trusted and there is
no external time source.

## The idea

A block's timestamp is **not** set by its proposer. It is the **median** of
the clock readings of the ≥ 2f+1 validators that signed the block. Each
validator contributes its own clock as part of its vote
(`Consensus.Vote.voteClock`); the agreed `blockTime` is `medianTime` of
those samples (`Core.medianTime`, mirrored from `Kernel.medianTime`).

## Why the median is safe

Suppose at most `f` of the `2f+1` signers are Byzantine (the BFT
assumption), and the honest validators' clocks all lie in some real
interval `[lo, hi]` (they are roughly synchronised — say within a few
seconds). Then:

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

## Honesty about assumptions

- **Clock synchrony of honest nodes.** We assume honest validators are
  loosely synchronised (the `[lo,hi]` interval). This is standard and easily
  met on a hospital LAN with NTP; the *width* of `[lo,hi]` is the
  granularity of the guarantee.
- **`n ≥ 3f+1`.** Enforced when a validator set is adopted
  (`wellFormedVSet`). With more Byzantine validators than `f`, neither
  agreement nor the time bound holds — this is fundamental to BFT, not a
  Sanctum limitation.
- **Cryptography.** Digests and signatures are assumed collision-resistant
  and unforgeable; see [threat-model.md](threat-model.md).
