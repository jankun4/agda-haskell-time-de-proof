# Limitations, assumptions, and what is *not* yet proven

This project is deliberately honest about the gap between what is
machine-checked and what is asserted. This page is the single source of
truth for that gap. (It was written up after an adversarial internal
review; several items below were found by deliberately attacking the
system.)

## 1. The proofs and the running code are connected by hand, not mechanically

The node's verified core (`haskell/src/Sanctum/Core.hs` — the quorum rule,
median, contract evaluator) is a **faithful hand-transcription** of the
Agda kernel (`agda/src/Sanctum/Kernel.agda`), and `scripts/extract.sh`
**does** generate Haskell from that kernel via MAlonzo and runs it. But the
node currently links the hand-written `Sanctum.Core`, **not** the extracted
module. So "what runs is what was proven" holds *by construction and by
test*, not *by the build graph*.

- **Mitigation in place:** CI runs both `check.sh` (the proofs) and
  `extract.sh` (generation), the property tests in `test/Spec.hs` assert
  the proven properties hold of `Core`, and `Core`/`Kernel` are kept
  line-for-line aligned.
- **Roadmap:** build `haskell/gen` into the node behind a cabal flag, or
  prove `Core ≡ Kernel` once and for all.

## 2. Two theorems are not yet wired all the way to the executable

- **Median existence.** `Proofs/Time.agda` proves: *if* a value has the
  median property (`IsMedian`), it lies within the honest clock interval.
  We do **not** yet prove that the executable `medianTime` (insertion sort
  + middle element) *produces* a value satisfying `IsMedian`. The
  algorithm is standard and tested, but the bridge lemma
  `IsMedian f (medianTime ts) ts` is future work.
- **No honest equivocation.** `P6_Harmony.no-two-conflicting` derives
  "two finalised blocks are equal" from a *hypothesis* that an honest
  validator never signs two different blocks at one height. Discharging
  this requires modelling a per-height voting record; today it is an
  assumed protocol rule, not a proved one. (The quorum-intersection core
  it rests on **is** fully proved.)
- **Reconfiguration lineage.** `Proofs/Append.Reconfiguration` proves the
  authority lineage over an *abstract* `Approves` relation. The concrete
  `Approves` is `Ledger.adoptValidatorSet` (which now verifies signatures —
  see the threat model); tying the abstract theorem to the concrete
  `Chain`/`epoch` is future work.

## 3. The bundled cryptography is a DEMO

`haskell/src/Sanctum/Crypto.hs` ships an FNV-style digest (**not**
collision-resistant) and a textbook Schnorr signature over a 61-bit prime
(**toy** parameters), plus deterministic seed-based key generation. This is
intentional: the project builds and runs with zero external dependencies,
offline. It is **not secure**. Before any real use:

- replace the digest with BLAKE2b/SHA-256 and the signature with Ed25519
  (e.g. `cryptonite`) — the `Crypto` module boundary is exactly the
  abstract interface the proofs assume, so nothing else changes;
- generate keys with a CSPRNG / HSM, never from `mkHospital name seed`.

See [threat-model.md](threat-model.md) for the full register.

## 4. What Sanctum proves about *time* — and what it does not

A finalised block's time is the **median of validator clocks**. The proof
guarantees this median lies within the honest validators' clock interval —
a **consistency** property (a Byzantine minority cannot move it), **not**
an absolute-wall-clock **correctness** property. If the honest validators'
shared time source (e.g. a single LAN NTP server) is wrong or attacked, the
timestamp is wrong *and the proof still holds*. See
[timestamping.md](timestamping.md) for the NTP attack and the required
mitigation (independent, cross-checked time sources across hospitals).

Sanctum also proves only **positive existence**: a Testament proves a
document existed by a time. The **absence** of a Testament proves nothing
(a document may have been censored, not non-existent). Do not read
"no record" as "never existed."

## 5. When you may not need Sanctum at all

If you are willing to trust a single timestamping authority, **RFC-3161**
TSAs with signed Merkle checkpoints are simpler, audited, and court-
recognised. Sanctum earns its extra machinery (BFT consensus,
reconfiguration) only when **no single timestamper is trusted**, the
parties are mutually distrusting, and verification must work **offline /
air-gapped** within the consortium. If those don't all hold, prefer the
simpler tool, or anchor periodic Sanctum checkpoints into an external chain
or a TSA.

## 6. Out of scope (engineering, not proofs)

Networking, gossip, persistence, key custody/HSMs, rate-limiting, and a
runnable light-client lineage verifier are **not implemented** — the `Node`
module is an in-memory stand-in. Liveness/availability is the usual BFT
partial-synchrony result and is not formally treated here.
