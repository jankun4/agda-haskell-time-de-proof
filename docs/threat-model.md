# Threat model and assumptions

Sanctum proves protocol-level properties **on top of** standard
cryptographic and distributed-systems assumptions. It does not re-prove
cryptography. This document states exactly what is assumed and what is
guaranteed.

## Adversary

- **Byzantine validators.** Up to `f` of the `n ≥ 3f+1` validators may be
  arbitrarily malicious: equivocate, lie about their clocks, withhold
  messages, collude. The remaining `≥ 2f+1` are honest.
- **Network.** Messages may be delayed, reordered, or dropped; the network
  may partition. Sanctum's *safety* (agreement, no forged history) does not
  depend on timing. Liveness (new blocks getting finalised) requires enough
  honest validators to be connected and roughly synchronised — the usual
  partial-synchrony assumption.
- **Outside world.** Assumed absent. Some sites are air-gapped. There is no
  trusted external clock or timestamping service.

## Cryptographic assumptions (the interface)

Modelled abstractly in Agda (`P2_Distinction.Crypto`) and realised in
`haskell/src/Sanctum/Crypto.hs`:

1. **Collision-resistant digest.** It is infeasible to find `x ≠ y` with
   `digest x = digest y`. This is what makes a `Fact` a faithful witness of
   a document and makes Merkle inclusion and hash-linking tamper-evident.
2. **Unforgeable signatures.** Without the secret key, it is infeasible to
   produce a signature that `verify` accepts under the corresponding public
   identity. This is what makes an `Attestation` attributable and a quorum
   certificate meaningful.

> ⚠ **The bundled implementation is a DEMO.** `Crypto.hs` uses an FNV-style
> digest (not collision-resistant) and a textbook Schnorr signature over a
> 61-bit prime (toy parameters). They are dependency-free so the project
> builds and runs offline. **For production, replace them** with BLAKE2b or
> SHA-256 and Ed25519 (e.g. `cryptonite`). The module boundary is exactly
> the abstract interface, so no other code changes — and none of the proofs
> change, because they assume only the interface.

## What is proved (given the assumptions)

| Property | Where | Statement |
|----------|-------|-----------|
| **Append-only** | `Proofs/Append.agda` | A prefix's blocks are byte-for-byte preserved by any later extension; genesis is fixed. |
| **Agreement** | `Proofs/Quorum.agda` + `P6_Harmony` | Any two quorums share an honest validator; with no honest equivocation, two finalised blocks at one height are identical — no forks. |
| **Timestamp soundness** | `Proofs/Time.agda` | The median block time lies within the honest validators' clock interval. |
| **Contract totality** | `Proofs/Totality.agda` | Every on-chain program halts; hence no gas is required. |
| **Reconfiguration safety** | `Proofs/Append.agda` | Every authorised validator set has an unbroken approval lineage to genesis. |

## What is *not* covered

- **Liveness / availability** is not formally proved here; it is the usual
  BFT partial-synchrony result and depends on deployment.
- **Confidentiality.** Sanctum proves *existence and time*, not secrecy.
  Documents are hashed, so the ledger reveals only digests, but metadata
  (who attested, when, how often) is visible to validators. Encrypt
  document contents off-ledger; share only digests.
- **Key management / HSMs**, rate-limiting, and the gossip layer are
  engineering concerns left to the deployment (the `Node` module is a thin
  in-memory stand-in).
- **Cryptographic security of the demo primitives** — see the warning above.

## Residual trust

A verifier must be provisioned, once, with a trustworthy **genesis
validator set** (or a later set reached by a verifiable lineage). This is
the single root of trust; everything else follows from quorum signatures and
the proofs. For a hospital consortium this is a one-time, out-of-band
onboarding step (e.g. a signed founding charter).
