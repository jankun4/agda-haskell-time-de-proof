# Threat model and assumptions

Sanctum proves protocol-level properties **on top of** standard
cryptographic and distributed-systems assumptions. It does not re-prove
cryptography. This document states exactly what is assumed and what is
guaranteed.

## Adversary

- **Byzantine validators.** Up to `f` of the `n ≥ 3f+1` validators may be
  arbitrarily malicious: equivocate, lie about their clocks, withhold
  messages, collude. With `n ≥ 3f+1` the remaining `≥ n−f` (honest) form a
  quorum.
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
| **Quorum intersection** | `Proofs/Quorum.agda` | Any two quorums (size `q`, `2q ≥ n+f+1`) share an honest validator — covers the deployment rule `q = n−f` for `n ≥ 3f+1`. |
| **Agreement** | `P6_Harmony` | From the above, two finalised blocks at one height coincide — *assuming* honest validators do not equivocate (that premise is **not yet discharged**; see limitations). |
| **Timestamp soundness** | `Proofs/Time.agda` | Any value with the median property lies within the honest clock interval. (That `medianTime` *has* that property is tested, not yet proved.) |
| **Contract totality** | `Kernel.agda`, `Proofs/Totality.agda` | The executed evaluator is a total Agda function; hence every contract halts and no gas is required. |
| **Reconfiguration safety** | `Proofs/Append.agda` (abstract) + `Ledger.adoptValidatorSet` (concrete) | Every authorised set has an unbroken approval lineage to genesis; the concrete check requires verified, set-and-epoch-bound current-member signatures. |

The exact line between *proved* and *assumed/tested* is in
[limitations.md](limitations.md).

## Operational threats and required procedures (the human is the weakest link)

- **Onboarding / genesis trust (most critical).** A verifier trusts whatever
  validator set it is provisioned with. That provisioning **is** the root of
  trust and must be a **ceremony**: the founding set distributed as a charter
  **signed by every founding hospital**, key fingerprints verified
  out-of-band through *multiple independent channels* (in-person key-signing,
  fingerprints read over the phone, a notarised consortium agreement), and
  air-gapped sites provisioned under **dual control** (two people, two
  hospitals). Never accept a validator set over a single, spoofable channel.
- **Operator/validator diversity.** The `n ≥ 3f+1` honest-majority assumption
  is organisational, not just numerical: validators must run under
  **different operators, vendors, and jurisdictions**, with keys in
  **HSMs/hardware tokens**, so coercing or compromising `f+1` is genuinely
  hard. All validators on one LAN, one vendor, or one admin ⇒ the assumption
  is false.
- **Backdating via authoring.** A signature proves *a key holder asserted X
  at time T*, not that X is true. Make attestation a **four-eyes** action,
  bound `claimedTime` to the validator-median window, and log every operator.
- **Reconfiguration as a slow coup.** Even with the signing fix, a colluding
  current quorum could hand authority to attackers over several hops; the
  continuity checks (overlap, bounded `f` growth) slow this, but governance
  (super-majority of *hospitals*, published change notices) is the real
  defence.

## What is *not* covered

- **Liveness / availability** is not formally proved here; it is the usual
  BFT partial-synchrony result and depends on deployment.
- **Confidentiality.** Sanctum proves *existence and time*, not secrecy.
  Documents are hashed, so the ledger reveals only digests, but metadata
  (who attested, when, how often) is visible to validators. Encrypt
  document contents off-ledger; share only digests. **Salt every digest
  with a high-entropy nonce** kept off-ledger — an unsalted hash of a
  low-entropy clinical form (a template + a name) is brute-forceable, which
  would confirm a specific document's existence to anyone.
- **Proof of absence.** Sanctum is *positive-evidence only*: a Testament
  proves existence-by-time; the absence of one proves nothing (the document
  may have been censored). Add signed submission receipts if "submitted but
  not recorded" must be provable.
- **Key management / HSMs**, rate-limiting, and the gossip layer are
  engineering concerns left to the deployment (the `Node` module is a thin
  in-memory stand-in).
- **Cryptographic security of the demo primitives** — see the warning above.

## Residual trust

A verifier must be provisioned, once, with a trustworthy **genesis
validator set** (or a later set reached by a verifiable lineage). This is
the single root of trust; everything else follows from quorum signatures and
the proofs. For a hospital consortium this is a one-time, out-of-band
onboarding step — but it must be the **signed, multi-channel, dual-control
ceremony** described above, not a casual hand-off, because whoever performs
it defines truth for that verifier forever.

If you cannot run that ceremony, or you are willing to trust one
timestamping authority, a plain RFC-3161 TSA may serve you better than
Sanctum — see [limitations.md](limitations.md) §5.
