# Roadmap — beyond perfection

This file is the project's forward motion: the transcendent directions the
review council's Agent 7 surfaces, triaged by the arbiter (Agent 1). The
rule is *transcendence proposes, truth disposes* — radical ideas are
recorded here and adopted only when net-positive, never as a big-bang
rewrite of a working, verified system.

## Near-term (close the seams the proofs sit on)

1. **Median-existence bridge** — prove `IsMedian f (medianTime ts) ts` so the
   time-soundness theorem applies to the value the node actually computes,
   and restate `median-bound` for `k ≥ 2f+1` samples (closes the frame
   mismatch in `limitations.md §2`). *Pure Agda, lowest risk, highest
   credibility.*
2. **Discharge no-equivocation** — model a per-height voting record and
   derive `no-two-conflicting` instead of assuming it.
3. **`Core ≡ extracted-Kernel` guard** — build `haskell/gen` into the test
   suite behind a cabal flag, or add a property test, so CI catches any
   drift between the hand-mirror and the proved kernel.
4. **Tie abstract `Approves` to concrete `adoptValidatorSet`** and the
   `Chain`/`epoch` so the lineage theorem is about the deployed chain.

## Mid-term (raise the guarantees)

5. **One language, proved and run (agda2hs).** Make the proved-total `eval`
   from `Proofs/Totality.agda` the *executed* contract evaluator by
   extracting it with agda2hs (readable Haskell), retiring the first-order
   `Kernel.Expr`/`Core.runContract`. Staged: extract behind a flag, prove it
   passes the existing tests against the mirror, then flip the default.
6. **Transaction-context validators.** Extend the calculus with a typed
   `TxContext` (block time, Merkle root, signer set) so contracts express
   real policies ("accept iff signed by the issuing hospital before T") —
   totality preserved trivially. Turns the toy into a gasless EUTXO-style
   validator platform.
7. **Verifiable external time.** Add authenticated time at the leaves
   (roughtime/NTS, ≥2 independent sources) plus periodic checkpoint
   anchoring into an external medium, upgrading time from *consistency*
   toward *correctness*. (VDFs are the wrong tool — they measure elapsed
   time, not wall-clock.)
8. **Signed founding charter + light-client lineage walker.** Make the
   genesis trust anchor a signed object the code verifies, and ship a
   runnable verifier that walks genesis→epoch reconfigurations so air-gapped
   sites can check *which* validator set to trust. (Closes threat-model
   T1/T4.)
9. **Salted commitments.** Add an off-ledger nonce to document digests so
   low-entropy clinical forms cannot be confirmed by brute force.

## Long-horizon (research-grade; bet only after the foundation is sound)

10. **Threshold/BLS quorum certs** — collapse a quorum into one O(1)
    signature; precondition for succinct light clients.
11. **Succinct light-client proofs** — a recursive SNARK/STARK proving the
    whole genesis→head lineage in constant size (the `Append.agda` lineage
    relation is the circuit spec).
12. **Zero-knowledge attestation/inclusion** — prove a document was
    timestamped without revealing its digest or metadata (a regulatory
    unlock for HIPAA/GDPR-sensitive records).
13. **Accountable BFT + DAG substrate** — cryptographic fork evidence that
    turns equivocation from an *assumption* into a *punishable, provable*
    event; a DAG of attestations for concurrent commits.

## The eighth principle — Reflection (P7)

The natural successor to the seven-principle stack: represent the validator
set, quorum rule, and fault budget as **on-ledger, verified data that
contracts can read and reason about**. Principles 0–6 build the object;
Principle 7 lets the object describe and check itself — a system that
carries its own verification as runtime state. Builds directly on (6).
