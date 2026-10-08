# Lean 4 formalization of arbitrary-accuracy spin-glass counting

This project proves the manuscript's counting guarantee and a polynomial total-operation bound for the same explicitly specified algorithms: deterministic support enumeration for fixed **p ≥ 3**, and randomized color-based evaluation for **SK, p = 2**. The final endpoints do not assume the main theorem, reverse hypercontractivity, a graphical-mass estimate, a mean-square estimate, graph-decomposition correctness, or a runtime bound.

The final certificate and exact source hashes are in [verification-status.json](verification-status.json). [COVERAGE.md](COVERAGE.md) maps the paper to the formal modules and explains the scope. The previous incomplete checkpoint is preserved under `history/`; it is not the current verification result.

## Main endpoints

- [`SpinGlass.HigherOrderTotalCost.end_to_end`](SpinGlass/HigherOrderTotalCost.lean): higher-order counting accuracy and total operation cost.
- [`SpinGlass.SKTotalCost.end_to_end`](SpinGlass/SKTotalTheorem.lean): SK counting accuracy and total operation cost.
- [`SpinGlass.PhysicalInput.higher_end_to_end` and `sk_end_to_end`](SpinGlass/PhysicalInputTheorems.lean): the same full guarantees directly on iid arrays indexed only by actual physical p-edges.
- [`SpinGlass.MainCorollaries`](SpinGlass/MainCorollaries.lean): both fourth-moment typical-instance corollaries and both real higher-moment polynomial-confidence corollaries, with the costed outputs.

For each fixed admissible p and temperature bound B, the main endpoints prove that one constant C > 0 works for all N ≥ p, β ∈ [0,B], ε ∈ (0,1), and δ ∈ (0,1):

```
P(|algorithm output − log Z_N| > ε) ≤ τ_N + δ
operations ≤ C · N^C · ε^(−C) · δ^(−C).
```

The disorder law is any symmetric real probability law with an integrable second moment equal to one. SK probability includes independent internal color randomness. The algorithm and its cost constants do not depend on the disorder law. The separate disorder-tail term τ_N remains present under the second-moment hypothesis; the moment corollaries establish its decay under their additional assumptions.

The formal target is the logarithm of the **unnormalized** partition function, with distinct unordered p-element interactions and scaling β/sqrt(N^(p−1)). Uniformity means that the same bounds hold for every specified admissible β and ε. It does not assert a single simultaneous success event over all adaptively selected requests.

## What the operation theorem means

The paper uses an exact-real arithmetic model with elementary-function oracles and finite uniform samples. The formalization gives value specifications, explicit saved-table/scalar loops, concrete finite generators and comparison procedures, and proved upper bounds for their schedules. It charges arithmetic, elementary functions, comparisons, finite indexing, cached input lookups, color draws, and the integer searches used to compute floor and ceiling cutoffs. Cached values are shared before they are reused.

This is a mathematical algorithm certificate in that model. It is not a floating-point implementation, a bit-complexity bound, a wall-clock prediction, or a bound on Lean's compiled evaluator. Real comparison and elementary-function oracles are part of the stated model. The fixed p- and B-dependent design constants belong to the fixed algorithm.

The proofs include two refinements that matter for cost: candidate subsets are produced by a pruned bounded-cardinality generator; the SK algorithm samples only the requested candidate/repetition/outside-vertex coordinates. The large ambient random tape is a mathematical probability space, and a proved marginal-law identity identifies it with the actual finite sampler.

## Reproduce the verification

The project pins Lean **4.32.1** and mathlib commit **520045ab14e26149ee970e2e617ca04b09bde5d6**. No global Lean default needs to change.

With Elan/Lean, Python 3, and the pinned dependency cache available:

```sh
./verify.sh
./verify-audit.sh
```

For a new checkout, first run `./scripts/get_cache.sh` to restore the dependencies. The archive excludes `.lake` and downloaded dependencies, so that step can require several gigabytes and network access.

`verify.sh` recompiles **every mathematical source**, in dependency order. Independent branches can compile concurrently (default 3; set `LEAN_VERIFY_JOBS=1` for serial verification). It rejects an omitted or duplicate module, checks the semantic boundary examples, and checks the axiom dependencies of every public and private declaration in the `SpinGlass` namespace. It also rejects a source tree that changes during the run.

The only allowed axioms are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. A `sorry`, an added mathematical axiom, or a compiler-trust axiom fails the audit. `verify-audit.sh` independently tests that deliberately inserted custom axioms and both public and private placeholder proofs are rejected. Those invalid fixtures are deleted automatically.

`verification.log`, `axiom-audit.log`, and `audit-self-check.log` record the final runs. Declaration counts include Lean-generated declarations; they are not counts of manuscript theorems.

## Reading the certificate accurately

The kernel checks the encoded propositions. The manuscript-to-definition correspondence and the intended operation model also received independent semantic review, recorded in `SEMANTIC_AUDIT.txt`. Successful verification is substantially stronger than a judgement that a proof “appears correct,” but it is still a certificate of precise formal statements relative to Lean's foundations and trusted checker. Bibliographic comparisons, historical assertions, and reported external regression runs are not mathematical theorems certified by this project.
