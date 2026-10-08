# Lean 4 formalization of the spin-glass manuscript

**Status: partial. This project does not prove the paper's main theorem.**

This is a source-checked collection of mathematical components, not an end-to-end certificate. It contains no placeholder proofs or added axioms for the paper's claims. The remaining obligations are listed in [COVERAGE.md](COVERAGE.md).

The project uses Lean **4.32.1** and mathlib commit **520045ab14e26149ee970e2e617ca04b09bde5d6**. The local `lean-toolchain` and `lake-manifest.json` pin the toolchain and dependencies; no global Lean setting was changed.

## Check the proofs

With Lean/Elan available, restore the pinned dependencies and check the sources:

```sh
./scripts/get_cache.sh
./verify.sh
```

If the dependency cache is already present, only `./verify.sh` is needed.

This recompiles every mathematical module, checks that no module was omitted from the aggregate import, runs the independent empty-case checks in `SemanticChecks.lean`, and runs `Audit.lean`. The audit requires named endpoints from every component and inspects the transitive axiom dependencies of every declaration in the `SpinGlass` namespace, including private declarations. It accepts only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. Any `sorryAx`, new mathematical axiom, or compiler-trust axiom fails the audit.

For a fresh checkout, `scripts/get_cache.sh` retrieves the pinned dependency cache for the imports actually used by this project. Network access and several gigabytes of free disk space may be needed. The ZIP excludes generated caches and downloaded dependencies. Temporary dependency build caches were cleared after the recorded verification because the machine was nearly out of disk space; the source, pinned dependency metadata, and verification logs are preserved.

`audit-self-check.log` records that deliberately introduced custom axioms, public placeholder proofs, and private placeholder proofs were all rejected. Reproduce these negative controls with `./verify-audit.sh` after `./verify.sh`; the generated invalid fixtures are deleted automatically and are not part of the mathematical sources.

`verification.log` records the source-checking run. `axiom-audit.log` contains the axiom-audit portion of that final run. Counts in those logs include Lean-generated declarations and must not be interpreted as a count of paper theorems proved.

## What the files establish

- `Expansion.lean` and `Partition.lean`: finite spin averaging, the even-hypergraph expansion, positivity, the exponential partition-function normalization, and uniform-sign moment identities.
- `Mobius.lean` and `LocalCube.lean`: exact-support inclusion–exclusion, its induced-interaction spin-polynomial identity, and equality of ambient and local spin averages.
- `Degree.lean`, `Support.lean`, and `Algebra.lean`: degree reduction, finite hypergraph counting bounds, and square-zero color monomials.
- The `ReverseHypercontractivity*`, `BilinearTwoPoint`, `Tensorization`, `ReverseHolder`, `NoiseKernel`, and `NoiseMomentReduction` modules prove finite-cube reverse hypercontractivity from an elementary two-point argument, through tensorization and duality. Its analytic conclusion is not assumed.
- `LowerTail.lean`, `Noise.lean`, and `FiniteLowerTail.lean`: moment interpolation, exponent identities, the actual noise operator, and its negative-moment and finite-probability lower-tail bounds.
- `ConditionalSpinGlass.lean`: those bounds applied to the actual normalized exponential partition function with fixed magnitudes and uniform edge signs. The right-hand side is the explicitly computed inflated even-graph mass. Integration over arbitrary symmetric disorder magnitudes and a uniform mass bound are still missing.
- `RandomCoefficient.lean`: exact truncation error and integrated squared-coefficient error identities in the explicitly specified independent-sign model.
- `GraphicalMass.lean`: the exact graphical-mass spin-average identity and its elementary exponential-moment upper bound, including the actual pure-p interaction family. The uniform entropy estimate remains unproved.
- `ErrorReduction.lean` and `AccuracyBudget.lean`: Chebyshev/logarithm error reduction and the paper's final parameter substitution. Their probability conclusions explicitly assume upstream lower-tail and mean-square estimates.

Most mathematical specifications use exact real numbers and are noncomputable Lean definitions. They are not an implementation of the paper's efficient algorithm or a proof of its operation count.

A successful Lean check establishes the encoded statements relative to the listed foundational axioms and Lean's trusted implementation. It does not establish omitted theorems or automatically certify that a specification captures every claim of the manuscript. Independent semantic reviews are included in `SEMANTIC_AUDIT.txt` and `ADDITIONAL_SEMANTIC_AUDIT.txt`. The former retains historical findings followed by explicitly superseding follow-ups; `COVERAGE.md` is the current scope statement.
