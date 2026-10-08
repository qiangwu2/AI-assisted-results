# Verification scope

This note accompanies **Arbitrary-Accuracy Counting for Pure Ising Spin Glasses**. It summarizes the preserved verification records and the review performed on 7 October 2026. It is not an unconditional certification of the manuscript or an implementation benchmark.

## Mathematical and computational scope

The proved counting guarantees concern pure, distinct-index, zero-field Ising models at a fixed strict margin below the stated graphical threshold. The algorithm is deterministic for interaction order p ≥ 3 and randomized for SK (p = 2). Accuracy is probabilistic over the disorder and, for SK, the algorithm's colors. Each requested parameter choice is specified independently of the disorder; the theorem does not assert one simultaneous success event for every request.

The cost model counts exact real arithmetic, elementary functions, comparisons, indexing, input access and finite random draws. It does not establish bit complexity, numerical stability or practical running time. The mathematical review covered the graphical truncation, finite evaluators, lower-tail argument, accuracy conversion and operation bounds. Small-instance exact checks supplemented that review; they do not replace the proofs.

## Lean coverage

The companion development formalizes the pure zero-field algorithms, their logarithmic error guarantees and complete operation counts. Its physical-input endpoints are:

- `SpinGlass.PhysicalInput.higher_end_to_end`
- `SpinGlass.PhysicalInput.sk_end_to_end`

The input is indexed by unordered p-element subsets. These endpoints estimate the logarithm of the actual exponential spin sum. They retain the model, disorder, temperature and accuracy hypotheses. Graphical mass bounds, evaluator correctness, mean-square bounds, lower-tail bounds and runtime guarantees are proved intermediate results, not extra analytic assumptions of the final endpoints.

The four `SpinGlass.MainCorollaries` endpoints `higher_fourth_end_to_end`, `higher_real_moment_end_to_end`, `sk_fourth_end_to_end` and `sk_real_moment_end_to_end` give the logarithmic moment consequences. The manuscript obtains relative partition-function error by the explicit accuracy substitution and exponentiation in its proof. Appendix A.4 describes the correspondence between formal definitions and the manuscript.

**The proposed finite-mixture and weak-field extensions in Section 5 are not formalized and are not proved counting theorems.** Bibliographical comparisons are also outside Lean coverage.

## Recorded build and subsequent checks

The preserved full source-verification run is dated **6 October 2026**. It used Lean **4.32.1** and mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`, rebuilt 159 mathematical modules and audited 3,061 theorem declarations / 4,084 total declarations, including public and private declarations in the `SpinGlass` namespace. The allowed axioms were `propext`, `Classical.choice` and `Quot.sound`. The audit reported no unfinished proofs or added mathematical axioms; negative controls tested rejection of a custom axiom and unfinished public and private proofs.

On **7 October 2026**, the archive and manifest hashes were checked. The physical-input theorem and main-corollary source files were freshly compiled against cached pinned dependencies; semantic checks, the namespace axiom audit and its three negative controls also passed. This was **not** a fresh rebuild of all 159 modules or an independent line-by-line review of the entire formal development.

No new Lean check was performed while preparing this publication note. The full-build claim refers to the recorded 6 October run; the targeted-check claim refers to the earlier 7 October review.

## Reproduction and limits

The companion is available as the browsable [lean4-formalization/](lean4-formalization/) folder. Its 192 files were extracted byte for byte from the `Lean4_Formalization.zip` archive identified in Appendix A.4, whose SHA-256 was:

```text
c3eee020900060c606be30c986d626b350f2a55d56dc3387b7b5c491e79fff7c
```

The ZIP has been replaced by the extracted folder; the original hash above identifies the preserved source snapshot. This packaging change does not constitute a new Lean build. [SHA256SUMS.txt](SHA256SUMS.txt) records hashes of the extracted files and the manuscript PDF, and the preserved [verification-status.json](lean4-formalization/verification-status.json) records source, configuration and log hashes from the verification run.

From the `lean4-formalization/` directory, restore the pinned dependencies using `./scripts/get_cache.sh`, then run `./verify.sh` and `./verify-audit.sh`. See the [formalization README](lean4-formalization/README.md) for details. Dependency restoration requires network access and storage.

Lean checks encoded propositions relative to its foundations and trusted checker. Connecting those propositions to the manuscript's definitions and claims additionally requires the correspondence review. The available evidence does not certify floating-point execution, an arbitrary later revision, or the proposed extensions.
