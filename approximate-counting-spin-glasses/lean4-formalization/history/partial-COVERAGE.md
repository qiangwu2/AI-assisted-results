# Coverage against the submitted paper

**The requested end-to-end formalization is not complete. The main results remain unverified by Lean.**

The theorem numbers below refer to the original PDF, *Arbitrary-Accuracy Counting for Pure Ising Spin Glasses by Support Resummation*. A proof of a local ingredient does not count as a proof of the result that uses it.

| Paper result or ingredient | Current formal status |
|---|---|
| Proposition 2.1: finite graphical identity | Proved for arbitrary finite indexed interactions, including the exponential/cosh/tanh normalization and strict positivity. The `p`-subset spin polynomial is explicitly specialized. |
| Lemma 4.1: disorder orthogonality and random coefficients | Uniform independent-sign first/second moments, exact retained-family error, and the integrated random-coefficient identity in an explicitly independent-sign model are proved. Deriving that model from arbitrary symmetric real disorder and reducing the squared weights to powers of the common disorder second moment remain unformalized. |
| Lemma 4.2 and Proposition 4.3: auxiliary exponential moment, graphical mass and edge tail | The finite mass/overlap identity and comparison with the explicit exponential moment are proved, including the coefficient restriction needed for the product inequality. The uniform entropy bound, the resulting constant, and the edge tail are not formalized. |
| Lemma 4.4: reverse hypercontractivity | **Proved** for every finite Boolean cube and positive function, in both the paper’s reverse-norm form and its negative-moment form. The proof establishes the two-point inequality, bilinear transfer, tensorization, and duality; no reverse-hypercontractivity premise remains. |
| Proposition 4.5: non-Gaussian lower tail | The finite-cube negative moment and lower tail are proved with the specified exponent. Their specialization to the actual normalized exponential partition function for fixed magnitudes is proved, with the exact inflated graphical mass on the right. Random magnitude integration, the uniform mass constant, and the coupling cutoff probability remain unformalized. |
| Proposition 5.1: exact-support extraction | Weighted exact-support Möbius inversion and its bridge to the actual induced-interaction spin polynomial are proved. Equality of ambient and local spin averages is proved through an explicit cube-splitting equivalence. The operation count remains unformalized. |
| Lemma 5.2 and Proposition 5.3: higher-order support mass and tail | The degree/support incidence inequality is proved. Enumeration, mass estimates, and tail bounds are not formalized. |
| Lemma 6.1 and Proposition 6.2: SK branching mass and truncation | The branching incidence bound is proved. Pairing enumeration, Gaussian integral bounds, and truncation estimates are not formalized. |
| SK degree/color algebra used in Section 7 | Degree reduction is a genuine six-state commutative additive monoid. Color-monomial multiplication and its nilpotence are proved. The full coefficient algebra, basis, and dimension are not formalized. |
| Propositions 7.1–7.3 and Corollary 7.4 | Primitive decomposition, path/cycle recurrences, exact evaluation, color probabilities, estimator unbiasedness/variance, and algorithm cost are not formalized. |
| Lemma 8.1 and Theorem 3.1 | Uniform cutoff selection, the complete approximation algorithm, its MSE, and polynomial arithmetic cost are not formalized. |
| Final reduction in Theorem 1.1 | The logarithm estimate, event inclusion, Chebyshev bound, and accuracy-budget algebra are proved. The required lower-tail and MSE estimates remain hypotheses. |
| Theorem 1.1 and Corollaries 1.2–1.3 as complete results | **Not proved.** No complete costed algorithm or asymptotic disorder-tail result is provided. |

## Critical remaining proof chain

1. Formalize the probability model: independent symmetric variance-one real couplings, sign/magnitude representation (including zero atoms), measurability, integrability, and joint algorithm randomness.
2. Prove the uniform inflated graphical mass and its edge tail.
3. Apply the proved finite-cube negative-moment and lower-tail results to the random coupling-magnitude distribution, including the cutoff event and its complement.
4. Prove both support/branching mass estimates, truncation bounds, and the cost of local-cube enumeration.
5. Implement a mathematical specification of the actual resummation/colouring algorithm, prove that its recurrences evaluate the retained graph families, and prove the coloring error bounds.
6. Give operation-count semantics and prove the uniform parameter selection, exact-enumeration branch, and polynomial bound over the full accuracy range.
7. Instantiate the proved final reduction with that algorithm and derive the moment corollaries.

These obligations cannot be replaced by axioms or premises of a theorem described as end-to-end verification. In particular, `logOutput_probability_with_paper_parameters` is intentionally a **conditional reduction**, not a renamed main theorem.

The manuscript cites Mossel–Oleszkiewicz–Sen, [Corollary 1.11](https://arxiv.org/pdf/1108.1210), for reverse hypercontractivity. This project proves the finite-cube case needed by the manuscript directly, rather than treating that citation as a formal axiom.
