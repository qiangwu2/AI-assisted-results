# Inverse Freezing in the Ghatak–Sherrington Model

[GitHub](https://github.com/qiangwu2/AI-assisted-results/tree/main/ghatak-sherrington-inverse-freezing) · [PDF](https://github.com/qiangwu2/AI-assisted-results/blob/main/ghatak-sherrington-inverse-freezing/gs-inverse-freezing.pdf) — 21 pages, revised October 7, 2026.

## Result and scope

For the zero-magnetic-field Ghatak–Sherrington model with spins in $\{0,\pm1\}$, the manuscript establishes a nonempty open set of positive crystal fields for which decreasing temperature gives three regimes:

- Paramagnetism at sufficiently high temperature.
- Replica-symmetry breaking on an intermediate temperature interval.
- Exact zero-overlap paramagnetism at sufficiently low temperature, with every global maximizing active-spin density tending to zero.

Each phase conclusion holds at **every global maximizing density**. Replica-symmetry breaking means that every constrained Parisi minimizer at such a density is not a single atom. The conclusions concern the thermodynamic variational problem; they do not separately identify the full unperturbed Gibbs overlap distribution.

This is an existential inverse-freezing theorem. It does not determine the complete phase diagram, transition curves, transition orders, or the number of replica-symmetry-breaking steps.

## Proof idea

At low temperature, a Gaussian comparison bounds the interaction energy at fixed active-spin density. The crystal-field penalty forces all maximizing densities into a dilute window, where Panchenko's exact paramagnetic criterion applies.

At intermediate temperature, a Gaussian-channel inequality identifies an exact paramagnetic density edge. Uniqueness, compactness, and differentiability of the constrained Parisi minimum transfer a positive density derivative to the true constrained pressure, producing a branch above every paramagnetic branch. Strict Gaussian Poincaré inequality and an admissible one-step variation exclude every positive-overlap replica-symmetric minimizer. A strict pressure gap makes the conclusion persist on an open temperature interval.

The manuscript cites its external inputs and discusses related work, including Panchenko's constrained Parisi formula, Chen's convexity and PDE results, and Albanese–Barra–Cirillo's interpolation formulas under prescribed RS or one-step RSB overlap assumptions.

## Development and revision history

- **February 2026:** Heejune and I began this project.
- **August 3, 2026:** a recovered 22-page manuscript dated this day provided the basis for the current revision.
- **October 7, 2026:** repeated AI audits and revisions produced the 21-page manuscript included here. The final revision incorporates the subsequent audit report's literature comparison and precision corrections and uses the title *Inverse Freezing in the Ghatak–Sherrington Model*.

The February entry records the start of the joint project; the later dates identify manuscript editions and revisions. An exact original AI prompt and a complete count of the original generation rounds have not been recovered.

## Human contribution and AI assistance

This work began as a joint project with Heejune in February 2026. AI subsequently played a significant role in developing and revising the manuscript and in auditing the proofs. The project is therefore included in the AI-assisted collection.

## Audit status

Several rounds of AI review checked the low-temperature comparison, the exact paramagnetic edge, the density-envelope argument, exclusion of positive-overlap replica symmetry, and the density endpoints. The revision corrected the additive constant in the comparison with Chen's functional, supplied the exact-density/shrinking-window equivalence proof, and clarified endpoint, regularity, and averaging conventions. A further audit checked the revised argument and prompted the final literature and precision edits.

Within the scope of these reviews, **no remaining substantive mathematical error or essential gap was identified**. The final PDF compiled successfully, and the affected rendered pages were inspected. The main theorem was preserved through the revisions.

This project has **no accompanying Lean formalization**. AI audits do not guarantee complete correctness or the absence of errors and gaps. Please use the results with caution.

## Files

- [gs-inverse-freezing.pdf](gs-inverse-freezing.pdf) — the updated 21-page manuscript.
- `README.md` — result, development history, and audit summary.
