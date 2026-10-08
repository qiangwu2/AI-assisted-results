# AI-assisted-results

AI-assisted proofs and mathematical results.

This repository collects manuscripts developed and revised with AI assistance. Each project includes its manuscript PDF and a description of its verification scope.

## Human contribution and AI assistance

These works build, to varying degrees, on my previous research. I contributed mathematical ideas and insights to guide the AI's proof development and checked the underlying proof ideas. I am more confident about the correctness of these results, though potential minor errors or gaps may remain.

## Projects

| Project | Manuscript | Revision |
| --- | --- | --- |
| [Mixed p-spin free-energy fluctuations throughout the high-temperature regime](https://github.com/qiangwu2/AI-assisted-results/tree/main/mixed-pspin-high-temperature-fluctuations) | [PDF](mixed-pspin-high-temperature-fluctuations/mixed-pspin-fluctuations.pdf) | 7 October 2026 |
| [Critical free-energy fluctuations of the pure Ising p-spin model](https://github.com/qiangwu2/AI-assisted-results/tree/main/pure-pspin-critical-fluctuations) | [PDF](https://github.com/qiangwu2/AI-assisted-results/blob/main/pure-pspin-critical-fluctuations/pure-pspin-critical-fluctuations.pdf) | 8 October 2026 |
| [Joint MPLE fluctuations in zero-field SK](https://github.com/qiangwu2/AI-assisted-results/tree/main/joint-mple-fluctuations) | [PDF](joint-mple-fluctuations/joint-mple-fluctuations.pdf) | 7 October 2026 |
| [Approximate counting for pure Ising spin glasses](https://github.com/qiangwu2/AI-assisted-results/tree/main/approximate-counting-spin-glasses) | [PDF](approximate-counting-spin-glasses/approximate-counting.pdf) | 7 October 2026 |

The dates above identify the current manuscript revisions, not the first discovery or generation of the results.

## Review and verification

The proofs have undergone several rounds of AI review, which identified no obvious remaining substantive errors or gaps in the stated results. Complete correctness is not guaranteed; please use the results with care and check the arguments independently.

Verification differs by project. The counting project includes a Lean companion for its pure zero-field results; its proposed mixed-model and weak-field extensions are outside that formalization. No Lean formalization of the revised mixed p-spin, joint MPLE, or critical pure p-spin manuscript is included. Each project's README, together with VERIFICATION.md where present, explains the assumptions, coverage and limits.
