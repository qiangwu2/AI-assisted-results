# Arbitrary-accuracy counting for pure Ising spin glasses

[Read the manuscript](approximate-counting.pdf) · [Verification scope](VERIFICATION.md)

**Author:** Qiang Wu  
**Email:** qiangw.math@gmail.com  
**Revision:** 7 October 2026 · 32 pages · 25 references

These files are the revised manuscript prepared on the date above. This date identifies the revision, not the first discovery or generation of the result.

## Result and scope

The manuscript gives exact-real-operation counting algorithms for pure, distinct-index, zero-field Ising spin glasses at a fixed margin below their graphical second-moment threshold. The algorithms are deterministic for interaction orders at least three and randomized for SK. The bounds track requested accuracy, disorder confidence and the coupling tail.

These are exact-operation bounds, without a finite-bit complexity or numerical-stability guarantee. Success is for each request specified independently of the disorder. Section 5 describes ideas for finite mixtures and vanishing external fields; it does not state proved extension theorems.

The related-work section compares classical counting–sampling reductions, graphical and zero-free algorithms, random-field methods, Glauber dynamics and diffusion/AMP/TAP samplers.

## Formal companion

[Lean4_Formalization.zip](Lean4_Formalization.zip) contains the existing pure-model formal development. Its exact coverage, pinned dependencies, recorded build and subsequent targeted checks are described in [VERIFICATION.md](VERIFICATION.md). The proposed extensions are outside this development.

## Review status

The manuscript has undergone several rounds of AI review. No obvious substantive error or gap was identified in the stated result during those reviews. This is not a guarantee of complete correctness; readers should check the arguments and the stated scope independently. See [VERIFICATION.md](VERIFICATION.md) for the evidence and limitations.

## Files

The manuscript is provided as a PDF.

[SHA256SUMS.txt](SHA256SUMS.txt) records the hashes of the distributed PDF and Lean companion.
