# Free-energy fluctuations of mixed p-spin models throughout the high-temperature regime

[Read the manuscript](mixed-pspin-fluctuations.pdf) · [LaTeX source](mixed-pspin-fluctuations.tex) · [Verification scope](VERIFICATION.md)

**Author:** Qiang Wu  
**Email:** qiangw.math@gmail.com  
**Revision:** 7 October 2026 · 14 pages · 19 references

These files are the revised manuscript prepared on the date above. This date identifies the revision, not the first discovery or generation of the result.

## Result and scope

The manuscript proves a quantitative mean-square quadratic approximation and a central limit theorem for finite, distinct-index Gaussian mixed p-spin models with no two-spin component and zero external field, throughout every fixed compact interval strictly below the thermodynamic critical inverse temperature. It retains the exact finite-size annealed centering. Chen's overlap theorem is a cited external input.

The temperature uniformity concerns a supremum of mean-square errors; it is not a functional central limit theorem or a result at the critical endpoint. The related-work section compares graphical, martingale, cavity, weak-field, multispecies and near-critical results.

## Review status

The manuscript has undergone several rounds of AI review. No obvious substantive error or gap was identified in the stated result during those reviews. This is not a guarantee of complete correctness; readers should check the arguments and the stated scope independently. See [VERIFICATION.md](VERIFICATION.md) for the evidence and limitations.

## Files and compilation

The PDF and standalone LaTeX source are included above. The bibliography is embedded in the source. With a suitable LaTeX distribution, compile using:

```sh
latexmk -pdf mixed-pspin-fluctuations.tex
```

[SHA256SUMS.txt](SHA256SUMS.txt) records the hashes of the distributed manuscript files and any formal companion.
