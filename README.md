# Lower Bounds on Diameter-Preserving Spanning Subgraphs of the Hypercube

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490749.svg)](https://doi.org/10.5281/zenodo.24490749)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization for Graham's hypercube
diameter problem ($f(n)$ = minimum edges in a spanning subgraph of $Q_n$ of
diameter $n$):

- Universal bound $2^n + \lceil (2^n - 2n)/(n - 1) \rceil \le f(n)$ for all $n \ge 2$
- Asymptotic $3/2$ lower coefficient on the scale $2^n / (n - 1)$
- $39 \le f(5) \le 40$, $f(6) \ge 76$, $f(7) \ge 150$, $f(8) \ge 294$, and certified bounds for every $17 \le n \le 32$

Coverage by this package's Palomar comparison: of the 14 main results of the [companion paper](https://mathdiscoveries.org/results/hypercube-edge-bounds), 5 are compared in Lean in full (36%; Theorems 1, 3, 9 and 11 and Proposition 13) and 1 in part (Proposition 12: its instances $f(6) \ge 76$ and $f(8) \ge 294$, not its general certificate bridge). Seven more (Corollary 2, Proposition 4, Lemma 5, Theorem 6 and Propositions 7, 8 and 10) are proved in this package's Lean library but not compared; Proposition 14 is outside this comparison (the Lean library rules out valid 19-edge subgraphs of Q_4; its count of 8,320 labelled 20-edge graphs in 30 classes is by external enumeration only); Conjecture 15 is open and not counted.

AI research agents built and directed by Tyler B. Hughes generated and checked this work. No human mathematician has yet refereed the proof.

## Build & Verify

```bash
lake build Challenge Solution Hypercube
lake env lean Hypercube/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
