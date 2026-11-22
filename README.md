# Lower Bounds on Diameter-Preserving Spanning Subgraphs of the Hypercube

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization for Graham's hypercube
diameter problem ($f(n)$ = minimum edges in a spanning subgraph of $Q_n$ of
diameter $n$):

- Universal bound $2^n + \lceil (2^n - 2n)/(n - 1) \rceil \le f(n)$ for all $n \ge 2$
- Asymptotic $3/2$ lower coefficient on the scale $2^n / (n - 1)$
- $39 \le f(5) \le 40$, $f(6) \ge 76$, $f(7) \ge 150$, $f(8) \ge 294$, and certified bounds through $n = 32$

## Build & Verify

```bash
lake build Challenge Solution Hypercube
lake env lean Hypercube/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
