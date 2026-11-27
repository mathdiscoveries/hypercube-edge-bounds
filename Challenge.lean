/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.Rat.Defs

/-!
# Palomar Challenge: Lower Bounds on Diameter-Preserving Spanning Subgraphs of the Hypercube

For the `n`-dimensional hypercube `Q n`, let `f n` be the minimum number of
edges in a spanning subgraph `G ≤ Q n` preserving diameter `n`.

This challenge states:
1. The universal lower bound `2^n + ⌈(2^n - 2n) / (n - 1)⌉ ≤ f n` for all `n ≥ 2`.
2. The asymptotic `3 / 2` bound for the excess `((f n - 2^n) * (n - 1)) / 2^n`.
3. Improved finite-dimension bounds `39 ≤ f 5 ≤ 40`,
   `76 ≤ f 6`, `150 ≤ f 7`, `294 ≤ f 8`, and certified bounds for `17 ≤ n ≤ 32`.
-/

@[expose] public section

namespace HypercubeChallenge

abbrev CubeVertex (n : ℕ) := Fin n → Bool

def Q (n : ℕ) : SimpleGraph (CubeVertex n) where
  Adj u v := hammingDist u v = 1
  symm := ⟨fun u v (h : hammingDist u v = 1) => (hammingDist_comm v u).trans h⟩
  loopless := ⟨fun u (h : hammingDist u u = 1) =>
    absurd ((hammingDist_self u).symm.trans h) zero_ne_one⟩

def IsValidSpanningSubgraph (n : ℕ) (G : SimpleGraph (CubeVertex n)) : Prop :=
  G ≤ Q n ∧ ∀ u v : CubeVertex n, G.Reachable u v ∧ G.edist u v ≤ n

def edgeCount {n : ℕ} (G : SimpleGraph (CubeVertex n)) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

noncomputable def f (n : ℕ) : ℕ :=
  sInf { e : ℕ | ∃ (G : SimpleGraph (CubeVertex n)) (_ : DecidableRel G.Adj),
    IsValidSpanningSubgraph n G ∧ edgeCount G = e }

theorem theorem1_f_lower_bound_nat {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n + (2 ^ n - 2 * n + (n - 2)) / (n - 1) ≤ f n := by
  sorry

theorem theorem5_asymptotic_three_halves :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((3 : ℚ) / 2 - ε) * (2 : ℚ) ^ n ≤ ((f n : ℚ) - (2 : ℚ) ^ n) * ((n : ℚ) - 1) := by
  sorry

theorem f_five_bounds : 39 ≤ f 5 ∧ f 5 ≤ 40 := by sorry
theorem f_six_ge_76 : 76 ≤ f 6 := by sorry
theorem f_seven_ge_150 : 150 ≤ f 7 := by sorry
theorem f_eight_ge_294 : 294 ≤ f 8 := by sorry

theorem theorem14_bounds_17_to_32 :
    140128 ≤ f 17 ∧ 279210 ≤ f 18 ∧ 556449 ≤ f 19 ∧ 1110320 ≤ f 20 ∧
    2214490 ≤ f 21 ∧ 4418155 ≤ f 22 ∧ 8816922 ≤ f 23 ∧ 17599972 ≤ f 24 ∧
    35138325 ≤ f 25 ∧ 70152107 ≤ f 26 ∧ 140081100 ≤ f 27 ∧ 279786071 ≤ f 28 ∧
    558766740 ≤ f 29 ∧ 1116183007 ≤ f 30 ∧ 2229577178 ≤ f 31 ∧ 4454492243 ≤ f 32 := by
  sorry

end HypercubeChallenge
