/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Hypercube.Defs
import Mathlib.Tactic

/-!
# Theorem 1: General Lower Bound, Refutation of 1995 Bound & Bass–Sudborough 2003 Table 1

Proves:
- `level_growth_bound`: `|S_k(v)| ≤ 2 + Y_{k-1}(v)` for `k ≥ 1`.
- `local_excess_ineq`: `2^(n-1) - n ≤ L(v)` (`L_n`).
- `hamming_ball_sum_identity`: `∑_{m ∈ R_n} B(n, m) = (n - 1) * 2^(n - 2)` for `n ≥ 2`.
- `theorem1_lower_bound`: for `n ≥ 2` and any valid spanning subgraph `G` of `Q n`,
  `(n - 1) * (|E(G)| - 2^n) ≥ 2^n - 2n`, and in ceiling forms (both `ℕ` and `ℤ`/`ℚ`).
- `theorem1_f_lower_bound` / `theorem1_f_lower_bound_nat`: `2^n + ⌈(2^n - 2n)/(n - 1)⌉ ≤ f n`.
- `theorem1_beats_1995`: for every `n ≥ 4`, Theorem 1 strictly exceeds the 1995 lower bound
  `2^n - 1 + ⌈(2^n - 1)/(2n - 1)⌉`.
- `bass_sudborough_table_refuted`: explicit refutation of Bass–Sudborough (2003) Table 1
  at `n = 4, 5, 6, 7, 8`: `18 < f 4 ∧ 35 < f 5 ∧ 69 < f 6 ∧ 137 < f 7 ∧ 272 < f 8`.
- `corollary31` and `f_seven_ge_148`: when `(n - 1) ∣ (2^n - 2n)` for `n ≥ 4`, the lower bound
  improves by `+1` (in particular `148 ≤ f 7`).
-/

@[expose] public section

namespace Hypercube

open Finset

/-- Size of the Hamming ball of radius `m` in `Q n`: `B(n, m) = ∑_{j=0}^m C(n, j)`. -/
def hammingBallSize (n m : ℕ) : ℕ :=
  ∑ j ∈ range (m + 1), n.choose j

/-- The 1995 lower bound (Bouabdallah–Delorme–Djelloul 1995) and Bass–Sudborough (2003) Table 1
remaining-edge formula: `2^n - 1 + ⌈(2^n - 1) / (2n - 1)⌉`. -/
noncomputable def bound1995 (n : ℕ) : ℤ :=
  (2 : ℤ) ^ n - 1 + ⌈((2 : ℚ) ^ n - 1) / (2 * (n : ℚ) - 1)⌉

/-- Theorem 1 lower bound formula: `2^n + ⌈(2^n - 2n) / (n - 1)⌉`. -/
noncomputable def boundTheorem1 (n : ℕ) : ℤ :=
  (2 : ℤ) ^ n + ⌈((2 : ℚ) ^ n - 2 * (n : ℚ)) / ((n : ℚ) - 1)⌉

theorem two_mul_le_two_pow {m : ℕ} (hm : 2 ≤ m) : 2 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem two_mul_lt_two_pow {m : ℕ} (hm : 3 ≤ m) : 2 * m < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem four_mul_le_two_pow {m : ℕ} (hm : 4 ≤ m) : 4 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

/-- Step 4 (BFS level growth bound): `|S_k(v)| ≤ 2 + Y_{k-1}(v)` for `k ≥ 1`. -/
theorem level_growth_bound {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hV : IsValidSpanningSubgraph n G) (v : CubeVertex n) {k : ℕ} (hk : 1 ≤ k) :
    ((levelSet G v k).card : ℤ) ≤ 2 + ballExcess G v (k - 1) := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have ha := part_a hG hc v k hk
  have h1 : 0 ≤ ∑ j ∈ Ico 2 k, extraParents G v j :=
    Finset.sum_nonneg fun j hj => extraParents_nonneg hc v (by simp only [Finset.mem_Ico] at hj; omega)
  have h2 : 0 ≤ extraParents G v k := extraParents_nonneg hc v hk
  linarith

/-- Step 5 (Local excess inequality `L_n`): `2^(n - 1) - n ≤ L(v)` for every vertex `v`. -/
theorem local_excess_ineq {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) (v : CubeVertex n) :
    (2 : ℤ) ^ (n - 1) - (n : ℤ) ≤ lSum G v := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hpc := part_c hn hG hD v
  have hw := weightedExtra_nonneg hc v
  linarith

theorem Q_dist_eq_hammingDist {n : ℕ} (u v : CubeVertex n) :
    (Q n).dist u v = hammingDist u v := by
  have hc := connected_of_ediam (Q_ediam n)
  have hle := (dist_hamming (le_refl (Q n)) hc u v).1
  obtain ⟨p, hp⟩ := exists_walk_hamming v (hammingDist u v) u rfl
  have hge : (Q n).dist u v ≤ hammingDist u v := by
    rw [← hp]
    exact SimpleGraph.dist_le p
  omega

theorem card_hamming_ball {n : ℕ} (v : CubeVertex n) (m : ℕ) :
    (univ.filter fun u : CubeVertex n => hammingDist v u < m + 1).card = hammingBallSize n m := by
  unfold hammingBallSize
  have h1 : ∀ j, (univ.filter fun u : CubeVertex n => hammingDist v u = j).card = n.choose j :=
    card_hamming_sphere v
  simp_rw [← h1]
  have hdisj : (range (m + 1) : Set ℕ).PairwiseDisjoint
      (fun j => univ.filter fun u : CubeVertex n => hammingDist v u = j) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro u hui huj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hui huj
    exact hij (hui.symm.trans huj)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨fun h => ⟨hammingDist v u, h, rfl⟩, fun ⟨j, hj, hju⟩ => hju ▸ hj⟩

/-- Step 6 (Hamming-ball pairing identity): for `n ≥ 2`,
`∑_{m ∈ R_n} B(n, m) = (n - 1) * 2^(n - 2)`. -/
theorem hamming_ball_sum_identity {n : ℕ} (hn : 2 ≤ n) :
    ∑ m ∈ rSet n, hammingBallSize n m = (n - 1) * 2 ^ (n - 2) := by
  let v0 : CubeVertex n := fun _ => false
  have hswap : ∑ m ∈ rSet n, hammingBallSize n m =
      ∑ u : CubeVertex n, (n - hammingDist v0 u) / 2 := by
    have h1 : ∀ m, hammingBallSize n m =
        ∑ u : CubeVertex n, if hammingDist v0 u < m + 1 then 1 else 0 := by
      intro m
      rw [← card_hamming_ball v0 m, Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.card_filter, card_rSet_ge (hammingDist_le_n v0 u)]
  have hQhalf := sum_half (G := Q n) hn (le_refl _) (Q_ediam n) v0
  have hgap : distGap (Q n) v0 = 0 := by
    unfold distGap distSum
    have hsum := sum_hammingDist_int (show 1 ≤ n by omega) v0
    have heq : ∑ u : CubeVertex n, (((Q n).dist u v0 : ℕ) : ℤ) =
        ∑ u : CubeVertex n, (hammingDist u v0 : ℤ) :=
      Finset.sum_congr rfl fun u _ => by rw [Q_dist_eq_hammingDist]
    linarith
  rw [hgap, sub_zero] at hQhalf
  have hQeq : ∑ u : CubeVertex n, (2 : ℤ) * (((n - (Q n).dist u v0) / 2 : ℕ) : ℤ) =
      (2 : ℤ) * ((∑ u : CubeVertex n, (n - hammingDist v0 u) / 2 : ℕ) : ℤ) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Q_dist_eq_hammingDist, hammingDist_comm]
  rw [hQeq] at hQhalf
  have hpow : (2 : ℤ) ^ (n - 1) = 2 * (2 : ℤ) ^ (n - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at hQhalf
  have hZ : ((∑ u : CubeVertex n, (n - hammingDist v0 u) / 2 : ℕ) : ℤ) =
      ((n : ℤ) - 1) * (2 : ℤ) ^ (n - 2) := by linarith
  rw [hswap]
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [← hn1] at hZ
  exact_mod_cast hZ

/-- Multiplicative integer form of Theorem 1: `(n - 1) * (|E(G)| - 2^n) ≥ 2^n - 2n`. -/
theorem theorem1_slack_bound {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) :
    (2 : ℤ) ^ n - 2 * (n : ℤ) ≤ ((n : ℤ) - 1) * edgeExcess G := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hd := part_d hn hG hD
  have hS1 : 0 ≤ ∑ w, excess G w * distGap G w :=
    Finset.sum_nonneg fun w _ =>
      mul_nonneg (excess_nonneg hn hG hD w) (distGap_nonneg (by omega) hG hD w)
  have hS2 : 0 ≤ ∑ v, weightedExtra G v :=
    Finset.sum_nonneg fun v _ => weightedExtra_nonneg hc v
  have hpow_pos : (0 : ℤ) < 2 ^ n := by positivity
  by_contra h
  push Not at h
  have h1 : ((n : ℤ) - 1) * edgeExcess G - ((2 : ℤ) ^ n - 2 * (n : ℤ)) < 0 := by linarith
  have h2 : (2 : ℤ) ^ n * (((n : ℤ) - 1) * edgeExcess G - ((2 : ℤ) ^ n - 2 * (n : ℤ))) < 0 :=
    mul_neg_of_pos_of_neg hpow_pos h1
  linarith

/-- For `n ≥ 2`, every valid spanning subgraph of `Q n` has at least `2^n` edges. -/
theorem two_pow_le_edgeSet_ncard {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) :
    2 ^ n ≤ G.edgeSet.ncard := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hX : 0 ≤ ∑ u : CubeVertex n, excess G u :=
    Finset.sum_nonneg fun u _ => excess_nonneg hn hG hD u
  rw [sum_excess] at hX
  unfold edgeExcess at hX
  exact_mod_cast (show (2 : ℤ) ^ n ≤ (G.edgeSet.ncard : ℤ) by linarith)

/-- Theorem 1 (Natural-number multiplicative form):
`2^n - 2n ≤ (n - 1) * (|E(G)| - 2^n)`. -/
theorem theorem1_lower_bound {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) :
    2 ^ n - 2 * n ≤ (n - 1) * (G.edgeSet.ncard - 2 ^ n) := by
  have hZ := theorem1_slack_bound hn hV
  have hge := two_pow_le_edgeSet_ncard hn hV
  have h2n := two_mul_le_two_pow hn
  unfold edgeExcess at hZ
  have hcast1 : ((2 ^ n - 2 * n : ℕ) : ℤ) = (2 : ℤ) ^ n - 2 * (n : ℤ) := by
    rw [Nat.cast_sub h2n]; push_cast; ring
  have hcast2 : (((n - 1) * (G.edgeSet.ncard - 2 ^ n) : ℕ) : ℤ) =
      ((n : ℤ) - 1) * ((G.edgeSet.ncard : ℤ) - (2 : ℤ) ^ n) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub hge]; push_cast; ring
  rw [← hcast1, ← hcast2] at hZ
  exact_mod_cast hZ

/-- Theorem 1 (Natural-number ceiling form):
`2^n + (2^n - 2n + (n - 2)) / (n - 1) ≤ |E(G)|`. -/
theorem theorem1_lower_bound_nat_ceil {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) :
    2 ^ n + (2 ^ n - 2 * n + (n - 2)) / (n - 1) ≤ G.edgeSet.ncard := by
  have hmul := theorem1_lower_bound hn hV
  have hge := two_pow_le_edgeSet_ncard hn hV
  have hdiv : (2 ^ n - 2 * n + (n - 2)) / (n - 1) ≤ G.edgeSet.ncard - 2 ^ n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have h1 : n - 1 - 1 = n - 2 := by omega
    rw [h1]
    have hcomm : (G.edgeSet.ncard - 2 ^ n) * (n - 1) = (n - 1) * (G.edgeSet.ncard - 2 ^ n) :=
      Nat.mul_comm _ _
    omega
  omega

/-- Theorem 1 (Rational-ceiling form):
`2^n + ⌈(2^n - 2n) / (n - 1)⌉ ≤ |E(G)|`. -/
theorem theorem1_lower_bound_ceil {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) :
    boundTheorem1 n ≤ (G.edgeSet.ncard : ℤ) := by
  have hkey := theorem1_slack_bound hn hV
  have hn1 : (0 : ℚ) < (n : ℚ) - 1 := by
    have h : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hkeyQ : (((2 : ℤ) ^ n - 2 * (n : ℤ) : ℤ) : ℚ) ≤
      ((((n : ℤ) - 1) * edgeExcess G : ℤ) : ℚ) := by
    exact_mod_cast hkey
  push_cast at hkeyQ
  have hceil : ⌈((2 : ℚ) ^ n - 2 * (n : ℚ)) / ((n : ℚ) - 1)⌉ ≤ edgeExcess G := by
    rw [Int.ceil_le, div_le_iff₀ hn1]
    linarith
  unfold boundTheorem1 edgeExcess at *
  linarith

/-- Theorem 1 for `f n` (`ℕ` ceiling form). -/
theorem theorem1_f_lower_bound_nat {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n + (2 ^ n - 2 * n + (n - 2)) / (n - 1) ≤ f n :=
  le_f_of_forall_valid fun _ hV => theorem1_lower_bound_nat_ceil hn hV

/-- Theorem 1 for `f n` (`ℤ`/`ℚ` ceiling form). -/
theorem theorem1_f_lower_bound {n : ℕ} (hn : 2 ≤ n) :
    boundTheorem1 n ≤ (f n : ℤ) := by
  have hnat : ∀ G : SimpleGraph (CubeVertex n), IsValidSpanningSubgraph n G →
      (boundTheorem1 n).toNat ≤ G.edgeSet.ncard := by
    intro G hV
    have h := theorem1_lower_bound_ceil hn hV
    omega
  have hf := le_f_of_forall_valid hnat
  have hnn : 0 ≤ boundTheorem1 n := by
    have h := theorem1_lower_bound_ceil hn (Q_valid n)
    unfold boundTheorem1
    have h0 : (0 : ℚ) ≤ ((2 : ℚ) ^ n - 2 * (n : ℚ)) / ((n : ℚ) - 1) := by
      apply div_nonneg
      · have h2n : (2 : ℚ) * (n : ℚ) ≤ (2 : ℚ) ^ n := by exact_mod_cast two_mul_le_two_pow hn
        linarith
      · have hn2 : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
        linarith
    have hc0 : (0 : ℤ) ≤ ⌈((2 : ℚ) ^ n - 2 * (n : ℚ)) / ((n : ℚ) - 1)⌉ :=
      Int.ceil_nonneg h0
    have hp : (0 : ℤ) ≤ (2 : ℤ) ^ n := by positivity
    linarith
  omega

/-- Step 7: For every `n ≥ 4`, Theorem 1's lower bound strictly exceeds the 1995 lower bound. -/
theorem theorem1_beats_1995 {n : ℕ} (hn : 4 ≤ n) :
    bound1995 n < boundTheorem1 n := by
  unfold bound1995 boundTheorem1
  have h4 : (4 : ℚ) * (n : ℚ) ≤ (2 : ℚ) ^ n := by exact_mod_cast four_mul_le_two_pow hn
  have hn4 : (4 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hden1 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  have hden2 : (0 : ℚ) < 2 * (n : ℚ) - 1 := by linarith
  have hfrac : ((2 : ℚ) ^ n - 1) / (2 * (n : ℚ) - 1) ≤
      ((2 : ℚ) ^ n - 2 * (n : ℚ)) / ((n : ℚ) - 1) := by
    rw [div_le_div_iff₀ hden2 hden1]
    nlinarith
  have hceil : ⌈((2 : ℚ) ^ n - 1) / (2 * (n : ℚ) - 1)⌉ ≤
      ⌈((2 : ℚ) ^ n - 2 * (n : ℚ)) / ((n : ℚ) - 1)⌉ :=
    Int.ceil_mono hfrac
  linarith

/-- For every `n ≥ 4`, the 1995 lower bound is never attained: `bound1995 n < f n`. -/
theorem not_attained_1995 {n : ℕ} (hn : 4 ≤ n) :
    bound1995 n < (f n : ℤ) :=
  lt_of_lt_of_le (theorem1_beats_1995 hn) (theorem1_f_lower_bound (by omega))

/-- Concrete Theorem 1 bounds at `n = 4, 5, 6, 7, 8`. -/
theorem theorem1_concrete_values :
    19 ≤ f 4 ∧ 38 ≤ f 5 ∧ 75 ≤ f 6 ∧ 147 ≤ f 7 ∧ 291 ≤ f 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := theorem1_f_lower_bound_nat (n := 4) (by norm_num); norm_num at h; exact h
  · have h := theorem1_f_lower_bound_nat (n := 5) (by norm_num); norm_num at h; exact h
  · have h := theorem1_f_lower_bound_nat (n := 6) (by norm_num); norm_num at h; exact h
  · have h := theorem1_f_lower_bound_nat (n := 7) (by norm_num); norm_num at h; exact h
  · have h := theorem1_f_lower_bound_nat (n := 8) (by norm_num); norm_num at h; exact h

/-- Refutation of Bass–Sudborough (2003) Table 1 at `n = 4, 5, 6, 7, 8`:
the published table claims valid spanning subgraphs of sizes 18, 35, 69, 137, 272 edges,
every one of which is strictly below `f n`. -/
theorem bass_sudborough_table_refuted :
    18 < f 4 ∧ 35 < f 5 ∧ 69 < f 6 ∧ 137 < f 7 ∧ 272 < f 8 := by
  obtain ⟨h4, h5, h6, h7, h8⟩ := theorem1_concrete_values
  omega

/-- Corollary 3.1 (`fn-bound/bound-2.md`): when `n ≥ 4` and `(n - 1) ∣ (2^n - 2n)`,
the lower bound improves by `+1`: `2^n + (2^n - 2n) / (n - 1) + 1 ≤ |E(G)|`. -/
theorem corollary31 {n : ℕ} (hn : 4 ≤ n) (hdvd : ((n : ℤ) - 1) ∣ ((2 : ℤ) ^ n - 2 * (n : ℤ)))
    {G : SimpleGraph (CubeVertex n)} (hV : IsValidSpanningSubgraph n G) :
    (2 : ℤ) ^ n + ((2 : ℤ) ^ n - 2 * (n : ℤ)) / ((n : ℤ) - 1) + 1 ≤ (G.edgeSet.ncard : ℤ) := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hn2 : 2 ≤ n := by omega
  have hc := connected_of_ediam hD
  obtain ⟨q, hq⟩ := hdvd
  have hn1 : ((n : ℤ) - 1) ≠ 0 := by omega
  rw [Int.ediv_eq_of_eq_mul_right hn1 hq]
  have hd := part_d hn2 hG hD
  have hS1 : 0 ≤ ∑ w, excess G w * distGap G w :=
    Finset.sum_nonneg fun w _ =>
      mul_nonneg (excess_nonneg hn2 hG hD w) (distGap_nonneg (by omega) hG hD w)
  have hS2 : 0 ≤ ∑ v, weightedExtra G v :=
    Finset.sum_nonneg fun v _ => weightedExtra_nonneg hc v
  have hpow_pos : (0 : ℤ) < 2 ^ n := by positivity
  have hn3 : (3 : ℤ) ≤ (n : ℤ) - 1 := by omega
  have hd' : (∑ w, excess G w * distGap G w) + 2 * (∑ v, weightedExtra G v) =
      (2 : ℤ) ^ n * (((n : ℤ) - 1) * (edgeExcess G - q)) := by
    rw [hd, hq]; ring
  have htq : q ≤ edgeExcess G := by
    by_contra h
    push Not at h
    have h1 : ((n : ℤ) - 1) * (edgeExcess G - q) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have h2 : (2 : ℤ) ^ n * (((n : ℤ) - 1) * (edgeExcess G - q)) < 0 :=
      mul_neg_of_pos_of_neg hpow_pos h1
    linarith
  suffices ht : q + 1 ≤ edgeExcess G by
    unfold edgeExcess at ht; linarith
  by_contra hlt
  push Not at hlt
  have hteq : edgeExcess G = q := by omega
  rw [hteq, sub_self, mul_zero, mul_zero] at hd'
  have hS1z : ∑ w, excess G w * distGap G w = 0 := by linarith
  have hS2z : ∑ v, weightedExtra G v = 0 := by linarith
  have hgt : (2 : ℤ) * n < 2 ^ n := by exact_mod_cast two_mul_lt_two_pow (show 3 ≤ n by omega)
  have hqpos : 0 < q := by by_contra h; push Not at h; nlinarith
  have hX : ∑ u : CubeVertex n, excess G u = 2 * edgeExcess G := sum_excess
  obtain ⟨w, hw⟩ : ∃ w, 0 < excess G w := by
    by_contra hno
    push Not at hno
    have : ∑ u, excess G u ≤ 0 := Finset.sum_nonpos fun u _ => hno u
    linarith
  have hδ : distGap G w = 0 := by
    have hnn : ∀ u ∈ (univ : Finset (CubeVertex n)), 0 ≤ excess G u * distGap G u := fun u _ =>
      mul_nonneg (excess_nonneg hn2 hG hD u) (distGap_nonneg (by omega) hG hD u)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS1z w (Finset.mem_univ w)
    exact (mul_eq_zero.1 h0).resolve_left (ne_of_gt hw)
  have hMw : weightedExtra G w = 0 := by
    have hnn : ∀ v ∈ (univ : Finset (CubeVertex n)), 0 ≤ weightedExtra G v := fun v _ =>
      weightedExtra_nonneg hc v
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS2z w (Finset.mem_univ w)
  have hgeo : ∀ v, G.dist v w = hammingDist v w := by
    have hsumh := sum_hammingDist_int (show 1 ≤ n by omega) w
    have hterm : ∑ v, ((G.dist v w : ℤ) - hammingDist v w) = 0 := by
      rw [Finset.sum_sub_distrib, hsumh]; unfold distGap distSum at hδ; linarith
    have hnn : ∀ v ∈ (univ : Finset (CubeVertex n)), 0 ≤ (G.dist v w : ℤ) - hammingDist v w := by
      intro v _
      have h1 := (dist_hamming hG hc v w).1
      have h2 : (hammingDist v w : ℤ) ≤ G.dist v w := by exact_mod_cast h1
      linarith
    intro v
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm v (Finset.mem_univ v)
    omega
  have hsphere : ∀ k, (levelSet G w k).card = n.choose k := by
    intro k
    rw [← card_hamming_sphere w k]
    congr 1; ext u
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [SimpleGraph.dist_comm, hgeo u, hammingDist_comm]
  have hMj : ∀ j ∈ Ico 2 n, extraParents G w j = 0 := by
    have hnn : ∀ j ∈ Ico 2 n, 0 ≤ ((n : ℤ) - j) * extraParents G w j := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      apply mul_nonneg
      · have : (j : ℤ) < n := by exact_mod_cast hj.2
        linarith
      · exact extraParents_nonneg hc w (by omega)
    unfold weightedExtra at hMw
    intro j hj
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hMw j hj
    have hpos : ((n : ℤ) - j) ≠ 0 := by simp only [Finset.mem_Ico] at hj; omega
    exact (mul_eq_zero.1 h0).resolve_left hpos
  have hsum0 : ∀ k, k ≤ n → ∑ j ∈ Ico 2 k, extraParents G w j = 0 := by
    intro k hk
    apply Finset.sum_eq_zero
    intro j hj
    apply hMj
    simp only [Finset.mem_Ico] at hj ⊢; omega
  have ha1 := part_a hG hc w (n - 1) (by omega)
  have ha2 := part_a hG hc w (n - 2) (by omega)
  rw [hsum0 (n - 1) (by omega), hMj (n - 1) (by simp only [Finset.mem_Ico]; omega), hsphere] at ha1
  rw [hsum0 (n - 2) (by omega), hMj (n - 2) (by simp only [Finset.mem_Ico]; omega), hsphere] at ha2
  have hY : ballExcess G w (n - 1 - 1) = ballExcess G w (n - 2 - 1) + levelExcess G w (n - 2) := by
    have e1 : n - 1 - 1 + 1 = n - 2 + 1 := by omega
    have e2 : n - 2 - 1 + 1 = n - 2 := by omega
    unfold ballExcess; rw [e1, e2, Finset.sum_range_succ]
  have hX0 : 0 ≤ levelExcess G w (n - 2) :=
    Finset.sum_nonneg fun u _ => excess_nonneg hn2 hG hD u
  have hle : ((n.choose (n - 2) : ℕ) : ℤ) ≤ ((n.choose (n - 1) : ℕ) : ℤ) := by linarith
  have hle' : n.choose (n - 2) ≤ n.choose (n - 1) := by exact_mod_cast hle
  rw [Nat.choose_symm (show 2 ≤ n by omega), Nat.choose_symm (show 1 ≤ n by omega),
    Nat.choose_two_right, Nat.choose_one_right] at hle'
  have hm := Nat.mul_le_mul_left n (show 3 ≤ n - 1 by omega)
  omega

/-- Corollary 3.1 at `n = 7`: `148 ≤ f 7`. -/
theorem f_seven_ge_148 : 148 ≤ f 7 := by
  apply le_f_of_forall_valid
  intro G hV
  have h := corollary31 (n := 7) (by norm_num) (by norm_num) hV
  norm_num at h
  exact_mod_cast h

end Hypercube
