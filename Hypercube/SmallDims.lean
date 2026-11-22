module

public import Hypercube.Theorem1
public import Hypercube.Construction
import Mathlib.Tactic

/-!
# Exact Small Dimensions (`f(2) = 4`, `f(3) = 9`, `f(4) = 20`) & Theorem 2 (`f(5) ≥ 39`)

Proves:
- `f_two_eq_four`: `f 2 = 4`.
- `f_three_eq_nine`: `f 3 = 9`.
- `f_four_ge_twenty` and `f_four_eq_twenty`: full formalization of the hand proof
  (`f4-proof/proof-1.md`, Steps 1–7) ruling out 19 edges on `Q_4`, yielding `f 4 = 20`.
- `f_five_ge_thirtynine` and `f_five_bounds`: full formalization of Theorem 2
  (`fn-bound/bound-1.md`, Steps 8–15) ruling out 38 edges on `Q_5`, yielding
  `39 ≤ f 5 ∧ f 5 ≤ 40`.
-/

@[expose] public section

namespace Hypercube

open Finset

/-! ### Exact values for `n = 2` and `n = 3` -/

/-- `f(2) = 4`. -/
theorem f_two_eq_four : f 2 = 4 := by
  have hlo := theorem1_f_lower_bound_nat (n := 2) (by norm_num)
  have hhi := f_two_le_four
  norm_num at hlo
  omega

/-- `f(3) = 9`. -/
theorem f_three_eq_nine : f 3 = 9 := by
  have hlo := theorem1_f_lower_bound_nat (n := 3) (by norm_num)
  have hhi := f_three_le_nine
  norm_num at hlo
  omega

/-! ### Shared helpers for `Q_4` and `Q_5` -/

private theorem weight_parity_of_dist {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) {u w : CubeVertex n} :
    (hammingWeight u + hammingWeight w) % 2 = G.dist u w % 2 := by
  have hpar := (dist_hamming hG hc u w).2
  have h1 : ∀ x y : CubeVertex n, (hammingWeight x + hammingWeight y) % 2 = hammingDist x y % 2 := by
    intro x y
    rw [hammingWeight_eq_hammingDist, hammingWeight_eq_hammingDist, hammingDist_eq_sum,
      hammingDist_eq_sum, hammingDist_eq_sum]
    have hsum :
        ∑ i : Fin n, (if (false : Bool) ≠ x i then 1 else 0 : ℕ) +
        ∑ i : Fin n, (if (false : Bool) ≠ y i then 1 else 0 : ℕ) =
        ∑ i : Fin n, ((if x i ≠ y i then 1 else 0 : ℕ) +
          2 * (if x i = true ∧ y i = true then 1 else 0 : ℕ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases hx : x i <;> cases hy : y i <;> decide
    rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
    omega
  rw [hpar, h1]

private theorem levelSet_one_eq_neighbor {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (v u : CubeVertex n) : u ∈ levelSet G v 1 ↔ G.Adj v u := by
  rw [mem_levelSet, SimpleGraph.dist_eq_one_iff_adj]

private theorem card_levelSet_one {n : ℕ} {G : SimpleGraph (CubeVertex n)} (v : CubeVertex n) :
    ((levelSet G v 1).card : ℤ) = 2 + excess G v := by
  classical
  have h : levelSet G v 1 = G.neighborFinset v := by
    ext u
    rw [levelSet_one_eq_neighbor, SimpleGraph.mem_neighborFinset]
  rw [h, SimpleGraph.card_neighborFinset_eq_degree, ← ncard_neighborSet_eq_degree]
  unfold excess
  ring

private theorem levelSet_two_subset_hamming_two {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (v : CubeVertex n) :
    levelSet G v 2 ⊆ univ.filter fun u => hammingDist v u = 2 := by
  intro u hu
  rw [mem_levelSet] at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hd := dist_hamming hG hc v u
  have hne : u ≠ v := by
    rintro rfl
    simp at hu
  have hpos : 0 < hammingDist v u := by
    by_contra h0
    have hz : hammingDist v u = 0 := by omega
    exact hne (hammingDist_eq_zero.1 hz).symm
  omega

private theorem card_levelSet_two_le {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (v : CubeVertex n) :
    (levelSet G v 2).card ≤ n.choose 2 := by
  calc (levelSet G v 2).card
      ≤ (univ.filter fun u => hammingDist v u = 2).card :=
        Finset.card_le_card (levelSet_two_subset_hamming_two hG hc v)
    _ = n.choose 2 := card_hamming_sphere v 2

/-! ### Exact `f(4) = 20`: Steps 1–7 of `f4-proof/proof-1.md` -/

private theorem part_excess_three_cases {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℤ)
    (hbound : ∀ a ∈ S, 1 ≤ x a ∧ x a ≤ 2)
    (hsum : ∑ a ∈ S, x a = 3) :
    (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ S = {a, b, c} ∧ x a = 1 ∧ x b = 1 ∧ x c = 1) ∨
    (∃ p q, p ≠ q ∧ S = {p, q} ∧ x p = 2 ∧ x q = 1) := by
  have hlo : (S.card : ℤ) ≤ 3 := by
    calc (S.card : ℤ) = ∑ _a ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ a ∈ S, x a := Finset.sum_le_sum fun a ha => (hbound a ha).1
      _ = 3 := hsum
  have hhi : 3 ≤ 2 * (S.card : ℤ) := by
    calc (3 : ℤ) = ∑ a ∈ S, x a := hsum.symm
      _ ≤ ∑ _a ∈ S, (2 : ℤ) := Finset.sum_le_sum fun a ha => (hbound a ha).2
      _ = 2 * (S.card : ℤ) := by simp; ring
  have hcard : S.card = 2 ∨ S.card = 3 := by omega
  rcases hcard with h2 | h3
  · right
    rcases Finset.card_eq_two.1 h2 with ⟨a, b, hab, rfl⟩
    have ha := hbound a (by simp)
    have hb := hbound b (by simp)
    rw [Finset.sum_pair hab] at hsum
    rcases (show (x a = 2 ∧ x b = 1) ∨ (x a = 1 ∧ x b = 2) by omega) with ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩
    · exact ⟨a, b, hab, rfl, hxa, hxb⟩
    · exact ⟨b, a, hab.symm, Finset.pair_comm a b, hxb, hxa⟩
  · left
    rcases Finset.card_eq_three.1 h3 with ⟨a, b, c, hab, hac, hbc, rfl⟩
    have ha := hbound a (by simp)
    have hb := hbound b (by simp)
    have hc := hbound c (by simp)
    have hnot1 : a ∉ ({b, c} : Finset α) := by simp [hab, hac]
    rw [Finset.sum_insert hnot1, Finset.sum_pair hbc] at hsum
    exact ⟨a, b, c, hab, hac, hbc, rfl, by omega, by omega, by omega⟩

/-- Local lemma `(L)` at `n = 4`: `4 ≤ 2 * x_v + X_1(v) + X_2(v)`. -/
private theorem local_lemma_q4 {G : SimpleGraph (CubeVertex 4)}
    (hV : IsValidSpanningSubgraph 4 G) (v : CubeVertex 4) :
    4 ≤ 2 * excess G v + levelExcess G v 1 + levelExcess G v 2 := by
  have ⟨_, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hL := local_excess_ineq (n := 4) (by norm_num) hV v
  have hr : rSet 4 = {0, 2} := by decide
  unfold lSum at hL
  rw [hr, Finset.sum_pair (by decide)] at hL
  have hY0 : ballExcess G v 0 = excess G v := by
    simp [ballExcess, levelExcess_zero hc v]
  have hY2 : ballExcess G v 2 = excess G v + levelExcess G v 1 + levelExcess G v 2 := by
    simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc v]
  rw [hY0, hY2] at hL
  norm_num at hL
  linarith

/-- Step 7, Case 2 helper: one parity part `{4, 3}` and the other `{3, 3, 3}` is impossible. -/
private theorem q4_case_43_333 {G : SimpleGraph (CubeVertex 4)}
    (hV : IsValidSpanningSubgraph 4 G)
    (r : ℕ) (hr : r < 2)
    (p q r1 r2 r3 : CubeVertex 4)
    (hpq : p ≠ q) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hBr : (univ.filter fun u => 0 < excess G u ∧ hammingWeight u % 2 = r) = {p, q})
    (hBo : (univ.filter fun u => 0 < excess G u ∧ hammingWeight u % 2 = 1 - r) = {r1, r2, r3})
    (hxp : excess G p = 2) (hxq : excess G q = 1)
    (hxr1 : excess G r1 = 1) (hxr2 : excess G r2 = 1) (hxr3 : excess G r3 = 1) :
    False := by
  classical
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  let B : Finset (CubeVertex 4) := univ.filter fun u => 0 < excess G u
  let D : Finset (CubeVertex 4) := univ.filter fun u => excess G u = 0
  have hBsplit : B = {p, q} ∪ {r1, r2, r3} := by
    rw [← hBr, ← hBo]
    ext u
    simp only [B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hdisj : Disjoint ({p, q} : Finset (CubeVertex 4)) {r1, r2, r3} := by
    rw [← hBr, ← hBo, Finset.disjoint_left]
    intro u h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  have hBcard : B.card = 5 := by
    rw [hBsplit, Finset.card_union_of_disjoint hdisj, Finset.card_pair hpq]
    have hnot : r1 ∉ ({r2, r3} : Finset (CubeVertex 4)) := by simp [h12, h13]
    rw [Finset.card_insert_of_notMem hnot, Finset.card_pair h23]
  have hDcard : D.card = 11 := by
    have hcomp : D = univ.filter (fun u => ¬(0 < excess G u)) := by
      ext u
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
      have hnn := excess_nonneg (by norm_num) hG hD u
      omega
    have htot := Finset.card_filter_add_card_filter_not (s := univ) (fun u : CubeVertex 4 => 0 < excess G u)
    rw [Finset.card_univ, card_vertices] at htot
    change B.card + (univ.filter fun u => ¬(0 < excess G u)).card = 2 ^ 4 at htot
    rw [← hcomp, hBcard] at htot
    norm_num at htot
    omega
  -- Define c(w) = |D ∩ (S_1(w) ∪ S_2(w))|
  let c : CubeVertex 4 → ℤ := fun w =>
    ((D.filter fun v => G.dist w v = 1).card : ℤ) + ((D.filter fun v => G.dist w v = 2).card : ℤ)
  -- Double counting (S): 4 * |D| ≤ ∑ w ∈ B, x_w * c(w)
  have hS : 44 ≤ ∑ w ∈ B, excess G w * c w := by
    have hsumD : 4 * (D.card : ℤ) ≤ ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) := by
      calc 4 * (D.card : ℤ) = ∑ _v ∈ D, (4 : ℤ) := by simp; ring
        _ ≤ ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hxv : excess G v = 0 := (Finset.mem_filter.1 hv).2
          have hL := local_lemma_q4 hV v
          linarith
    have hswap : ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) =
        ∑ w ∈ B, excess G w * c w := by
      have h1 : ∀ k : ℕ, ∑ v ∈ D, levelExcess G v k =
          ∑ w ∈ B, excess G w * ((D.filter fun v => G.dist w v = k).card : ℤ) := by
        intro k
        simp only [levelExcess, levelSet, Finset.sum_filter]
        rw [Finset.sum_comm]
        have hzero : ∑ w : CubeVertex 4, ∑ v ∈ D, (if G.dist v w = k then excess G w else 0) =
            ∑ w ∈ B, ∑ v ∈ D, (if G.dist v w = k then excess G w else 0) := by
          rw [← Finset.sum_subset (Finset.subset_univ B)]
          intro w _ hw
          have hxw : excess G w = 0 := by
            simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hw
            have hnn := excess_nonneg (by norm_num) hG hD w
            omega
          simp [hxw]
        rw [hzero]
        refine Finset.sum_congr rfl fun w _ => ?_
        have hcomm : ∀ v, (if G.dist v w = k then excess G w else 0) =
            if G.dist w v = k then excess G w else 0 := fun v => by rw [SimpleGraph.dist_comm]
        simp_rw [hcomm]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [Finset.sum_add_distrib, h1 1, h1 2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => by simp only [c]; ring
    rw [hDcard] at hsumD
    norm_num at hsumD
    linarith
  -- Bound (C) for any vertex w
  have hC : ∀ w : CubeVertex 4,
      c w ≤ (2 + excess G w - ((B.filter fun u => G.dist w u = 1).card : ℤ)) +
        min 6 (2 + excess G w + levelExcess G w 1) -
        ((B.filter fun u => G.dist w u = 2).card : ℤ) := by
    intro w
    have hpart : ∀ k : ℕ, ((D.filter fun u => G.dist w u = k).card : ℤ) +
        ((B.filter fun u => G.dist w u = k).card : ℤ) = ((levelSet G w k).card : ℤ) := by
      intro k
      have hunion : (D.filter fun u => G.dist w u = k) ∪ (B.filter fun u => G.dist w u = k) =
          levelSet G w k := by
        ext u
        simp only [D, B, levelSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        have hnn := excess_nonneg (by norm_num) hG hD u
        omega
      have hd : Disjoint (D.filter fun u => G.dist w u = k) (B.filter fun u => G.dist w u = k) := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        simp only [D, B, Finset.mem_filter] at h1 h2
        omega
      have hc' := Finset.card_union_of_disjoint hd
      rw [hunion] at hc'
      exact_mod_cast hc'.symm
    have hp1 := hpart 1
    have hp2 := hpart 2
    rw [card_levelSet_one] at hp1
    have hs2a : ((levelSet G w 2).card : ℤ) ≤ 6 := by
      have h := card_levelSet_two_le hG hc w
      exact_mod_cast h
    have hs2b : ((levelSet G w 2).card : ℤ) ≤ 2 + excess G w + levelExcess G w 1 := by
      have h := level_growth_bound hV w (k := 2) (by norm_num)
      have hY1 : ballExcess G w (2 - 1) = excess G w + levelExcess G w 1 := by
        simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc w]
      linarith
    have hmin : ((levelSet G w 2).card : ℤ) ≤ min 6 (2 + excess G w + levelExcess G w 1) :=
      le_min hs2a hs2b
    simp only [c]
    linarith
  -- Parity of vertices
  have hp_par : hammingWeight p % 2 = r := by
    have hm : p ∈ ({p, q} : Finset (CubeVertex 4)) := by simp
    rw [← hBr] at hm; exact (Finset.mem_filter.1 hm).2.2
  have hq_par : hammingWeight q % 2 = r := by
    have hm : q ∈ ({p, q} : Finset (CubeVertex 4)) := by simp
    rw [← hBr] at hm; exact (Finset.mem_filter.1 hm).2.2
  have hr_par : ∀ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)), hammingWeight u % 2 = 1 - r := by
    intro u hu; rw [← hBo] at hu; exact (Finset.mem_filter.1 hu).2.2
  -- For u ∈ {p, q}, every neighbor in B lies in {r1, r2, r3} so has excess 1
  have hX1_pq : ∀ w, hammingWeight w % 2 = r →
      levelExcess G w 1 = ((B.filter fun u => G.dist w u = 1).card : ℤ) := by
    intro w hw
    unfold levelExcess
    have hsub : ∑ u ∈ levelSet G w 1, excess G u =
        ∑ u ∈ B.filter (fun u => G.dist w u = 1), excess G u := by
      symm
      refine Finset.sum_subset (fun u hu => ?_) (fun u hu hnot => ?_)
      · simp only [Finset.mem_filter] at hu; rw [mem_levelSet]; exact hu.2
      · rw [mem_levelSet] at hu
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, hu, and_true] at hnot
        have hnn := excess_nonneg (by norm_num) hG hD u
        omega
    rw [hsub]
    have h1 : ∀ u ∈ B.filter (fun u => G.dist w u = 1), excess G u = 1 := by
      intro u hu
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have hpar := weight_parity_of_dist hG hc (u := w) (w := u)
      have hu_par : hammingWeight u % 2 = 1 - r := by omega
      have hmem : u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)) := by
        rw [← hBo]; exact Finset.mem_filter.2 ⟨Finset.mem_univ u, hu.1, hu_par⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl <;> assumption
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Bounds on c(p) ≤ 8 and c(q) ≤ 6
  have hcp : c p ≤ 8 := by
    have h1 := hC p
    rw [hxp, hX1_pq p hp_par] at h1
    omega
  have hcq : c q ≤ 6 := by
    have h1 := hC q
    rw [hxq, hX1_pq q hq_par] at h1
    omega
  -- For ri ∈ {r1, r2, r3}, c(ri) ≤ 6 + [G.Adj ri p] - b2(ri)
  let adjP : CubeVertex 4 → ℤ := fun u => if G.Adj u p then 1 else 0
  have hcri : ∀ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)),
      c u ≤ 6 + adjP u - ((B.filter fun v => G.dist u v = 2).card : ℤ) := by
    intro u hu
    have hxu : excess G u = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    have hup := hr_par u hu
    have h1 := hC u
    -- levelExcess G u 1 - b1(u) = adjP u
    have hdiff : levelExcess G u 1 - ((B.filter fun v => G.dist u v = 1).card : ℤ) = adjP u := by
      have hsub : levelExcess G u 1 = ∑ v ∈ B.filter (fun v => G.dist u v = 1), excess G v := by
        unfold levelExcess
        symm
        refine Finset.sum_subset (fun v hv => ?_) (fun v hv hnot => ?_)
        · simp only [Finset.mem_filter] at hv; rw [mem_levelSet]; exact hv.2
        · rw [mem_levelSet] at hv
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, hv, and_true] at hnot
          have hnn := excess_nonneg (by norm_num) hG hD v
          omega
      rw [hsub]
      have hterm : ∑ v ∈ B.filter (fun v => G.dist u v = 1), excess G v -
          ((B.filter fun v => G.dist u v = 1).card : ℤ) =
          ∑ v ∈ B.filter (fun v => G.dist u v = 1), (excess G v - 1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hterm]
      have hsub2 : B.filter (fun v => G.dist u v = 1) ⊆ {p, q} := by
        intro v hv
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hpar := weight_parity_of_dist hG hc (u := u) (w := v)
        rw [← hBr]
        exact Finset.mem_filter.2 ⟨Finset.mem_univ v, hv.1, by omega⟩
      have hsum_pq : ∑ v ∈ B.filter (fun v => G.dist u v = 1), (excess G v - 1) =
          ∑ v ∈ ({p, q} : Finset (CubeVertex 4)),
            if v ∈ B.filter (fun v => G.dist u v = 1) then excess G v - 1 else 0 := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub2]
      rw [hsum_pq, Finset.sum_pair hpq, hxp, hxq]
      have hpB : p ∈ B := Finset.mem_filter.2 ⟨Finset.mem_univ p, by omega⟩
      simp only [Finset.mem_filter, hpB, true_and, SimpleGraph.dist_eq_one_iff_adj, adjP]
      split_ifs <;> omega
    rw [hxu] at h1
    linarith [min_le_right (6 : ℤ) (2 + 1 + levelExcess G u 1)]
  -- Let K = {u ∈ {r1, r2, r3} | G.Adj u p}, k = K.card.
  let K : Finset (CubeVertex 4) := ({r1, r2, r3} : Finset (CubeVertex 4)).filter fun u => G.Adj u p
  have hdist2 : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.dist u v = 2 := by
    intro u hu v hv huv
    simp only [K, Finset.mem_filter] at hu hv
    have htri : G.dist u v ≤ G.dist u p + G.dist p v := hc.dist_triangle
    have h1 : G.dist u p = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hu.2
    have h2 : G.dist p v = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hv.2.symm
    have hpar := weight_parity_of_dist hG hc (u := u) (w := v)
    have hup := hr_par u hu.1
    have hvp := hr_par v hv.1
    have hpos : 0 < G.dist u v := by
      by_contra h0
      exact huv (hc.dist_eq_zero_iff.1 (by omega))
    omega
  have hb2_ge : ∀ u ∈ K, (K.card : ℤ) - 1 ≤ ((B.filter fun v => G.dist u v = 2).card : ℤ) := by
    intro u hu
    have hsub : K.erase u ⊆ B.filter (fun v => G.dist u v = 2) := by
      intro v hv
      have hne : v ≠ u := Finset.ne_of_mem_erase hv
      have hvK : v ∈ K := Finset.mem_of_mem_erase hv
      have hvB : v ∈ B := by
        rw [hBsplit]
        exact Finset.mem_union_right _ (Finset.mem_filter.1 hvK).1
      exact Finset.mem_filter.2 ⟨hvB, hdist2 u hu v hvK hne.symm⟩
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hu] at hc1
    have hpos : 1 ≤ K.card := Finset.card_pos.2 ⟨u, hu⟩
    omega
  -- Sum over r1, r2, r3
  have hsum_r : c r1 + c r2 + c r3 ≤ 19 := by
    have hnot : r1 ∉ ({r2, r3} : Finset (CubeVertex 4)) := by simp [h12, h13]
    have hsum1 : c r1 + c r2 + c r3 = ∑ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)), c u := by
      rw [Finset.sum_insert hnot, Finset.sum_pair h23]; ring
    rw [hsum1]
    have hle1 : ∑ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)), c u ≤
        ∑ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)),
          (6 + adjP u - ((B.filter fun v => G.dist u v = 2).card : ℤ)) :=
      Finset.sum_le_sum hcri
    have hKsum : ∑ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)), adjP u = (K.card : ℤ) := by
      simp only [adjP, K]
      rw [← Finset.natCast_card_filter]
    have hb2sum : (K.card : ℤ) * ((K.card : ℤ) - 1) ≤
        ∑ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)),
          ((B.filter fun v => G.dist u v = 2).card : ℤ) := by
      calc (K.card : ℤ) * ((K.card : ℤ) - 1)
          = ∑ _u ∈ K, ((K.card : ℤ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ u ∈ K, ((B.filter fun v => G.dist u v = 2).card : ℤ) := Finset.sum_le_sum hb2_ge
        _ ≤ ∑ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)),
              ((B.filter fun v => G.dist u v = 2).card : ℤ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    have hsum_rhs :
        ∑ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)),
          (6 + adjP u - ((B.filter fun v => G.dist u v = 2).card : ℤ)) =
        18 + (K.card : ℤ) -
          ∑ u ∈ ({r1, r2, r3} : Finset (CubeVertex 4)),
            ((B.filter fun v => G.dist u v = 2).card : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_insert_of_notMem hnot, Finset.card_pair h23, hKsum]
      norm_num
    rw [hsum_rhs] at hle1
    nlinarith [sq_nonneg ((K.card : ℤ) - 1)]
  -- Expand ∑ w ∈ B, x_w * c(w) = 2*c(p) + c(q) + c(r1) + c(r2) + c(r3)
  have hBsum : ∑ w ∈ B, excess G w * c w = 2 * c p + c q + (c r1 + c r2 + c r3) := by
    rw [hBsplit, Finset.sum_union hdisj, Finset.sum_pair hpq]
    have hnot : r1 ∉ ({r2, r3} : Finset (CubeVertex 4)) := by simp [h12, h13]
    rw [Finset.sum_insert hnot, Finset.sum_pair h23, hxp, hxq, hxr1, hxr2, hxr3]
    ring
  linarith

/-- No valid spanning subgraph of `Q_4` has `19` edges (Steps 1–7 of `f4-proof/proof-1.md`). -/
theorem no_valid_q4_nineteen_edges {G : SimpleGraph (CubeVertex 4)}
    (hV : IsValidSpanningSubgraph 4 G) (he : G.edgeSet.ncard = 19) : False := by
  classical
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have ht : edgeExcess G = 3 := by unfold edgeExcess; rw [he]; norm_num
  -- Split branch vertices by parity class
  let B0 : Finset (CubeVertex 4) := univ.filter fun u => 0 < excess G u ∧ hammingWeight u % 2 = 0
  let B1 : Finset (CubeVertex 4) := univ.filter fun u => 0 < excess G u ∧ hammingWeight u % 2 = 1
  have hsum_part : ∀ r, r < 2 →
      ∑ u ∈ univ.filter (fun u : CubeVertex 4 => 0 < excess G u ∧ hammingWeight u % 2 = r),
        excess G u = 3 := by
    intro r hr
    have h1 := sum_excess_part (n := 4) (by norm_num) hG r hr
    rw [ht] at h1
    rw [← h1]
    refine Finset.sum_subset (fun u hu => ?_) (fun u hu hnot => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢; exact hu.2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hnot
      have hnn := excess_nonneg (by norm_num) hG hD u
      omega
  have hbound : ∀ r, ∀ u ∈ univ.filter (fun u : CubeVertex 4 => 0 < excess G u ∧ hammingWeight u % 2 = r),
      1 ≤ excess G u ∧ excess G u ≤ 2 := by
    intro r u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hle := excess_le hG u
    omega
  have hc0 := part_excess_three_cases B0 (excess G) (hbound 0) (hsum_part 0 (by norm_num))
  have hc1 := part_excess_three_cases B1 (excess G) (hbound 1) (hsum_part 1 (by norm_num))
  rcases hc0 with ⟨a0, b0, c0, hab0, hac0, hbc0, hB0, hxa0, hxb0, hxc0⟩ |
                  ⟨p0, q0, hpq0, hB0, hxp0, hxq0⟩
  · rcases hc1 with ⟨a1, b1, c1, hab1, hac1, hbc1, hB1, hxa1, hxb1, hxc1⟩ |
                    ⟨p1, q1, hpq1, hB1, hxp1, hxq1⟩
    · -- Case 1: both parts {3, 3, 3}
      let B : Finset (CubeVertex 4) := univ.filter fun u => 0 < excess G u
      let D : Finset (CubeVertex 4) := univ.filter fun u => excess G u = 0
      have hBsplit : B = B0 ∪ B1 := by
        ext u
        simp only [B, B0, B1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hdisj : Disjoint B0 B1 := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        simp only [B0, B1, Finset.mem_filter] at h1 h2
        omega
      have hBcard : B.card = 6 := by
        rw [hBsplit, Finset.card_union_of_disjoint hdisj, hB0, hB1]
        have hn0 : a0 ∉ ({b0, c0} : Finset (CubeVertex 4)) := by simp [hab0, hac0]
        have hn1 : a1 ∉ ({b1, c1} : Finset (CubeVertex 4)) := by simp [hab1, hac1]
        rw [Finset.card_insert_of_notMem hn0, Finset.card_pair hbc0,
          Finset.card_insert_of_notMem hn1, Finset.card_pair hbc1]
      have hDcard : D.card = 10 := by
        have hcomp : D = univ.filter (fun u => ¬(0 < excess G u)) := by
          ext u
          simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
          have hnn := excess_nonneg (by norm_num) hG hD u
          omega
        have htot := Finset.card_filter_add_card_filter_not (s := univ) (fun u : CubeVertex 4 => 0 < excess G u)
        rw [Finset.card_univ, card_vertices] at htot
        change B.card + (univ.filter fun u => ¬(0 < excess G u)).card = 2 ^ 4 at htot
        rw [← hcomp, hBcard] at htot
        norm_num at htot
        omega
      have hall1 : ∀ w ∈ B, excess G w = 1 := by
        intro w hw
        rw [hBsplit, hB0, hB1, Finset.mem_union] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> assumption
      let c : CubeVertex 4 → ℤ := fun w =>
        ((D.filter fun v => G.dist w v = 1).card : ℤ) + ((D.filter fun v => G.dist w v = 2).card : ℤ)
      have hS : 40 ≤ ∑ w ∈ B, c w := by
        have hsumD : 4 * (D.card : ℤ) ≤ ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) := by
          calc 4 * (D.card : ℤ) = ∑ _v ∈ D, (4 : ℤ) := by simp; ring
            _ ≤ ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) := by
              refine Finset.sum_le_sum fun v hv => ?_
              have hxv : excess G v = 0 := (Finset.mem_filter.1 hv).2
              have hL := local_lemma_q4 hV v
              linarith
        have hswap : ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) =
            ∑ w ∈ B, excess G w * c w := by
          have h1 : ∀ k : ℕ, ∑ v ∈ D, levelExcess G v k =
              ∑ w ∈ B, excess G w * ((D.filter fun v => G.dist w v = k).card : ℤ) := by
            intro k
            simp only [levelExcess, levelSet, Finset.sum_filter]
            rw [Finset.sum_comm]
            have hzero : ∑ w : CubeVertex 4, ∑ v ∈ D, (if G.dist v w = k then excess G w else 0) =
                ∑ w ∈ B, ∑ v ∈ D, (if G.dist v w = k then excess G w else 0) := by
              rw [← Finset.sum_subset (Finset.subset_univ B)]
              intro w _ hw
              have hxw : excess G w = 0 := by
                simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hw
                have hnn := excess_nonneg (by norm_num) hG hD w
                omega
              simp [hxw]
            rw [hzero]
            refine Finset.sum_congr rfl fun w _ => ?_
            have hcomm : ∀ v, (if G.dist v w = k then excess G w else 0) =
                if G.dist w v = k then excess G w else 0 := fun v => by rw [SimpleGraph.dist_comm]
            simp_rw [hcomm]
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          rw [Finset.sum_add_distrib, h1 1, h1 2, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => by simp only [c]; ring
        have hB1' : ∑ w ∈ B, excess G w * c w = ∑ w ∈ B, c w :=
          Finset.sum_congr rfl fun w hw => by rw [hall1 w hw, one_mul]
        rw [hDcard] at hsumD
        norm_num at hsumD
        linarith
      have hcle : ∀ w ∈ B, c w ≤ 6 := by
        intro w hw
        have hpart : ∀ k : ℕ, ((D.filter fun u => G.dist w u = k).card : ℤ) +
            ((B.filter fun u => G.dist w u = k).card : ℤ) = ((levelSet G w k).card : ℤ) := by
          intro k
          have hunion : (D.filter fun u => G.dist w u = k) ∪ (B.filter fun u => G.dist w u = k) =
              levelSet G w k := by
            ext u
            simp only [D, B, levelSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            have hnn := excess_nonneg (by norm_num) hG hD u
            omega
          have hd : Disjoint (D.filter fun u => G.dist w u = k) (B.filter fun u => G.dist w u = k) := by
            rw [Finset.disjoint_left]; intro u h1 h2; simp only [D, B, Finset.mem_filter] at h1 h2; omega
          have hc' := Finset.card_union_of_disjoint hd
          rw [hunion] at hc'
          exact_mod_cast hc'.symm
        have hp1 := hpart 1
        have hp2 := hpart 2
        rw [card_levelSet_one, hall1 w hw] at hp1
        have hs2 : ((levelSet G w 2).card : ℤ) ≤ 2 + excess G w + levelExcess G w 1 := by
          have h := level_growth_bound hV w (k := 2) (by norm_num)
          have hY1 : ballExcess G w (2 - 1) = excess G w + levelExcess G w 1 := by
            simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc w]
          linarith
        have hX1 : levelExcess G w 1 = ((B.filter fun u => G.dist w u = 1).card : ℤ) := by
          unfold levelExcess
          have hsub : ∑ u ∈ levelSet G w 1, excess G u =
              ∑ u ∈ B.filter (fun u => G.dist w u = 1), excess G u := by
            symm
            refine Finset.sum_subset (fun u hu => ?_) (fun u hu hnot => ?_)
            · simp only [Finset.mem_filter] at hu; rw [mem_levelSet]; exact hu.2
            · rw [mem_levelSet] at hu
              simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, hu, and_true] at hnot
              have hnn := excess_nonneg (by norm_num) hG hD u
              omega
          rw [hsub, Finset.sum_congr rfl fun u hu => hall1 u (Finset.mem_filter.1 hu).1,
            Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hall1 w hw, hX1] at hs2
        simp only [c]
        omega
      have htot : ∑ w ∈ B, c w ≤ 36 := by
        calc ∑ w ∈ B, c w ≤ ∑ _w ∈ B, (6 : ℤ) := Finset.sum_le_sum hcle
          _ = 6 * (B.card : ℤ) := by simp; ring
          _ = 36 := by rw [hBcard]; norm_num
      linarith
    · -- Case 2 (part 1 is {4, 3}, part 0 is {3, 3, 3})
      exact q4_case_43_333 hV 1 (by norm_num) p1 q1 a0 b0 c0 hpq1 hab0 hac0 hbc0
        hB1 hB0 hxp1 hxq1 hxa0 hxb0 hxc0
  · rcases hc1 with ⟨a1, b1, c1, hab1, hac1, hbc1, hB1, hxa1, hxb1, hxc1⟩ |
                    ⟨p1, q1, hpq1, hB1, hxp1, hxq1⟩
    · -- Case 2 (part 0 is {4, 3}, part 1 is {3, 3, 3})
      exact q4_case_43_333 hV 0 (by norm_num) p0 q0 a1 b1 c1 hpq0 hab1 hac1 hbc1
        hB0 hB1 hxp0 hxq0 hxa1 hxb1 hxc1
    · -- Case 3: both parts {4, 3}
      let B : Finset (CubeVertex 4) := univ.filter fun u => 0 < excess G u
      let D : Finset (CubeVertex 4) := univ.filter fun u => excess G u = 0
      have hBsplit : B = ({p0, q0} : Finset (CubeVertex 4)) ∪ {p1, q1} := by
        rw [← hB0, ← hB1]
        ext u
        simp only [B, B0, B1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hdisj : Disjoint ({p0, q0} : Finset (CubeVertex 4)) {p1, q1} := by
        rw [← hB0, ← hB1, Finset.disjoint_left]
        intro u h1 h2
        simp only [B0, B1, Finset.mem_filter] at h1 h2
        omega
      have hBcard : B.card = 4 := by
        rw [hBsplit, Finset.card_union_of_disjoint hdisj, Finset.card_pair hpq0, Finset.card_pair hpq1]
      have hDcard : D.card = 12 := by
        have hcomp : D = univ.filter (fun u => ¬(0 < excess G u)) := by
          ext u
          simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
          have hnn := excess_nonneg (by norm_num) hG hD u
          omega
        have htot := Finset.card_filter_add_card_filter_not (s := univ) (fun u : CubeVertex 4 => 0 < excess G u)
        rw [Finset.card_univ, card_vertices] at htot
        change B.card + (univ.filter fun u => ¬(0 < excess G u)).card = 2 ^ 4 at htot
        rw [← hcomp, hBcard] at htot
        norm_num at htot
        omega
      let c : CubeVertex 4 → ℤ := fun w =>
        ((D.filter fun v => G.dist w v = 1).card : ℤ) + ((D.filter fun v => G.dist w v = 2).card : ℤ)
      have hS : 48 ≤ 2 * c p0 + c q0 + 2 * c p1 + c q1 := by
        have hsumD : 4 * (D.card : ℤ) ≤ ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) := by
          calc 4 * (D.card : ℤ) = ∑ _v ∈ D, (4 : ℤ) := by simp; ring
            _ ≤ ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) := by
              refine Finset.sum_le_sum fun v hv => ?_
              have hxv : excess G v = 0 := (Finset.mem_filter.1 hv).2
              have hL := local_lemma_q4 hV v
              linarith
        have hswap : ∑ v ∈ D, (levelExcess G v 1 + levelExcess G v 2) =
            ∑ w ∈ B, excess G w * c w := by
          have h1 : ∀ k : ℕ, ∑ v ∈ D, levelExcess G v k =
              ∑ w ∈ B, excess G w * ((D.filter fun v => G.dist w v = k).card : ℤ) := by
            intro k
            simp only [levelExcess, levelSet, Finset.sum_filter]
            rw [Finset.sum_comm]
            have hzero : ∑ w : CubeVertex 4, ∑ v ∈ D, (if G.dist v w = k then excess G w else 0) =
                ∑ w ∈ B, ∑ v ∈ D, (if G.dist v w = k then excess G w else 0) := by
              rw [← Finset.sum_subset (Finset.subset_univ B)]
              intro w _ hw
              have hxw : excess G w = 0 := by
                simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hw
                have hnn := excess_nonneg (by norm_num) hG hD w
                omega
              simp [hxw]
            rw [hzero]
            refine Finset.sum_congr rfl fun w _ => ?_
            have hcomm : ∀ v, (if G.dist v w = k then excess G w else 0) =
                if G.dist w v = k then excess G w else 0 := fun v => by rw [SimpleGraph.dist_comm]
            simp_rw [hcomm]
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          rw [Finset.sum_add_distrib, h1 1, h1 2, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => by simp only [c]; ring
        have hBsum : ∑ w ∈ B, excess G w * c w = 2 * c p0 + c q0 + 2 * c p1 + c q1 := by
          rw [hBsplit, Finset.sum_union hdisj, Finset.sum_pair hpq0, Finset.sum_pair hpq1,
            hxp0, hxq0, hxp1, hxq1]
          ring
        rw [hDcard] at hsumD
        norm_num at hsumD
        linarith
      -- Bound (C) for any vertex w
      have hC : ∀ w : CubeVertex 4,
          c w ≤ (2 + excess G w - ((B.filter fun u => G.dist w u = 1).card : ℤ)) +
            min 6 (2 + excess G w + levelExcess G w 1) -
            ((B.filter fun u => G.dist w u = 2).card : ℤ) := by
        intro w
        have hpart : ∀ k : ℕ, ((D.filter fun u => G.dist w u = k).card : ℤ) +
            ((B.filter fun u => G.dist w u = k).card : ℤ) = ((levelSet G w k).card : ℤ) := by
          intro k
          have hunion : (D.filter fun u => G.dist w u = k) ∪ (B.filter fun u => G.dist w u = k) =
              levelSet G w k := by
            ext u
            simp only [D, B, levelSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            have hnn := excess_nonneg (by norm_num) hG hD u
            omega
          have hd : Disjoint (D.filter fun u => G.dist w u = k) (B.filter fun u => G.dist w u = k) := by
            rw [Finset.disjoint_left]; intro u h1 h2; simp only [D, B, Finset.mem_filter] at h1 h2; omega
          have hc' := Finset.card_union_of_disjoint hd
          rw [hunion] at hc'
          exact_mod_cast hc'.symm
        have hp1 := hpart 1
        have hp2 := hpart 2
        rw [card_levelSet_one] at hp1
        have hs2a : ((levelSet G w 2).card : ℤ) ≤ 6 :=
          by exact_mod_cast card_levelSet_two_le hG hc w
        have hs2b : ((levelSet G w 2).card : ℤ) ≤ 2 + excess G w + levelExcess G w 1 := by
          have h := level_growth_bound hV w (k := 2) (by norm_num)
          have hY1 : ballExcess G w (2 - 1) = excess G w + levelExcess G w 1 := by
            simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc w]
          linarith
        have hmin : ((levelSet G w 2).card : ℤ) ≤ min 6 (2 + excess G w + levelExcess G w 1) :=
          le_min hs2a hs2b
        simp only [c]
        linarith
      -- Indicator variables a, s, t, u, β, β' ∈ {0, 1}
      let a : ℤ := if G.Adj p0 p1 then 1 else 0
      let s : ℤ := if G.Adj q0 p1 then 1 else 0
      let t : ℤ := if G.Adj p0 q1 then 1 else 0
      let u : ℤ := if G.Adj q0 q1 then 1 else 0
      let β : ℤ := if G.dist p0 q0 = 2 then 1 else 0
      let β' : ℤ := if G.dist p1 q1 = 2 then 1 else 0
      -- Exact formulas for b1, X1, b2, X2 at p0, q0, p1, q1
      have hp0_par : hammingWeight p0 % 2 = 0 := by
        have hm : p0 ∈ B0 := by rw [hB0]; simp
        exact (Finset.mem_filter.1 hm).2.2
      have hq0_par : hammingWeight q0 % 2 = 0 := by
        have hm : q0 ∈ B0 := by rw [hB0]; simp
        exact (Finset.mem_filter.1 hm).2.2
      have hp1_par : hammingWeight p1 % 2 = 1 := by
        have hm : p1 ∈ B1 := by rw [hB1]; simp
        exact (Finset.mem_filter.1 hm).2.2
      have hq1_par : hammingWeight q1 % 2 = 1 := by
        have hm : q1 ∈ B1 := by rw [hB1]; simp
        exact (Finset.mem_filter.1 hm).2.2
      -- Helper to evaluate ∑_{v ∈ B, dist w v = k} g v when B ∩ parity(w+k) = {x, y}
      have heval_pair : ∀ (w x y : CubeVertex 4) (k : ℕ) (hxy : x ≠ y)
          (hBk : ∀ v ∈ B, G.dist w v = k → v ∈ ({x, y} : Finset (CubeVertex 4)))
          (hxB : x ∈ B) (hyB : y ∈ B) (g : CubeVertex 4 → ℤ),
          ∑ v ∈ B.filter (fun v => G.dist w v = k), g v =
            (if G.dist w x = k then g x else 0) + (if G.dist w y = k then g y else 0) := by
        intro w x y k hxy hBk hxB hyB g
        have hsub : B.filter (fun v => G.dist w v = k) ⊆ {x, y} := fun v hv =>
          hBk v (Finset.mem_filter.1 hv).1 (Finset.mem_filter.1 hv).2
        have h1 : ∑ v ∈ B.filter (fun v => G.dist w v = k), g v =
            ∑ v ∈ ({x, y} : Finset (CubeVertex 4)),
              if v ∈ B.filter (fun v => G.dist w v = k) then g v else 0 := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
        rw [h1, Finset.sum_pair hxy]
        simp [hxB, hyB]
      have hX_eq : ∀ w k, levelExcess G w k =
          ∑ v ∈ B.filter (fun v => G.dist w v = k), excess G v := by
        intro w k
        unfold levelExcess
        symm
        refine Finset.sum_subset (fun v hv => ?_) (fun v hv hnot => ?_)
        · rw [mem_levelSet]; exact (Finset.mem_filter.1 hv).2
        · rw [mem_levelSet] at hv
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, hv, and_true] at hnot
          have hnn := excess_nonneg (by norm_num) hG hD v
          omega
      have hp0B : p0 ∈ B := by rw [hBsplit]; simp
      have hq0B : q0 ∈ B := by rw [hBsplit]; simp
      have hp1B : p1 ∈ B := by rw [hBsplit]; simp
      have hq1B : q1 ∈ B := by rw [hBsplit]; simp
      have hB_odd_of_even : ∀ w, hammingWeight w % 2 = 0 →
          ∀ v ∈ B, G.dist w v = 1 → v ∈ ({p1, q1} : Finset (CubeVertex 4)) := by
        intro w hw v hv hd
        have hpar := weight_parity_of_dist hG hc (u := w) (w := v)
        rw [← hB1]; exact Finset.mem_filter.2 ⟨Finset.mem_univ v, (Finset.mem_filter.1 hv).2, by omega⟩
      have hB_even_of_odd : ∀ w, hammingWeight w % 2 = 1 →
          ∀ v ∈ B, G.dist w v = 1 → v ∈ ({p0, q0} : Finset (CubeVertex 4)) := by
        intro w hw v hv hd
        have hpar := weight_parity_of_dist hG hc (u := w) (w := v)
        rw [← hB0]; exact Finset.mem_filter.2 ⟨Finset.mem_univ v, (Finset.mem_filter.1 hv).2, by omega⟩
      have hB_even_of_even : ∀ w, hammingWeight w % 2 = 0 →
          ∀ v ∈ B, G.dist w v = 2 → v ∈ ({p0, q0} : Finset (CubeVertex 4)) := by
        intro w hw v hv hd
        have hpar := weight_parity_of_dist hG hc (u := w) (w := v)
        rw [← hB0]; exact Finset.mem_filter.2 ⟨Finset.mem_univ v, (Finset.mem_filter.1 hv).2, by omega⟩
      have hB_odd_of_odd : ∀ w, hammingWeight w % 2 = 1 →
          ∀ v ∈ B, G.dist w v = 2 → v ∈ ({p1, q1} : Finset (CubeVertex 4)) := by
        intro w hw v hv hd
        have hpar := weight_parity_of_dist hG hc (u := w) (w := v)
        rw [← hB1]; exact Finset.mem_filter.2 ⟨Finset.mem_univ v, (Finset.mem_filter.1 hv).2, by omega⟩
      -- Evaluate c bounds at p0, q0, p1, q1
      have hcp0 : c p0 ≤ (4 - (a + t)) + min 6 (4 + 2 * a + t) - β := by
        have h1 := hC p0
        have hb1 : ((B.filter fun v => G.dist p0 v = 1).card : ℤ) = a + t := by
          have h := heval_pair p0 p1 q1 1 hpq1 (hB_odd_of_even p0 hp0_par) hp1B hq1B (fun _ => (1 : ℤ))
          rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
          rw [h]
          simp only [SimpleGraph.dist_eq_one_iff_adj, a, t]
        have hX1 : levelExcess G p0 1 = 2 * a + t := by
          rw [hX_eq, heval_pair p0 p1 q1 1 hpq1 (hB_odd_of_even p0 hp0_par) hp1B hq1B (excess G)]
          simp only [SimpleGraph.dist_eq_one_iff_adj, hxp1, hxq1, a, t]
          split_ifs <;> ring
        have hb2 : ((B.filter fun v => G.dist p0 v = 2).card : ℤ) = β := by
          have h := heval_pair p0 p0 q0 2 hpq0 (hB_even_of_even p0 hp0_par) hp0B hq0B (fun _ => (1 : ℤ))
          rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
          rw [h, SimpleGraph.dist_self]
          norm_num [β]
        rw [hxp0, hb1, hX1, hb2] at h1
        have hmin : min (6 : ℤ) (2 + 2 + (2 * a + t)) = min 6 (4 + 2 * a + t) := by ring_nf
        rw [hmin] at h1
        linarith
      have hcq0 : c q0 ≤ (3 - (s + u)) + min 6 (3 + 2 * s + u) - β := by
        have h1 := hC q0
        have hb1 : ((B.filter fun v => G.dist q0 v = 1).card : ℤ) = s + u := by
          have h := heval_pair q0 p1 q1 1 hpq1 (hB_odd_of_even q0 hq0_par) hp1B hq1B (fun _ => (1 : ℤ))
          rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
          rw [h]
          simp only [SimpleGraph.dist_eq_one_iff_adj, s, u]
        have hX1 : levelExcess G q0 1 = 2 * s + u := by
          rw [hX_eq, heval_pair q0 p1 q1 1 hpq1 (hB_odd_of_even q0 hq0_par) hp1B hq1B (excess G)]
          simp only [SimpleGraph.dist_eq_one_iff_adj, hxp1, hxq1, s, u]
          split_ifs <;> ring
        have hb2 : ((B.filter fun v => G.dist q0 v = 2).card : ℤ) = β := by
          have h := heval_pair q0 p0 q0 2 hpq0 (hB_even_of_even q0 hq0_par) hp0B hq0B (fun _ => (1 : ℤ))
          rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
          rw [h, SimpleGraph.dist_self, SimpleGraph.dist_comm (u := q0) (v := p0)]
          norm_num [β]
        rw [hxq0, hb1, hX1, hb2] at h1
        have hmin : min (6 : ℤ) (2 + 1 + (2 * s + u)) = min 6 (3 + 2 * s + u) := by ring_nf
        rw [hmin] at h1
        linarith
      have hcp1 : c p1 ≤ (4 - (a + s)) + min 6 (4 + 2 * a + s) - β' := by
        have h1 := hC p1
        have hb1 : ((B.filter fun v => G.dist p1 v = 1).card : ℤ) = a + s := by
          have h := heval_pair p1 p0 q0 1 hpq0 (hB_even_of_odd p1 hp1_par) hp0B hq0B (fun _ => (1 : ℤ))
          rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
          rw [h]
          simp only [SimpleGraph.dist_eq_one_iff_adj, G.adj_comm p1 p0, G.adj_comm p1 q0, a, s]
        have hX1 : levelExcess G p1 1 = 2 * a + s := by
          rw [hX_eq, heval_pair p1 p0 q0 1 hpq0 (hB_even_of_odd p1 hp1_par) hp0B hq0B (excess G)]
          simp only [SimpleGraph.dist_eq_one_iff_adj, G.adj_comm p1 p0, G.adj_comm p1 q0, hxp0, hxq0, a, s]
          split_ifs <;> ring
        have hb2 : ((B.filter fun v => G.dist p1 v = 2).card : ℤ) = β' := by
          have h := heval_pair p1 p1 q1 2 hpq1 (hB_odd_of_odd p1 hp1_par) hp1B hq1B (fun _ => (1 : ℤ))
          rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
          rw [h, SimpleGraph.dist_self]
          norm_num [β']
        rw [hxp1, hb1, hX1, hb2] at h1
        have hmin : min (6 : ℤ) (2 + 2 + (2 * a + s)) = min 6 (4 + 2 * a + s) := by ring_nf
        rw [hmin] at h1
        linarith
      have hcq1 : c q1 ≤ (3 - (t + u)) + min 6 (3 + 2 * t + u) - β' := by
        have h1 := hC q1
        have hb1 : ((B.filter fun v => G.dist q1 v = 1).card : ℤ) = t + u := by
          have h := heval_pair q1 p0 q0 1 hpq0 (hB_even_of_odd q1 hq1_par) hp0B hq0B (fun _ => (1 : ℤ))
          rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
          rw [h]
          simp only [SimpleGraph.dist_eq_one_iff_adj, G.adj_comm q1 p0, G.adj_comm q1 q0, t, u]
        have hX1 : levelExcess G q1 1 = 2 * t + u := by
          rw [hX_eq, heval_pair q1 p0 q0 1 hpq0 (hB_even_of_odd q1 hq1_par) hp0B hq0B (excess G)]
          simp only [SimpleGraph.dist_eq_one_iff_adj, G.adj_comm q1 p0, G.adj_comm q1 q0, hxp0, hxq0, t, u]
          split_ifs <;> ring
        have hb2 : ((B.filter fun v => G.dist q1 v = 2).card : ℤ) = β' := by
          have h := heval_pair q1 p1 q1 2 hpq1 (hB_odd_of_odd q1 hq1_par) hp1B hq1B (fun _ => (1 : ℤ))
          rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
          rw [h, SimpleGraph.dist_self, SimpleGraph.dist_comm (u := q1) (v := p1)]
          norm_num [β']
        rw [hxq1, hb1, hX1, hb2] at h1
        have hmin : min (6 : ℤ) (2 + 1 + (2 * t + u)) = min 6 (3 + 2 * t + u) := by ring_nf
        rw [hmin] at h1
        linarith
      -- Check bounds on indicator variables: forces s = 0, β = 0!
      have ha01 : a = 0 ∨ a = 1 := by simp only [a]; split_ifs <;> simp
      have hs01 : s = 0 ∨ s = 1 := by simp only [s]; split_ifs <;> simp
      have ht01 : t = 0 ∨ t = 1 := by simp only [t]; split_ifs <;> simp
      have hu01 : u = 0 ∨ u = 1 := by simp only [u]; split_ifs <;> simp
      have hβ01 : β = 0 ∨ β = 1 := by simp only [β]; split_ifs <;> simp
      have hβ'01 : β' = 0 ∨ β' = 1 := by simp only [β']; split_ifs <;> simp
      have hforce : s = 0 ∧ β = 0 := by omega
      -- Now (L) fails at q0!
      have hLq0 := local_lemma_q4 hV q0
      have hX1q0 : levelExcess G q0 1 = 2 * s + u := by
        rw [hX_eq, heval_pair q0 p1 q1 1 hpq1 (hB_odd_of_even q0 hq0_par) hp1B hq1B (excess G)]
        simp only [SimpleGraph.dist_eq_one_iff_adj, hxp1, hxq1, s, u]
        split_ifs <;> ring
      have hX2q0 : levelExcess G q0 2 = 2 * β := by
        rw [hX_eq, heval_pair q0 p0 q0 2 hpq0 (hB_even_of_even q0 hq0_par) hp0B hq0B (excess G)]
        rw [SimpleGraph.dist_self, SimpleGraph.dist_comm (u := q0) (v := p0), hxp0]
        simp only [β]
        split_ifs <;> first | contradiction | norm_num
      omega

/-- `f(4) ≥ 20` (Theorem of `f4-proof/proof-1.md`). -/
theorem f_four_ge_twenty : 20 ≤ f 4 := by
  apply le_f_of_forall_valid
  intro G hV
  have h19 := theorem1_lower_bound_nat_ceil (n := 4) (by norm_num) hV
  norm_num at h19
  by_contra hlt
  have h19eq : G.edgeSet.ncard = 19 := by omega
  exact no_valid_q4_nineteen_edges hV h19eq

/-- Exact value `f(4) = 20`. -/
theorem f_four_eq_twenty : f 4 = 20 :=
  le_antisymm f_four_le_twenty f_four_ge_twenty

/-! ### Theorem 2 (`f(5) ≥ 39`): Steps 8–15 of `fn-bound/bound-1.md` -/

/-- Concentration dichotomy on a parity part with excess sum `6` and each `0 ≤ x_u ≤ 3`:
`∑ x_u^2 ≤ 18`, and `15 ≤ ∑ x_u^2` forces the `{3, 3}` configuration (two vertices of excess 3,
all others of excess 0). -/
private theorem part_sum_sq_dichotomy {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℤ)
    (hbound : ∀ a ∈ S, 0 ≤ x a ∧ x a ≤ 3)
    (hsum : ∑ a ∈ S, x a = 6) :
    (∑ a ∈ S, x a ^ 2 ≤ 18) ∧
    (15 ≤ ∑ a ∈ S, x a ^ 2 →
      ∃ a1 a2, a1 ∈ S ∧ a2 ∈ S ∧ a1 ≠ a2 ∧ x a1 = 3 ∧ x a2 = 3 ∧
        ∀ u ∈ S, u ≠ a1 → u ≠ a2 → x u = 0) := by
  constructor
  · calc ∑ a ∈ S, x a ^ 2 ≤ ∑ a ∈ S, 3 * x a := by
          refine Finset.sum_le_sum fun a ha => ?_
          have ⟨h0, h3⟩ := hbound a ha
          nlinarith
      _ = 3 * ∑ a ∈ S, x a := by rw [← Finset.mul_sum]
      _ = 18 := by rw [hsum]; norm_num
  · intro h15
    -- First find a1 ∈ S with x a1 = 3
    have hex1 : ∃ a1 ∈ S, x a1 = 3 := by
      by_contra hno
      push Not at hno
      have hle : ∑ a ∈ S, x a ^ 2 ≤ 12 := by
        calc ∑ a ∈ S, x a ^ 2 ≤ ∑ a ∈ S, 2 * x a := by
              refine Finset.sum_le_sum fun a ha => ?_
              have ⟨h0, h3⟩ := hbound a ha
              have hne := hno a ha
              have hle2 : x a ≤ 2 := by omega
              nlinarith
          _ = 2 * ∑ a ∈ S, x a := by rw [← Finset.mul_sum]
          _ = 12 := by rw [hsum]; norm_num
      linarith
    obtain ⟨a1, ha1, hxa1⟩ := hex1
    let S' := S.erase a1
    have hsum' : ∑ a ∈ S', x a = 3 := by
      have h := Finset.add_sum_erase S x ha1
      linarith
    have hsq' : 6 ≤ ∑ a ∈ S', x a ^ 2 := by
      have h := Finset.add_sum_erase S (fun a => x a ^ 2) ha1
      rw [hxa1] at h
      linarith
    -- Next find a2 ∈ S' with x a2 = 3
    have hex2 : ∃ a2 ∈ S', x a2 = 3 := by
      by_contra hno
      push Not at hno
      have hle : ∀ a ∈ S', 0 ≤ 2 * x a - x a ^ 2 := by
        intro a ha
        have ⟨h0, h3⟩ := hbound a (Finset.mem_of_mem_erase ha)
        have hne := hno a ha
        have hle2 : x a ≤ 2 := by omega
        nlinarith
      have hsum_diff : ∑ a ∈ S', (2 * x a - x a ^ 2) ≤ 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum']
        linarith
      have hsum_zero : ∑ a ∈ S', (2 * x a - x a ^ 2) = 0 :=
        le_antisymm hsum_diff (Finset.sum_nonneg hle)
      have hall_even : ∀ a ∈ S', 2 ∣ x a := by
        intro a ha
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg hle).1 hsum_zero a ha
        have ⟨hlo, hhi⟩ := hbound a (Finset.mem_of_mem_erase ha)
        have hor : x a = 0 ∨ x a = 1 ∨ x a = 2 ∨ x a = 3 := by omega
        rcases hor with h | h | h | h
        · simp [h]
        · simp [h] at h0
        · simp [h]
        · simp [h] at h0
      have hdvd : (2 : ℤ) ∣ ∑ a ∈ S', x a := Finset.dvd_sum hall_even
      rw [hsum'] at hdvd
      omega
    obtain ⟨a2, ha2', hxa2⟩ := hex2
    have ha2 : a2 ∈ S := Finset.mem_of_mem_erase ha2'
    have hne12 : a1 ≠ a2 := (Finset.ne_of_mem_erase ha2').symm
    refine ⟨a1, a2, ha1, ha2, hne12, hxa1, hxa2, fun u hu hu1 hu2 => ?_⟩
    have hrem : ∑ a ∈ S'.erase a2, x a = 0 := by
      have h := Finset.add_sum_erase S' x ha2'
      linarith
    have hu' : u ∈ S'.erase a2 := Finset.mem_erase.2 ⟨hu2, Finset.mem_erase.2 ⟨hu1, hu⟩⟩
    exact (Finset.sum_eq_zero_iff_of_nonneg fun a ha =>
      (hbound a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha))).1).1 hrem u hu'

/-- Two distinct degree-5 vertices at Hamming distance 2 in `Q_5` create `extraParents G a1 2 ≥ 1`. -/
private theorem q5_full_degree_hamming_two_extraParents {G : SimpleGraph (CubeVertex 5)}
    (hG : G ≤ Q 5) (hc : G.Connected)
    {a1 a2 : CubeVertex 5} (hh : hammingDist a1 a2 = 2)
    (hx1 : excess G a1 = 3) (hx2 : excess G a2 = 3) :
    1 ≤ extraParents G a1 2 := by
  -- Every Q_5-neighbor of a1 (or a2) is a G-neighbor, because degree = 5 = |Q_5-neighbors|.
  have hfull : ∀ w : CubeVertex 5, excess G w = 3 → ∀ u, hammingDist w u = 1 → G.Adj w u := by
    intro w hxw u hwu
    have hdeg : (G.neighborSet w).ncard = 5 := by unfold excess at hxw; omega
    have hsub : G.neighborSet w ⊆
        ((univ.filter fun y => hammingDist w y = 1 : Finset (CubeVertex 5)) : Set (CubeVertex 5)) := by
      intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hG hy
    have hcard : ((univ.filter fun y => hammingDist w y = 1 : Finset (CubeVertex 5)) : Set (CubeVertex 5)).ncard = 5 := by
      rw [Set.ncard_coe_finset, card_hamming_sphere w 1]
      norm_num
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hdeg, hcard]) (Set.toFinite _)
    have hmem : u ∈ ((univ.filter fun y => hammingDist w y = 1 : Finset (CubeVertex 5)) : Set (CubeVertex 5)) := by
      simp [hwu]
    rw [← heq] at hmem
    exact hmem
  -- Find the two distinct coordinates i ≠ j where a1 and a2 differ
  rw [hammingDist, Finset.card_eq_two] at hh
  obtain ⟨i, j, hij, hdiff⟩ := hh
  have hi : a1 i ≠ a2 i := by
    have hm : i ∈ univ.filter (fun k => a1 k ≠ a2 k) := by rw [hdiff]; simp
    exact (Finset.mem_filter.1 hm).2
  have hj : a1 j ≠ a2 j := by
    have hm : j ∈ univ.filter (fun k => a1 k ≠ a2 k) := by rw [hdiff]; simp
    exact (Finset.mem_filter.1 hm).2
  have hhh : hammingDist a1 a2 = 2 := by rw [hammingDist, hdiff, Finset.card_pair hij]
  let c1 := flipAt i a1
  let c2 := flipAt j a1
  have hc12 : c1 ≠ c2 := by
    intro heq
    have h := congr_fun heq i
    simp only [c1, c2, flipAt_apply_self, flipAt_apply_of_ne a1 hij] at h
    exact bool_ne_not (a1 i) h.symm
  have hc1_a1 : G.Adj a1 c1 := hfull a1 hx1 c1 (hammingDist_flipAt i a1)
  have hc2_a1 : G.Adj a1 c2 := hfull a1 hx1 c2 (hammingDist_flipAt j a1)
  have hc1_a2 : G.Adj a2 c1 := by
    apply hfull a2 hx2 c1
    rw [hammingDist_comm]
    change hammingDist (flipAt i a1) a2 = 1
    have h := hammingDist_flipAt_of_ne hi
    omega
  have hc2_a2 : G.Adj a2 c2 := by
    apply hfull a2 hx2 c2
    rw [hammingDist_comm]
    change hammingDist (flipAt j a1) a2 = 1
    have h := hammingDist_flipAt_of_ne hj
    omega
  -- Hence G.dist a1 a2 = 2
  have hdist : G.dist a1 a2 = 2 := by
    have hle : G.dist a1 a2 ≤ 2 := by
      have h1 : G.dist a1 c1 = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hc1_a1
      have h2 : G.dist c1 a2 = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hc1_a2.symm
      have ht := hc.dist_triangle (u := a1) (v := c1) (w := a2)
      omega
    have hge := (dist_hamming hG hc a1 a2).1
    omega
  -- And both c1, c2 are parents of a2 in level 2 from a1
  have hpar2 : 2 ≤ parentCount G a1 2 a2 := by
    have hsub : ({c1, c2} : Set (CubeVertex 5)) ⊆ {w | G.Adj a2 w ∧ G.dist a1 w + 1 = 2} := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨hc1_a2, by rw [SimpleGraph.dist_eq_one_iff_adj.2 hc1_a1]⟩
      · exact ⟨hc2_a2, by rw [SimpleGraph.dist_eq_one_iff_adj.2 hc2_a1]⟩
    calc 2 = ({c1, c2} : Set (CubeVertex 5)).ncard := (Set.ncard_pair hc12).symm
      _ ≤ parentCount G a1 2 a2 := Set.ncard_le_ncard hsub
  have ha2_mem : a2 ∈ levelSet G a1 2 := mem_levelSet.2 hdist
  have hnn : ∀ u ∈ levelSet G a1 2, 0 ≤ ((parentCount G a1 2 u : ℤ) - 1) := by
    intro u hu
    rw [mem_levelSet] at hu
    obtain ⟨w, hw, hwd⟩ := exists_parent hc (show 1 ≤ G.dist a1 u by omega)
    have hpos : 0 < parentCount G a1 2 u := (Set.ncard_pos (Set.toFinite _)).2 ⟨w, hw, by omega⟩
    omega
  unfold extraParents
  calc (1 : ℤ) ≤ ((parentCount G a1 2 a2 : ℤ) - 1) := by omega
    _ ≤ ∑ u ∈ levelSet G a1 2, ((parentCount G a1 2 u : ℤ) - 1) :=
        Finset.single_le_sum hnn ha2_mem

/-- Theorem 2 (`fn-bound/bound-1.md`, Steps 8–15): no valid spanning subgraph of `Q_5`
has `38` edges. -/
theorem no_valid_q5_thirtyeight_edges {G : SimpleGraph (CubeVertex 5)}
    (hV : IsValidSpanningSubgraph 5 G) (he : G.edgeSet.ncard = 38) : False := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have ht : edgeExcess G = 6 := by unfold edgeExcess; rw [he]; norm_num
  have hXtot : ∑ u : CubeVertex 5, excess G u = 12 := by rw [sum_excess, ht]; norm_num
  have hnn : ∀ u : CubeVertex 5, 0 ≤ excess G u := excess_nonneg (by norm_num) hG hD
  have hle3 : ∀ u : CubeVertex 5, excess G u ≤ 3 := fun u => by
    have := excess_le hG u; norm_num at this; exact this
  -- Step 8: Y_1(v) + Y_3(v) = 11 + M(v)
  have hstep8 : ∀ v : CubeVertex 5,
      ballExcess G v 1 + ballExcess G v 3 = 11 + weightedExtra G v := by
    intro v
    have hpc := part_c (n := 5) (by norm_num) hG hD v
    have hr : rSet 5 = {1, 3} := by decide
    unfold lSum at hpc
    rw [hr, Finset.sum_pair (by decide)] at hpc
    norm_num at hpc
    linarith
  -- Step 9: farExcess(v) + M(v) = Y_1(v) + 1, and Z(v̄) + M(v) ≤ Y_1(v) + 1 (A)
  let farExcess : CubeVertex 5 → ℤ := fun v =>
    ∑ u ∈ univ.filter (fun u => 4 ≤ G.dist v u), excess G u
  have hY3_far : ∀ v : CubeVertex 5, ballExcess G v 3 + farExcess v = 12 := by
    intro v
    have hY3 : ballExcess G v 3 = ∑ u, if G.dist v u < 4 then excess G u else 0 := by
      unfold ballExcess; simp only [levelExcess]; exact levels_sum v (excess G) 4
    have hF : farExcess v = ∑ u, if ¬(G.dist v u < 4) then excess G u else 0 := by
      simp only [farExcess, Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => by
        by_cases h : 4 ≤ G.dist v u
        · have h' : ¬(G.dist v u < 4) := by omega
          simp [h, h']
        · have h' : G.dist v u < 4 := by omega
          simp [h, h']
    rw [hY3, hF, ← Finset.sum_add_distrib]
    have h1 : ∀ u, (if G.dist v u < 4 then excess G u else 0) +
        (if ¬(G.dist v u < 4) then excess G u else 0) = excess G u := by
      intro u; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun u _ => h1 u, hXtot]
  have hstep9 : ∀ v : CubeVertex 5,
      farExcess v + weightedExtra G v = ballExcess G v 1 + 1 := by
    intro v; linarith [hstep8 v, hY3_far v]
  let Z : CubeVertex 5 → ℤ := fun w =>
    excess G w + ∑ u ∈ univ.filter (fun u => hammingDist w u = 1), excess G u
  have hZ_le_far : ∀ v : CubeVertex 5, Z (antipode v) ≤ farExcess v := by
    intro v
    let S1 : Finset (CubeVertex 5) :=
      insert (antipode v) (univ.filter fun u => hammingDist (antipode v) u = 1)
    have hnot : antipode v ∉ univ.filter (fun u => hammingDist (antipode v) u = 1) := by simp
    have hZeq : Z (antipode v) = ∑ u ∈ S1, excess G u := by
      simp only [Z, S1, Finset.sum_insert hnot]
    rw [hZeq]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) (fun u _ _ => hnn u)
    simp only [S1, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    have hd := (dist_hamming hG hc v u).1
    rw [hammingDist_comm v u] at hd
    have ha := hammingDist_antipode_left v u
    rw [hammingDist_comm v u] at ha
    rcases hu with rfl | h1
    · rw [hammingDist_self] at ha; omega
    · omega
  have hA : ∀ v : CubeVertex 5,
      Z (antipode v) + weightedExtra G v ≤ ballExcess G v 1 + 1 := fun v => by
    linarith [hstep9 v, hZ_le_far v]
  -- Step 10: Y_1(w) ≤ Z(w), hence M(v) ≤ 2 and M_2(v) = 0
  have hY1_le_Z : ∀ w : CubeVertex 5, ballExcess G w 1 ≤ Z w := by
    intro w
    have hY1 : ballExcess G w 1 = excess G w + levelExcess G w 1 := by
      simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc w]
    rw [hY1]
    simp only [Z, levelExcess]
    have hsub : levelSet G w 1 ⊆ univ.filter fun u => hammingDist w u = 1 := by
      intro u hu
      rw [levelSet_one_eq_neighbor] at hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hG hu
    linarith [Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => hnn u]
  have hM2_zero : ∀ v : CubeVertex 5, extraParents G v 2 = 0 := by
    intro v
    have h1 := hA v
    have h2 := hA (antipode v)
    rw [antipode_antipode] at h2
    have h3 := hY1_le_Z (antipode v)
    have h4 := hY1_le_Z v
    have hMnn1 := weightedExtra_nonneg hc v
    have hMnn2 := weightedExtra_nonneg hc (antipode v)
    have hMle : weightedExtra G v ≤ 2 := by linarith
    have hMexp : weightedExtra G v =
        3 * extraParents G v 2 + 2 * extraParents G v 3 + extraParents G v 4 := by
      unfold weightedExtra
      have hI : Ico 2 5 = {2, 3, 4} := by decide
      rw [hI]
      simp [Finset.sum_insert]
      ring
    have hm2 := extraParents_nonneg hc v (k := 2) (by norm_num)
    have hm3 := extraParents_nonneg hc v (k := 3) (by norm_num)
    have hm4 := extraParents_nonneg hc v (k := 4) (by norm_num)
    linarith
  -- Step 11: Global count (♦): 232 ≤ 4 S2 + 2 P1 + P2
  let S2 : ℤ := ∑ u : CubeVertex 5, excess G u ^ 2
  let P1 : ℤ := ∑ u : CubeVertex 5, excess G u * levelExcess G u 1
  let P2 : ℤ := ∑ u : CubeVertex 5, excess G u * levelExcess G u 2
  have hdiamond : 232 ≤ 4 * S2 + 2 * P1 + P2 := by
    have hsum9 : ∑ v : CubeVertex 5, farExcess v + ∑ v : CubeVertex 5, weightedExtra G v =
        ∑ v : CubeVertex 5, ballExcess G v 1 + 32 := by
      have h := Finset.sum_congr rfl fun v (_ : v ∈ univ) => hstep9 v
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
      have hc32 : ∑ _v : CubeVertex 5, (1 : ℤ) = 32 := by
        rw [Finset.sum_const, Finset.card_univ, card_vertices]; norm_num
      linarith
    have hsumM : 0 ≤ ∑ v : CubeVertex 5, weightedExtra G v :=
      Finset.sum_nonneg fun v _ => weightedExtra_nonneg hc v
    -- Compute ∑ v, Y_1(v) = 36 + S2
    have hsumY1 : ∑ v : CubeVertex 5, ballExcess G v 1 = 36 + S2 := by
      have h1 : ∀ v : CubeVertex 5, ballExcess G v 1 = excess G v + levelExcess G v 1 := fun v => by
        simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc v]
      simp_rw [h1]
      rw [Finset.sum_add_distrib, hXtot]
      have hswap : ∑ v : CubeVertex 5, levelExcess G v 1 =
          ∑ u : CubeVertex 5, excess G u * ((levelSet G u 1).card : ℤ) := by
        simp only [levelExcess, levelSet, Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        have hcomm : ∀ v, (if G.dist v u = 1 then excess G u else 0) =
            if G.dist u v = 1 then excess G u else 0 := fun v => by rw [SimpleGraph.dist_comm]
        simp_rw [hcomm]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [hswap]
      have h2 : ∑ u : CubeVertex 5, excess G u * ((levelSet G u 1).card : ℤ) =
          2 * (∑ u : CubeVertex 5, excess G u) + S2 := by
        simp_rw [card_levelSet_one]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => by ring
      rw [h2, hXtot]
      ring
    -- Compute ∑ v, farExcess v ≥ 300 - 3*S2 - 2*P1 - P2
    have hsumFar : 300 - 3 * S2 - 2 * P1 - P2 ≤ ∑ v : CubeVertex 5, farExcess v := by
      have hswap : ∑ v : CubeVertex 5, farExcess v =
          ∑ u : CubeVertex 5, excess G u * ((univ.filter fun v => 4 ≤ G.dist u v).card : ℤ) := by
        simp only [farExcess, Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        have hcomm : ∀ v, (if 4 ≤ G.dist v u then excess G u else 0) =
            if 4 ≤ G.dist u v then excess G u else 0 := fun v => by rw [SimpleGraph.dist_comm]
        simp_rw [hcomm]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [hswap]
      have hfar_card : ∀ u : CubeVertex 5,
          25 - 3 * excess G u - 2 * levelExcess G u 1 - levelExcess G u 2 ≤
            ((univ.filter fun v => 4 ≤ G.dist u v).card : ℤ) := by
        intro u
        have htot32 : ((levelSet G u 0).card : ℤ) + ((levelSet G u 1).card : ℤ) +
            ((levelSet G u 2).card : ℤ) + ((levelSet G u 3).card : ℤ) +
            ((univ.filter fun v => 4 ≤ G.dist u v).card : ℤ) = 32 := by
          have hls := levels_sum (G := G) u (fun _ => (1 : ℤ)) 4
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_range_succ,
            Finset.sum_range_zero, zero_add] at hls
          have hfar' : ((univ.filter fun v => 4 ≤ G.dist u v).card : ℤ) =
              ∑ v : CubeVertex 5, if ¬(G.dist u v < 4) then (1 : ℤ) else 0 := by
            rw [← Finset.natCast_card_filter]
            congr 2; ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
          rw [hls, hfar', ← Finset.sum_add_distrib]
          have hpt : ∀ v : CubeVertex 5,
              (if G.dist u v < 4 then (1 : ℤ) else 0) + (if ¬(G.dist u v < 4) then 1 else 0) = 1 :=
            fun v => by split_ifs <;> ring
          rw [Finset.sum_congr rfl fun v _ => hpt v, Finset.sum_const, Finset.card_univ,
            card_vertices]
          norm_num
        have hs0 : ((levelSet G u 0).card : ℤ) = 1 := by rw [card_levelSet_zero hc u]; norm_num
        have hs1 := card_levelSet_one (G := G) u
        have hs2 := part_a hG hc u 2 (by norm_num)
        have hI2 : ∑ j ∈ Ico 2 2, extraParents G u j = 0 := by simp
        have hY1 : ballExcess G u (2 - 1) = excess G u + levelExcess G u 1 := by
          simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc u]
        rw [hI2, hY1, hM2_zero u] at hs2
        have hs3 := part_a hG hc u 3 (by norm_num)
        have hI3 : ∑ j ∈ Ico 2 3, extraParents G u j = extraParents G u 2 := by
          have : Ico 2 3 = {2} := by decide
          rw [this, Finset.sum_singleton]
        have hY2 : ballExcess G u (3 - 1) = excess G u + levelExcess G u 1 + levelExcess G u 2 := by
          simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc u]
        rw [hI3, hY2, hM2_zero u] at hs3
        have hm3 := extraParents_nonneg hc u (k := 3) (by norm_num)
        linarith
      calc 300 - 3 * S2 - 2 * P1 - P2
          = ∑ u : CubeVertex 5,
              excess G u * (25 - 3 * excess G u - 2 * levelExcess G u 1 - levelExcess G u 2) := by
            have h1 : ∀ u : CubeVertex 5,
                excess G u * (25 - 3 * excess G u - 2 * levelExcess G u 1 - levelExcess G u 2) =
                25 * excess G u - 3 * excess G u ^ 2 - 2 * (excess G u * levelExcess G u 1) -
                  excess G u * levelExcess G u 2 := fun u => by ring
            simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
            rw [hXtot]
            ring
        _ ≤ ∑ u : CubeVertex 5, excess G u * ((univ.filter fun v => 4 ≤ G.dist u v).card : ℤ) :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hfar_card u) (hnn u)
    linarith
  -- Step 12: P1 ≤ P4Q + 12
  let P4Q : ℤ := ∑ u : CubeVertex 5,
    excess G u * (∑ w ∈ univ.filter (fun w => hammingDist u w = 4), excess G w)
  have hstep12 : P1 ≤ P4Q + 12 := by
    have h1 : ∑ u : CubeVertex 5, excess G u * Z u ≤
        ∑ u : CubeVertex 5, excess G u * (ballExcess G (antipode u) 1 + 1) := by
      refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hnn u)
      have ha := hA (antipode u)
      rw [antipode_antipode] at ha
      have hMnn := weightedExtra_nonneg hc (antipode u)
      linarith
    have hLHS : S2 + P1 ≤ ∑ u : CubeVertex 5, excess G u * Z u := by
      calc S2 + P1 = ∑ u : CubeVertex 5, excess G u * ballExcess G u 1 := by
            have hb : ∀ u, excess G u * ballExcess G u 1 =
                excess G u ^ 2 + excess G u * levelExcess G u 1 := fun u => by
              simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc u]; ring
            simp_rw [hb, Finset.sum_add_distrib]
            rfl
        _ ≤ ∑ u : CubeVertex 5, excess G u * Z u :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hY1_le_Z u) (hnn u)
    have hanti_sq : ∑ u : CubeVertex 5, excess G u * excess G (antipode u) ≤ S2 := by
      have hbij : ∑ u : CubeVertex 5, excess G (antipode u) ^ 2 = S2 := by
        refine Finset.sum_nbij' antipode antipode ?_ ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro _ _; exact Finset.mem_univ _
        · intro u _; exact antipode_antipode u
        · intro u _; exact antipode_antipode u
        · intro _ _; rfl
      have h2 : 2 * ∑ u : CubeVertex 5, excess G u * excess G (antipode u) ≤
          ∑ u : CubeVertex 5, (excess G u ^ 2 + excess G (antipode u) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun u _ => by nlinarith [sq_nonneg (excess G u - excess G (antipode u))]
      rw [Finset.sum_add_distrib, hbij] at h2
      linarith
    have hanti_X1 : ∑ u : CubeVertex 5, excess G u * levelExcess G (antipode u) 1 ≤ P4Q := by
      refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hnn u)
      unfold levelExcess
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_) (fun w _ _ => hnn w)
      rw [levelSet_one_eq_neighbor] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : hammingDist (antipode u) w = 1 := hG hw
      have ha := hammingDist_antipode_left u w
      omega
    have hRHS : ∑ u : CubeVertex 5, excess G u * (ballExcess G (antipode u) 1 + 1) ≤ S2 + P4Q + 12 := by
      have hexp : ∑ u : CubeVertex 5, excess G u * (ballExcess G (antipode u) 1 + 1) =
          (∑ u : CubeVertex 5, excess G u * excess G (antipode u)) +
          (∑ u : CubeVertex 5, excess G u * levelExcess G (antipode u) 1) +
          (∑ u : CubeVertex 5, excess G u) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => by
          simp [ballExcess, Finset.sum_range_succ, levelExcess_zero hc (antipode u)]; ring
      rw [hexp, hXtot]
      linarith
    linarith
  -- Step 13: P2 + P4Q ≤ 72 - S2
  let Ppart : ℕ → Finset (CubeVertex 5) := fun r =>
    univ.filter fun u => hammingWeight u % 2 = r
  have hpart_sum : ∀ r, r < 2 → ∑ u ∈ Ppart r, excess G u = 6 := by
    intro r hr
    have h := sum_excess_part (n := 5) (by norm_num) hG r hr
    rw [ht] at h
    exact h
  have hstep13 : P2 + P4Q ≤ 72 - S2 := by
    have hpt : ∀ u : CubeVertex 5,
        levelExcess G u 2 + (∑ w ∈ univ.filter (fun w => hammingDist u w = 4), excess G w) ≤
          6 - excess G u := by
      intro u
      have hdisj : Disjoint (levelSet G u 2) (univ.filter fun w => hammingDist u w = 4) := by
        rw [Finset.disjoint_left]
        intro w h1 h2
        have hle := (levelSet_two_subset_hamming_two hG hc u) h1
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hle h2
        omega
      have hsub : levelSet G u 2 ∪ (univ.filter fun w => hammingDist u w = 4) ⊆
          (Ppart (hammingWeight u % 2)).erase u := by
        intro w hw
        simp only [Finset.mem_union, mem_levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ w, ?_⟩⟩
        · rintro rfl
          rcases hw with h | h
          · simp at h
          · simp at h
        · rcases hw with h | h
          · have hp := weight_parity_of_dist hG hc (u := u) (w := w); omega
          · have hp := weight_parity_of_dist hG hc (u := u) (w := w)
            have hd := (dist_hamming hG hc u w).2; omega
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => hnn w
      rw [Finset.sum_union hdisj] at hle
      have hu_mem : u ∈ Ppart (hammingWeight u % 2) := Finset.mem_filter.2 ⟨Finset.mem_univ u, rfl⟩
      have heq := Finset.add_sum_erase (Ppart (hammingWeight u % 2)) (excess G) hu_mem
      have hps := hpart_sum (hammingWeight u % 2) (Nat.mod_lt _ (by norm_num))
      unfold levelExcess
      linarith
    have hsum_le : P2 + P4Q ≤ ∑ u : CubeVertex 5, excess G u * (6 - excess G u) := by
      simp only [P2, P4Q, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun u _ => ?_
      have h1 : excess G u * levelExcess G u 2 +
          excess G u * (∑ w ∈ univ.filter (fun w => hammingDist u w = 4), excess G w) =
          excess G u * (levelExcess G u 2 +
            ∑ w ∈ univ.filter (fun w => hammingDist u w = 4), excess G w) := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left (hpt u) (hnn u)
    have hrhs : ∑ u : CubeVertex 5, excess G u * (6 - excess G u) = 72 - S2 := by
      have h1 : ∀ u : CubeVertex 5, excess G u * (6 - excess G u) =
          6 * excess G u - excess G u ^ 2 := fun u => by ring
      simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hXtot]
      ring
    linarith
  -- Step 14: 32 ≤ S2, so some part is {3, 3}
  have hP2_nn : 0 ≤ P2 :=
    Finset.sum_nonneg fun u _ => mul_nonneg (hnn u) (Finset.sum_nonneg fun w _ => hnn w)
  have hS2_ge : 32 ≤ S2 := by linarith
  have hS2_split : S2 = ∑ u ∈ Ppart 0, excess G u ^ 2 + ∑ u ∈ Ppart 1, excess G u ^ 2 := by
    have h1 : Ppart 1 = univ.filter (fun u : CubeVertex 5 => ¬(hammingWeight u % 2 = 0)) := by
      ext u; simp only [Ppart, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [h1]
    exact (Finset.sum_filter_add_sum_filter_not univ
      (fun u : CubeVertex 5 => hammingWeight u % 2 = 0) (fun u => excess G u ^ 2)).symm
  -- Step 15 helper: a part r with {3, 3} leads to contradiction
  have hpart33_contra : ∀ r, r < 2 →
      (∃ a1 a2, a1 ∈ Ppart r ∧ a2 ∈ Ppart r ∧ a1 ≠ a2 ∧ excess G a1 = 3 ∧ excess G a2 = 3 ∧
        ∀ u ∈ Ppart r, u ≠ a1 → u ≠ a2 → excess G u = 0) → False := by
    intro r hr ⟨a1, a2, ha1, ha2, hne12, hxa1, hxa2, hzero⟩
    -- Prove h(a1, a2) = 4, hence d(a1, a2) ≥ 4
    have hha12 : hammingDist a1 a2 = 4 := by
      have hle5 := hammingDist_le_n a1 a2
      have hpos : 0 < hammingDist a1 a2 := by
        by_contra h0; exact hne12 (hammingDist_eq_zero.1 (by omega))
      have hpar := weight_parity_of_dist hG hc (u := a1) (w := a2)
      have hd := (dist_hamming hG hc a1 a2).2
      have hp1 : hammingWeight a1 % 2 = r := (Finset.mem_filter.1 ha1).2
      have hp2 : hammingWeight a2 % 2 = r := (Finset.mem_filter.1 ha2).2
      have hne2 : hammingDist a1 a2 ≠ 2 := by
        intro h2
        have hm := q5_full_degree_hamming_two_extraParents hG hc h2 hxa1 hxa2
        linarith [hM2_zero a1]
      omega
    have hda12 : 4 ≤ G.dist a1 a2 := by linarith [(dist_hamming hG hc a1 a2).1]
    -- Part r contributes 0 to P2
    have hP2_r : ∑ u ∈ Ppart r, excess G u * levelExcess G u 2 = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      by_cases hu1 : u = a1
      · subst hu1
        have hX2 : levelExcess G u 2 = 0 := by
          refine Finset.sum_eq_zero fun w hw => ?_
          rw [mem_levelSet] at hw
          have hwp : w ∈ Ppart r := by
            have hp := weight_parity_of_dist hG hc (u := u) (w := w)
            have hp1 : hammingWeight u % 2 = r := (Finset.mem_filter.1 ha1).2
            exact Finset.mem_filter.2 ⟨Finset.mem_univ w, by omega⟩
          have hw1 : w ≠ u := by rintro rfl; simp at hw
          have hw2 : w ≠ a2 := by rintro rfl; omega
          exact hzero w hwp hw1 hw2
        rw [hX2, mul_zero]
      · by_cases hu2 : u = a2
        · subst hu2
          have hX2 : levelExcess G u 2 = 0 := by
            refine Finset.sum_eq_zero fun w hw => ?_
            rw [mem_levelSet] at hw
            have hwp : w ∈ Ppart r := by
              have hp := weight_parity_of_dist hG hc (u := u) (w := w)
              have hp2 : hammingWeight u % 2 = r := (Finset.mem_filter.1 ha2).2
              exact Finset.mem_filter.2 ⟨Finset.mem_univ w, by omega⟩
            have hw1 : w ≠ a1 := by rintro rfl; rw [SimpleGraph.dist_comm] at hw; omega
            have hw2 : w ≠ u := by rintro rfl; simp at hw
            exact hzero w hwp hw1 hw2
          rw [hX2, mul_zero]
        · rw [hzero u hu hu1 hu2, zero_mul]
    -- Part r has ∑ x^2 = 18
    have hS2_r : ∑ u ∈ Ppart r, excess G u ^ 2 = 18 := by
      have h1 : ∑ u ∈ Ppart r, excess G u ^ 2 = ∑ u ∈ ({a1, a2} : Finset (CubeVertex 5)), excess G u ^ 2 := by
        symm
        refine Finset.sum_subset (fun u hu => ?_) (fun u hu hnot => ?_)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> assumption
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
          rw [hzero u hu hnot.1 hnot.2]; norm_num
      rw [h1, Finset.sum_pair hne12, hxa1, hxa2]; norm_num
    -- P1 ≤ 36 (neighborhoods of a1 and a2 are disjoint subsets of Ppart (1 - r))
    have hP1_le : P1 ≤ 36 := by
      have hP1_split : P1 = ∑ u ∈ Ppart r, excess G u * levelExcess G u 1 +
          ∑ u ∈ Ppart (1 - r), excess G u * levelExcess G u 1 := by
        simp only [P1, Ppart]
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun u : CubeVertex 5 => hammingWeight u % 2 = r)]
        congr 2; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hP1_sym : ∑ u ∈ Ppart (1 - r), excess G u * levelExcess G u 1 =
          ∑ u ∈ Ppart r, excess G u * levelExcess G u 1 := by
        simp only [levelExcess, levelSet, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
        rw [Finset.sum_comm]
        have hzero1 : ∑ w : CubeVertex 5, ∑ u ∈ Ppart (1 - r),
            (if G.dist u w = 1 then excess G u * excess G w else 0) =
            ∑ w ∈ Ppart r, ∑ u ∈ Ppart (1 - r),
              (if G.dist u w = 1 then excess G u * excess G w else 0) := by
          rw [← Finset.sum_subset (Finset.subset_univ (Ppart r))]
          intro w _ hw
          refine Finset.sum_eq_zero fun u hu => ?_
          have hne : G.dist u w ≠ 1 := by
            intro hd
            have hp := weight_parity_of_dist hG hc (u := u) (w := w)
            have hu' : hammingWeight u % 2 = 1 - r := (Finset.mem_filter.1 hu).2
            exact hw (Finset.mem_filter.2 ⟨Finset.mem_univ w, by omega⟩)
          simp [hne]
        rw [hzero1]
        refine Finset.sum_congr rfl fun w hw => ?_
        have hzero2 : ∑ u ∈ Ppart (1 - r), (if G.dist u w = 1 then excess G u * excess G w else 0) =
            ∑ u : CubeVertex 5, (if G.dist w u = 1 then excess G w * excess G u else 0) := by
          symm
          rw [← Finset.sum_subset (Finset.subset_univ (Ppart (1 - r)))]
          · refine Finset.sum_congr rfl fun u _ => by rw [SimpleGraph.dist_comm, mul_comm]
          · intro u _ hu
            have hne : G.dist w u ≠ 1 := by
              intro hd
              have hp := weight_parity_of_dist hG hc (u := w) (w := u)
              have hw' : hammingWeight w % 2 = r := (Finset.mem_filter.1 hw).2
              exact hu (Finset.mem_filter.2 ⟨Finset.mem_univ u, by omega⟩)
            simp [hne]
        exact hzero2
      have hP1_r : ∑ u ∈ Ppart r, excess G u * levelExcess G u 1 =
          3 * (levelExcess G a1 1 + levelExcess G a2 1) := by
        have h1 : ∑ u ∈ Ppart r, excess G u * levelExcess G u 1 =
            ∑ u ∈ ({a1, a2} : Finset (CubeVertex 5)), excess G u * levelExcess G u 1 := by
          symm
          refine Finset.sum_subset (fun u hu => ?_) (fun u hu hnot => ?_)
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl <;> assumption
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
            rw [hzero u hu hnot.1 hnot.2, zero_mul]
        rw [h1, Finset.sum_pair hne12, hxa1, hxa2]; ring
      have hdisj12 : Disjoint (levelSet G a1 1) (levelSet G a2 1) := by
        rw [Finset.disjoint_left]
        intro w h1 h2
        rw [mem_levelSet] at h1 h2
        have ht := hc.dist_triangle (u := a1) (v := w) (w := a2)
        rw [SimpleGraph.dist_comm (u := w) (v := a2)] at ht
        omega
      have hsub12 : levelSet G a1 1 ∪ levelSet G a2 1 ⊆ Ppart (1 - r) := by
        intro w hw
        simp only [Finset.mem_union, mem_levelSet] at hw
        rcases hw with h | h
        · have hp := weight_parity_of_dist hG hc (u := a1) (w := w)
          have hp1 : hammingWeight a1 % 2 = r := (Finset.mem_filter.1 ha1).2
          exact Finset.mem_filter.2 ⟨Finset.mem_univ w, by omega⟩
        · have hp := weight_parity_of_dist hG hc (u := a2) (w := w)
          have hp2 : hammingWeight a2 % 2 = r := (Finset.mem_filter.1 ha2).2
          exact Finset.mem_filter.2 ⟨Finset.mem_univ w, by omega⟩
      have hsum12 : levelExcess G a1 1 + levelExcess G a2 1 ≤ 6 := by
        unfold levelExcess
        rw [← Finset.sum_union hdisj12]
        calc ∑ w ∈ levelSet G a1 1 ∪ levelSet G a2 1, excess G w
            ≤ ∑ w ∈ Ppart (1 - r), excess G w :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub12 fun w _ _ => hnn w
          _ = 6 := hpart_sum (1 - r) (by omega)
      linarith
    -- Split P2 and S2 into part r and part (1 - r)
    let s : ℤ := ∑ u ∈ Ppart (1 - r), excess G u ^ 2
    have hS2_eq : S2 = 18 + s := by
      have hs : S2 = ∑ u ∈ Ppart r, excess G u ^ 2 + ∑ u ∈ Ppart (1 - r), excess G u ^ 2 := by
        simp only [S2, Ppart]
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun u : CubeVertex 5 => hammingWeight u % 2 = r)]
        congr 2; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      linarith
    have hP2_le : P2 ≤ 36 - s := by
      have hP2_split : P2 = ∑ u ∈ Ppart r, excess G u * levelExcess G u 2 +
          ∑ u ∈ Ppart (1 - r), excess G u * levelExcess G u 2 := by
        simp only [P2, Ppart]
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun u : CubeVertex 5 => hammingWeight u % 2 = r)]
        congr 2; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hother : ∑ u ∈ Ppart (1 - r), excess G u * levelExcess G u 2 ≤ 36 - s := by
        have hpt : ∀ u ∈ Ppart (1 - r), levelExcess G u 2 ≤ 6 - excess G u := by
          intro u hu
          have hsub : levelSet G u 2 ⊆ (Ppart (1 - r)).erase u := by
            intro w hw
            rw [mem_levelSet] at hw
            refine Finset.mem_erase.2 ⟨by rintro rfl; simp at hw, Finset.mem_filter.2 ⟨Finset.mem_univ w, ?_⟩⟩
            have hp := weight_parity_of_dist hG hc (u := u) (w := w)
            have hu' : hammingWeight u % 2 = 1 - r := (Finset.mem_filter.1 hu).2
            omega
          have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => hnn w
          have heq := Finset.add_sum_erase (Ppart (1 - r)) (excess G) hu
          have hps := hpart_sum (1 - r) (by omega)
          unfold levelExcess
          linarith
        calc ∑ u ∈ Ppart (1 - r), excess G u * levelExcess G u 2
            ≤ ∑ u ∈ Ppart (1 - r), excess G u * (6 - excess G u) :=
              Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hpt u hu) (hnn u)
          _ = 36 - s := by
              have h1 : ∀ u, excess G u * (6 - excess G u) = 6 * excess G u - excess G u ^ 2 :=
                fun u => by ring
              simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
              rw [hpart_sum (1 - r) (by omega)]
              ring
      linarith
    -- Thus 232 ≤ 4*(18 + s) + 72 + (36 - s) = 180 + 3*s, so 18 ≤ s!
    have hs18 : 18 ≤ s := by linarith
    -- So part (1 - r) is ALSO {3, 3}, giving P2 = 0!
    have hdich := part_sum_sq_dichotomy (Ppart (1 - r)) (excess G)
      (fun u _ => ⟨hnn u, hle3 u⟩) (hpart_sum (1 - r) (by omega))
    obtain ⟨b1, b2, hb1, hb2, hneb12, hxb1, hxb2, hzerob⟩ := hdich.2 (by omega)
    have hhb12 : hammingDist b1 b2 = 4 := by
      have hle5 := hammingDist_le_n b1 b2
      have hpos : 0 < hammingDist b1 b2 := by
        by_contra h0; exact hneb12 (hammingDist_eq_zero.1 (by omega))
      have hpar := weight_parity_of_dist hG hc (u := b1) (w := b2)
      have hd := (dist_hamming hG hc b1 b2).2
      have hp1 : hammingWeight b1 % 2 = 1 - r := (Finset.mem_filter.1 hb1).2
      have hp2 : hammingWeight b2 % 2 = 1 - r := (Finset.mem_filter.1 hb2).2
      have hne2 : hammingDist b1 b2 ≠ 2 := by
        intro h2
        have hm := q5_full_degree_hamming_two_extraParents hG hc h2 hxb1 hxb2
        linarith [hM2_zero b1]
      omega
    have hdb12 : 4 ≤ G.dist b1 b2 := by linarith [(dist_hamming hG hc b1 b2).1]
    have hP2_other : ∑ u ∈ Ppart (1 - r), excess G u * levelExcess G u 2 = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      by_cases hu1 : u = b1
      · subst hu1
        have hX2 : levelExcess G u 2 = 0 := by
          refine Finset.sum_eq_zero fun w hw => ?_
          rw [mem_levelSet] at hw
          have hwp : w ∈ Ppart (1 - r) := by
            have hp := weight_parity_of_dist hG hc (u := u) (w := w)
            have hp1 : hammingWeight u % 2 = 1 - r := (Finset.mem_filter.1 hb1).2
            exact Finset.mem_filter.2 ⟨Finset.mem_univ w, by omega⟩
          have hw1 : w ≠ u := by rintro rfl; simp at hw
          have hw2 : w ≠ b2 := by rintro rfl; omega
          exact hzerob w hwp hw1 hw2
        rw [hX2, mul_zero]
      · by_cases hu2 : u = b2
        · subst hu2
          have hX2 : levelExcess G u 2 = 0 := by
            refine Finset.sum_eq_zero fun w hw => ?_
            rw [mem_levelSet] at hw
            have hwp : w ∈ Ppart (1 - r) := by
              have hp := weight_parity_of_dist hG hc (u := u) (w := w)
              have hp2 : hammingWeight u % 2 = 1 - r := (Finset.mem_filter.1 hb2).2
              exact Finset.mem_filter.2 ⟨Finset.mem_univ w, by omega⟩
            have hw1 : w ≠ b1 := by rintro rfl; rw [SimpleGraph.dist_comm] at hw; omega
            have hw2 : w ≠ u := by rintro rfl; simp at hw
            exact hzerob w hwp hw1 hw2
          rw [hX2, mul_zero]
        · rw [hzerob u hu hu1 hu2, zero_mul]
    have hP2_zero : P2 = 0 := by
      have hP2_split : P2 = ∑ u ∈ Ppart r, excess G u * levelExcess G u 2 +
          ∑ u ∈ Ppart (1 - r), excess G u * levelExcess G u 2 := by
        simp only [P2, Ppart]
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun u : CubeVertex 5 => hammingWeight u % 2 = r)]
        congr 2; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      linarith
    have hs_eq : s = 18 := le_antisymm hdich.1 hs18
    -- Final contradiction: 232 ≤ 4 * 36 + 2 * 36 + 0 = 216
    linarith
  -- Apply dichotomy to part 0 or part 1 (whichever has ∑ x^2 ≥ 16)
  by_cases h0 : 15 ≤ ∑ u ∈ Ppart 0, excess G u ^ 2
  · have hd0 := part_sum_sq_dichotomy (Ppart 0) (excess G)
      (fun u _ => ⟨hnn u, hle3 u⟩) (hpart_sum 0 (by norm_num))
    exact hpart33_contra 0 (by norm_num) (hd0.2 h0)
  · have h1 : 15 ≤ ∑ u ∈ Ppart 1, excess G u ^ 2 := by omega
    have hd1 := part_sum_sq_dichotomy (Ppart 1) (excess G)
      (fun u _ => ⟨hnn u, hle3 u⟩) (hpart_sum 1 (by norm_num))
    exact hpart33_contra 1 (by norm_num) (hd1.2 h1)

/-- Theorem 2: `f(5) ≥ 39`. -/
theorem f_five_ge_thirtynine : 39 ≤ f 5 := by
  apply le_f_of_forall_valid
  intro G hV
  have h38 := theorem1_lower_bound_nat_ceil (n := 5) (by norm_num) hV
  norm_num at h38
  by_contra hlt
  have h38eq : G.edgeSet.ncard = 38 := by omega
  exact no_valid_q5_thirtyeight_edges hV h38eq

/-- Combined bounds for `Q_5`: `39 ≤ f(5) ≤ 40`. -/
theorem f_five_bounds : 39 ≤ f 5 ∧ f 5 ≤ 40 :=
  ⟨f_five_ge_thirtynine, f_five_le_forty⟩

end Hypercube
