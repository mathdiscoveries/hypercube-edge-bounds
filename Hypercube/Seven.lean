/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Hypercube.StrongerBounds
import Mathlib.Tactic

@[expose] public section

/-! The radii 1, 3, 5 are assigned to sphere levels 2, 3, 4 in dimension seven. -/
namespace Hypercube.DraftThree

open Finset

private def sevenLevel (m : ℕ) : ℕ := (m + 3) / 2

private theorem sevenLevel_valid : IsValidRecipe 7 sevenLevel := by
  intro m hm
  simp only [rSetPos, Finset.mem_filter, rSet, Finset.mem_range] at hm
  unfold sevenLevel
  omega

private theorem seven_weights (x : ℤ) (hx : 0 ≤ x) (k : ℕ)
    (hk : k ∈ Ico 2 (7 - 1)) :
    0 ≤ 2 * x + (2 * x) * (recipeCount 7 sevenLevel (k + 2) - recipeCount 7 sevenLevel k) := by
  have hk' : 2 ≤ k ∧ k < 6 := Finset.mem_Ico.mp hk
  have hd : -1 ≤ recipeCount 7 sevenLevel (k + 2) - recipeCount 7 sevenLevel k := by
    obtain ⟨hk1,hk2⟩ := hk'
    interval_cases k <;> decide
  nlinarith [mul_nonneg hx (show 0 ≤ 1 + recipeCount 7 sevenLevel (k + 2) -
      recipeCount 7 sevenLevel k by omega)]

private theorem seven_floor (x : ℤ) (hx : 0 ≤ x) (hx' : x ≤ 5) :
    x * 184 ≤ 5 * cappedFloor 7 sevenLevel (2 * x) x 21 := by
  interval_cases x <;> decide

/-- The sum of the local antipodal floors excludes every graph with at most 149 edges. -/
theorem seven_ge_150 : 150 ≤ f 7 := by
  apply le_f_of_forall_valid
  intro G hV
  obtain ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  by_contra he
  have ht : edgeExcess G ≤ 21 := by
    unfold edgeExcess
    norm_num
    omega
  have hpt (w : CubeVertex 7) : excess G w * 184 ≤ 5 * psi G w := by
    have hx := excess_nonneg (by decide) hG hD w
    have htop := excess_le hG w
    have h0 := seven_floor (excess G w) hx (by omega)
    have h1 := cappedFloor_antitone_t 7 sevenLevel (2 * excess G w) (excess G w)
      (by decide) ht (seven_weights _ hx)
    have h2 := theorem13_capped_floor (by decide) hV w sevenLevel sevenLevel_valid
      (show 0 ≤ 2 * excess G w by omega) (seven_weights _ hx)
    omega
  have hall : (∑ w : CubeVertex 7, excess G w) * 184 ≤ 5 * ∑ w : CubeVertex 7, psi G w := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hpt w
  rw [sum_excess, sum_psi (by decide) hV] at hall
  norm_num at hall
  omega


end Hypercube.DraftThree
