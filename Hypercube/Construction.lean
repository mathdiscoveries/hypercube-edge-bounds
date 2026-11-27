/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Hypercube.Defs
import Mathlib.Tactic

/-!
# General Hypercube Upper-Bound Construction (`f n ≤ 2^n + C(n, ⌊n/2⌋) - 2`)

Constructs the canonical diameter-preserving spanning subgraph `grahamConstruction n` of `Q n`
for every `n ≥ 1` using the prefix-sum (Greene–Kleitman symmetric chain) matching between
consecutive Hamming layers:
- Every vertex `u` with `0 < |u|` has a downward edge to weight `|u| - 1`, giving `dist(u, 0) ≤ |u|`.
- Every vertex `u` with `|u| < n` has an upward edge to weight `|u| + 1`, giving `dist(u, 1) ≤ n - |u|`.
- Therefore every pair `u, w` satisfies `dist(u, w) ≤ min(|u| + |w|, 2n - |u| - |w|) ≤ n`.
- Exact edge count (`grahamConstruction_edgeCount`): `2^n + n.choose (n / 2) - 2` for all `n ≥ 1`.
- Corollaries: `f 2 ≤ 4`, `f 3 ≤ 9`, `f 4 ≤ 20`, `f 5 ≤ 40`.
-/

@[expose] public section

namespace Hypercube

open Finset

/-- Prefix balance `P(x, j) = #{i < j | x i = false} - #{i < j | x i = true}`. -/
def prefixSum {n : ℕ} (x : CubeVertex n) (j : ℕ) : ℤ :=
  ∑ i ∈ univ.filter (fun i : Fin n => i.1 < j), (if x i then (-1 : ℤ) else 1)

theorem prefixSum_zero {n : ℕ} (x : CubeVertex n) : prefixSum x 0 = 0 := by
  unfold prefixSum
  have h : (univ.filter fun i : Fin n => i.1 < 0) = ∅ := by
    ext i; simp
  rw [h, Finset.sum_empty]

theorem prefixSum_succ {n : ℕ} (x : CubeVertex n) {j : ℕ} (hj : j < n) :
    prefixSum x (j + 1) = prefixSum x j + (if x ⟨j, hj⟩ then (-1 : ℤ) else 1) := by
  unfold prefixSum
  have h : (univ.filter fun i : Fin n => i.1 < j + 1) =
      insert ⟨j, hj⟩ (univ.filter fun i : Fin n => i.1 < j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨j, hj⟩ : Fin n) ∉ univ.filter (fun i : Fin n => i.1 < j) := by
    simp
  rw [h, Finset.sum_insert hnot, add_comm]

theorem prefixSum_n {n : ℕ} (x : CubeVertex n) :
    prefixSum x n = (n : ℤ) - 2 * (hammingWeight x : ℤ) := by
  unfold prefixSum hammingWeight
  have hfilt : (univ.filter fun i : Fin n => i.1 < n) = univ := by
    ext i; simp
  rw [hfilt]
  have hpt : ∀ i : Fin n, (if x i then (-1 : ℤ) else 1) =
      1 - 2 * (if x i = true then (1 : ℤ) else 0) := by
    intro i; cases x i <;> decide
  rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← Finset.natCast_card_filter]

theorem prefixSum_flipAt_le {n : ℕ} (x : CubeVertex n) (k : Fin n) {j : ℕ} (hj : j ≤ k.1) :
    prefixSum (flipAt k x) j = prefixSum x j := by
  unfold prefixSum
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hne : i ≠ k := fun h => by subst h; omega
  rw [flipAt_apply_of_ne x hne]

theorem prefixSum_flipAt_gt_of_false {n : ℕ} (x : CubeVertex n) (k : Fin n)
    (hk : x k = false) {j : ℕ} (hj : k.1 < j) :
    prefixSum (flipAt k x) j = prefixSum x j - 2 := by
  unfold prefixSum
  have hmem : k ∈ univ.filter (fun i : Fin n => i.1 < j) := by
    simp [hj]
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have hrest :
      ∑ i ∈ (univ.filter fun i : Fin n => i.1 < j).erase k,
        (if flipAt k x i then (-1 : ℤ) else 1) =
      ∑ i ∈ (univ.filter fun i : Fin n => i.1 < j).erase k,
        (if x i then (-1 : ℤ) else 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [flipAt_apply_of_ne x (Finset.ne_of_mem_erase hi)]
  rw [hrest, flipAt_apply_self, hk]
  norm_num
  ring

theorem hammingWeight_flipAt_of_false {n : ℕ} (x : CubeVertex n) (k : Fin n)
    (hk : x k = false) : hammingWeight (flipAt k x) = hammingWeight x + 1 := by
  unfold hammingWeight
  have h : (univ.filter fun i : Fin n => flipAt k x i = true) =
      insert k (univ.filter fun i : Fin n => x i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hik : i = k
    · subst hik; simp [flipAt_apply_self, hk]
    · simp [flipAt_apply_of_ne x hik, hik]
  have hnot : k ∉ univ.filter (fun i : Fin n => x i = true) := by simp [hk]
  rw [h, Finset.card_insert_of_notMem hnot]

theorem hammingWeight_flipAt_of_true {n : ℕ} (x : CubeVertex n) (k : Fin n)
    (hk : x k = true) : hammingWeight (flipAt k x) + 1 = hammingWeight x := by
  have h := hammingWeight_flipAt_of_false (flipAt k x) k (by rw [flipAt_apply_self, hk]; rfl)
  rw [flipAt_flipAt] at h
  exact h.symm

/-- Minimum prefix balance `min_{0 ≤ j ≤ n} P(x, j)`. -/
def minPrefix {n : ℕ} (x : CubeVertex n) : ℤ :=
  ((range (n + 1)).image (prefixSum x)).min' (by simp)

theorem minPrefix_le {n : ℕ} (x : CubeVertex n) {j : ℕ} (hj : j ≤ n) :
    minPrefix x ≤ prefixSum x j := by
  unfold minPrefix
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))

theorem minPrefix_nonpos {n : ℕ} (x : CubeVertex n) : minPrefix x ≤ 0 := by
  have h := minPrefix_le x (Nat.zero_le n)
  rwa [prefixSum_zero] at h

/-- Positions `j ∈ {0, ..., n}` achieving `prefixSum x j = minPrefix x`. -/
def minPositions {n : ℕ} (x : CubeVertex n) : Finset ℕ :=
  (range (n + 1)).filter fun j => prefixSum x j = minPrefix x

theorem minPositions_nonempty {n : ℕ} (x : CubeVertex n) : (minPositions x).Nonempty := by
  have hmem : minPrefix x ∈ (range (n + 1)).image (prefixSum x) := Finset.min'_mem _ _
  rcases Finset.mem_image.1 hmem with ⟨j, hj, hjeq⟩
  exact ⟨j, Finset.mem_filter.2 ⟨hj, hjeq⟩⟩

/-- Smallest position achieving `minPrefix x`. -/
def firstMin {n : ℕ} (x : CubeVertex n) : ℕ :=
  (minPositions x).min' (minPositions_nonempty x)

/-- Largest position achieving `minPrefix x`. -/
def lastMin {n : ℕ} (x : CubeVertex n) : ℕ :=
  (minPositions x).max' (minPositions_nonempty x)

theorem firstMin_le_n {n : ℕ} (x : CubeVertex n) : firstMin x ≤ n := by
  have h : firstMin x ∈ minPositions x := Finset.min'_mem (minPositions x) (minPositions_nonempty x)
  simp only [minPositions, Finset.mem_filter, Finset.mem_range] at h
  omega

theorem prefixSum_firstMin {n : ℕ} (x : CubeVertex n) : prefixSum x (firstMin x) = minPrefix x := by
  have h := Finset.min'_mem (minPositions x) (minPositions_nonempty x)
  exact (Finset.mem_filter.1 h).2

theorem lastMin_le_n {n : ℕ} (x : CubeVertex n) : lastMin x ≤ n := by
  have h : lastMin x ∈ minPositions x := Finset.max'_mem (minPositions x) (minPositions_nonempty x)
  simp only [minPositions, Finset.mem_filter, Finset.mem_range] at h
  omega

theorem prefixSum_lastMin {n : ℕ} (x : CubeVertex n) : prefixSum x (lastMin x) = minPrefix x := by
  have h := Finset.max'_mem (minPositions x) (minPositions_nonempty x)
  exact (Finset.mem_filter.1 h).2

theorem lastMin_lt_n_of_two_mul_weight_lt {n : ℕ} (x : CubeVertex n)
    (hx : 2 * hammingWeight x < n) : lastMin x < n := by
  have hle := lastMin_le_n x
  have hne : lastMin x ≠ n := by
    intro heq
    have h1 := prefixSum_lastMin x
    rw [heq, prefixSum_n] at h1
    have h2 := minPrefix_nonpos x
    omega
  omega

theorem x_at_lastMin_eq_false {n : ℕ} (x : CubeVertex n) (hx : 2 * hammingWeight x < n) :
    x ⟨lastMin x, lastMin_lt_n_of_two_mul_weight_lt x hx⟩ = false := by
  have hlt := lastMin_lt_n_of_two_mul_weight_lt x hx
  have hstep := prefixSum_succ x hlt
  have hgt : minPrefix x < prefixSum x (lastMin x + 1) := by
    have hle := minPrefix_le x (show lastMin x + 1 ≤ n by omega)
    have hne : prefixSum x (lastMin x + 1) ≠ minPrefix x := by
      intro heq
      have hmem : lastMin x + 1 ∈ minPositions x :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), heq⟩
      have hmax := Finset.le_max' (minPositions x) (lastMin x + 1) hmem
      unfold lastMin at hmax
      omega
    omega
  rw [prefixSum_lastMin] at hstep
  cases hval : x ⟨lastMin x, hlt⟩
  · rfl
  · rw [hval] at hstep; simp at hstep; omega

/-- Symmetric-chain upward step for `2 * hammingWeight x < n`: flips coordinate `lastMin x`. -/
def upVertex {n : ℕ} (x : CubeVertex n) (hx : 2 * hammingWeight x < n) : CubeVertex n :=
  flipAt ⟨lastMin x, lastMin_lt_n_of_two_mul_weight_lt x hx⟩ x

theorem minPrefix_upVertex {n : ℕ} (x : CubeVertex n) (hx : 2 * hammingWeight x < n) :
    minPrefix (upVertex x hx) = minPrefix x - 1 := by
  have hlt := lastMin_lt_n_of_two_mul_weight_lt x hx
  have hfalse := x_at_lastMin_eq_false x hx
  set k : Fin n := ⟨lastMin x, hlt⟩
  have hge : ∀ j ≤ n, minPrefix x - 1 ≤ prefixSum (upVertex x hx) j := by
    intro j hj
    by_cases hjk : j ≤ k.1
    · rw [upVertex, prefixSum_flipAt_le x k hjk]
      have := minPrefix_le x hj
      omega
    · have hgt : k.1 < j := by omega
      rw [upVertex, prefixSum_flipAt_gt_of_false x k hfalse hgt]
      have hmin := minPrefix_le x hj
      have hne : prefixSum x j ≠ minPrefix x := by
        intro heq
        have hmem : j ∈ minPositions x := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), heq⟩
        have hmax := Finset.le_max' (minPositions x) j hmem
        change j ≤ k.1 at hmax
        omega
      omega
  have heq : prefixSum (upVertex x hx) (k.1 + 1) = minPrefix x - 1 := by
    rw [upVertex, prefixSum_flipAt_gt_of_false x k hfalse (Nat.lt_succ_self k.1),
      prefixSum_succ x hlt, hfalse, prefixSum_lastMin]
    simp
    ring
  apply le_antisymm
  · rw [← heq]
    exact minPrefix_le (upVertex x hx) (by omega)
  · unfold minPrefix
    apply Finset.le_min'
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨j, hj, rfl⟩
    exact hge j (by simp only [Finset.mem_range] at hj; omega)

theorem firstMin_upVertex {n : ℕ} (x : CubeVertex n) (hx : 2 * hammingWeight x < n) :
    firstMin (upVertex x hx) = lastMin x + 1 := by
  have hlt := lastMin_lt_n_of_two_mul_weight_lt x hx
  have hfalse := x_at_lastMin_eq_false x hx
  have hmin := minPrefix_upVertex x hx
  set k : Fin n := ⟨lastMin x, hlt⟩
  have hmem : k.1 + 1 ∈ minPositions (upVertex x hx) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    rw [hmin, upVertex, prefixSum_flipAt_gt_of_false x k hfalse (Nat.lt_succ_self k.1),
      prefixSum_succ x hlt, hfalse, prefixSum_lastMin]
    simp
    ring
  apply le_antisymm
  · exact Finset.min'_le _ _ hmem
  · unfold firstMin
    apply Finset.le_min'
    intro j hj
    simp only [minPositions, Finset.mem_filter, Finset.mem_range] at hj
    by_contra hle
    have hjk : j ≤ k.1 := by dsimp only [k]; omega
    have hpref : prefixSum (upVertex x hx) j = prefixSum x j :=
      prefixSum_flipAt_le x k hjk
    rw [hpref, hmin] at hj
    have := minPrefix_le x (show j ≤ n by omega)
    omega

theorem firstMin_pos_of_minPrefix_neg {n : ℕ} (y : CubeVertex n) (hy : minPrefix y < 0) :
    1 ≤ firstMin y := by
  by_contra h
  have h0 : firstMin y = 0 := by omega
  have h1 := prefixSum_firstMin y
  rw [h0, prefixSum_zero] at h1
  omega

theorem y_at_firstMin_sub_one_eq_true {n : ℕ} (y : CubeVertex n) (hy : minPrefix y < 0) :
    y ⟨firstMin y - 1, by have := firstMin_le_n y; have := firstMin_pos_of_minPrefix_neg y hy; omega⟩ =
      true := by
  have hpos := firstMin_pos_of_minPrefix_neg y hy
  have hle := firstMin_le_n y
  have hlt : firstMin y - 1 < n := by omega
  have hstep := prefixSum_succ y hlt
  have heq : firstMin y - 1 + 1 = firstMin y := by omega
  rw [heq, prefixSum_firstMin] at hstep
  have hgt : minPrefix y < prefixSum y (firstMin y - 1) := by
    have h1 := minPrefix_le y (show firstMin y - 1 ≤ n by omega)
    have hne : prefixSum y (firstMin y - 1) ≠ minPrefix y := by
      intro heq'
      have hmem : firstMin y - 1 ∈ minPositions y :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), heq'⟩
      have hmin := Finset.min'_le (minPositions y) (firstMin y - 1) hmem
      unfold firstMin at hmin
      omega
    omega
  cases hval : y ⟨firstMin y - 1, hlt⟩
  · rw [hval] at hstep; simp at hstep; omega
  · rfl

/-- Canonical downward parent of `y` in the symmetric-chain construction:
uses `firstMin y - 1` when `minPrefix y < 0`, else flips the first `true` coordinate. -/
def parentVertex {n : ℕ} (y : CubeVertex n) : CubeVertex n :=
  if hy : minPrefix y < 0 then
    flipAt ⟨firstMin y - 1, by
      have := firstMin_le_n y; have := firstMin_pos_of_minPrefix_neg y hy; omega⟩ y
  else if hw : (univ.filter fun i : Fin n => y i = true).Nonempty then
    flipAt ((univ.filter fun i : Fin n => y i = true).min' hw) y
  else
    y

theorem hammingDist_parentVertex {n : ℕ} {y : CubeVertex n} (hy : 0 < hammingWeight y) :
    hammingDist (parentVertex y) y = 1 := by
  unfold parentVertex
  split_ifs with h1 h2
  · rw [hammingDist_comm]; exact hammingDist_flipAt _ y
  · rw [hammingDist_comm]; exact hammingDist_flipAt _ y
  · exfalso
    unfold hammingWeight at hy
    exact h2 (Finset.card_pos.1 hy)

theorem hammingWeight_parentVertex {n : ℕ} {y : CubeVertex n} (hy : 0 < hammingWeight y) :
    hammingWeight (parentVertex y) + 1 = hammingWeight y := by
  unfold parentVertex
  split_ifs with h1 h2
  · exact hammingWeight_flipAt_of_true y _ (y_at_firstMin_sub_one_eq_true y h1)
  · have hmem := Finset.min'_mem (univ.filter fun i : Fin n => y i = true) h2
    exact hammingWeight_flipAt_of_true y _ (Finset.mem_filter.1 hmem).2
  · exfalso
    unfold hammingWeight at hy
    exact h2 (Finset.card_pos.1 hy)

theorem parentVertex_upVertex {n : ℕ} (x : CubeVertex n) (hx : 2 * hammingWeight x < n) :
    parentVertex (upVertex x hx) = x := by
  have hmin : minPrefix (upVertex x hx) < 0 := by
    rw [minPrefix_upVertex x hx]
    have := minPrefix_nonpos x
    omega
  unfold parentVertex
  simp only [hmin, ↓reduceDIte]
  have hf := firstMin_upVertex x hx
  have hfin : (⟨firstMin (upVertex x hx) - 1, by
      have := firstMin_le_n (upVertex x hx)
      have := firstMin_pos_of_minPrefix_neg (upVertex x hx) hmin
      omega⟩ : Fin n) = ⟨lastMin x, lastMin_lt_n_of_two_mul_weight_lt x hx⟩ := by
    ext
    simp [hf]
  rw [hfin]
  exact flipAt_flipAt _ x

/-- Directed upward edge in Graham's construction between layer `|u|` and layer `|u| + 1`. -/
def grahamDirEdge (n : ℕ) (u v : CubeVertex n) : Prop :=
  hammingWeight u + 1 = hammingWeight v ∧
    ((2 * hammingWeight u < n ∧ parentVertex v = u) ∨
     (n ≤ 2 * hammingWeight u ∧ parentVertex (antipode u) = antipode v))

instance instDecidableGrahamDirEdge (n : ℕ) (u v : CubeVertex n) :
    Decidable (grahamDirEdge n u v) := by
  unfold grahamDirEdge
  infer_instance

/-- Graham's diameter-preserving spanning subgraph of `Q n` (`2^n + C(n, ⌊n/2⌋) - 2` edges). -/
def grahamConstruction (n : ℕ) : SimpleGraph (CubeVertex n) where
  Adj u v := grahamDirEdge n u v ∨ grahamDirEdge n v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega⟩

instance instDecidableRelGrahamAdj (n : ℕ) : DecidableRel (grahamConstruction n).Adj :=
  fun u v => inferInstanceAs (Decidable (grahamDirEdge n u v ∨ grahamDirEdge n v u))

theorem grahamConstruction_le_Q (n : ℕ) : grahamConstruction n ≤ Q n := by
  intro u v h
  have hdir : ∀ a b, grahamDirEdge n a b → hammingDist a b = 1 := by
    rintro a b ⟨hw, ⟨_, hpar⟩ | ⟨_, hpar⟩⟩
    · rw [← hpar]
      exact hammingDist_parentVertex (by omega)
    · have hwa : 0 < hammingWeight (antipode a) := by
        have h1 := hammingWeight_antipode a
        have h2 := hammingDist_le_n (fun _ => false) b
        rw [← hammingWeight_eq_hammingDist] at h2
        omega
      have h1 := hammingDist_parentVertex hwa
      rw [hpar, hammingDist_antipode_antipode, hammingDist_comm] at h1
      exact h1
  rcases h with h | h
  · exact hdir u v h
  · change hammingDist u v = 1
    rw [hammingDist_comm]; exact hdir v u h

theorem exists_down_neighbor {n : ℕ} {u : CubeVertex n} (hu : 0 < hammingWeight u) :
    ∃ v : CubeVertex n, (grahamConstruction n).Adj u v ∧ hammingWeight v + 1 = hammingWeight u := by
  by_cases hlow : 2 * (hammingWeight u - 1) < n
  · refine ⟨parentVertex u, Or.inr ⟨hammingWeight_parentVertex hu, Or.inl ⟨?_, rfl⟩⟩,
      hammingWeight_parentVertex hu⟩
    have := hammingWeight_parentVertex hu
    omega
  · have ha : 2 * hammingWeight (antipode u) < n := by
      have h1 := hammingWeight_antipode u
      omega
    let v : CubeVertex n := antipode (upVertex (antipode u) ha)
    have hwu : hammingWeight (upVertex (antipode u) ha) = hammingWeight (antipode u) + 1 :=
      hammingWeight_flipAt_of_false _ _ (x_at_lastMin_eq_false _ ha)
    have hwv : hammingWeight v + 1 = hammingWeight u := by
      have h1 := hammingWeight_antipode (upVertex (antipode u) ha)
      have h2 := hammingWeight_antipode u
      change hammingWeight (antipode (upVertex (antipode u) ha)) + 1 = hammingWeight u
      omega
    refine ⟨v, Or.inr ⟨hwv, Or.inr ⟨by omega, ?_⟩⟩, hwv⟩
    simp only [v, antipode_antipode]
    exact parentVertex_upVertex (antipode u) ha

theorem exists_up_neighbor {n : ℕ} {u : CubeVertex n} (hu : hammingWeight u < n) :
    ∃ v : CubeVertex n, (grahamConstruction n).Adj u v ∧ hammingWeight u + 1 = hammingWeight v := by
  by_cases hlow : 2 * hammingWeight u < n
  · let v : CubeVertex n := upVertex u hlow
    have hwv : hammingWeight u + 1 = hammingWeight v :=
      (hammingWeight_flipAt_of_false u _ (x_at_lastMin_eq_false u hlow)).symm
    refine ⟨v, Or.inl ⟨hwv, Or.inl ⟨hlow, parentVertex_upVertex u hlow⟩⟩, hwv⟩
  · have hwa : 0 < hammingWeight (antipode u) := by
      have h1 := hammingWeight_antipode u
      omega
    let v : CubeVertex n := antipode (parentVertex (antipode u))
    have hwp := hammingWeight_parentVertex hwa
    have hwv : hammingWeight u + 1 = hammingWeight v := by
      have h1 := hammingWeight_antipode (parentVertex (antipode u))
      have h2 := hammingWeight_antipode u
      change hammingWeight u + 1 = hammingWeight (antipode (parentVertex (antipode u)))
      omega
    refine ⟨v, Or.inl ⟨hwv, Or.inr ⟨by omega, ?_⟩⟩, hwv⟩
    simp only [v, antipode_antipode]

theorem exists_walk_to_zero {n : ℕ} :
    ∀ (k : ℕ) (u : CubeVertex n), hammingWeight u = k →
      ∃ p : (grahamConstruction n).Walk u (fun _ => false), p.length = k := by
  intro k
  induction k with
  | zero =>
    intro u hu
    rw [hammingWeight_eq_hammingDist, hammingDist_eq_zero] at hu
    subst hu
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ k ih =>
    intro u hu
    obtain ⟨v, hadj, hwv⟩ := exists_down_neighbor (show 0 < hammingWeight u by omega)
    obtain ⟨p, hp⟩ := ih v (by omega)
    exact ⟨SimpleGraph.Walk.cons hadj p, by rw [SimpleGraph.Walk.length_cons, hp]⟩

theorem exists_walk_to_ones {n : ℕ} :
    ∀ (k : ℕ) (u : CubeVertex n), n - hammingWeight u = k →
      ∃ p : (grahamConstruction n).Walk u (fun _ => true), p.length = k := by
  intro k
  induction k with
  | zero =>
    intro u hu
    have hle : hammingWeight u ≤ n := by
      rw [hammingWeight_eq_hammingDist]; exact hammingDist_le_n _ _
    have hwa : hammingWeight (antipode u) = 0 := by
      have := hammingWeight_antipode u; omega
    rw [hammingWeight_eq_hammingDist, hammingDist_eq_zero] at hwa
    have hueq : u = fun _ => true := by
      funext i
      have hi := congr_fun hwa i
      simp only [antipode] at hi
      cases h : u i
      · rw [h] at hi; simp at hi
      · rfl
    subst hueq
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ k ih =>
    intro u hu
    have hlt : hammingWeight u < n := by omega
    obtain ⟨v, hadj, hwv⟩ := exists_up_neighbor hlt
    obtain ⟨p, hp⟩ := ih v (by omega)
    exact ⟨SimpleGraph.Walk.cons hadj p, by rw [SimpleGraph.Walk.length_cons, hp]⟩

/-- Graham's construction is a valid diameter-preserving spanning subgraph of `Q n`. -/
theorem grahamConstruction_valid (n : ℕ) : IsValidSpanningSubgraph n (grahamConstruction n) := by
  refine ⟨grahamConstruction_le_Q n, fun u w => ?_⟩
  obtain ⟨pu0, hpu0⟩ := exists_walk_to_zero (hammingWeight u) u rfl
  obtain ⟨pw0, hpw0⟩ := exists_walk_to_zero (hammingWeight w) w rfl
  obtain ⟨pu1, hpu1⟩ := exists_walk_to_ones (n - hammingWeight u) u rfl
  obtain ⟨pw1, hpw1⟩ := exists_walk_to_ones (n - hammingWeight w) w rfl
  let p0 : (grahamConstruction n).Walk u w := pu0.append pw0.reverse
  let p1 : (grahamConstruction n).Walk u w := pu1.append pw1.reverse
  have hlen0 : p0.length = hammingWeight u + hammingWeight w := by
    simp [p0, hpu0, hpw0]
  have hlen1 : p1.length = (n - hammingWeight u) + (n - hammingWeight w) := by
    simp [p1, hpu1, hpw1]
  have hwu : hammingWeight u ≤ n := by rw [hammingWeight_eq_hammingDist]; exact hammingDist_le_n _ _
  have hww : hammingWeight w ≤ n := by rw [hammingWeight_eq_hammingDist]; exact hammingDist_le_n _ _
  refine ⟨⟨p0⟩, ?_⟩
  by_cases h : hammingWeight u + hammingWeight w ≤ n
  · calc (grahamConstruction n).edist u w ≤ p0.length := SimpleGraph.edist_le p0
      _ = ((hammingWeight u + hammingWeight w : ℕ) : ℕ∞) := by rw [hlen0]
      _ ≤ (n : ℕ∞) := by exact_mod_cast h
  · calc (grahamConstruction n).edist u w ≤ p1.length := SimpleGraph.edist_le p1
      _ = (((n - hammingWeight u) + (n - hammingWeight w) : ℕ) : ℕ∞) := by rw [hlen1]
      _ ≤ (n : ℕ∞) := by exact_mod_cast (show (n - hammingWeight u) + (n - hammingWeight w) ≤ n by omega)

/-- Exact edge count of Graham's construction: `2^n + C(n, ⌊n/2⌋) - 2` for every `n ≥ 1`. -/
theorem grahamConstruction_edgeCount {n : ℕ} (hn : 1 ≤ n) :
    edgeCount (grahamConstruction n) = 2 ^ n + n.choose (n / 2) - 2 := by
  unfold edgeCount
  let Sdown : Finset (CubeVertex n) :=
    univ.filter fun v => 1 ≤ hammingWeight v ∧ 2 * (hammingWeight v - 1) < n
  let Sup : Finset (CubeVertex n) :=
    univ.filter fun u => hammingWeight u < n ∧ n ≤ 2 * hammingWeight u
  -- Bijection between `Sdown ⊕ Sup` (represented via `disjSum`) and `edgeFinset`.
  let φ : CubeVertex n ⊕ CubeVertex n → Sym2 (CubeVertex n) := fun x =>
    match x with
    | Sum.inl v => s(parentVertex v, v)
    | Sum.inr u => s(u, antipode (parentVertex (antipode u)))
  have hbij : (grahamConstruction n).edgeFinset.card = Sdown.card + Sup.card := by
    rw [← Finset.card_disjSum]
    symm
    refine Finset.card_bij (fun x _ => φ x) ?_ ?_ ?_
    · intro x hx
      rw [SimpleGraph.mem_edgeFinset]
      cases x with
      | inl v =>
        rw [Finset.inl_mem_disjSum] at hx
        simp only [Sdown, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hw := hammingWeight_parentVertex (y := v) (by omega)
        exact Or.inl ⟨hw, Or.inl ⟨by dsimp only; omega, rfl⟩⟩
      | inr u =>
        rw [Finset.inr_mem_disjSum] at hx
        simp only [Sup, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hwa : 0 < hammingWeight (antipode u) := by
          have := hammingWeight_antipode u; omega
        have hwp := hammingWeight_parentVertex hwa
        have hwv : hammingWeight u + 1 = hammingWeight (antipode (parentVertex (antipode u))) := by
          have h1 := hammingWeight_antipode (parentVertex (antipode u))
          have h2 := hammingWeight_antipode u
          omega
        exact Or.inl ⟨hwv, Or.inr ⟨hx.2, by rw [antipode_antipode]⟩⟩
    · intro x hx y hy hxy
      cases x with
      | inl v1 =>
        rw [Finset.inl_mem_disjSum] at hx
        simp only [Sdown, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hw1 := hammingWeight_parentVertex (y := v1) (by omega)
        cases y with
        | inl v2 =>
          rw [Finset.inl_mem_disjSum] at hy
          simp only [Sdown, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have hw2 := hammingWeight_parentVertex (y := v2) (by omega)
          rcases Sym2.eq_iff.1 hxy with ⟨_, rfl⟩ | ⟨h1, h2⟩
          · rfl
          · exfalso
            have hw1' : hammingWeight v2 + 1 = hammingWeight v1 := by rw [← h1]; exact hw1
            have hw2' : hammingWeight v1 + 1 = hammingWeight v2 := by rw [h2]; exact hw2
            omega
        | inr u2 =>
          rw [Finset.inr_mem_disjSum] at hy
          simp only [Sup, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have hwa2 : 0 < hammingWeight (antipode u2) := by
            have := hammingWeight_antipode u2; omega
          have hwp2 := hammingWeight_parentVertex (y := antipode u2) hwa2
          have hw2 : hammingWeight u2 + 1 = hammingWeight (antipode (parentVertex (antipode u2))) := by
            have h1 := hammingWeight_antipode (parentVertex (antipode u2))
            have h2 := hammingWeight_antipode u2; omega
          rcases Sym2.eq_iff.1 hxy with ⟨h1, _⟩ | ⟨h1, h2⟩
          · exfalso; rw [h1] at hw1; omega
          · exfalso
            have h1' : hammingWeight (antipode (parentVertex (antipode u2))) + 1 = hammingWeight v1 := by
              rw [← h1]; exact hw1
            rw [h2] at h1'; omega
      | inr u1 =>
        rw [Finset.inr_mem_disjSum] at hx
        simp only [Sup, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hwa1 : 0 < hammingWeight (antipode u1) := by
          have := hammingWeight_antipode u1; omega
        have hwp1 := hammingWeight_parentVertex (y := antipode u1) hwa1
        have hw1 : hammingWeight u1 + 1 = hammingWeight (antipode (parentVertex (antipode u1))) := by
          have h1 := hammingWeight_antipode (parentVertex (antipode u1))
          have h2 := hammingWeight_antipode u1; omega
        cases y with
        | inl v2 =>
          rw [Finset.inl_mem_disjSum] at hy
          simp only [Sdown, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have hw2 := hammingWeight_parentVertex (y := v2) (by omega)
          rcases Sym2.eq_iff.1 hxy with ⟨h1, _⟩ | ⟨h1, h2⟩
          · exfalso; rw [← h1] at hw2; omega
          · exfalso
            have hw1' : hammingWeight u1 + 1 = hammingWeight (parentVertex v2) := by rw [← h2]; exact hw1
            rw [h1] at hw1'; omega
        | inr u2 =>
          rw [Finset.inr_mem_disjSum] at hy
          simp only [Sup, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have hwa2 : 0 < hammingWeight (antipode u2) := by
            have := hammingWeight_antipode u2; omega
          have hwp2 := hammingWeight_parentVertex (y := antipode u2) hwa2
          have hw2 : hammingWeight u2 + 1 = hammingWeight (antipode (parentVertex (antipode u2))) := by
            have h1 := hammingWeight_antipode (parentVertex (antipode u2))
            have h2 := hammingWeight_antipode u2; omega
          rcases Sym2.eq_iff.1 hxy with ⟨rfl, _⟩ | ⟨h1, h2⟩
          · rfl
          · exfalso
            have hw1' : hammingWeight u1 + 1 = hammingWeight u2 := by rw [← h2]; exact hw1
            have hw2' : hammingWeight u2 + 1 = hammingWeight u1 := by rw [h1]; exact hw2
            omega
    · intro e he
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e using Sym2.ind with
      | _ a b =>
        have hdir : ∀ u v, grahamDirEdge n u v →
            ∃ x ∈ Sdown.disjSum Sup, φ x = s(u, v) := by
          rintro u v ⟨hw, ⟨hlow, hpar⟩ | ⟨hhi, hpar⟩⟩
          · refine ⟨Sum.inl v, ?_, by simp [φ, hpar]⟩
            rw [Finset.inl_mem_disjSum]
            simp only [Sdown, Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          · have hvu : antipode (parentVertex (antipode u)) = v := by
              rw [hpar, antipode_antipode]
            have hlt : hammingWeight u < n := by
              have hvb : hammingWeight v ≤ n := by
                rw [hammingWeight_eq_hammingDist]; exact hammingDist_le_n _ _
              omega
            refine ⟨Sum.inr u, ?_, by simp [φ, hvu]⟩
            rw [Finset.inr_mem_disjSum]
            simp only [Sup, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hlt, hhi⟩
        rcases he with h | h
        · obtain ⟨x, hx, hxe⟩ := hdir a b h
          exact ⟨x, hx, hxe⟩
        · obtain ⟨x, hx, hxe⟩ := hdir b a h
          exact ⟨x, hx, hxe.trans (Sym2.eq_swap)⟩
  rw [hbij]
  -- Count `Sdown.card + Sup.card` using `card_union_add_card_inter`.
  rcases eq_or_lt_of_le hn with rfl | hn2
  · have h1 : Sdown.card = 1 := by
      have : Sdown = {fun _ : Fin 1 => true} := by
        ext v
        simp only [Sdown, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro ⟨hv1, _⟩
          funext i
          fin_cases i
          by_contra h
          have hf : v 0 = false := by cases hv : v 0 <;> simp_all
          have hw0 : hammingWeight v = 0 := by
            unfold hammingWeight
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro j _; fin_cases j; simp [hf]
          omega
        · rintro rfl
          have hw1 : hammingWeight (fun _ : Fin 1 => true) = 1 := by decide
          omega
      rw [this, Finset.card_singleton]
    have h2 : Sup.card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u _; omega
    rw [h1, h2]
    norm_num
  · have hm1 : 1 ≤ (n + 1) / 2 := by omega
    have hmn : (n + 1) / 2 < n := by omega
    have hunion : Sdown ∪ Sup =
        univ.filter (fun u : CubeVertex n => 1 ≤ hammingWeight u ∧ hammingWeight u < n) := by
      ext u
      simp only [Sdown, Sup, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      have hle : hammingWeight u ≤ n := by
        rw [hammingWeight_eq_hammingDist]; exact hammingDist_le_n _ _
      omega
    have hinter : Sdown ∩ Sup =
        univ.filter (fun u : CubeVertex n => hammingWeight u = (n + 1) / 2) := by
      ext u
      simp only [Sdown, Sup, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hcard_union : (Sdown ∪ Sup).card + 2 = 2 ^ n := by
      rw [hunion]
      have hcomp : univ.filter (fun u : CubeVertex n => ¬(1 ≤ hammingWeight u ∧ hammingWeight u < n)) =
          {fun _ : Fin n => false, fun _ : Fin n => true} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        have hle : hammingWeight u ≤ n := by
          rw [hammingWeight_eq_hammingDist]; exact hammingDist_le_n _ _
        constructor
        · intro h
          rcases (show hammingWeight u = 0 ∨ hammingWeight u = n by omega) with h0 | hn'
          · left
            rw [hammingWeight_eq_hammingDist, hammingDist_eq_zero] at h0
            exact h0.symm
          · right
            have hwa : hammingWeight (antipode u) = 0 := by
              have := hammingWeight_antipode u; omega
            rw [hammingWeight_eq_hammingDist, hammingDist_eq_zero] at hwa
            funext i
            have hi := congr_fun hwa i
            simp only [antipode] at hi
            cases hval : u i
            · rw [hval] at hi; simp at hi
            · rfl
        · rintro (rfl | rfl)
          · have : hammingWeight (fun _ : Fin n => false) = 0 := by
              rw [hammingWeight_eq_hammingDist, hammingDist_self]
            omega
          · have : hammingWeight (fun _ : Fin n => true) = n := by
              rw [hammingWeight_eq_hammingDist]
              have h1 := hammingDist_antipode_self (fun _ : Fin n => false)
              rw [hammingDist_comm] at h1
              exact h1
            omega
      have hne : (fun _ : Fin n => false) ≠ (fun _ : Fin n => true) := by
        intro h
        have h0 := congr_fun h ⟨0, by omega⟩
        simp at h0
      have hadd := Finset.card_filter_add_card_filter_not (s := univ)
        (fun u : CubeVertex n => 1 ≤ hammingWeight u ∧ hammingWeight u < n)
      rw [hcomp, Finset.card_pair hne, Finset.card_univ, card_vertices] at hadd
      exact hadd
    have hcard_inter : (Sdown ∩ Sup).card = n.choose (n / 2) := by
      rw [hinter]
      have hs : (univ.filter fun u : CubeVertex n => hammingWeight u = (n + 1) / 2).card =
          n.choose ((n + 1) / 2) := by
        have h := card_hamming_sphere (fun _ : Fin n => false) ((n + 1) / 2)
        convert h using 2
        ext u
        simp [hammingWeight_eq_hammingDist]
      rw [hs]
      by_cases heven : n % 2 = 0
      · have : (n + 1) / 2 = n / 2 := by omega
        rw [this]
      · have hsym := Nat.choose_symm (show n / 2 ≤ n by omega)
        have hsub : n - n / 2 = (n + 1) / 2 := by omega
        rw [hsub] at hsym
        exact hsym
    have hsum := Finset.card_union_add_card_inter Sdown Sup
    omega

/-- General upper bound: `f n ≤ 2^n + C(n, ⌊n/2⌋) - 2` for every `n ≥ 1`. -/
theorem f_le_construction {n : ℕ} (hn : 1 ≤ n) :
    f n ≤ 2 ^ n + n.choose (n / 2) - 2 := by
  calc f n ≤ edgeCount (grahamConstruction n) :=
        f_le_of_valid (grahamConstruction n) (grahamConstruction_valid n)
    _ = 2 ^ n + n.choose (n / 2) - 2 := grahamConstruction_edgeCount hn

theorem f_two_le_four : f 2 ≤ 4 := by
  have h := f_le_construction (n := 2) (by norm_num)
  norm_num at h
  exact h

theorem f_three_le_nine : f 3 ≤ 9 := by
  have h := f_le_construction (n := 3) (by norm_num)
  norm_num at h
  exact h

theorem f_four_le_twenty : f 4 ≤ 20 := by
  have h := f_le_construction (n := 4) (by norm_num)
  norm_num at h
  exact h

theorem f_five_le_forty : f 5 ≤ 40 := by
  have h := f_le_construction (n := 5) (by norm_num)
  norm_num at h
  exact h

end Hypercube
