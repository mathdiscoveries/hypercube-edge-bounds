module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Sum

import Mathlib.Tactic

/-!
# Faithful Hypercube & Diameter-Preserving Spanning Subgraph Definitions

This module defines the `n`-dimensional hypercube `Q n` on `CubeVertex n := Fin n → Bool`,
the diameter-preserving spanning subgraph predicate `IsValidSpanningSubgraph`, the exact
edge-count minimum `f n`, basic hypercube parity and Hamming geometry, and the BFS-level
machinery (`levelSet`, `excess`, `levelExcess`, `ballExcess`, `parentCount`, `extraParents`,
`weightedExtra`, `lSum`, `distSum`, `distGap`, `edgeExcess`) leading to the exact level
identities `part_a`, `part_b`, `part_c`, and `part_d`.
-/

@[expose] public section

namespace Hypercube

open Finset

/-- Vertices of the `n`-dimensional hypercube: `n`-bit binary strings. -/
abbrev CubeVertex (n : ℕ) := Fin n → Bool

/-- The `n`-dimensional hypercube graph `Q n`: two vertices are adjacent iff their
Hamming distance equals `1`. -/
def Q (n : ℕ) : SimpleGraph (CubeVertex n) where
  Adj u v := hammingDist u v = 1
  symm := ⟨fun u v (h : hammingDist u v = 1) => (hammingDist_comm v u).trans h⟩
  loopless := ⟨fun u (h : hammingDist u u = 1) =>
    absurd ((hammingDist_self u).symm.trans h) zero_ne_one⟩

instance instDecidableRelQAdj (n : ℕ) : DecidableRel (Q n).Adj :=
  fun u v => inferInstanceAs (Decidable (hammingDist u v = 1))

/-- A spanning subgraph `G` of `Q n` is **valid** (diameter-preserving) iff `G ≤ Q n` and
every pair of vertices is connected by a path of length at most `n` in `G`.
Because `G ≤ Q n` forces `edist ≥ hammingDist` and antipodes are at Hamming distance `n`,
this is equivalent to `G ≤ Q n ∧ G.ediam = n` (proved in `isValidSpanningSubgraph_iff_ediam`). -/
def IsValidSpanningSubgraph (n : ℕ) (G : SimpleGraph (CubeVertex n)) : Prop :=
  G ≤ Q n ∧ ∀ u v : CubeVertex n, G.Reachable u v ∧ G.edist u v ≤ n

/-- Number of edges of a spanning subgraph `G` of `Q n`. -/
def edgeCount {n : ℕ} (G : SimpleGraph (CubeVertex n)) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- `f n`: the minimum number of edges of a diameter-preserving spanning subgraph of `Q n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf { e : ℕ | ∃ (G : SimpleGraph (CubeVertex n)) (_ : DecidableRel G.Adj),
    IsValidSpanningSubgraph n G ∧ edgeCount G = e }

theorem edgeCount_eq_ncard {n : ℕ} (G : SimpleGraph (CubeVertex n)) [DecidableRel G.Adj] :
    edgeCount G = G.edgeSet.ncard := by
  unfold edgeCount
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]

/-! ### Boolean and Hamming-distance helpers -/

theorem bool_ne_not (b : Bool) : b ≠ !b := by
  cases b <;> decide

theorem bool_not_eq_of_ne {a b : Bool} (h : a ≠ b) : (!a) = b := by
  revert h
  cases a <;> cases b <;> decide

theorem bool_flip_iff (a b : Bool) : ((!a) ≠ b) ↔ ¬(a ≠ b) := by
  cases a <;> cases b <;> decide

theorem bool_ite_add (a b c : Bool) (h : b ≠ c) :
    (if a ≠ c then 1 else 0 : ℕ) + (if a ≠ b then 1 else 0) = 1 := by
  revert h
  cases a <;> cases b <;> cases c <;> decide

theorem hammingDist_eq_sum {n : ℕ} (x y : CubeVertex n) :
    hammingDist x y = ∑ i, (if x i ≠ y i then 1 else 0 : ℕ) := by
  rw [hammingDist, Finset.card_filter]

/-- Hamming weight (number of `true` coordinates) of a hypercube vertex. -/
def hammingWeight {n : ℕ} (x : CubeVertex n) : ℕ :=
  (univ.filter fun i : Fin n => x i = true).card

theorem hammingWeight_eq_hammingDist {n : ℕ} (x : CubeVertex n) :
    hammingWeight x = hammingDist (fun _ => false) x := by
  unfold hammingWeight
  rw [hammingDist]
  congr 1
  ext i
  cases x i <;> simp

/-- Antipode of a hypercube vertex: flip every coordinate. -/
def antipode {n : ℕ} (x : CubeVertex n) : CubeVertex n :=
  fun i => !x i

theorem antipode_antipode {n : ℕ} (x : CubeVertex n) : antipode (antipode x) = x := by
  funext i
  simp [antipode]

theorem hammingDist_antipode_left {n : ℕ} (x y : CubeVertex n) :
    hammingDist (antipode x) y + hammingDist x y = n := by
  rw [hammingDist_eq_sum, hammingDist_eq_sum, ← Finset.sum_add_distrib]
  have h : ∀ i : Fin n,
      (if antipode x i ≠ y i then 1 else 0 : ℕ) + (if x i ≠ y i then 1 else 0) = 1 := by
    intro i
    show (if (!x i) ≠ y i then 1 else 0 : ℕ) + (if x i ≠ y i then 1 else 0) = 1
    cases hx : x i <;> cases hy : y i <;> simp
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

theorem hammingDist_antipode_right {n : ℕ} (x y : CubeVertex n) :
    hammingDist x (antipode y) + hammingDist x y = n := by
  rw [hammingDist_comm x (antipode y), hammingDist_comm x y]
  exact hammingDist_antipode_left y x

theorem hammingDist_antipode_antipode {n : ℕ} (x y : CubeVertex n) :
    hammingDist (antipode x) (antipode y) = hammingDist x y := by
  rw [hammingDist_eq_sum, hammingDist_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (if (!x i) ≠ (!y i) then 1 else 0 : ℕ) = (if x i ≠ y i then 1 else 0)
  cases hx : x i <;> cases hy : y i <;> simp

theorem hammingDist_antipode_self {n : ℕ} (x : CubeVertex n) :
    hammingDist (antipode x) x = n := by
  have h := hammingDist_antipode_left x x
  rw [hammingDist_self] at h
  omega

theorem hammingWeight_antipode {n : ℕ} (x : CubeVertex n) :
    hammingWeight (antipode x) + hammingWeight x = n := by
  rw [hammingWeight_eq_hammingDist, hammingWeight_eq_hammingDist]
  exact hammingDist_antipode_right _ x

theorem hammingDist_le_n {n : ℕ} (x y : CubeVertex n) : hammingDist x y ≤ n := by
  have h : hammingDist x y ≤ Fintype.card (Fin n) := hammingDist_le_card_fintype
  rwa [Fintype.card_fin] at h

theorem exists_coord_of_hammingDist_eq_one {n : ℕ} {u w : CubeVertex n}
    (h : hammingDist u w = 1) : ∃ i, ∀ j, u j ≠ w j ↔ j = i := by
  rw [hammingDist, Finset.card_eq_one] at h
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun j => ?_⟩
  have hj := Finset.ext_iff.1 hi j
  simpa using hj

/-- One edge of `Q n` changes the Hamming distance to any fixed vertex `v` by `±1`. -/
theorem hammingDist_step {n : ℕ} {u w : CubeVertex n} (h : hammingDist u w = 1)
    (v : CubeVertex n) :
    hammingDist v w + 1 = hammingDist v u ∨ hammingDist v u + 1 = hammingDist v w := by
  obtain ⟨i, key⟩ := exists_coord_of_hammingDist_eq_one h
  have hi : u i ≠ w i := (key i).2 rfl
  have hw := hammingDist_eq_sum v w
  have hu := hammingDist_eq_sum v u
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hw hu
  have hS : ∑ j ∈ univ.erase i, (if v j ≠ w j then 1 else 0 : ℕ) =
      ∑ j ∈ univ.erase i, (if v j ≠ u j then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have huw : u j = w j := by
      by_contra hne
      exact Finset.ne_of_mem_erase hj ((key j).1 hne)
    rw [huw]
  have hb := bool_ite_add (v i) (u i) (w i) hi
  omega

theorem hammingDist_of_adj {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) {u w : CubeVertex n} (h : G.Adj u w) :
    hammingDist u w = 1 :=
  hG h

/-- Step 1 (Walk length lower bound & parity): every walk in a subgraph of `Q n` has
length at least the Hamming distance of its endpoints and matching parity. -/
theorem walk_length_parity {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) {u w : CubeVertex n} (p : G.Walk u w) :
    hammingDist u w ≤ p.length ∧ p.length % 2 = hammingDist u w % 2 := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have h2 := hammingDist_step (hammingDist_of_adj hG h) c
    rw [hammingDist_comm c b, hammingDist_comm c a] at h2
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Flip coordinate `i` of a hypercube vertex `x`. -/
def flipAt {n : ℕ} (i : Fin n) (x : CubeVertex n) : CubeVertex n :=
  fun j => if j = i then !x j else x j

theorem flipAt_apply_self {n : ℕ} (i : Fin n) (x : CubeVertex n) :
    flipAt i x i = !x i := by
  simp [flipAt]

theorem flipAt_apply_of_ne {n : ℕ} {i j : Fin n} (x : CubeVertex n) (h : j ≠ i) :
    flipAt i x j = x j := by
  simp [flipAt, h]

theorem flipAt_flipAt {n : ℕ} (i : Fin n) (x : CubeVertex n) :
    flipAt i (flipAt i x) = x := by
  funext j
  by_cases h : j = i
  · subst h; simp [flipAt]
  · simp [flipAt, h]

theorem hammingDist_flipAt {n : ℕ} (i : Fin n) (x : CubeVertex n) :
    hammingDist x (flipAt i x) = 1 := by
  rw [hammingDist, Finset.card_eq_one]
  refine ⟨i, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
  · rw [Finset.mem_filter, flipAt_apply_self]
    exact ⟨Finset.mem_univ i, bool_ne_not (x i)⟩
  · intro j hj
    by_contra h
    rw [Finset.mem_filter, flipAt_apply_of_ne x h] at hj
    exact hj.2 rfl

theorem hammingDist_flipAt_of_ne {n : ℕ} {i : Fin n} {u w : CubeVertex n}
    (h : u i ≠ w i) :
    hammingDist (flipAt i u) w + 1 = hammingDist u w := by
  have hf := hammingDist_eq_sum (flipAt i u) w
  have hu := hammingDist_eq_sum u w
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hf hu
  have hS :
      ∑ j ∈ univ.erase i, (if flipAt i u j ≠ w j then 1 else 0 : ℕ) =
        ∑ j ∈ univ.erase i, (if u j ≠ w j then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [flipAt_apply_of_ne u (Finset.ne_of_mem_erase hj)]
  have ha : (if u i ≠ w i then 1 else 0 : ℕ) = 1 := by simp [h]
  have hb : (if flipAt i u i ≠ w i then 1 else 0 : ℕ) = 0 := by
    rw [flipAt_apply_self, bool_not_eq_of_ne h]
    simp
  omega

/-- In `Q n`, there is a walk from `u` to `w` of length `hammingDist u w`. -/
theorem exists_walk_hamming {n : ℕ} (w : CubeVertex n) :
    ∀ (k : ℕ) (u : CubeVertex n), hammingDist u w = k →
      ∃ p : (Q n).Walk u w, p.length = k := by
  intro k
  induction k with
  | zero =>
    intro u hu
    rw [hammingDist_eq_zero] at hu
    subst hu
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ k ih =>
    intro u hu
    have hne : ∃ i, u i ≠ w i := by
      by_contra hall
      push Not at hall
      have huw : u = w := funext hall
      rw [huw, hammingDist_self] at hu
      omega
    obtain ⟨i, hi⟩ := hne
    have hk : hammingDist (flipAt i u) w = k := by
      have h1 := hammingDist_flipAt_of_ne hi
      omega
    obtain ⟨p, hp⟩ := ih (flipAt i u) hk
    have hadj : (Q n).Adj u (flipAt i u) := hammingDist_flipAt i u
    exact ⟨SimpleGraph.Walk.cons hadj p, by rw [SimpleGraph.Walk.length_cons, hp]⟩

theorem Q_reachable {n : ℕ} (u w : CubeVertex n) : (Q n).Reachable u w := by
  obtain ⟨p, _⟩ := exists_walk_hamming w (hammingDist u w) u rfl
  exact ⟨p⟩

/-- Any subgraph `G ≤ Q n` has `hammingDist u v ≤ G.edist u v`. -/
theorem hammingDist_le_edist {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (u v : CubeVertex n) :
    (hammingDist u v : ℕ∞) ≤ G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp]
    exact_mod_cast (walk_length_parity hG p).1
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

/-- Any subgraph `G ≤ Q n` has extended diameter at least `n` (forced by antipodes). -/
theorem n_le_ediam_of_le_Q {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) : (n : ℕ∞) ≤ G.ediam := by
  have h1 := hammingDist_le_edist hG (antipode (fun _ => false)) (fun _ => false)
  rw [hammingDist_antipode_self] at h1
  exact h1.trans SimpleGraph.edist_le_ediam

/-- Equivalence of `IsValidSpanningSubgraph n G` with `G ≤ Q n ∧ G.ediam = n`. -/
theorem isValidSpanningSubgraph_iff_ediam {n : ℕ} (G : SimpleGraph (CubeVertex n)) :
    IsValidSpanningSubgraph n G ↔ G ≤ Q n ∧ G.ediam = (n : ℕ∞) := by
  constructor
  · rintro ⟨hG, h⟩
    refine ⟨hG, le_antisymm ?_ (n_le_ediam_of_le_Q hG)⟩
    exact SimpleGraph.ediam_le_of_edist_le fun u v => (h u v).2
  · rintro ⟨hG, hD⟩
    refine ⟨hG, fun u v => ?_⟩
    have hle : G.edist u v ≤ (n : ℕ∞) := by
      calc G.edist u v ≤ G.ediam := SimpleGraph.edist_le_ediam
        _ = (n : ℕ∞) := hD
    have hne : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hle
    exact ⟨SimpleGraph.edist_ne_top_iff_reachable.1 hne, hle⟩

/-- `Q n` itself is a valid diameter-preserving spanning subgraph of `Q n`. -/
theorem Q_valid (n : ℕ) : IsValidSpanningSubgraph n (Q n) := by
  refine ⟨le_refl _, fun u v => ⟨Q_reachable u v, ?_⟩⟩
  obtain ⟨p, hp⟩ := exists_walk_hamming v (hammingDist u v) u rfl
  calc (Q n).edist u v ≤ p.length := SimpleGraph.edist_le p
    _ = (hammingDist u v : ℕ∞) := by rw [hp]
    _ ≤ (n : ℕ∞) := by exact_mod_cast hammingDist_le_n u v

/-- `Q n` has diameter `n`. -/
theorem Q_ediam (n : ℕ) : (Q n).ediam = (n : ℕ∞) :=
  ((isValidSpanningSubgraph_iff_ediam (Q n)).1 (Q_valid n)).2

theorem f_set_nonempty (n : ℕ) :
    { e : ℕ | ∃ (G : SimpleGraph (CubeVertex n)) (_ : DecidableRel G.Adj),
      IsValidSpanningSubgraph n G ∧ edgeCount G = e }.Nonempty :=
  ⟨edgeCount (Q n), Q n, inferInstance, Q_valid n, rfl⟩

theorem f_le_of_valid {n : ℕ} (G : SimpleGraph (CubeVertex n)) [DecidableRel G.Adj]
    (hG : IsValidSpanningSubgraph n G) : f n ≤ edgeCount G :=
  Nat.sInf_le ⟨G, inferInstance, hG, rfl⟩

theorem le_f_of_forall_valid {n m : ℕ}
    (h : ∀ G : SimpleGraph (CubeVertex n), IsValidSpanningSubgraph n G → m ≤ G.edgeSet.ncard) :
    m ≤ f n := by
  apply le_csInf (f_set_nonempty n)
  rintro e ⟨G, _, hG, rfl⟩
  rw [edgeCount_eq_ncard]
  exact h G hG

/-! ### Cube counting lemmas -/

theorem card_filter_half {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] (φ : α → α) (hφ : ∀ x, φ (φ x) = x)
    (hP : ∀ x, P (φ x) ↔ ¬P x) :
    2 * (univ.filter P).card = Fintype.card α := by
  have h1 : (univ.filter P).card = (univ.filter fun x => ¬P x).card := by
    refine Finset.card_nbij' φ φ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact fun h => ((hP x).1 h) hx
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hP x).2 hx
    · intro x _; exact hφ x
    · intro x _; exact hφ x
  have h2 := Finset.card_filter_add_card_filter_not (s := univ) P
  rw [Finset.card_univ] at h2
  omega

theorem card_vertices (n : ℕ) : Fintype.card (CubeVertex n) = 2 ^ n := by
  rw [Fintype.card_pi_const, Fintype.card_bool]

theorem card_hamming_parity {n : ℕ} (hn : 1 ≤ n) (v : CubeVertex n) (r : ℕ) (hr : r < 2) :
    (univ.filter fun u => hammingDist v u % 2 = r).card = 2 ^ (n - 1) := by
  have hP : ∀ u : CubeVertex n,
      hammingDist v (flipAt ⟨0, hn⟩ u) % 2 = r ↔ ¬(hammingDist v u % 2 = r) := by
    intro u
    have h := hammingDist_step (hammingDist_flipAt ⟨0, hn⟩ u) v
    constructor <;> intro h' <;> omega
  have h2 := card_filter_half (fun u => hammingDist v u % 2 = r)
    (flipAt ⟨0, hn⟩) (flipAt_flipAt ⟨0, hn⟩) hP
  rw [card_vertices] at h2
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- Flip the coordinates in `s` of a vertex `w`. -/
def flipSet {n : ℕ} (w : CubeVertex n) (s : Finset (Fin n)) : CubeVertex n :=
  fun i => if i ∈ s then !w i else w i

theorem card_hamming_sphere {n : ℕ} (w : CubeVertex n) (k : ℕ) :
    (univ.filter fun u => hammingDist w u = k).card = n.choose k := by
  have hc : (powersetCard k (univ : Finset (Fin n))).card = n.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hc]
  refine Finset.card_nbij' (fun u => univ.filter fun j => w j ≠ u j) (flipSet w) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hu⟩
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hs.2, hammingDist]
    congr 1
    ext j
    simp only [flipSet]
    by_cases hj : j ∈ s <;> simp [hj]
  · intro u _
    funext j
    show (if j ∈ univ.filter (fun j => w j ≠ u j) then !w j else w j) = u j
    by_cases h : w j = u j
    · simp [h]
    · simp [h, bool_not_eq_of_ne h]
  · intro s _
    ext j
    simp only [flipSet]
    by_cases hj : j ∈ s <;> simp [hj]

theorem sum_hammingDist {n : ℕ} (w : CubeVertex n) :
    2 * ∑ v, hammingDist v w = n * 2 ^ n := by
  have h2 : ∀ i : Fin n,
      2 * ∑ v : CubeVertex n, (if v i ≠ w i then 1 else 0 : ℕ) = 2 ^ n := by
    intro i
    rw [← Finset.card_filter]
    rw [card_filter_half (fun v : CubeVertex n => v i ≠ w i) (flipAt i)
      (flipAt_flipAt i) ?_, card_vertices]
    intro v
    simp only [flipAt_apply_self]
    exact bool_flip_iff (v i) (w i)
  simp_rw [hammingDist_eq_sum]
  rw [Finset.sum_comm, Finset.mul_sum,
    Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ### BFS Levels, Excess, Extra Parents, and Exact Level Identities -/

noncomputable section

/-- `R_n`: the radii `m ≤ n - 2` with `m ≡ n (mod 2)`. -/
def rSet (n : ℕ) : Finset ℕ :=
  (range (n - 1)).filter fun m => m % 2 = n % 2

/-- `S_k(v)`: vertices at distance `k` from `v` in `G`. -/
def levelSet {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n)
    (k : ℕ) : Finset (CubeVertex n) :=
  univ.filter fun u => G.dist v u = k

/-- `x_u = d_u - 2`, the degree excess of `u` in `G`. -/
def excess {n : ℕ} (G : SimpleGraph (CubeVertex n)) (u : CubeVertex n) : ℤ :=
  ((G.neighborSet u).ncard : ℤ) - 2

/-- `X_k(v)`: total excess on BFS level `S_k(v)`. -/
def levelExcess {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n) (k : ℕ) : ℤ :=
  ∑ u ∈ levelSet G v k, excess G u

/-- `Y_m(v) = X_0(v) + ... + X_m(v)`: total excess in the radius-`m` BFS ball around `v`. -/
def ballExcess {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n) (m : ℕ) : ℤ :=
  ∑ k ∈ range (m + 1), levelExcess G v k

/-- `p_v(u)` for `u ∈ S_k(v)`: number of neighbours of `u` at distance `k - 1` from `v`. -/
def parentCount {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n)
    (k : ℕ) (u : CubeVertex n) : ℕ :=
  {w | G.Adj u w ∧ G.dist v w + 1 = k}.ncard

/-- `M_k(v) = ∑_{u ∈ S_k(v)} (p_v(u) - 1)`: extra parent edges entering level `k`. -/
def extraParents {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n) (k : ℕ) : ℤ :=
  ∑ u ∈ levelSet G v k, ((parentCount G v k u : ℤ) - 1)

/-- `M(v) = ∑_{j=2}^{n-1} (n - j) M_j(v)`. -/
def weightedExtra {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n) : ℤ :=
  ∑ j ∈ Ico 2 n, ((n : ℤ) - j) * extraParents G v j

/-- `L(v) = ∑_{m ∈ R_n} Y_m(v)`. -/
def lSum {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n) : ℤ :=
  ∑ m ∈ rSet n, ballExcess G v m

/-- `D(w) = ∑_v d(v, w)`: sum of distances to `w` in `G`. -/
def distSum {n : ℕ} (G : SimpleGraph (CubeVertex n)) (w : CubeVertex n) : ℤ :=
  ∑ v, (G.dist v w : ℤ)

/-- `δ(w) = D(w) - n 2^(n-1)`: total distance gap relative to `Q n` from `w`. -/
def distGap {n : ℕ} (G : SimpleGraph (CubeVertex n)) (w : CubeVertex n) : ℤ :=
  distSum G w - (n : ℤ) * 2 ^ (n - 1)

/-- `t = e - 2^n`: edge count above `2^n`. -/
def edgeExcess {n : ℕ} (G : SimpleGraph (CubeVertex n)) : ℤ :=
  (G.edgeSet.ncard : ℤ) - 2 ^ n

/-- Number of children of `u` at level `k` from `v`. -/
def childCount {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n)
    (k : ℕ) (u : CubeVertex n) : ℕ :=
  {w | G.Adj u w ∧ G.dist v w = k + 1}.ncard

theorem connected_of_ediam {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hD : G.ediam = (n : ℕ∞)) : G.Connected :=
  SimpleGraph.connected_of_ediam_ne_top (by rw [hD]; exact ENat.natCast_ne_top n)

theorem dist_le_of_ediam {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hD : G.ediam = (n : ℕ∞)) (u w : CubeVertex n) : G.dist u w ≤ n := by
  have h1 : G.edist u w ≤ G.ediam := SimpleGraph.edist_le_ediam
  rw [hD, ← ((connected_of_ediam hD).preconnected u w).coe_dist_eq_edist] at h1
  exact_mod_cast h1

theorem dist_hamming {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (u w : CubeVertex n) :
    hammingDist u w ≤ G.dist u w ∧ G.dist u w % 2 = hammingDist u w % 2 := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u w
  rw [← hp]
  exact walk_length_parity hG p

theorem adj_levels {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) {u w : CubeVertex n} (h : G.Adj u w) (v : CubeVertex n) :
    G.dist v w = G.dist v u + 1 ∨ G.dist v u = G.dist v w + 1 := by
  have t1 : G.dist v w ≤ G.dist v u + G.dist u w := hc.dist_triangle
  have t2 : G.dist v u ≤ G.dist v w + G.dist w u := hc.dist_triangle
  have e1 : G.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 h
  have e2 : G.dist w u = 1 := SimpleGraph.dist_eq_one_iff_adj.2 h.symm
  have pu := (dist_hamming hG hc v u).2
  have pw := (dist_hamming hG hc v w).2
  have hs := hammingDist_step (hammingDist_of_adj hG h) v
  omega

theorem exists_parent {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) {v u : CubeVertex n} (hu : 1 ≤ G.dist v u) :
    ∃ w, G.Adj u w ∧ G.dist v w + 1 = G.dist v u := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  have e0 : G.dist v u = G.dist u v := SimpleGraph.dist_comm
  cases p with
  | nil => simp at hu
  | @cons _ w _ h q =>
    refine ⟨w, h, ?_⟩
    have h1 : G.dist w v ≤ q.length := SimpleGraph.dist_le q
    have h2 : G.dist u v ≤ G.dist u w + G.dist w v := hc.dist_triangle
    have h3 : G.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 h
    have e1 : G.dist v w = G.dist w v := SimpleGraph.dist_comm
    rw [SimpleGraph.Walk.length_cons] at hp
    omega

/-- Step 2 (Minimum degree): for `n ≥ 2`, every vertex in a valid subgraph of `Q n`
has degree at least `2`. -/
theorem two_le_ncard_neighborSet {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (u : CubeVertex n) :
    2 ≤ (G.neighborSet u).ncard := by
  have hc := connected_of_ediam hD
  have h0 : 1 ≤ G.dist (flipAt ⟨0, by omega⟩ u) u := by
    have h := (dist_hamming hG hc (flipAt ⟨0, by omega⟩ u) u).1
    rw [hammingDist_comm, hammingDist_flipAt] at h
    exact h
  obtain ⟨a, ha, -⟩ := exists_parent hc h0
  let z : CubeVertex n := antipode a
  have hza : hammingDist z a = n := hammingDist_antipode_self a
  have hzu : hammingDist z u = n - 1 := by
    have hs := hammingDist_step (hammingDist_of_adj hG ha) z
    have hle := hammingDist_le_n z u
    omega
  have hd := dist_hamming hG hc z u
  have hdle := dist_le_of_ediam hD z u
  have hdzu : G.dist z u = n - 1 := by omega
  obtain ⟨b, hb, hbd⟩ := exists_parent hc (show 1 ≤ G.dist z u by omega)
  have hzb := (dist_hamming hG hc z b).1
  have hab : a ≠ b := by
    rintro rfl
    omega
  have hsub : ({a, b} : Set (CubeVertex n)) ⊆ G.neighborSet u := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  calc 2 = ({a, b} : Set (CubeVertex n)).ncard := (Set.ncard_pair hab).symm
    _ ≤ (G.neighborSet u).ncard := Set.ncard_le_ncard hsub

theorem ncard_neighborSet_eq_degree {n : ℕ} {G : SimpleGraph (CubeVertex n)} [DecidableRel G.Adj]
    (u : CubeVertex n) : (G.neighborSet u).ncard = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
    SimpleGraph.coe_neighborFinset]

theorem two_le_degree {n : ℕ} {G : SimpleGraph (CubeVertex n)} [DecidableRel G.Adj]
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) (u : CubeVertex n) :
    2 ≤ G.degree u := by
  rw [← ncard_neighborSet_eq_degree]
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  exact two_le_ncard_neighborSet hn hG hD u

theorem ncard_neighborSet_le_n {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (u : CubeVertex n) : (G.neighborSet u).ncard ≤ n := by
  have hsub : G.neighborSet u ⊆ (univ.filter fun w => hammingDist u w = 1 : Finset (CubeVertex n)) := by
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hG hw
  calc (G.neighborSet u).ncard
      ≤ ((univ.filter fun w => hammingDist u w = 1 : Finset (CubeVertex n)) : Set (CubeVertex n)).ncard :=
        Set.ncard_le_ncard hsub
    _ = (univ.filter fun w => hammingDist u w = 1).card := Set.ncard_coe_finset _
    _ = n.choose 1 := card_hamming_sphere u 1
    _ = n := Nat.choose_one_right n

theorem excess_nonneg {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (u : CubeVertex n) :
    0 ≤ excess G u := by
  have h := two_le_ncard_neighborSet hn hG hD u
  unfold excess
  omega

theorem excess_le {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (u : CubeVertex n) : excess G u ≤ (n : ℤ) - 2 := by
  have h := ncard_neighborSet_le_n hG u
  unfold excess
  omega

theorem ncard_eq_sum {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    {x | P x}.ncard = ∑ x, (if P x then 1 else 0 : ℕ) := by
  rw [← Finset.card_filter, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

theorem mem_levelSet {n : ℕ} {G : SimpleGraph (CubeVertex n)} {v u : CubeVertex n} {k : ℕ} :
    u ∈ levelSet G v k ↔ G.dist v u = k := by
  simp [levelSet]

theorem degree_split {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) {v u : CubeVertex n} {k : ℕ} (hu : G.dist v u = k) :
    (G.neighborSet u).ncard = parentCount G v k u + childCount G v k u := by
  have hset : G.neighborSet u =
      {w | G.Adj u w ∧ G.dist v w + 1 = k} ∪ {w | G.Adj u w ∧ G.dist v w = k + 1} := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro h
      rcases adj_levels hG hc h v with h1 | h1
      · exact Or.inr ⟨h, by omega⟩
      · exact Or.inl ⟨h, by omega⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint {w | G.Adj u w ∧ G.dist v w + 1 = k}
      {w | G.Adj u w ∧ G.dist v w = k + 1} := by
    rw [Set.disjoint_left]
    rintro w ⟨_, h1⟩ ⟨_, h2⟩
    omega
  unfold parentCount childCount
  rw [hset, Set.ncard_union_eq hdisj]

theorem sum_child_eq {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (_hG : G ≤ Q n) (_hc : G.Connected) (v : CubeVertex n) (k : ℕ) :
    ∑ u ∈ levelSet G v k, (childCount G v k u : ℤ) =
      ∑ w ∈ levelSet G v (k + 1), (parentCount G v (k + 1) w : ℤ) := by
  classical
  have hA : ∀ u : CubeVertex n,
      (if G.dist v u = k then childCount G v k u else 0) =
        ∑ w, (if G.dist v u = k ∧ G.Adj u w ∧ G.dist v w = k + 1 then 1 else 0 : ℕ) := by
    intro u
    by_cases hu : G.dist v u = k
    · simp only [hu, ↓reduceIte, childCount, ncard_eq_sum, true_and]
    · simp only [hu, ↓reduceIte, false_and, Finset.sum_const_zero]
  have hB : ∀ w : CubeVertex n,
      (if G.dist v w = k + 1 then parentCount G v (k + 1) w else 0) =
        ∑ u, (if G.dist v u = k ∧ G.Adj u w ∧ G.dist v w = k + 1 then 1 else 0 : ℕ) := by
    intro w
    by_cases hw : G.dist v w = k + 1
    · simp only [hw, ↓reduceIte, parentCount, ncard_eq_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs with h1 h2 h2
      · rfl
      · exfalso; exact h2 ⟨by omega, h1.1.symm, trivial⟩
      · exfalso; exact h1 ⟨h2.2.1.symm, by omega⟩
      · rfl
    · simp only [hw, ↓reduceIte, and_false, Finset.sum_const_zero]
  suffices h : ∑ u ∈ levelSet G v k, childCount G v k u =
      ∑ w ∈ levelSet G v (k + 1), parentCount G v (k + 1) w by
    exact_mod_cast h
  simp only [levelSet, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun u _ => hA u, Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => (hB w).symm

theorem level_step {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (v : CubeVertex n) (k : ℕ) :
    ((levelSet G v (k + 1)).card : ℤ) =
      (levelSet G v k).card + levelExcess G v k - extraParents G v k -
        extraParents G v (k + 1) := by
  have hdeg : ∑ u ∈ levelSet G v k, ((G.neighborSet u).ncard : ℤ) =
      ∑ u ∈ levelSet G v k, (parentCount G v k u : ℤ) +
        ∑ u ∈ levelSet G v k, (childCount G v k u : ℤ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [mem_levelSet] at hu
    rw [degree_split hG hc hu, Nat.cast_add]
  have hU := sum_child_eq hG hc v k
  have hX : levelExcess G v k =
      ∑ u ∈ levelSet G v k, ((G.neighborSet u).ncard : ℤ) -
        2 * (levelSet G v k).card := by
    simp only [levelExcess, excess, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hM0 : extraParents G v k =
      ∑ u ∈ levelSet G v k, (parentCount G v k u : ℤ) - (levelSet G v k).card := by
    simp [extraParents, Finset.sum_sub_distrib]
  have hM1 : extraParents G v (k + 1) =
      ∑ w ∈ levelSet G v (k + 1), (parentCount G v (k + 1) w : ℤ) -
        (levelSet G v (k + 1)).card := by
    simp [extraParents, Finset.sum_sub_distrib]
  linarith

theorem card_levelSet_zero {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (v : CubeVertex n) : (levelSet G v 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨v, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
  · rw [mem_levelSet]; exact SimpleGraph.dist_self
  · intro u hu; rw [mem_levelSet] at hu; exact (hc.dist_eq_zero_iff.1 hu).symm

theorem levelSet_zero {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (v : CubeVertex n) : levelSet G v 0 = {v} := by
  ext u
  simp only [mem_levelSet, Finset.mem_singleton]
  exact ⟨fun h => (hc.dist_eq_zero_iff.1 h).symm, fun h => by subst h; exact SimpleGraph.dist_self⟩

theorem levelExcess_zero {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (v : CubeVertex n) : levelExcess G v 0 = excess G v := by
  simp [levelExcess, levelSet_zero hc v]

theorem parentCount_zero {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (v u : CubeVertex n) : parentCount G v 0 u = 0 := by
  have hset : {w | G.Adj u w ∧ G.dist v w + 1 = 0} = (∅ : Set (CubeVertex n)) := by
    ext w; simp
  unfold parentCount
  rw [hset, Set.ncard_empty]

theorem extraParents_zero {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (v : CubeVertex n) : extraParents G v 0 = -1 := by
  have h1 : extraParents G v 0 = ∑ _u ∈ levelSet G v 0, (-1 : ℤ) := by
    unfold extraParents
    refine Finset.sum_congr rfl fun u _ => by simp [parentCount_zero]
  simp [h1, card_levelSet_zero hc v]

theorem parentCount_one {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) {v u : CubeVertex n} (hu : G.dist v u = 1) :
    parentCount G v 1 u = 1 := by
  have hadj : G.Adj u v := (SimpleGraph.dist_eq_one_iff_adj.1 hu).symm
  have hset : {w | G.Adj u w ∧ G.dist v w + 1 = 1} = ({v} : Set (CubeVertex n)) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, h⟩
      have h0 : G.dist v w = 0 := by omega
      exact (hc.dist_eq_zero_iff.1 h0).symm
    · rintro rfl
      exact ⟨hadj, by simp⟩
  unfold parentCount
  rw [hset, Set.ncard_singleton]

theorem extraParents_one {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (v : CubeVertex n) : extraParents G v 1 = 0 := by
  unfold extraParents
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [mem_levelSet] at hu
  simp [parentCount_one hc hu]

theorem extraParents_nonneg {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (v : CubeVertex n) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ extraParents G v k := by
  unfold extraParents
  refine Finset.sum_nonneg fun u hu => ?_
  rw [mem_levelSet] at hu
  obtain ⟨w, hw, hwd⟩ := exists_parent hc (show 1 ≤ G.dist v u by omega)
  have h1 : 0 < parentCount G v k u :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨w, hw, by omega⟩
  omega

theorem levelSet_eq_empty {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hD : G.ediam = (n : ℕ∞)) (v : CubeVertex n) {k : ℕ} (hk : n < k) :
    levelSet G v k = ∅ := by
  unfold levelSet
  rw [Finset.filter_eq_empty_iff]
  intro u _ h
  have := dist_le_of_ediam hD v u
  omega

theorem levels_sum {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (v : CubeVertex n) (g : CubeVertex n → ℤ) (N : ℕ) :
    ∑ k ∈ range N, ∑ u ∈ levelSet G v k, g u =
      ∑ u, if G.dist v u < N then g u else 0 := by
  simp only [levelSet, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

theorem sum_levelExcess {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hD : G.ediam = (n : ℕ∞)) (v : CubeVertex n) :
    ∑ k ∈ range (n + 1), levelExcess G v k = ∑ u, excess G u := by
  simp only [levelExcess]
  rw [levels_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hlt : G.dist v u < n + 1 := Nat.lt_succ_of_le (dist_le_of_ediam hD v u)
  simp [hlt]

theorem sum_ncard_neighborSet {n : ℕ} {G : SimpleGraph (CubeVertex n)} :
    ∑ u, (G.neighborSet u).ncard = 2 * G.edgeSet.ncard := by
  classical
  have h := G.sum_degrees_eq_twice_card_edges
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h
  rw [← h]
  exact Finset.sum_congr rfl fun u _ => ncard_neighborSet_eq_degree u

theorem sum_excess {n : ℕ} {G : SimpleGraph (CubeVertex n)} :
    ∑ u : CubeVertex n, excess G u = 2 * edgeExcess G := by
  have h : (∑ u, ((G.neighborSet u).ncard : ℤ)) = 2 * (G.edgeSet.ncard : ℤ) := by
    exact_mod_cast sum_ncard_neighborSet (G := G)
  have hc : (Finset.univ : Finset (CubeVertex n)).card = 2 ^ n := by
    rw [Finset.card_univ, card_vertices]
  simp only [excess, edgeExcess, Finset.sum_sub_distrib, Finset.sum_const, hc, nsmul_eq_mul]
  push_cast
  linarith

/-- Bipartite edge balance: each parity class of `Q n` has degrees summing to `|E(G)|`. -/
theorem sum_ncard_neighborSet_part {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (r : ℕ) (hr : r < 2) :
    ∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u % 2 = r),
      (G.neighborSet u).ncard = G.edgeSet.ncard := by
  classical
  have hnb : ∀ u : CubeVertex n, (G.neighborSet u).ncard = ∑ w, (if G.Adj u w then 1 else 0 : ℕ) :=
    fun u => ncard_eq_sum (fun w => G.Adj u w)
  have h2 : ∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u % 2 = r),
      (G.neighborSet u).ncard =
      ∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u % 2 = 1 - r),
      (G.neighborSet u).ncard := by
    have hA : ∀ u, (if hammingWeight u % 2 = r then (G.neighborSet u).ncard else 0) =
        ∑ w, (if hammingWeight u % 2 = r ∧ G.Adj u w then 1 else 0 : ℕ) := by
      intro u
      by_cases hu : hammingWeight u % 2 = r
      · simp only [hu, ↓reduceIte, hnb, true_and]
      · simp only [hu, ↓reduceIte, false_and, Finset.sum_const_zero]
    have hB : ∀ w, (if hammingWeight w % 2 = 1 - r then (G.neighborSet w).ncard else 0) =
        ∑ u, (if hammingWeight u % 2 = r ∧ G.Adj u w then 1 else 0 : ℕ) := by
      intro w
      by_cases hw : hammingWeight w % 2 = 1 - r
      · simp only [hw, ↓reduceIte, hnb]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hadj : G.Adj w u
        · have hs := hammingDist_step (hammingDist_of_adj hG hadj) (fun _ => false)
          rw [← hammingWeight_eq_hammingDist, ← hammingWeight_eq_hammingDist] at hs
          have hu : hammingWeight u % 2 = r := by omega
          simp [hadj, hu, hadj.symm]
        · have hnot : ¬(hammingWeight u % 2 = r ∧ G.Adj u w) := fun h => hadj h.2.symm
          simp [hadj, hnot]
      · simp only [hw, ↓reduceIte]
        symm
        refine Finset.sum_eq_zero fun u _ => ?_
        have hnot : ¬(hammingWeight u % 2 = r ∧ G.Adj u w) := by
          rintro ⟨hu, hadj⟩
          have hs := hammingDist_step (hammingDist_of_adj hG hadj) (fun _ => false)
          rw [← hammingWeight_eq_hammingDist, ← hammingWeight_eq_hammingDist] at hs
          omega
        simp [hnot]
    simp only [Finset.sum_filter]
    rw [Finset.sum_congr rfl fun u _ => hA u, Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => (hB w).symm
  have htot := sum_ncard_neighborSet (G := G)
  have hsplit : ∑ u : CubeVertex n, (G.neighborSet u).ncard =
      ∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u % 2 = r), (G.neighborSet u).ncard +
      ∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u % 2 = 1 - r), (G.neighborSet u).ncard := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun u : CubeVertex n => hammingWeight u % 2 = r)]
    congr 2
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  omega

/-- Each parity part's excesses sum to `edgeExcess G = |E(G)| - 2^n`. -/
theorem sum_excess_part {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 1 ≤ n) (hG : G ≤ Q n) (r : ℕ) (hr : r < 2) :
    ∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u % 2 = r), excess G u =
      edgeExcess G := by
  have hdeg : (∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u % 2 = r),
      ((G.neighborSet u).ncard : ℤ)) = (G.edgeSet.ncard : ℤ) := by
    exact_mod_cast sum_ncard_neighborSet_part hG r hr
  have hcard : (univ.filter (fun u : CubeVertex n => hammingWeight u % 2 = r)).card =
      2 ^ (n - 1) := by
    have h := card_hamming_parity hn (fun _ => false) r hr
    convert h using 2
    ext u
    simp [hammingWeight_eq_hammingDist]
  have hpow : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  simp only [excess, edgeExcess, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast
  linarith

/-- Exact BFS level-size identity (`part_a`): for `k ≥ 1`,
`|S_k(v)| = 2 + Y_{k-1}(v) - 2 ∑_{j=2}^{k-1} M_j(v) - M_k(v)`. -/
theorem part_a {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (v : CubeVertex n) (k : ℕ) (hk : 1 ≤ k) :
    ((levelSet G v k).card : ℤ) =
      2 + ballExcess G v (k - 1) -
        2 * (∑ j ∈ Ico 2 k, extraParents G v j) - extraParents G v k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h := level_step hG hc v 0
    simp only [zero_add] at h
    rw [card_levelSet_zero hc v, Nat.cast_one, extraParents_zero hc v, extraParents_one hc v] at h
    have hY : ballExcess G v (1 - 1) = levelExcess G v 0 := by simp [ballExcess]
    have hI : ∑ j ∈ Ico 2 1, extraParents G v j = 0 :=
      Finset.sum_eq_zero fun j hj => by simp only [Finset.mem_Ico] at hj; omega
    rw [hY, hI, extraParents_one hc v]
    linarith
  | succ k hk ih =>
    have h := level_step hG hc v k
    have hY : ballExcess G v (k + 1 - 1) = ballExcess G v (k - 1) + levelExcess G v k := by
      have e1 : k + 1 - 1 = k := by omega
      have e2 : k - 1 + 1 = k := by omega
      simp only [ballExcess, e1, e2, Finset.sum_range_succ]
    have hI : ∑ j ∈ Ico 2 (k + 1), extraParents G v j =
        ∑ j ∈ Ico 2 k, extraParents G v j + extraParents G v k := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        have z1 : ∑ j ∈ Ico 2 (1 + 1), extraParents G v j = 0 :=
          Finset.sum_eq_zero fun j hj => by simp only [Finset.mem_Ico] at hj; omega
        have z2 : ∑ j ∈ Ico 2 1, extraParents G v j = 0 :=
          Finset.sum_eq_zero fun j hj => by simp only [Finset.mem_Ico] at hj; omega
        linarith [extraParents_one hc v]
      · exact Finset.sum_Ico_succ_top hk2 _
    rw [hY, hI]
    linarith

theorem Icc_eq_Ico (m : ℕ) : Icc 2 m = Ico 2 (m + 1) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  exact ⟨fun h => by omega, fun h => by omega⟩

/-- Exact total extra-parents identity (`part_b`): `∑_{j=2}^n M_j(v) = edgeExcess G + 1`. -/
theorem part_b {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (v : CubeVertex n) :
    (∑ j ∈ Icc 2 n, extraParents G v j) = edgeExcess G + 1 := by
  have hc := connected_of_ediam hD
  have hT := Finset.sum_range_sub (fun k => ((levelSet G v k).card : ℤ)) (n + 1)
  have hsum : ∑ i ∈ range (n + 1),
      (((levelSet G v (i + 1)).card : ℤ) - (levelSet G v i).card) =
        ∑ i ∈ range (n + 1), (levelExcess G v i - extraParents G v i -
          extraParents G v (i + 1)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have := level_step hG hc v i
    linarith
  have hsplit : ∑ i ∈ range (n + 1), (levelExcess G v i -
      extraParents G v i - extraParents G v (i + 1)) =
        ∑ i ∈ range (n + 1), levelExcess G v i -
          ∑ i ∈ range (n + 1), extraParents G v i -
            ∑ i ∈ range (n + 1), extraParents G v (i + 1) := by
    simp only [Finset.sum_sub_distrib]
  have hX : ∑ i ∈ range (n + 1), levelExcess G v i = 2 * edgeExcess G := by
    rw [sum_levelExcess hD v, sum_excess]
  have hs0 : ((levelSet G v 0).card : ℤ) = 1 := by
    rw [card_levelSet_zero hc v, Nat.cast_one]
  have hsn : ((levelSet G v (n + 1)).card : ℤ) = 0 := by
    simp [levelSet_eq_empty hD v (Nat.lt_succ_self n)]
  have hMn : extraParents G v (n + 1) = 0 := by
    simp [extraParents, levelSet_eq_empty hD v (Nat.lt_succ_self n)]
  have e1 := Finset.sum_range_succ (fun i => extraParents G v (i + 1)) n
  have e2 := Finset.sum_range_succ' (fun i => extraParents G v i) n
  have e3 := Finset.sum_range_add_sum_Ico (fun j => extraParents G v j)
    (show 2 ≤ n + 1 by omega)
  have e4 : ∑ j ∈ range 2, extraParents G v j = extraParents G v 0 + extraParents G v 1 := by
    simp [Finset.sum_range_succ]
  rw [← Icc_eq_Ico] at e3
  have m0 := extraParents_zero hc v
  have m1 := extraParents_one hc v
  linarith

private def mu {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n) (j : ℕ) : ℤ :=
  if 2 ≤ j then extraParents G v j else 0

private theorem sum_range_if_two (g : ℕ → ℤ) (k : ℕ) :
    ∑ j ∈ range k, (if 2 ≤ j then g j else 0) = ∑ j ∈ Ico 2 k, g j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  exact ⟨fun h => by omega, fun h => by omega⟩

private theorem sum_mu {n : ℕ} {G : SimpleGraph (CubeVertex n)} (v : CubeVertex n) (k : ℕ) :
    ∑ j ∈ range k, mu G v j = ∑ j ∈ Ico 2 k, extraParents G v j :=
  sum_range_if_two (fun j => extraParents G v j) k

private def PairClaim {n : ℕ} (G : SimpleGraph (CubeVertex n)) (v : CubeVertex n) (m : ℕ) : Prop :=
  ∑ k ∈ range (m + 1), (if k % 2 = m % 2 then ((levelSet G v k).card : ℤ) else 0) =
    (m : ℤ) + 1 +
      ∑ k ∈ range m, (if k % 2 = m % 2 then 0 else ballExcess G v k) -
        ∑ j ∈ range (m + 1), ((m : ℤ) + 1 - j) * mu G v j

private theorem pairClaim_zero {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (v : CubeVertex n) : PairClaim G v 0 := by
  unfold PairClaim
  simp [mu, card_levelSet_zero hc v]

private theorem pairClaim_one {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (v : CubeVertex n) : PairClaim G v 1 := by
  have ha := part_a hG hc v 1 le_rfl
  have hI : ∑ j ∈ Ico 2 1, extraParents G v j = 0 :=
    Finset.sum_eq_zero fun j hj => by simp only [Finset.mem_Ico] at hj; omega
  simp only [hI, extraParents_one hc v, Nat.sub_self, mul_zero, sub_zero] at ha
  unfold PairClaim
  simp [Finset.sum_range_succ, mu]
  linarith

private theorem pairClaim_add_two {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (v : CubeVertex n) (m : ℕ) (h : PairClaim G v m) :
    PairClaim G v (m + 2) := by
  unfold PairClaim at h ⊢
  have hmod : (m + 2) % 2 = m % 2 := by omega
  simp only [hmod]
  have p1 : ∑ k ∈ range (m + 2 + 1),
      (if k % 2 = m % 2 then ((levelSet G v k).card : ℤ) else 0) =
        ∑ k ∈ range (m + 2), (if k % 2 = m % 2 then ((levelSet G v k).card : ℤ) else 0) +
          (if (m + 2) % 2 = m % 2 then ((levelSet G v (m + 2)).card : ℤ) else 0) :=
    Finset.sum_range_succ _ (m + 2)
  have p2 : ∑ k ∈ range (m + 2),
      (if k % 2 = m % 2 then ((levelSet G v k).card : ℤ) else 0) =
        ∑ k ∈ range (m + 1), (if k % 2 = m % 2 then ((levelSet G v k).card : ℤ) else 0) +
          (if (m + 1) % 2 = m % 2 then ((levelSet G v (m + 1)).card : ℤ) else 0) :=
    Finset.sum_range_succ _ (m + 1)
  have p3 : (if (m + 1) % 2 = m % 2 then ((levelSet G v (m + 1)).card : ℤ) else 0) = 0 := by
    have : ¬((m + 1) % 2 = m % 2) := by omega
    simp [this]
  have p4 : (if (m + 2) % 2 = m % 2 then ((levelSet G v (m + 2)).card : ℤ) else 0) =
      (levelSet G v (m + 2)).card := by simp [hmod]
  have q1 : ∑ k ∈ range (m + 2), (if k % 2 = m % 2 then 0 else ballExcess G v k) =
      ∑ k ∈ range (m + 1), (if k % 2 = m % 2 then 0 else ballExcess G v k) +
        (if (m + 1) % 2 = m % 2 then 0 else ballExcess G v (m + 1)) :=
    Finset.sum_range_succ _ (m + 1)
  have q2 : ∑ k ∈ range (m + 1), (if k % 2 = m % 2 then 0 else ballExcess G v k) =
      ∑ k ∈ range m, (if k % 2 = m % 2 then 0 else ballExcess G v k) +
        (if m % 2 = m % 2 then 0 else ballExcess G v m) :=
    Finset.sum_range_succ _ m
  have q3 : (if (m + 1) % 2 = m % 2 then 0 else ballExcess G v (m + 1)) =
      ballExcess G v (m + 1) := by
    have : ¬((m + 1) % 2 = m % 2) := by omega
    simp [this]
  have q4 : (if m % 2 = m % 2 then 0 else ballExcess G v m) = 0 := by simp
  have w1 : ∑ j ∈ range (m + 2 + 1), (((m + 2 : ℕ) : ℤ) + 1 - j) * mu G v j =
      ∑ j ∈ range (m + 2), (((m + 2 : ℕ) : ℤ) + 1 - j) * mu G v j +
        (((m + 2 : ℕ) : ℤ) + 1 - ((m + 2 : ℕ) : ℤ)) * mu G v (m + 2) :=
    Finset.sum_range_succ _ (m + 2)
  have w2 : ∑ j ∈ range (m + 2), (((m + 2 : ℕ) : ℤ) + 1 - j) * mu G v j =
      ∑ j ∈ range (m + 1), (((m + 2 : ℕ) : ℤ) + 1 - j) * mu G v j +
        (((m + 2 : ℕ) : ℤ) + 1 - ((m + 1 : ℕ) : ℤ)) * mu G v (m + 1) :=
    Finset.sum_range_succ _ (m + 1)
  have w3 : ∑ j ∈ range (m + 1), (((m + 2 : ℕ) : ℤ) + 1 - j) * mu G v j =
      ∑ j ∈ range (m + 1), ((m : ℤ) + 1 - j) * mu G v j +
        2 * ∑ j ∈ range (m + 1), mu G v j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have w4 : (((m + 2 : ℕ) : ℤ) + 1 - ((m + 2 : ℕ) : ℤ)) * mu G v (m + 2) = mu G v (m + 2) := by
    ring
  have w5 : (((m + 2 : ℕ) : ℤ) + 1 - ((m + 1 : ℕ) : ℤ)) * mu G v (m + 1) =
      2 * mu G v (m + 1) := by
    push_cast
    ring
  have ha := part_a hG hc v (m + 2) (by omega)
  have e1 : m + 2 - 1 = m + 1 := by omega
  rw [e1, ← sum_mu] at ha
  have hmu2 : mu G v (m + 2) = extraParents G v (m + 2) := by
    unfold mu
    have hge : 2 ≤ m + 2 := by omega
    simp only [hge, ↓reduceIte]
  have s1 : ∑ j ∈ range (m + 2), mu G v j = ∑ j ∈ range (m + 1), mu G v j + mu G v (m + 1) :=
    Finset.sum_range_succ _ (m + 1)
  have hcast : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by omega
  rw [hcast]
  rw [hcast] at w1 w2 w3 w4 w5
  linarith

private theorem pairClaim_all {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (v : CubeVertex n) (m : ℕ) :
    PairClaim G v m ∧ PairClaim G v (m + 1) := by
  induction m with
  | zero => exact ⟨pairClaim_zero hc v, pairClaim_one hG hc v⟩
  | succ m ih => exact ⟨ih.2, pairClaim_add_two hG hc v m ih.1⟩

theorem sum_K {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (v : CubeVertex n) :
    ∑ k ∈ range n, (if k % 2 = (n - 1) % 2 then ((levelSet G v k).card : ℤ) else 0) =
      2 ^ (n - 1) := by
  have hc := connected_of_ediam hD
  have h1 : ∀ k, ∑ u ∈ levelSet G v k,
      (if G.dist v u % 2 = (n - 1) % 2 then (1 : ℤ) else 0) =
        if k % 2 = (n - 1) % 2 then ((levelSet G v k).card : ℤ) else 0 := by
    intro k
    have e : ∑ u ∈ levelSet G v k, (if G.dist v u % 2 = (n - 1) % 2 then (1 : ℤ) else 0) =
        ∑ _u ∈ levelSet G v k, (if k % 2 = (n - 1) % 2 then (1 : ℤ) else 0) :=
      Finset.sum_congr rfl fun u hu => by rw [mem_levelSet.1 hu]
    rw [e]
    by_cases hk : k % 2 = (n - 1) % 2 <;> simp [hk]
  have h2 : ∑ k ∈ range (n + 1), (if k % 2 = (n - 1) % 2 then ((levelSet G v k).card : ℤ) else 0) =
      ∑ u, (if G.dist v u % 2 = (n - 1) % 2 then (1 : ℤ) else 0) := by
    rw [← Finset.sum_congr rfl fun k _ => h1 k, levels_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hlt : G.dist v u < n + 1 := Nat.lt_succ_of_le (dist_le_of_ediam hD v u)
    simp [hlt]
  have h3 : ∑ u, (if G.dist v u % 2 = (n - 1) % 2 then (1 : ℤ) else 0) = 2 ^ (n - 1) := by
    have e : ∀ u, (if G.dist v u % 2 = (n - 1) % 2 then (1 : ℤ) else 0) =
        if hammingDist v u % 2 = (n - 1) % 2 then 1 else 0 := by
      intro u
      rw [(dist_hamming hG hc v u).2]
    rw [Finset.sum_congr rfl fun u _ => e u, ← Finset.natCast_card_filter,
      card_hamming_parity (by omega) v ((n - 1) % 2) (Nat.mod_lt _ (by norm_num))]
    simp
  have h4 := Finset.sum_range_succ (fun k => if k % 2 = (n - 1) % 2 then
    ((levelSet G v k).card : ℤ) else 0) n
  have h5 : (if n % 2 = (n - 1) % 2 then ((levelSet G v n).card : ℤ) else 0) = 0 := by
    have : ¬(n % 2 = (n - 1) % 2) := by omega
    simp [this]
  linarith

/-- Exact local excess identity (`part_c`): `L(v) = 2^(n-1) - n + M(v)`. -/
theorem part_c {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (v : CubeVertex n) :
    lSum G v = (2 : ℤ) ^ (n - 1) - (n : ℤ) + weightedExtra G v := by
  have hc := connected_of_ediam hD
  have hP := (pairClaim_all hG hc v (n - 1)).1
  unfold PairClaim at hP
  have e1 : n - 1 + 1 = n := by omega
  rw [e1] at hP
  have hK := sum_K hn hG hD v
  have hL : ∑ k ∈ range (n - 1), (if k % 2 = (n - 1) % 2 then 0 else ballExcess G v k) =
      lSum G v := by
    unfold lSum rSet
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> first | rfl | omega
  have hW : ∑ j ∈ range n, (((n - 1 : ℕ) : ℤ) + 1 - j) * mu G v j = weightedExtra G v := by
    have hcast : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
    rw [hcast]
    unfold weightedExtra
    rw [← sum_range_if_two (fun j => ((n : ℤ) - j) * extraParents G v j) n]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold mu
    split_ifs <;> simp
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hcast] at hP hW
  linarith

theorem weightedExtra_nonneg {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (v : CubeVertex n) : 0 ≤ weightedExtra G v := by
  unfold weightedExtra
  refine Finset.sum_nonneg fun j hj => ?_
  simp only [Finset.mem_Ico] at hj
  apply mul_nonneg
  · have : (j : ℤ) < n := by exact_mod_cast hj.2
    linarith
  · exact extraParents_nonneg hc v (by omega)

theorem card_rSet_ge {n d : ℕ} (hd : d ≤ n) :
    ((rSet n).filter fun m => d < m + 1).card = (n - d) / 2 := by
  rw [← Finset.card_range ((n - d) / 2)]
  refine Finset.card_nbij' (fun m => (n - 2 - m) / 2) (fun i => n - 2 - 2 * i) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, rSet, Finset.mem_range] at hm ⊢
    omega
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, rSet, Finset.mem_range] at hi ⊢
    omega
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, rSet, Finset.mem_range] at hm
    dsimp only
    omega
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    dsimp only
    omega

theorem lSum_eq {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hD : G.ediam = (n : ℕ∞)) (v : CubeVertex n) :
    lSum G v = ∑ u, (((n - G.dist v u) / 2 : ℕ) : ℤ) * excess G u := by
  have hY : ∀ m, ballExcess G v m = ∑ u, if G.dist v u < m + 1 then excess G u else 0 := by
    intro m
    unfold ballExcess
    simp only [levelExcess]
    exact levels_sum v (excess G) (m + 1)
  unfold lSum
  simp only [hY]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← card_rSet_ge (dist_le_of_ediam hD v u), Finset.natCast_card_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

theorem pow_eq_two_mul {n : ℕ} (hn : 1 ≤ n) : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
  rw [← pow_succ']
  congr 1
  omega

theorem sum_half {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (u : CubeVertex n) :
    ∑ v, (2 : ℤ) * (((n - G.dist v u) / 2 : ℕ) : ℤ) =
      ((n : ℤ) - 1) * 2 ^ (n - 1) - distGap G u := by
  have hc := connected_of_ediam hD
  have hpt : ∀ v, (2 : ℤ) * (((n - G.dist v u) / 2 : ℕ) : ℤ) =
      (n : ℤ) - G.dist v u - (if hammingDist u v % 2 = (n + 1) % 2 then 1 else 0) := by
    intro v
    have hd := dist_le_of_ediam hD v u
    have hp := (dist_hamming hG hc v u).2
    rw [hammingDist_comm u v]
    split_ifs with h <;> omega
  rw [Finset.sum_congr rfl fun v _ => hpt v, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hpar : ∑ v, (if hammingDist u v % 2 = (n + 1) % 2 then (1 : ℤ) else 0) = 2 ^ (n - 1) := by
    rw [← Finset.natCast_card_filter, card_hamming_parity (by omega) u
      ((n + 1) % 2) (Nat.mod_lt _ (by norm_num))]
    simp
  have hconst : ∑ _v : CubeVertex n, (n : ℤ) = (n : ℤ) * 2 ^ n := by
    rw [Finset.sum_const, Finset.card_univ, card_vertices, nsmul_eq_mul]
    push_cast
    ring
  have hpow := pow_eq_two_mul (show 1 ≤ n by omega)
  rw [hpar, hconst]
  unfold distGap distSum
  linear_combination (n : ℤ) * hpow

theorem sum_hammingDist_int {n : ℕ} (hn : 1 ≤ n) (w : CubeVertex n) :
    ∑ v, (hammingDist v w : ℤ) = (n : ℤ) * 2 ^ (n - 1) := by
  have h1 : (2 : ℤ) * ∑ v, (hammingDist v w : ℤ) = (n : ℤ) * 2 ^ n := by
    exact_mod_cast sum_hammingDist w
  rw [pow_eq_two_mul hn] at h1
  linarith

theorem distGap_nonneg {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 1 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (w : CubeVertex n) :
    0 ≤ distGap G w := by
  have hc := connected_of_ediam hD
  have hsumh := sum_hammingDist_int hn w
  unfold distGap distSum
  have h : ∑ v, (hammingDist v w : ℤ) ≤ ∑ v, (G.dist v w : ℤ) :=
    Finset.sum_le_sum fun v _ => by exact_mod_cast (dist_hamming hG hc v w).1
  linarith

/-- Global exact excess identity (`part_d`):
`∑_w x_w δ(w) + 2 ∑_v M(v) = 2^n ((n - 1) t - (2^n - 2n))`. -/
theorem part_d {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) :
    (∑ w : CubeVertex n, excess G w * distGap G w) +
        2 * (∑ v : CubeVertex n, weightedExtra G v) =
      (2 : ℤ) ^ n * (((n : ℤ) - 1) * edgeExcess G - ((2 : ℤ) ^ n - 2 * (n : ℤ))) := by
  have hcs : ∑ v, lSum G v = (2 : ℤ) ^ n * ((2 : ℤ) ^ (n - 1) - n) + ∑ v, weightedExtra G v := by
    rw [Finset.sum_congr rfl fun v _ => part_c hn hG hD v, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, card_vertices, nsmul_eq_mul]
    norm_num
  have h2L : 2 * ∑ v, lSum G v =
      ∑ u, excess G u * (((n : ℤ) - 1) * 2 ^ (n - 1) - distGap G u) := by
    simp only [lSum_eq hD, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← sum_half hn hG hD u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have hsplit : ∑ u, excess G u * (((n : ℤ) - 1) * 2 ^ (n - 1) - distGap G u) =
      ((n : ℤ) - 1) * 2 ^ (n - 1) * ∑ u, excess G u - ∑ u, excess G u * distGap G u := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have hX : ∑ u : CubeVertex n, excess G u = 2 * edgeExcess G := sum_excess
  have hpow := pow_eq_two_mul (show 1 ≤ n by omega)
  linear_combination (-2 : ℤ) * hcs + h2L + hsplit +
    ((n : ℤ) - 1) * 2 ^ (n - 1) * hX +
      ((2 : ℤ) ^ n - ((n : ℤ) - 1) * edgeExcess G) * hpow

end

end Hypercube
