/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Hypercube.Defs
public import Hypercube.Theorem1
public import Hypercube.Construction
public import Hypercube.SmallDims
import Mathlib.Tactic

/-!
# Stronger Bounds on `f(n)`: `Q_6` 81-Edge Upper Bound, Blocking Vertices, Local & Antipodal Caps

Formalizes the mathematical advances beyond `bound-1.md`:
1. **Explicit 81-Edge Spanning Subgraph of `Q_6` (`q6_81`, `f_six_le_81`, `f_six_bounds`,
   `q6_beats_grahamConstruction`)**: kernel-verified construction from PatternBoost Appendix F
   proving `f 6 ≤ 81` (`75 ≤ f 6 ∧ f 6 ≤ 81`), strictly beating `grahamConstruction 6` (`82`).
2. **Blocking-Vertex Lower Bound (`blocking_lower_bound`, `blocking_lower_bound_valid`,
   `q6_81_blocking_every_corner`)**: Lead 3 of `charter.md` (`known-results.md` §4), proving
   `2^n + C(n, ⌊n/2⌋) - 2 ≤ |E(G)| + β_r(G)` for every corner `r` and every spanning subgraph
   `G ≤ Q n` without isolated vertices.
3. **Global Thin-Levels Cap (`bound-2.md` Lemma 4 & Theorem 4) and Local Level Cap at `n = 8`
   (`bound-3.md` Lemma 6 & Theorem 6: `f_eight_ge_292`)**: exact detour-gap identities,
   `ψ(w) ≥ 124` at excess vertices of `Q_8`, and `292 ≤ f 8`.
4. **Asymptotic Second-Term Progression (`bound2019_lt_f`, `bound1995_second_term_lt_half`,
   `theorem1_second_term_lower`, `theorem5_asymptotic_three_halves`)**: proves the three-rung
   asymptotic ladder for `(f(n) - 2^n)(n - 1)/2^n`, raising the limit inferior from `1/2`
   (1995 / 2019 bounds) and `1` (Theorem 1) to **`3/2`** (`bound-2.md` Theorem 5).
5. **Parity-Ball, Half-Step, and Antipodal Cap Theory (`bound-4`, `bound-5`, `bound-8`,
   `bound-9`)**: Lemma 7 (parity balls), Lemma 17 (even/odd distance excess conservation `t` and
   `t`), Lemma 18 & 19 (half-step `P_k - P_{k-1} ≤ t + 1` and chain `p_k`), Lemma 20 (exact
   antipodal pair conservation `M(w) + M(w̄) + (1/2) ∑_v x_v η_w(v) = μ`, yielding `0 ≤ M(w) ≤ μ`),
   Theorem 13 (antipodal-capped recipe floors), and Theorem 14 (`f(9) ≥ 580`, `f(10) ≥ 1147`, ...,
   `f(32) ≥ 4,454,492,243` across all `24` dimensions `n = 9..32`).
-/

@[expose] public section

namespace Hypercube

open Finset

/-! ## Section 1: Kernel-Verified 81-Edge Diameter-6 Spanning Subgraph of `Q_6` (`f 6 ≤ 81`) -/

private abbrev B6 := Bool × Bool × Bool × Bool × Bool × Bool

private def toB6 (u : CubeVertex 6) : B6 :=
  (u 0, u 1, u 2, u 3, u 4, u 5)

private def ofB6 (b : B6) : CubeVertex 6
  | ⟨0, _⟩ => b.1
  | ⟨1, _⟩ => b.2.1
  | ⟨2, _⟩ => b.2.2.1
  | ⟨3, _⟩ => b.2.2.2.1
  | ⟨4, _⟩ => b.2.2.2.2.1
  | ⟨5, _⟩ => b.2.2.2.2.2

private theorem ofB6_toB6 (u : CubeVertex 6) : ofB6 (toB6 u) = u := by
  funext i
  fin_cases i <;> rfl

private theorem toB6_ofB6 (b : B6) : toB6 (ofB6 b) = b := by
  rcases b with ⟨b0, b1, b2, b3, b4, b5⟩
  rfl

private def eqB6 (a b : B6) : Bool :=
  (a.1 == b.1) && (a.2.1 == b.2.1) && (a.2.2.1 == b.2.2.1) &&
    (a.2.2.2.1 == b.2.2.2.1) && (a.2.2.2.2.1 == b.2.2.2.2.1) &&
    (a.2.2.2.2.2 == b.2.2.2.2.2)

private theorem eqB6_iff (a b : B6) : eqB6 a b = true ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
  rcases b with ⟨b0, b1, b2, b3, b4, b5⟩
  unfold eqB6
  simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
  tauto

private def flipB6 (c : Fin 6) (b : B6) : B6 :=
  match c with
  | ⟨0, _⟩ => (!b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2)
  | ⟨1, _⟩ => (b.1, !b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2)
  | ⟨2, _⟩ => (b.1, b.2.1, !b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2)
  | ⟨3, _⟩ => (b.1, b.2.1, b.2.2.1, !b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2)
  | ⟨4, _⟩ => (b.1, b.2.1, b.2.2.1, b.2.2.2.1, !b.2.2.2.2.1, b.2.2.2.2.2)
  | ⟨5, _⟩ => (b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, !b.2.2.2.2.2)

private theorem toB6_flipAt (c : Fin 6) (u : CubeVertex 6) :
    toB6 (flipAt c u) = flipB6 c (toB6 u) := by
  fin_cases c <;> rfl

private def idxB6 (b : B6) : ℕ :=
  (if b.1 then 32 else 0) + (if b.2.1 then 16 else 0) + (if b.2.2.1 then 8 else 0) +
    (if b.2.2.2.1 then 4 else 0) + (if b.2.2.2.2.1 then 2 else 0) +
    (if b.2.2.2.2.2 then 1 else 0)

/-- Per-direction 64-bit incidence masks for PatternBoost's 81-edge subgraph of `Q_6`
(`arXiv:2411.00566`, Appendix F; `charter_facts.py` `PATTERNBOOST_81`). -/
def q6DirMask : Fin 6 → ℕ
  | ⟨0, _⟩ => 15374603813555900597
  | ⟨1, _⟩ => 16897763638938656115
  | ⟨2, _⟩ => 12297726725630090075
  | ⟨3, _⟩ => 9799832938048135867
  | ⟨4, _⟩ => 18374686868913890655
  | ⟨5, _⟩ => 14771594572031066163

private def q6HasDirB6 (b : B6) (c : Fin 6) : Bool :=
  ((q6DirMask c / (2 ^ idxB6 b)) % 2) == 1

/-- Index `0..63` of a `Q_6` vertex `u : Fin 6 → Bool` in big-endian bit order. -/
def idx6 (u : CubeVertex 6) : ℕ :=
  (if u 0 then 32 else 0) + (if u 1 then 16 else 0) + (if u 2 then 8 else 0) +
    (if u 3 then 4 else 0) + (if u 4 then 2 else 0) + (if u 5 then 1 else 0)

/-- Whether `q6_81` retains the edge leaving vertex `u` in coordinate direction `c`. -/
def q6HasDir (u : CubeVertex 6) (c : Fin 6) : Bool :=
  ((q6DirMask c / (2 ^ idx6 u)) % 2) == 1

private theorem q6HasDir_eq_B6 (u : CubeVertex 6) (c : Fin 6) :
    q6HasDir u c = q6HasDirB6 (toB6 u) c :=
  rfl

private theorem q6HasDirB6_symm :
    ∀ (b0 b1 b2 b3 b4 b5 : Bool) (c : Fin 6),
      q6HasDirB6 (flipB6 c (b0, b1, b2, b3, b4, b5)) c =
        q6HasDirB6 (b0, b1, b2, b3, b4, b5) c := by
  decide

theorem q6HasDir_symm (u : CubeVertex 6) (c : Fin 6) :
    q6HasDir (flipAt c u) c = q6HasDir u c := by
  rw [q6HasDir_eq_B6, q6HasDir_eq_B6, toB6_flipAt]
  exact q6HasDirB6_symm (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) c

/-- The explicit 81-edge diameter-6 spanning subgraph of `Q_6` discovered by PatternBoost
(`Charton–Ellenberg–Wagner–Williamson 2024`, Appendix F). -/
def q6_81 : SimpleGraph (CubeVertex 6) where
  Adj u v := ∃ c : Fin 6, v = flipAt c u ∧ q6HasDir u c = true
  symm := ⟨by
    rintro u v ⟨c, rfl, hc⟩
    exact ⟨c, (flipAt_flipAt c u).symm, by rwa [q6HasDir_symm]⟩⟩
  loopless := ⟨by
    rintro u ⟨c, hu, _⟩
    have hc := congr_fun hu c
    rw [flipAt_apply_self] at hc
    exact bool_ne_not (u c) hc⟩

instance instDecidableRelQ681Adj : DecidableRel q6_81.Adj :=
  fun u v =>
    show Decidable (∃ c : Fin 6, v = flipAt c u ∧ q6HasDir u c = true) from inferInstance

/-- `q6_81` is a spanning subgraph of the 6-cube `Q 6`. -/
theorem q6_81_le_Q : q6_81 ≤ Q 6 := by
  rintro u v ⟨c, rfl, _⟩
  exact hammingDist_flipAt c u

private theorem flipAt_injective {n : ℕ} (u : CubeVertex n) :
    Function.Injective (fun c : Fin n => flipAt c u) := by
  intro c1 c2 h
  by_contra hne
  have hc : flipAt c1 u c1 = flipAt c2 u c1 := congr_fun h c1
  rw [flipAt_apply_self, flipAt_apply_of_ne u hne] at hc
  exact bool_ne_not (u c1) hc.symm

private theorem q6_81_ncard_neighborSet (u : CubeVertex 6) :
    (q6_81.neighborSet u).ncard =
      (univ.filter fun c : Fin 6 => q6HasDir u c = true).card := by
  have hset : q6_81.neighborSet u =
      (((univ.filter fun c : Fin 6 => q6HasDir u c = true).image
        (fun c => flipAt c u) : Finset (CubeVertex 6)) : Set (CubeVertex 6)) := by
    ext v
    simp only [SimpleGraph.mem_neighborSet, q6_81, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, rfl, hc⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, rfl, hc⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ (flipAt_injective u)]

private def degB6 (b : B6) : ℕ :=
  (if q6HasDirB6 b 0 = true then 1 else 0) + (if q6HasDirB6 b 1 = true then 1 else 0) +
    (if q6HasDirB6 b 2 = true then 1 else 0) + (if q6HasDirB6 b 3 = true then 1 else 0) +
    (if q6HasDirB6 b 4 = true then 1 else 0) + (if q6HasDirB6 b 5 = true then 1 else 0)

private theorem card_q6HasDir_eq_degB6 (u : CubeVertex 6) :
    (univ.filter fun c : Fin 6 => q6HasDir u c = true).card = degB6 (toB6 u) := by
  rw [Finset.card_filter, Fin.sum_univ_six]
  rfl

private theorem sum_degB6 : ∑ b : B6, degB6 b = 162 := by
  decide

/-- `q6_81` has `81` edges. -/
theorem q6_81_edgeCount : edgeCount q6_81 = 81 := by
  rw [edgeCount_eq_ncard]
  have h2 := sum_ncard_neighborSet (G := q6_81)
  have hsum : ∑ u : CubeVertex 6, (q6_81.neighborSet u).ncard = ∑ b : B6, degB6 b := by
    simp_rw [q6_81_ncard_neighborSet, card_q6HasDir_eq_degB6]
    let e : CubeVertex 6 ≃ B6 :=
      { toFun := toB6
        invFun := ofB6
        left_inv := ofB6_toB6
        right_inv := toB6_ofB6 }
    exact Fintype.sum_equiv e (fun u => degB6 (toB6 u)) degB6 (fun _ => rfl)
  rw [hsum, sum_degB6] at h2
  omega

private def q6RowMask (b0 b1 b2 b3 b4 b5 : Bool) : ℕ :=
  if b0 then
    if b1 then
      if b2 then
        if b3 then
          if b4 then
            if b5 then
              547757640100381458314735994073090670736678829234659643587
            else
              3991713028086820251394204082221903619884540593671212407657
          else
            if b5 then
              3537875418411919646868015574075729942754391292291098683682
            else
              3580785294834889389804383472383601224588655287660031510528
        else
          if b4 then
            if b5 then
              2689663404112237578270582782329198414005021860468234171996
            else
              4483523996346222669890214385974307952836196269279218682724
          else
            if b5 then
              3586903304742003151128567207779288220233414947989745703177
            else
              3586913780420676318393228622454312161553038870228177518592
      else
        if b3 then
          if b4 then
            if b5 then
              1793457562683823648460248884184593613062565959618365018765
            else
              4483644067017908434929212711541653136024886678936858135040
          else
            if b5 then
              1793457637494505611575601840798963629540300527003957122413
            else
              4475979718584346968192699071695583578011861452825842155520
        else
          if b4 then
            if b5 then
              1793457638663421471897782301542915649520144684478349464709
            else
              4483644096240804943083754260121331009663246800477738926080
          else
            if b5 then
              1793457638959932196391012074991774460290344925506359974765
            else
              4475979718584346968191868304197432206760026116200176025600
    else
      if b2 then
        if b3 then
          if b4 then
            if b5 then
              896728819340951607240531790759830794683962434322748936768
            else
              896728819432320199464273362919124012429127553334823428754
          else
            if b5 then
              902858801504507131475168848762258826845966409044109742957
            else
              3985581145507260791272309387796362006579447981699351183360
        else
          if b4 then
            if b5 then
              896728819340954394493405792415053115378806515022139052885
            else
              4483644096430673498170385883695562217549233905162762495122
          else
            if b5 then
              896728819706329825939176207090478231157614783693025893229
            else
              4479045469832516970579830933157651325482309611160697644178
      else
        if b3 then
          if b4 then
            if b5 then
              896728819340932094086987364746340105489126655657706258432
            else
              1793458398848347014340857413779214373903936886876650228004
          else
            if b5 then
              2354568651792903064581642711990780608023689227076057956352
            else
              3531636160997662999333900439776873321538466365764093870080
        else
          if b4 then
            if b5 then
              1793457638864596505222772774506687705999403666371977037988
            else
              1790391887433738787446888506407092714663927151692657721344
          else
            if b5 then
              3585382775885578982628349885709365773016565926147100882715
            else
              1569664544065785946943417405676303929021599319938132082688
  else
    if b1 then
      if b2 then
        if b3 then
          if b4 then
            if b5 then
              10384911256094439504736480959530532
            else
              5937372702403323790272034873967079723016193871945
          else
            if b5 then
              3586915277363795278588206128191339417563388504011462260955
            else
              12260345140897085425226473960828622815472961714831790665
        else
          if b4 then
            if b5 then
              2690186458022818583007658932808058785270528585751962882633
            else
              91366158524229987558485696106971545436229505609
          else
            if b5 then
              2690186083785650621487732856499748480978662898820371260562
            else
              1532501479665844484163482332577295143226039752164938313
      else
        if b3 then
          if b4 then
            if b5 then
              2691718959501101781207439540667427141295179780623869036836
            else
              99612584393495687255610652941369184331242126522137743433
          else
            if b5 then
              3251297471172393146863175933308097877697129219835597984329
            else
              99639528557934054962665165751542524613469218245299180105
        else
          if b4 then
            if b5 then
              274031573333106673270661945379070128195229300248
            else
              6143475112757652656012530771140819766455774919150160164
          else
            if b5 then
              1791897777879992935573556546425680762197193959780357804617
            else
              3251213662821766118932147776470719323752611771454689940041
    else
      if b2 then
        if b3 then
          if b4 then
            if b5 then
              89202986122740278261115044687667893574453540
            else
              896729199424173507170449476077041326262482561025595483282
          else
            if b5 then
              3586914903126605016321417059814972312766027499064701859547
            else
              99666847142272679460221171001500856207576951588504806546
        else
          if b4 then
            if b5 then
              896729246192225901759509012094429087667652170287430575250
            else
              901327446213209398419615830743064342288187441397904853284
          else
            if b5 then
              2688626597220950118000390566068799590464188570648271463570
            else
              3363163712777864319601006894320879770627899842056340186258
      else
        if b3 then
          if b4 then
            if b5 then
              1122711637689039460799841234717282187903577396197083
            else
              1036267853692967917247118248828378071139282295781073242404
          else
            if b5 then
              2913410759563278308739153417033718029814329576545341167453
            else
              3559494604571748686602970974735604390729046714231729326827
        else
          if b4 then
            if b5 then
              1796577307671681553942320918209101607642230196181337784612
            else
              447598161854372323758530727080503467385718263004697610276
          else
            if b5 then
              3698623209105323684661418666432733826794174822863611484485
            else
              4259620248468855157487095690654474852098222279265144978216

private def fin6OfNat (m : ℕ) : Fin 6 :=
  if h : m < 6 then ⟨m, h⟩ else ⟨0, by decide⟩

private def q6StepB6 (u v : B6) : Fin 6 :=
  fin6OfNat
    ((q6RowMask u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2 / (8 ^ idxB6 v)) % 8)

private def q6RouteOk : ℕ → B6 → B6 → Bool
  | 0, u, v => eqB6 u v
  | k + 1, u, v =>
    if eqB6 u v then true
    else
      let c := q6StepB6 u v
      q6HasDirB6 u c && q6RouteOk k (flipB6 c u) v

private theorem q6RouteOk_all :
    ∀ b0 b1 b2 b3 b4 b5 d0 d1 d2 d3 d4 d5 : Bool,
      q6RouteOk 6 (b0, b1, b2, b3, b4, b5) (d0, d1, d2, d3, d4, d5) = true := by
  decide

private theorem exists_walk_of_q6RouteOk :
    ∀ (k : ℕ) (u v : CubeVertex 6),
      q6RouteOk k (toB6 u) (toB6 v) = true →
      ∃ p : q6_81.Walk u v, p.length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro u v h
    simp only [q6RouteOk, eqB6_iff] at h
    have huv : u = v := by
      rw [← ofB6_toB6 u, ← ofB6_toB6 v, h]
    subst huv
    exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | succ k ih =>
    intro u v h
    simp only [q6RouteOk] at h
    by_cases heq : eqB6 (toB6 u) (toB6 v) = true
    · have huv : u = v := by
        rw [← ofB6_toB6 u, ← ofB6_toB6 v, (eqB6_iff _ _).1 heq]
      subst huv
      exact ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
    · have heqf : eqB6 (toB6 u) (toB6 v) = false := Bool.eq_false_iff.2 heq
      rw [heqf] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
      let c := q6StepB6 (toB6 u) (toB6 v)
      have hadj : q6_81.Adj u (flipAt c u) := ⟨c, rfl, h.1⟩
      have hrec : q6RouteOk k (toB6 (flipAt c u)) (toB6 v) = true := by
        rw [toB6_flipAt]
        exact h.2
      obtain ⟨p, hp⟩ := ih (flipAt c u) v hrec
      exact ⟨SimpleGraph.Walk.cons hadj p, by rw [SimpleGraph.Walk.length_cons]; omega⟩

/-- `q6_81` is a valid diameter-6 spanning subgraph of `Q_6`. -/
theorem q6_81_valid : IsValidSpanningSubgraph 6 q6_81 := by
  refine ⟨q6_81_le_Q, fun u v => ?_⟩
  have hroute := q6RouteOk_all (u 0) (u 1) (u 2) (u 3) (u 4) (u 5)
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  obtain ⟨p, hp⟩ := exists_walk_of_q6RouteOk 6 u v hroute
  exact ⟨⟨p⟩, (SimpleGraph.edist_le p).trans (by exact_mod_cast hp)⟩

/-- Upper bound at `n = 6`: `f 6 ≤ 81`. -/
theorem f_six_le_81 : f 6 ≤ 81 := by
  calc f 6 ≤ edgeCount q6_81 := f_le_of_valid q6_81 q6_81_valid
    _ = 81 := q6_81_edgeCount

/-- Combined kernel-verified bounds at `n = 6`: `75 ≤ f 6 ∧ f 6 ≤ 81`. -/
theorem f_six_bounds : 75 ≤ f 6 ∧ f 6 ≤ 81 :=
  ⟨theorem1_concrete_values.2.2.1, f_six_le_81⟩

/-- The symmetric-chain construction on `Q_6` uses `82` edges. -/
theorem grahamConstruction_six_edgeCount : edgeCount (grahamConstruction 6) = 82 := by
  rw [grahamConstruction_edgeCount (by norm_num)]
  decide

/-- PatternBoost's 81-edge subgraph refutes optimality of the symmetric-chain construction
at `n = 6`: `f 6 < edgeCount (grahamConstruction 6)`. -/
theorem q6_beats_grahamConstruction : f 6 < edgeCount (grahamConstruction 6) := by
  rw [grahamConstruction_six_edgeCount]
  exact Nat.lt_of_le_of_lt f_six_le_81 (by norm_num)


/-! ## Section 2: Lead 3 — Blocking-Vertex Lower Bound (`charter.md`, `known-results.md` §4) -/

/-- `u` has an edge in `G` stepping one Hamming layer farther from corner `r`. -/
def hasUpNeighbor {n : ℕ} (G : SimpleGraph (CubeVertex n)) (r u : CubeVertex n) : Prop :=
  ∃ w, G.Adj u w ∧ hammingDist r u + 1 = hammingDist r w

/-- `u` has an edge in `G` stepping one Hamming layer closer to corner `r`. -/
def hasDownNeighbor {n : ℕ} (G : SimpleGraph (CubeVertex n)) (r u : CubeVertex n) : Prop :=
  ∃ w, G.Adj u w ∧ hammingDist r w + 1 = hammingDist r u

/-- `u` is a **blocking vertex** of `G` relative to corner `r` (`charter.md` Lead 3) iff
`u ∉ {r, antipode r}` and `u` lacks either an up-edge or a down-edge relative to `r`. -/
def isBlockingVertex {n : ℕ} (G : SimpleGraph (CubeVertex n)) (r u : CubeVertex n) : Prop :=
  u ≠ r ∧ u ≠ antipode r ∧ ¬(hasUpNeighbor G r u ∧ hasDownNeighbor G r u)

/-- `β_r(G)`: number of blocking vertices of `G` relative to corner `r`. -/
noncomputable def blockingCount {n : ℕ} (G : SimpleGraph (CubeVertex n))
    (r : CubeVertex n) : ℕ :=
  {u : CubeVertex n | isBlockingVertex G r u}.ncard

private theorem hammingDist_eq_n_iff_antipode {n : ℕ} (r u : CubeVertex n) :
    hammingDist r u = n ↔ u = antipode r := by
  constructor
  · intro h
    have ha := hammingDist_antipode_left r u
    rw [h] at ha
    have h0 : hammingDist (antipode r) u = 0 := by omega
    exact (hammingDist_eq_zero.1 h0).symm
  · rintro rfl
    rw [hammingDist_comm]
    exact hammingDist_antipode_self r

private theorem interior_layer_iff {n : ℕ} (r u : CubeVertex n) :
    (1 ≤ hammingDist r u ∧ hammingDist r u < n) ↔ (u ≠ r ∧ u ≠ antipode r) := by
  have hle := hammingDist_le_n r u
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro rfl; rw [hammingDist_self] at h1; omega
    · intro ha; rw [(hammingDist_eq_n_iff_antipode r u).2 ha] at h2; omega
  · rintro ⟨hne0, hnea⟩
    have h0 : hammingDist r u ≠ 0 := fun h => hne0 (hammingDist_eq_zero.1 h).symm
    have hn' : hammingDist r u ≠ n := fun h => hnea ((hammingDist_eq_n_iff_antipode r u).1 h)
    omega

/-- **Lead 3 (Blocking-Vertex Lower Bound, `charter.md` / `known-results.md` §4)**:
For every `n ≥ 1`, every spanning subgraph `G ≤ Q n` with no isolated vertex, and every
corner `r : CubeVertex n`,
`2^n + C(n, ⌊n/2⌋) - 2 ≤ |E(G)| + β_r(G)`.
Notice neither connectivity nor diameter `n` is needed: non-isolation suffices. -/
theorem blocking_lower_bound {n : ℕ} (hn : 1 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hiso : ∀ u : CubeVertex n, ∃ w, G.Adj u w) (r : CubeVertex n) :
    2 ^ n + n.choose (n / 2) - 2 ≤ G.edgeSet.ncard + blockingCount G r := by
  classical
  rcases eq_or_lt_of_le hn with rfl | hn2
  · obtain ⟨w, hw⟩ := hiso r
    have hmem : s(r, w) ∈ G.edgeSet := hw
    have hpos : 1 ≤ G.edgeSet.ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨s(r, w), hmem⟩
    norm_num
    omega
  · let m := (n + 1) / 2
    have hm1 : 1 ≤ m := by omega
    have hmn : m < n := by omega
    let Sdown : Finset (CubeVertex n) :=
      univ.filter fun u => 1 ≤ hammingDist r u ∧ hammingDist r u ≤ m
    let Sup : Finset (CubeVertex n) :=
      univ.filter fun u => m ≤ hammingDist r u ∧ hammingDist r u < n
    let D_ok : Finset (CubeVertex n) := Sdown.filter fun u => hasDownNeighbor G r u
    let D_bad : Finset (CubeVertex n) := Sdown.filter fun u => ¬hasDownNeighbor G r u
    let U_ok : Finset (CubeVertex n) := Sup.filter fun u => hasUpNeighbor G r u
    let U_bad : Finset (CubeVertex n) := Sup.filter fun u => ¬hasUpNeighbor G r u
    have hD_split : D_ok.card + D_bad.card = Sdown.card :=
      Finset.card_filter_add_card_filter_not _
    have hU_split : U_ok.card + U_bad.card = Sup.card :=
      Finset.card_filter_add_card_filter_not _
    -- Partition G.edgeSet into bottom edges (min layer < m) and top edges (min layer ≥ m)
    let Ebot : Set (Sym2 (CubeVertex n)) :=
      {e ∈ G.edgeSet | ∃ u w, e = s(u, w) ∧ hammingDist r u + 1 = hammingDist r w ∧
        hammingDist r w ≤ m}
    let Etop : Set (Sym2 (CubeVertex n)) :=
      {e ∈ G.edgeSet | ∃ u w, e = s(u, w) ∧ hammingDist r u + 1 = hammingDist r w ∧
        m ≤ hammingDist r u}
    have hE_disj : Disjoint Ebot Etop := by
      rw [Set.disjoint_left]
      rintro e ⟨_, u1, w1, he1, hd1, hle1⟩ ⟨_, u2, w2, he2, hd2, hge2⟩
      rw [he1, Sym2.eq_iff] at he2
      rcases he2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    have hE_sub : Ebot ∪ Etop ⊆ G.edgeSet := by
      rintro e (he | he) <;> exact he.1
    have hE_card : Ebot.ncard + Etop.ncard ≤ G.edgeSet.ncard := by
      rw [← Set.ncard_union_eq hE_disj]
      exact Set.ncard_le_ncard hE_sub
    -- Injection from D_ok into Ebot
    have hDok_le : D_ok.card ≤ Ebot.ncard := by
      have hex : ∀ w : CubeVertex n, w ∈ D_ok →
          ∃ u, G.Adj w u ∧ hammingDist r u + 1 = hammingDist r w := by
        intro w hw
        simp only [D_ok, Finset.mem_filter] at hw
        exact hw.2
      let pickD : CubeVertex n → Sym2 (CubeVertex n) := fun w =>
        if hw : w ∈ D_ok then s(Classical.choose (hex w hw), w) else s(w, w)
      have hpickD : ∀ w (hw : w ∈ D_ok), pickD w = s(Classical.choose (hex w hw), w) := by
        intro w hw; dsimp only [pickD]; split_ifs; rfl
      have hmaps : Set.MapsTo pickD (D_ok : Set (CubeVertex n)) Ebot := by
        intro w hw
        have hw' : w ∈ D_ok := hw
        have hspec := Classical.choose_spec (hex w hw')
        have hmemS : w ∈ Sdown := (Finset.mem_filter.1 hw').1
        simp only [Sdown, Finset.mem_filter, Finset.mem_univ, true_and] at hmemS
        refine ⟨?_, Classical.choose (hex w hw'), w, hpickD w hw', hspec.2, hmemS.2⟩
        rw [hpickD w hw', SimpleGraph.mem_edgeSet]
        exact hspec.1.symm
      have hinj : Set.InjOn pickD (D_ok : Set (CubeVertex n)) := by
        intro w1 hw1 w2 hw2 heq
        have hw1' : w1 ∈ D_ok := hw1
        have hw2' : w2 ∈ D_ok := hw2
        rw [hpickD w1 hw1', hpickD w2 hw2', Sym2.eq_iff] at heq
        set c1 := Classical.choose (hex w1 hw1')
        set c2 := Classical.choose (hex w2 hw2')
        have hs1 : hammingDist r c1 + 1 = hammingDist r w1 := (Classical.choose_spec (hex w1 hw1')).2
        have hs2 : hammingDist r c2 + 1 = hammingDist r w2 := (Classical.choose_spec (hex w2 hw2')).2
        rcases heq with ⟨_, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · rw [h1] at hs1
          rw [← h2] at hs2
          omega
      rw [← Set.ncard_coe_finset D_ok]
      exact Set.ncard_le_ncard_of_injOn pickD hmaps hinj (Set.toFinite _)
    -- Injection from U_ok into Etop
    have hUok_le : U_ok.card ≤ Etop.ncard := by
      have hex : ∀ u : CubeVertex n, u ∈ U_ok →
          ∃ w, G.Adj u w ∧ hammingDist r u + 1 = hammingDist r w := by
        intro u hu
        simp only [U_ok, Finset.mem_filter] at hu
        exact hu.2
      let pickU : CubeVertex n → Sym2 (CubeVertex n) := fun u =>
        if hu : u ∈ U_ok then s(u, Classical.choose (hex u hu)) else s(u, u)
      have hpickU : ∀ u (hu : u ∈ U_ok), pickU u = s(u, Classical.choose (hex u hu)) := by
        intro u hu; dsimp only [pickU]; split_ifs; rfl
      have hmaps : Set.MapsTo pickU (U_ok : Set (CubeVertex n)) Etop := by
        intro u hu
        have hu' : u ∈ U_ok := hu
        have hspec := Classical.choose_spec (hex u hu')
        have hmemS : u ∈ Sup := (Finset.mem_filter.1 hu').1
        simp only [Sup, Finset.mem_filter, Finset.mem_univ, true_and] at hmemS
        refine ⟨?_, u, Classical.choose (hex u hu'), hpickU u hu', hspec.2, hmemS.1⟩
        rw [hpickU u hu', SimpleGraph.mem_edgeSet]
        exact hspec.1
      have hinj : Set.InjOn pickU (U_ok : Set (CubeVertex n)) := by
        intro u1 hu1 u2 hu2 heq
        have hu1' : u1 ∈ U_ok := hu1
        have hu2' : u2 ∈ U_ok := hu2
        rw [hpickU u1 hu1', hpickU u2 hu2', Sym2.eq_iff] at heq
        set c1 := Classical.choose (hex u1 hu1')
        set c2 := Classical.choose (hex u2 hu2')
        have hs1 : hammingDist r u1 + 1 = hammingDist r c1 := (Classical.choose_spec (hex u1 hu1')).2
        have hs2 : hammingDist r u2 + 1 = hammingDist r c2 := (Classical.choose_spec (hex u2 hu2')).2
        rcases heq with ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact h1
        · rw [h2] at hs1
          rw [← h1] at hs2
          omega
      rw [← Set.ncard_coe_finset U_ok]
      exact Set.ncard_le_ncard_of_injOn pickU hmaps hinj (Set.toFinite _)
    -- Disjointness of D_bad and U_bad inside blockingSet (since no vertex is isolated)
    have hbad_disj : Disjoint D_bad U_bad := by
      rw [Finset.disjoint_left]
      intro v hvD hvU
      simp only [D_bad, U_bad, Finset.mem_filter] at hvD hvU
      obtain ⟨w, hw⟩ := hiso v
      rcases hammingDist_step (hammingDist_of_adj hG hw) r with hstep | hstep
      · exact hvD.2 ⟨w, hw, hstep⟩
      · exact hvU.2 ⟨w, hw, hstep⟩
    have hbad_sub : ((D_bad ∪ U_bad : Finset (CubeVertex n)) : Set (CubeVertex n)) ⊆
        {u : CubeVertex n | isBlockingVertex G r u} := by
      intro u hu
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, D_bad, U_bad, Sdown, Sup,
        Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hu with ⟨⟨h1, h2⟩, hnd⟩ | ⟨⟨h1, h2⟩, hnu⟩
      · have hint : u ≠ r ∧ u ≠ antipode r := (interior_layer_iff r u).1 ⟨h1, by omega⟩
        exact ⟨hint.1, hint.2, fun hboth => hnd hboth.2⟩
      · have hint : u ≠ r ∧ u ≠ antipode r := (interior_layer_iff r u).1 ⟨by omega, h2⟩
        exact ⟨hint.1, hint.2, fun hboth => hnu hboth.1⟩
    have hbad_le : D_bad.card + U_bad.card ≤ blockingCount G r := by
      rw [← Finset.card_union_of_disjoint hbad_disj, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hbad_sub
    -- Sum of |Sdown| + |Sup| = 2^n + C(n, n/2) - 2
    have hunion : Sdown ∪ Sup =
        univ.filter (fun u : CubeVertex n => 1 ≤ hammingDist r u ∧ hammingDist r u < n) := by
      ext u
      simp only [Sdown, Sup, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      have hle := hammingDist_le_n r u
      omega
    have hinter : Sdown ∩ Sup =
        univ.filter (fun u : CubeVertex n => hammingDist r u = m) := by
      ext u
      simp only [Sdown, Sup, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hcard_union : (Sdown ∪ Sup).card + 2 = 2 ^ n := by
      rw [hunion]
      have hcomp : univ.filter
          (fun u : CubeVertex n => ¬(1 ≤ hammingDist r u ∧ hammingDist r u < n)) =
          {r, antipode r} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, interior_layer_iff]
        tauto
      have hne : r ≠ antipode r := by
        intro h
        have h1 := hammingDist_antipode_self r
        rw [← h, hammingDist_self] at h1
        omega
      have hadd := Finset.card_filter_add_card_filter_not (s := univ)
        (fun u : CubeVertex n => 1 ≤ hammingDist r u ∧ hammingDist r u < n)
      rw [hcomp, Finset.card_pair hne, Finset.card_univ, card_vertices] at hadd
      exact hadd
    have hcard_inter : (Sdown ∩ Sup).card = n.choose (n / 2) := by
      rw [hinter, card_hamming_sphere r m]
      by_cases heven : n % 2 = 0
      · have : m = n / 2 := by omega
        rw [this]
      · have hsym := Nat.choose_symm (show n / 2 ≤ n by omega)
        have hsub : n - n / 2 = m := by omega
        rw [hsub] at hsym
        exact hsym
    have hsum := Finset.card_union_add_card_inter Sdown Sup
    omega

/-- Specialization of Lead 3 (`blocking_lower_bound`) to valid diameter-preserving spanning
subgraphs of `Q_n` (`n ≥ 1`): saving `s` edges below `grahamConstruction n` forces at least
`s` blocking vertices at **every** corner `r` of `Q_n`. -/
theorem blocking_lower_bound_valid {n : ℕ} (hn : 1 ≤ n)
    {G : SimpleGraph (CubeVertex n)} [DecidableRel G.Adj]
    (hV : IsValidSpanningSubgraph n G) (r : CubeVertex n) :
    2 ^ n + n.choose (n / 2) - 2 ≤ edgeCount G + blockingCount G r := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hiso : ∀ u : CubeVertex n, ∃ w, G.Adj u w := by
    intro u
    have hd : 1 ≤ G.dist (antipode u) u := by
      have h1 := (dist_hamming hG hc (antipode u) u).1
      rw [hammingDist_antipode_self] at h1
      omega
    obtain ⟨w, hw, _⟩ := exists_parent hc hd
    exact ⟨w, hw⟩
  rw [edgeCount_eq_ncard]
  exact blocking_lower_bound hn hG hiso r

/-- Every corner `r` of `Q_6` sees at least one blocking vertex in `q6_81`. -/
theorem q6_81_blocking_every_corner (r : CubeVertex 6) :
    1 ≤ blockingCount q6_81 r := by
  have h := blocking_lower_bound_valid (n := 6) (by norm_num) q6_81_valid r
  rw [q6_81_edgeCount] at h
  have hc : (6 : ℕ).choose (6 / 2) = 20 := by decide
  omega


/-! ## Section 3: Thin Levels (`bound-2.md` Lemma 4 & Theorem 4) and `f(8) ≥ 292` (`bound-3.md`) -/

noncomputable section

/-- `ψ(w) = x_w δ(w) + 2 M(w)`, the per-vertex excess-detour potential of `bound-3.md`. -/
def psi {n : ℕ} (G : SimpleGraph (CubeVertex n)) (w : CubeVertex n) : ℤ :=
  excess G w * distGap G w + 2 * weightedExtra G w

theorem psi_nonneg {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) (w : CubeVertex n) :
    0 ≤ psi G w := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  unfold psi
  have h1 := mul_nonneg (excess_nonneg hn hG hD w) (distGap_nonneg (by omega) hG hD w)
  have h2 := weightedExtra_nonneg hc w
  linarith

/-- Global conservation identity (`bound-3.md`):
`∑_w ψ(w) = 2^n ((n - 1) t - (2^n - 2n))`. -/
theorem sum_psi {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hV : IsValidSpanningSubgraph n G) :
    ∑ w : CubeVertex n, psi G w =
      (2 : ℤ) ^ n * (((n : ℤ) - 1) * edgeExcess G - ((2 : ℤ) ^ n - 2 * (n : ℤ))) := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hd := part_d hn hG hD
  unfold psi
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact hd

/-- `|B_G(w, k)| = ∑_{j=0}^k |S_j(w)|`: size of the radius-`k` ball in `G` around `w`. -/
def graphBallCard {n : ℕ} (G : SimpleGraph (CubeVertex n)) (w : CubeVertex n) (k : ℕ) : ℕ :=
  ∑ j ∈ range (k + 1), (levelSet G w j).card

/-- `g_k(w) = B(n, k) - |B_G(w, k)|`: ball size deficit at radius `k` (`bound-3.md` Step 31). -/
def ballGap {n : ℕ} (G : SimpleGraph (CubeVertex n)) (w : CubeVertex n) (k : ℕ) : ℤ :=
  (hammingBallSize n k : ℤ) - (graphBallCard G w k : ℤ)

theorem graphBallCard_eq_filter {n : ℕ} (G : SimpleGraph (CubeVertex n))
    (w : CubeVertex n) (k : ℕ) :
    graphBallCard G w k = (univ.filter fun u => G.dist w u < k + 1).card := by
  have h := levels_sum (G := G) w (fun _ => (1 : ℤ)) (k + 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [← Finset.natCast_card_filter] at h
  unfold graphBallCard
  exact_mod_cast h

theorem ballGap_nonneg {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (w : CubeVertex n) (k : ℕ) :
    0 ≤ ballGap G w k := by
  unfold ballGap
  rw [graphBallCard_eq_filter, ← card_hamming_ball w k]
  have hsub : (univ.filter fun u : CubeVertex n => G.dist w u < k + 1) ⊆
      univ.filter (fun u : CubeVertex n => hammingDist w u < k + 1) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    have hd := (dist_hamming hG hc w u).1
    omega
  have hle := Finset.card_le_card hsub
  omega

/-- Step 24 (`bound-2.md`): `δ(w) = ∑_{k=0}^{n-1} (B(n, k) - |B_G(w, k)|)`. -/
theorem distGap_eq_sum_ballGap {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 1 ≤ n) (hD : G.ediam = (n : ℕ∞)) (w : CubeVertex n) :
    distGap G w = ∑ k ∈ range n, ballGap G w k := by
  have hdist : ∀ u : CubeVertex n,
      (G.dist u w : ℤ) = (n : ℤ) - ∑ k ∈ range n, (if G.dist w u < k + 1 then 1 else 0 : ℤ) := by
    intro u
    rw [SimpleGraph.dist_comm]
    have hle := dist_le_of_ediam hD w u
    rw [← Finset.natCast_card_filter]
    have hflt : (range n).filter (fun k => G.dist w u < k + 1) = Ico (G.dist w u) n := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hflt, Nat.card_Ico]
    omega
  have hham : ∀ u : CubeVertex n,
      (hammingDist u w : ℤ) =
        (n : ℤ) - ∑ k ∈ range n, (if hammingDist w u < k + 1 then 1 else 0 : ℤ) := by
    intro u
    rw [hammingDist_comm u w]
    have hle := hammingDist_le_n w u
    rw [← Finset.natCast_card_filter]
    have hflt : (range n).filter (fun k => hammingDist w u < k + 1) = Ico (hammingDist w u) n := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hflt, Nat.card_Ico]
    omega
  have hDsum : distSum G w =
      ∑ u : CubeVertex n, ((n : ℤ) - ∑ k ∈ range n, (if G.dist w u < k + 1 then 1 else 0 : ℤ)) :=
    Finset.sum_congr rfl fun u _ => hdist u
  have hHsum : (n : ℤ) * 2 ^ (n - 1) =
      ∑ u : CubeVertex n,
        ((n : ℤ) - ∑ k ∈ range n, (if hammingDist w u < k + 1 then 1 else 0 : ℤ)) := by
    rw [← sum_hammingDist_int hn w]
    exact Finset.sum_congr rfl fun u _ => hham u
  unfold distGap
  rw [hDsum, hHsum, ← Finset.sum_sub_distrib]
  have hsimp : ∀ u : CubeVertex n,
      ((n : ℤ) - ∑ k ∈ range n, (if G.dist w u < k + 1 then 1 else 0 : ℤ)) -
        ((n : ℤ) - ∑ k ∈ range n, (if hammingDist w u < k + 1 then 1 else 0 : ℤ)) =
      ∑ k ∈ range n,
        ((if hammingDist w u < k + 1 then 1 else 0 : ℤ) -
          (if G.dist w u < k + 1 then 1 else 0 : ℤ)) := by
    intro u
    rw [Finset.sum_sub_distrib]
    ring
  rw [Finset.sum_congr rfl fun u _ => hsimp u, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_sub_distrib, ← Finset.natCast_card_filter, ← Finset.natCast_card_filter,
    card_hamming_ball w k, ← graphBallCard_eq_filter]
  rfl

/-- `β_s(k)` (`bound-2.md` Notation): recursive ball cap `β_s(0) = 1`,
`β_s(k + 1) = min(B(n, k + 1), β_s(k) + s)`. -/
def ballCapBeta (n s : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => min (hammingBallSize n (k + 1)) (ballCapBeta n s k + s)

/-- `Δ(n, s) = ∑_{k=0}^{n-1} (B(n, k) - β_s(k))` (`bound-2.md` Lemma 4). -/
def ballCapDelta (n s : ℕ) : ℤ :=
  ∑ k ∈ range n, ((hammingBallSize n k : ℤ) - (ballCapBeta n s k : ℤ))

theorem ballCapBeta_le_hammingBallSize (n s k : ℕ) :
    ballCapBeta n s k ≤ hammingBallSize n k := by
  cases k with
  | zero => simp [ballCapBeta, hammingBallSize]
  | succ k => simp [ballCapBeta]

theorem ballCapDelta_nonneg (n s : ℕ) : 0 ≤ ballCapDelta n s := by
  unfold ballCapDelta
  refine Finset.sum_nonneg fun k _ => ?_
  have h := ballCapBeta_le_hammingBallSize n s k
  omega

/-- **Lemma 4 (`bound-2.md` Step 24)**: if every BFS sphere `S_k(w)` (`k ≥ 1`) has size at
most `s`, then `δ(w) ≥ Δ(n, s)`. -/
theorem lemma4_ball_cap {n : ℕ} (hn : 1 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (w : CubeVertex n) (s : ℕ)
    (hcap : ∀ k, 1 ≤ k → (levelSet G w k).card ≤ s) :
    ballCapDelta n s ≤ distGap G w := by
  have hc := connected_of_ediam hD
  have hball : ∀ k, graphBallCard G w k ≤ ballCapBeta n s k := by
    intro k
    induction k with
    | zero =>
      simp [graphBallCard, ballCapBeta, card_levelSet_zero hc w]
    | succ k ih =>
      simp only [ballCapBeta, le_min_iff]
      refine ⟨?_, ?_⟩
      · have h0 := ballGap_nonneg hG hc w (k + 1)
        unfold ballGap at h0
        omega
      · unfold graphBallCard at ih ⊢
        rw [Finset.sum_range_succ]
        have hs := hcap (k + 1) (by omega)
        omega
  rw [distGap_eq_sum_ballGap hn hD w]
  unfold ballCapDelta
  refine Finset.sum_le_sum fun k _ => ?_
  unfold ballGap
  have hk := hball k
  omega

/-- Step 25 (`bound-2.md`): every BFS sphere `S_k(w)` (`k ≥ 1`) has at most `2 + 2t` vertices. -/
theorem level_card_le_two_add_two_edgeExcess {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (CubeVertex n)} (hV : IsValidSpanningSubgraph n G)
    (w : CubeVertex n) {k : ℕ} (hk : 1 ≤ k) :
    ((levelSet G w k).card : ℤ) ≤ 2 + 2 * edgeExcess G := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hg := level_growth_bound hV w hk
  have hYle : ballExcess G w (k - 1) ≤ 2 * edgeExcess G := by
    rw [← sum_excess, ← sum_levelExcess hD w]
    unfold ballExcess
    by_cases hkn : k - 1 ≤ n
    · have hsub : range (k - 1 + 1) ⊆ range (n + 1) := by
        intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
        Finset.sum_nonneg fun u _ => excess_nonneg hn hG hD u
    · have heq : ∑ j ∈ range (k - 1 + 1), levelExcess G w j =
          ∑ j ∈ range (n + 1), levelExcess G w j := by
        symm
        refine Finset.sum_subset (fun j hj => by simp only [Finset.mem_range] at hj ⊢; omega) ?_
        intro j hj hnj
        simp only [Finset.mem_range] at hj hnj
        have hjgt : n < j := by omega
        simp [levelExcess, levelSet_eq_empty hD w hjgt]
      rw [heq]
  linarith

/-- **Theorem 4 (`bound-2.md` Step 26, Thin Levels)**:
For every `n ≥ 2` and every valid spanning subgraph `G` of `Q n` with `t = |E(G)| - 2^n`,
`2 t Δ(n, 2 + 2t) ≤ 2^n ((n - 1) t - (2^n - 2n))`. -/
theorem theorem4_thin_levels {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (CubeVertex n)} (hV : IsValidSpanningSubgraph n G) :
    2 * edgeExcess G * ballCapDelta n (2 + 2 * (G.edgeSet.ncard - 2 ^ n)) ≤
      (2 : ℤ) ^ n * (((n : ℤ) - 1) * edgeExcess G - ((2 : ℤ) ^ n - 2 * (n : ℤ))) := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hge := two_pow_le_edgeSet_ncard hn hV
  let s : ℕ := 2 + 2 * (G.edgeSet.ncard - 2 ^ n)
  have hs_cast : (s : ℤ) = 2 + 2 * edgeExcess G := by
    unfold s edgeExcess
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hge]
    push_cast
    ring
  have hcap : ∀ w : CubeVertex n, ballCapDelta n s ≤ distGap G w := by
    intro w
    refine lemma4_ball_cap (by omega) hG hD w s fun k hk => ?_
    have hl := level_card_le_two_add_two_edgeExcess hn hV w hk
    rw [← hs_cast] at hl
    exact_mod_cast hl
  have hsum1 : 2 * edgeExcess G * ballCapDelta n s ≤
      ∑ w : CubeVertex n, excess G w * distGap G w := by
    rw [← sum_excess, Finset.sum_mul]
    exact Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hcap w) (excess_nonneg hn hG hD w)
  have hsum2 : 0 ≤ ∑ v : CubeVertex n, weightedExtra G v :=
    Finset.sum_nonneg fun v _ => weightedExtra_nonneg (connected_of_ediam hD) v
  have hd := part_d hn hG hD
  linarith

/-- Immediate `n = 10` consequence of Theorem 4 (`bound-2.md` Table): `1137 ≤ f 10`
(strictly exceeding Theorem 1's `1136`). -/
theorem f_ten_ge_1137 : 1137 ≤ f 10 := by
  apply le_f_of_forall_valid
  intro G hV
  have ht1 := theorem1_lower_bound_nat_ceil (n := 10) (by norm_num) hV
  norm_num at ht1
  by_contra hlt
  have he : G.edgeSet.ncard = 1136 := by omega
  have ht4 := theorem4_thin_levels (n := 10) (by norm_num) hV
  have hex : edgeExcess G = 112 := by unfold edgeExcess; rw [he]; norm_num
  rw [he, hex] at ht4
  have hdelta : ballCapDelta 10 (2 + 2 * (1136 - 2 ^ 10)) = 36 := by decide
  rw [hdelta] at ht4
  norm_num at ht4

/-- Step 31 (`bound-3.md`): `|S_1(w)| = deg(w) = 2 + x_w`. -/
theorem card_levelSet_one {n : ℕ} {G : SimpleGraph (CubeVertex n)} (w : CubeVertex n) :
    ((levelSet G w 1).card : ℤ) = 2 + excess G w := by
  have heq : (levelSet G w 1 : Set (CubeVertex n)) = G.neighborSet w := by
    ext u
    simp only [Finset.mem_coe, mem_levelSet, SimpleGraph.mem_neighborSet,
      SimpleGraph.dist_eq_one_iff_adj]
  rw [← Set.ncard_coe_finset, heq]
  unfold excess
  ring

/-- Step 31 (`bound-3.md`, Branching Bound): `|S_2(w)| ≤ (n - 1) * |S_1(w)|`. -/
theorem levelTwo_le_branch {n : ℕ} (hn : 1 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (w : CubeVertex n) :
    (levelSet G w 2).card ≤ (n - 1) * (levelSet G w 1).card := by
  have hchild : ∑ u ∈ levelSet G w 1, (childCount G w 1 u : ℤ) =
      ∑ v ∈ levelSet G w 2, (parentCount G w 2 v : ℤ) :=
    sum_child_eq hG hc w 1
  have hge_s2 : ((levelSet G w 2).card : ℤ) ≤
      ∑ v ∈ levelSet G w 2, (parentCount G w 2 v : ℤ) := by
    have hex := extraParents_nonneg hc w (k := 2) (by norm_num)
    unfold extraParents at hex
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hex
    linarith
  have hle_c : ∀ u ∈ levelSet G w 1, (childCount G w 1 u : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
    intro u hu
    rw [mem_levelSet] at hu
    have hsplit := degree_split hG hc hu
    have hp1 := parentCount_one hc hu
    have hdeg := ncard_neighborSet_le_n hG u
    omega
  have hsum_le : ∑ u ∈ levelSet G w 1, (childCount G w 1 u : ℤ) ≤
      ((levelSet G w 1).card : ℤ) * ((n - 1 : ℕ) : ℤ) := by
    calc ∑ u ∈ levelSet G w 1, (childCount G w 1 u : ℤ)
        ≤ ∑ _u ∈ levelSet G w 1, ((n - 1 : ℕ) : ℤ) := Finset.sum_le_sum hle_c
      _ = ((levelSet G w 1).card : ℤ) * ((n - 1 : ℕ) : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hZ : ((levelSet G w 2).card : ℤ) ≤ (((n - 1) * (levelSet G w 1).card : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast hZ

theorem ballExcess_mono {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hn : 2 ≤ n) (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (w : CubeVertex n)
    {j k : ℕ} (hjk : j ≤ k) :
    ballExcess G w j ≤ ballExcess G w k := by
  unfold ballExcess
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega) ?_
  intro i _ _
  exact Finset.sum_nonneg fun u _ => excess_nonneg hn hG hD u

/-- **Lemma 6 (`bound-3.md` Steps 31–34)**:
In any valid diameter-8 spanning subgraph `G` of `Q_8`, every vertex `w` of positive degree
excess (`1 ≤ excess G w`) satisfies `124 ≤ ψ(w)`. -/
theorem lemma6_psi_ge_124 {G : SimpleGraph (CubeVertex 8)}
    (hV : IsValidSpanningSubgraph 8 G) (w : CubeVertex 8) (hx : 1 ≤ excess G w) :
    124 ≤ psi G w := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hx_le : excess G w ≤ 6 := by
    have := excess_le hG w
    omega
  -- Unpack rSet 8 = {0, 2, 4, 6} and part_c
  have hr8 : rSet 8 = ({0, 2, 4, 6} : Finset ℕ) := by decide
  have hpc := part_c (n := 8) (by norm_num) hG hD w
  have hl8 : lSum G w =
      ballExcess G w 0 + ballExcess G w 2 + ballExcess G w 4 + ballExcess G w 6 := by
    unfold lSum
    rw [hr8]
    simp [add_assoc]
  have hY0 : ballExcess G w 0 = excess G w := by
    simp [ballExcess, levelExcess_zero hc w]
  -- Local level growth caps at k = 3, 4, 5, 6 and monotonicity of Y_m
  have hc3 := level_growth_bound hV w (k := 3) (by norm_num)
  have hc4 := level_growth_bound hV w (k := 4) (by norm_num)
  have hc5 := level_growth_bound hV w (k := 5) (by norm_num)
  have hc6 := level_growth_bound hV w (k := 6) (by norm_num)
  have hr4 : ballExcess G w 3 ≤ ballExcess G w 4 := ballExcess_mono (by norm_num) hG hD w (by omega)
  have hr5 : ballExcess G w 4 ≤ ballExcess G w 5 := ballExcess_mono (by norm_num) hG hD w (by omega)
  have hr6 : ballExcess G w 5 ≤ ballExcess G w 6 := ballExcess_mono (by norm_num) hG hD w (by omega)
  -- Ball gaps g_0..g_7 and B(8, k) values
  have hδ : distGap G w = ballGap G w 0 + ballGap G w 1 + ballGap G w 2 + ballGap G w 3 +
      ballGap G w 4 + ballGap G w 5 + ballGap G w 6 + ballGap G w 7 := by
    rw [distGap_eq_sum_ballGap (by norm_num) hD w]
    simp [Finset.sum_range_succ, add_assoc]
  have hg0 : 0 ≤ ballGap G w 0 := ballGap_nonneg hG hc w 0
  have hg2 : 0 ≤ ballGap G w 2 := ballGap_nonneg hG hc w 2
  have hg3 : 0 ≤ ballGap G w 3 := ballGap_nonneg hG hc w 3
  have hg4 : 0 ≤ ballGap G w 4 := ballGap_nonneg hG hc w 4
  have hg5 : 0 ≤ ballGap G w 5 := ballGap_nonneg hG hc w 5
  have hg6 : 0 ≤ ballGap G w 6 := ballGap_nonneg hG hc w 6
  have hg7 : 0 ≤ ballGap G w 7 := ballGap_nonneg hG hc w 7
  have hs0 : ((levelSet G w 0).card : ℤ) = 1 := by simp [card_levelSet_zero hc w]
  have hs1 : ((levelSet G w 1).card : ℤ) = 2 + excess G w := card_levelSet_one w
  have hB1 : (hammingBallSize 8 1 : ℤ) = 9 := by decide
  have hB2 : (hammingBallSize 8 2 : ℤ) = 37 := by decide
  have hB4 : (hammingBallSize 8 4 : ℤ) = 163 := by decide
  have hB5 : (hammingBallSize 8 5 : ℤ) = 219 := by decide
  have hB6 : (hammingBallSize 8 6 : ℤ) = 247 := by decide
  have hg1_eq : ballGap G w 1 = 6 - excess G w := by
    unfold ballGap graphBallCard
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Nat.cast_add]
    linarith
  have hs345 : ((levelSet G w 3).card : ℤ) + (levelSet G w 4).card + (levelSet G w 5).card =
      182 + ballGap G w 2 - ballGap G w 5 := by
    have e2 : ballGap G w 2 = 37 - ((graphBallCard G w 2 : ℕ) : ℤ) := by unfold ballGap; linarith
    have e5 : ballGap G w 5 = 219 - ((graphBallCard G w 5 : ℕ) : ℤ) := by unfold ballGap; linarith
    have eb : ((graphBallCard G w 5 : ℕ) : ℤ) - (graphBallCard G w 2 : ℤ) =
        ((levelSet G w 3).card : ℤ) + (levelSet G w 4).card + (levelSet G w 5).card := by
      unfold graphBallCard
      simp only [Finset.sum_range_succ, Nat.cast_add]
      ring
    linarith
  -- Step 32: M(w) ≥ x + 56 + g_2 - g_5
  have hM_E : excess G w + 56 + ballGap G w 2 - ballGap G w 5 ≤ weightedExtra G w := by
    norm_num at hpc hc3 hc4 hc5
    linarith
  by_cases hx2 : 2 ≤ excess G w
  · -- Step 33: 2 ≤ x ≤ 6
    unfold psi
    rw [hδ, hg1_eq]
    nlinarith
  · -- Step 34: x = 1
    have hx1 : excess G w = 1 := by omega
    have hs34 : ((levelSet G w 3).card : ℤ) + (levelSet G w 4).card =
        126 + ballGap G w 2 - ballGap G w 4 := by
      have e2 : ballGap G w 2 = 37 - ((graphBallCard G w 2 : ℕ) : ℤ) := by unfold ballGap; linarith
      have e4 : ballGap G w 4 = 163 - ((graphBallCard G w 4 : ℕ) : ℤ) := by unfold ballGap; linarith
      have eb : ((graphBallCard G w 4 : ℕ) : ℤ) - (graphBallCard G w 2 : ℤ) =
          ((levelSet G w 3).card : ℤ) + (levelSet G w 4).card := by
        unfold graphBallCard
        simp only [Finset.sum_range_succ, Nat.cast_add]
        ring
      linarith
    have hs6 : ((levelSet G w 6).card : ℤ) = 28 + ballGap G w 5 - ballGap G w 6 := by
      have e5 : ballGap G w 5 = 219 - ((graphBallCard G w 5 : ℕ) : ℤ) := by unfold ballGap; linarith
      have e6 : ballGap G w 6 = 247 - ((graphBallCard G w 6 : ℕ) : ℤ) := by unfold ballGap; linarith
      have eb : ((graphBallCard G w 6 : ℕ) : ℤ) - (graphBallCard G w 5 : ℤ) =
          ((levelSet G w 6).card : ℤ) := by
        unfold graphBallCard
        simp only [Finset.sum_range_succ, Nat.cast_add]
        ring
      linarith
    have hM_G : excess G w + 28 + ballGap G w 2 - ballGap G w 4 + ballGap G w 5 - ballGap G w 6 ≤
        weightedExtra G w := by
      norm_num at hpc hc3 hc4 hc6
      linarith
    have hbr : ((levelSet G w 2).card : ℤ) ≤ 21 := by
      have hb := levelTwo_le_branch (n := 8) (by norm_num) hG hc w
      have hbZ : ((levelSet G w 2).card : ℤ) ≤ 7 * ((levelSet G w 1).card : ℤ) := by
        exact_mod_cast hb
      linarith
    have hg2_12 : 12 ≤ ballGap G w 2 := by
      have e2 : ballGap G w 2 = 37 - (((levelSet G w 0).card : ℤ) +
          (levelSet G w 1).card + (levelSet G w 2).card) := by
        unfold ballGap graphBallCard
        simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Nat.cast_add]
        linarith
      linarith
    unfold psi
    rw [hδ, hg1_eq, hx1]
    linarith

/-- **Theorem 6 (`bound-3.md` Step 35)**: no valid spanning subgraph of `Q_8` has `291` edges. -/
theorem no_valid_q8_291_edges {G : SimpleGraph (CubeVertex 8)}
    (hV : IsValidSpanningSubgraph 8 G) :
    G.edgeSet.ncard ≠ 291 := by
  intro he
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hpt : ∀ w : CubeVertex 8, 124 * excess G w ≤ 6 * psi G w := by
    intro w
    have hx0 := excess_nonneg (by norm_num) hG hD w
    have hx6 : excess G w ≤ 6 := by have := excess_le hG w; omega
    by_cases hx1 : 1 ≤ excess G w
    · have h124 := lemma6_psi_ge_124 hV w hx1
      linarith
    · have hxz : excess G w = 0 := by omega
      have hp0 := psi_nonneg (by norm_num) hV w
      rw [hxz]
      linarith
  have hsum : 124 * ∑ w : CubeVertex 8, excess G w ≤ 6 * ∑ w : CubeVertex 8, psi G w := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hpt w
  rw [sum_excess, sum_psi (by norm_num) hV] at hsum
  have hex : edgeExcess G = 35 := by unfold edgeExcess; rw [he]; norm_num
  rw [hex] at hsum
  norm_num at hsum

/-- **Theorem 6 (`bound-3.md`)**: `292 ≤ f 8`, strictly beating Theorem 1's `291`. -/
theorem f_eight_ge_292 : 292 ≤ f 8 := by
  apply le_f_of_forall_valid
  intro G hV
  have ht1 := theorem1_lower_bound_nat_ceil (n := 8) (by norm_num) hV
  norm_num at ht1
  have hne := no_valid_q8_291_edges hV
  omega


/-! ## Section 4: Asymptotic Second-Term Coefficient `3/2` (`bound-2.md` Theorem 5) -/

/-- Nenadov–Sawhney–Sudakov–Wagner (2019, Proposition 4.2) lower bound:
`2^n - 1 + ⌈(2^n - 1) / (2n)⌉`. -/
def bound2019 (n : ℕ) : ℤ :=
  (2 : ℤ) ^ n - 1 + ⌈((2 : ℚ) ^ n - 1) / (2 * (n : ℚ))⌉

/-- For every `n ≥ 1`, the 2019 lower bound does not exceed the 1995 lower bound. -/
theorem bound2019_le_bound1995 {n : ℕ} (hn : 1 ≤ n) :
    bound2019 n ≤ bound1995 n := by
  unfold bound2019 bound1995
  have hnQ : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hpow : (2 : ℚ) ≤ (2 : ℚ) ^ n := by
    have hp : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact_mod_cast hp
  have hd1 : (0 : ℚ) < 2 * (n : ℚ) := by linarith
  have hd2 : (0 : ℚ) < 2 * (n : ℚ) - 1 := by linarith
  have hfrac : ((2 : ℚ) ^ n - 1) / (2 * (n : ℚ)) ≤
      ((2 : ℚ) ^ n - 1) / (2 * (n : ℚ) - 1) := by
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith
  have hc := Int.ceil_mono hfrac
  linarith

/-- For every `n ≥ 4`, the 2019 lower bound is strictly below `f n`. -/
theorem bound2019_lt_f {n : ℕ} (hn : 4 ≤ n) :
    bound2019 n < (f n : ℤ) :=
  lt_of_le_of_lt (bound2019_le_bound1995 (by omega)) (not_attained_1995 hn)

/-- Normalized second-term upper bound for the 1995 bound: for every `n ≥ 2`,
`(bound1995 n - 2^n) * (n - 1) < (1/2) * 2^n`. -/
theorem bound1995_second_term_lt_half {n : ℕ} (hn : 2 ≤ n) :
    ((bound1995 n : ℚ) - (2 : ℚ) ^ n) * ((n : ℚ) - 1) < ((1 : ℚ) / 2) * (2 : ℚ) ^ n := by
  unfold bound1995
  push_cast
  let q : ℚ := ((2 : ℚ) ^ n - 1) / (2 * (n : ℚ) - 1)
  have hceil : (⌈q⌉ : ℚ) < q + 1 := Int.ceil_lt_add_one q
  have hnQ : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn1 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  have hd : (0 : ℚ) < 2 * (n : ℚ) - 1 := by linarith
  have hpow : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
  have h1 : ((2 : ℚ) ^ n - 1 + (⌈q⌉ : ℚ) - (2 : ℚ) ^ n) * ((n : ℚ) - 1) <
      q * ((n : ℚ) - 1) := by nlinarith
  have h2 : q * ((n : ℚ) - 1) < ((1 : ℚ) / 2) * (2 : ℚ) ^ n := by
    dsimp only [q]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith
  linarith

/-- Normalized second-term lower bound for Theorem 1: for every `n ≥ 2`,
`1 * 2^n - 2n ≤ (boundTheorem1 n - 2^n) * (n - 1)`. -/
theorem theorem1_second_term_lower {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℚ) ^ n - 2 * (n : ℚ) ≤ ((boundTheorem1 n : ℚ) - (2 : ℚ) ^ n) * ((n : ℚ) - 1) := by
  unfold boundTheorem1
  push_cast
  let q : ℚ := ((2 : ℚ) ^ n - 2 * (n : ℚ)) / ((n : ℚ) - 1)
  have hceil : q ≤ (⌈q⌉ : ℚ) := Int.le_ceil q
  have hnQ : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn1 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  have hq : q * ((n : ℚ) - 1) = (2 : ℚ) ^ n - 2 * (n : ℚ) := div_mul_cancel₀ _ (ne_of_gt hn1)
  nlinarith

private def spin {n : ℕ} (u : CubeVertex n) (i : Fin n) : ℤ :=
  if u i = true then 1 else -1

private theorem centered_hammingWeight_eq_sum_spin {n : ℕ} (u : CubeVertex n) :
    2 * (hammingWeight u : ℤ) - (n : ℤ) = ∑ i : Fin n, spin u i := by
  have hw : (hammingWeight u : ℤ) = ∑ i : Fin n, (if u i = true then (1 : ℤ) else 0) := by
    unfold hammingWeight
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases u i <;> simp
  have hn : (n : ℤ) = ∑ _i : Fin n, (1 : ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hw, Finset.mul_sum, hn, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold spin
  cases u i <;> decide

/-- Exact second-moment identity on the hypercube:
`∑_{u ∈ Q_n} (2 |u| - n)^2 = n 2^n`. -/
theorem sum_centered_hamming_sq (n : ℕ) :
    ∑ u : CubeVertex n, (2 * (hammingWeight u : ℤ) - (n : ℤ)) ^ 2 = (n : ℤ) * (2 : ℤ) ^ n := by
  have hsq : ∀ u : CubeVertex n,
      (2 * (hammingWeight u : ℤ) - (n : ℤ)) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, spin u i * spin u j := by
    intro u
    rw [centered_hammingWeight_eq_sum_spin, sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hinner : ∀ i : Fin n,
      ∑ u : CubeVertex n, ∑ j : Fin n, spin u i * spin u j = (2 : ℤ) ^ n := by
    intro i
    rw [Finset.sum_comm]
    have hij : ∀ j : Fin n,
        ∑ u : CubeVertex n, spin u i * spin u j = if j = i then (2 : ℤ) ^ n else 0 := by
      intro j
      by_cases hji : j = i
      · subst hji
        have h1 : ∀ u : CubeVertex n, spin u j * spin u j = 1 := by
          intro u; unfold spin; cases u j <;> decide
        simp_rw [h1]
        rw [Finset.sum_const, Finset.card_univ, card_vertices, nsmul_eq_mul, mul_one]
        push_cast; rfl
      · simp only [hji, ↓reduceIte]
        let e : CubeVertex n ≃ CubeVertex n :=
          { toFun := flipAt i
            invFun := flipAt i
            left_inv := flipAt_flipAt i
            right_inv := flipAt_flipAt i }
        have heq := Fintype.sum_equiv e
          (fun u => spin (flipAt i u) i * spin (flipAt i u) j)
          (fun u => spin u i * spin u j) (fun _ => rfl)
        have hneg : ∀ u : CubeVertex n,
            spin (flipAt i u) i * spin (flipAt i u) j = -(spin u i * spin u j) := by
          intro u
          have hi : spin (flipAt i u) i = -spin u i := by
            unfold spin; rw [flipAt_apply_self]; cases u i <;> decide
          have hj : spin (flipAt i u) j = spin u j := by
            unfold spin; rw [flipAt_apply_of_ne u hji]
          rw [hi, hj, neg_mul]
        simp_rw [hneg, Finset.sum_neg_distrib] at heq
        linarith
    simp_rw [hij]
    simp
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Algebraic Chebyshev tail bound for the Hamming ball: for `2 * j0 ≤ n`,
`(n - 2 j0)^2 B(n, j0) ≤ n 2^n`. -/
theorem chebyshev_hammingBall_tail {n j0 : ℕ} (hj : 2 * j0 ≤ n) :
    ((n : ℤ) - 2 * (j0 : ℤ)) ^ 2 * (hammingBallSize n j0 : ℤ) ≤ (n : ℤ) * (2 : ℤ) ^ n := by
  let v0 : CubeVertex n := fun _ => false
  have hcard : hammingBallSize n j0 =
      (univ.filter fun u : CubeVertex n => hammingWeight u < j0 + 1).card := by
    rw [← card_hamming_ball v0 j0]
    congr 1; ext u
    simp [hammingWeight_eq_hammingDist, v0]
  rw [hcard, ← sum_centered_hamming_sq n]
  have hconst : ((n : ℤ) - 2 * (j0 : ℤ)) ^ 2 *
      (((univ.filter fun u : CubeVertex n => hammingWeight u < j0 + 1).card : ℕ) : ℤ) =
      ∑ _u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u < j0 + 1),
        ((n : ℤ) - 2 * (j0 : ℤ)) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hconst]
  calc ∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u < j0 + 1),
        ((n : ℤ) - 2 * (j0 : ℤ)) ^ 2
      ≤ ∑ u ∈ univ.filter (fun u : CubeVertex n => hammingWeight u < j0 + 1),
          (2 * (hammingWeight u : ℤ) - (n : ℤ)) ^ 2 := by
        refine Finset.sum_le_sum fun u hu => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        have huZ : (hammingWeight u : ℤ) ≤ (j0 : ℤ) := by omega
        have hjZ : 2 * (j0 : ℤ) ≤ (n : ℤ) := by omega
        nlinarith
    _ ≤ ∑ u : CubeVertex n, (2 * (hammingWeight u : ℤ) - (n : ℤ)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

/-- Upper-tail symmetry of Hamming balls via `antipode`: whenever `n ≤ k + j0 + 1`,
`2^n - B(n, j0) ≤ B(n, k)`. -/
theorem hammingBall_upper_tail {n j0 k : ℕ} (h : n ≤ k + j0 + 1) :
    (2 : ℤ) ^ n - (hammingBallSize n j0 : ℤ) ≤ (hammingBallSize n k : ℤ) := by
  let v0 : CubeVertex n := fun _ => false
  have hk : hammingBallSize n k =
      (univ.filter fun u : CubeVertex n => hammingWeight u < k + 1).card := by
    rw [← card_hamming_ball v0 k]
    congr 1; ext u; simp [hammingWeight_eq_hammingDist, v0]
  have hj : hammingBallSize n j0 =
      (univ.filter fun u : CubeVertex n => hammingWeight u < j0 + 1).card := by
    rw [← card_hamming_ball v0 j0]
    congr 1; ext u; simp [hammingWeight_eq_hammingDist, v0]
  let Shi := univ.filter fun u : CubeVertex n => ¬(hammingWeight u < k + 1)
  let Slo := univ.filter fun u : CubeVertex n => hammingWeight u < j0 + 1
  have hle : Shi.card ≤ Slo.card := by
    refine Finset.card_le_card_of_injOn antipode ?_ ?_
    · intro u hu
      simp only [Finset.mem_coe, Shi, Slo, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      have ha := hammingWeight_antipode u
      omega
    · intro u1 _ u2 _ heq
      have h1 := antipode_antipode u1
      have h2 := antipode_antipode u2
      rw [← h1, ← h2, heq]
  have htot := Finset.card_filter_add_card_filter_not (s := univ)
    (fun u : CubeVertex n => hammingWeight u < k + 1)
  rw [Finset.card_univ, card_vertices] at htot
  dsimp only [Shi] at hle
  rw [hk, hj]
  have hnat : 2 ^ n ≤ (univ.filter fun u : CubeVertex n => hammingWeight u < k + 1).card +
      Slo.card := by omega
  have hZ : ((2 ^ n : ℕ) : ℤ) ≤
      (((univ.filter fun u : CubeVertex n => hammingWeight u < k + 1).card + Slo.card : ℕ) : ℤ) := by
    exact_mod_cast hnat
  push_cast at hZ
  linarith

theorem ballCapBeta_step_le (n s j0 r : ℕ) :
    ballCapBeta n s (j0 + r) ≤ hammingBallSize n j0 + r * s := by
  induction r with
  | zero =>
    simp [ballCapBeta_le_hammingBallSize]
  | succ r ih =>
    rw [← Nat.add_assoc]
    have hstep : ballCapBeta n s (j0 + r + 1) ≤ ballCapBeta n s (j0 + r) + s := by
      simp [ballCapBeta]
    have hmul : (r + 1) * s = r * s + s := Nat.succ_mul r s
    omega

private theorem two_mul_sum_range (m : ℕ) :
    2 * ∑ r ∈ range (m + 1), (r : ℤ) = (m : ℤ) * ((m : ℤ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

private theorem arith_prog_sum_sq_lower {A s : ℤ} (j0 : ℕ) (hA : 0 ≤ A) (hs : 1 ≤ s) :
    let m := min (A.toNat / s.toNat) j0
    let D := max 0 (A - (j0 : ℤ) * s)
    (∀ r ∈ range (m + 1), 0 ≤ A - (r : ℤ) * s) ∧
      A ^ 2 - D ^ 2 ≤ 2 * s * ∑ r ∈ range (m + 1), (A - (r : ℤ) * s) := by
  intro m D
  have hAcast : (A.toNat : ℤ) = A := Int.toNat_of_nonneg hA
  have hscast : (s.toNat : ℤ) = s := Int.toNat_of_nonneg (by omega)
  have hspos : 0 < s.toNat := by omega
  have hdivmod := Nat.div_add_mod A.toNat s.toNat
  have hmodlt := Nat.mod_lt A.toNat hspos
  set qNat := A.toNat / s.toNat
  set remNat := A.toNat % s.toNat
  have hdecomp : (s.toNat : ℤ) * (qNat : ℤ) + (remNat : ℤ) = (A.toNat : ℤ) := by
    exact_mod_cast hdivmod
  rw [hscast, hAcast] at hdecomp
  have hrem_lt : (remNat : ℤ) < s := by
    rw [← hscast]; exact_mod_cast hmodlt
  have hrem_nn : 0 ≤ (remNat : ℤ) := Nat.cast_nonneg remNat
  have hm_le_q : (m : ℤ) ≤ (qNat : ℤ) := by
    have : m ≤ qNat := Nat.min_le_left _ _
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_range] at hr
    have hr_le : (r : ℤ) ≤ (m : ℤ) := by omega
    nlinarith
  · have hsum : 2 * ∑ r ∈ range (m + 1), (A - (r : ℤ) * s) =
        ((m : ℤ) + 1) * (2 * A - (m : ℤ) * s) := by
      have hsr := two_mul_sum_range m
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.sum_mul]
      push_cast
      linear_combination -s * hsr
    have hmul : 2 * s * ∑ r ∈ range (m + 1), (A - (r : ℤ) * s) =
        s * (((m : ℤ) + 1) * (2 * A - (m : ℤ) * s)) := by
      linarith [congrArg (s * ·) hsum]
    rw [hmul]
    by_cases hqj : qNat ≤ j0
    · have hmq : m = qNat := Nat.min_eq_left hqj
      have hmqZ : (m : ℤ) = (qNat : ℤ) := by rw [hmq]
      have hq_nn : 0 ≤ (qNat : ℤ) := Nat.cast_nonneg qNat
      have hD_sq : 0 ≤ D ^ 2 := sq_nonneg D
      rw [hmqZ]
      nlinarith
    · have hmj : m = j0 := Nat.min_eq_right (by omega)
      have hmjZ : (m : ℤ) = (j0 : ℤ) := by rw [hmj]
      have hj_lt : (j0 : ℤ) + 1 ≤ (qNat : ℤ) := by omega
      have hAj : (j0 : ℤ) * s ≤ A := by nlinarith
      have hDeq : D = A - (j0 : ℤ) * s := max_eq_right (by linarith)
      rw [hmjZ, hDeq]
      have hj_nn : 0 ≤ (j0 : ℤ) := Nat.cast_nonneg j0
      nlinarith

/-- Quadratic lower bound on `2 s Δ(n, s)` at cut index `j0` (`2 * j0 < n`). -/
theorem ballCapDelta_lower_of_j0 {n s j0 : ℕ} (hs : 1 ≤ s) (hj : 2 * j0 < n)
    (hA : 0 ≤ (2 : ℤ) ^ n - 2 * (hammingBallSize n j0 : ℤ) -
      ((n - 1 - 2 * j0 : ℕ) : ℤ) * (s : ℤ)) :
    let A := (2 : ℤ) ^ n - 2 * (hammingBallSize n j0 : ℤ) -
      ((n - 1 - 2 * j0 : ℕ) : ℤ) * (s : ℤ)
    let D := max 0 (A - (j0 : ℤ) * (s : ℤ))
    A ^ 2 - D ^ 2 ≤ 2 * (s : ℤ) * ballCapDelta n s := by
  intro A D
  let k1 := n - 1 - j0
  let i1 := n - 1 - 2 * j0
  have hsZ : 1 ≤ (s : ℤ) := by omega
  obtain ⟨hpos, hsq⟩ := arith_prog_sum_sq_lower (A := A) (s := (s : ℤ)) j0 hA hsZ
  let m := min (A.toNat / (s : ℤ).toNat) j0
  have hterm : ∀ r ∈ range (m + 1),
      A - (r : ℤ) * (s : ℤ) ≤
        (hammingBallSize n (k1 + r) : ℤ) - (ballCapBeta n s (k1 + r) : ℤ) := by
    intro r _
    have hup := hammingBall_upper_tail (n := n) (j0 := j0) (k := k1 + r) (by omega)
    have hkeq : k1 + r = j0 + (i1 + r) := by omega
    have hbeta : (ballCapBeta n s (k1 + r) : ℤ) ≤
        (hammingBallSize n j0 : ℤ) + ((i1 : ℤ) + (r : ℤ)) * (s : ℤ) := by
      rw [hkeq]
      have hb := ballCapBeta_step_le n s j0 (i1 + r)
      have hbZ : (ballCapBeta n s (j0 + (i1 + r)) : ℤ) ≤
          ((hammingBallSize n j0 + (i1 + r) * s : ℕ) : ℤ) := by exact_mod_cast hb
      push_cast at hbZ
      exact hbZ
    have hAdef : A = (2 : ℤ) ^ n - 2 * (hammingBallSize n j0 : ℤ) - (i1 : ℤ) * (s : ℤ) := rfl
    linarith
  let emb : ℕ ↪ ℕ := ⟨fun r => k1 + r, fun r1 r2 h => by dsimp at h; omega⟩
  have hsub : (range (m + 1)).map emb ⊆ range n := by
    intro k hk
    simp only [Finset.mem_map, Finset.mem_range] at hk ⊢
    obtain ⟨r, hr, rfl⟩ := hk
    change k1 + r < n
    have hm_le : m ≤ j0 := Nat.min_le_right _ _
    omega
  have hsum_le : ∑ r ∈ range (m + 1), (A - (r : ℤ) * (s : ℤ)) ≤ ballCapDelta n s := by
    calc ∑ r ∈ range (m + 1), (A - (r : ℤ) * (s : ℤ))
        ≤ ∑ r ∈ range (m + 1),
            ((hammingBallSize n (k1 + r) : ℤ) - (ballCapBeta n s (k1 + r) : ℤ)) :=
          Finset.sum_le_sum hterm
      _ = ∑ k ∈ (range (m + 1)).map emb,
            ((hammingBallSize n k : ℤ) - (ballCapBeta n s k : ℤ)) := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑ k ∈ range n, ((hammingBallSize n k : ℤ) - (ballCapBeta n s k : ℤ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => ?_
          have hb := ballCapBeta_le_hammingBallSize n s k
          omega
  nlinarith

private theorem four_mul_sq_le_two_pow {m : ℕ} (hm : 8 ≤ m) :
    4 * m ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc 4 * (k + 1) ^ 2 ≤ 8 * k ^ 2 := by nlinarith
      _ = 2 * (4 * k ^ 2) := by ring
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by ring

private theorem theorem5_int_step {n L : ℕ} (hL40 : 40 ≤ L) (hn : 64 * L ^ 3 ≤ n)
    {G : SimpleGraph (CubeVertex n)} (hV : IsValidSpanningSubgraph n G) :
    (3 * (L : ℤ) - 30) * (2 : ℤ) ^ n ≤
      2 * (L : ℤ) * ((n : ℤ) - 1) * edgeExcess G := by
  have hL3_ge : 40 ^ 3 ≤ L ^ 3 := Nat.pow_le_pow_left hL40 3
  have hn8 : 8 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hL_le_L3 : L ≤ L ^ 3 := by
    rw [pow_three]
    exact le_trans (Nat.le_mul_of_pos_right L (by omega)) (Nat.le_mul_of_pos_left _ (by omega))
  have h64L_le_n : 64 * L ≤ n := le_trans (Nat.mul_le_mul_left 64 hL_le_L3) hn
  let P2 : ℤ := (2 : ℤ) ^ n
  let t : ℤ := edgeExcess G
  have hP2_pos : 0 < P2 := by positivity
  by_cases hbig : 3 * P2 ≤ (2 * (n : ℤ) - 2) * t
  · calc (3 * (L : ℤ) - 30) * P2
        ≤ 3 * (L : ℤ) * P2 :=
          mul_le_mul_of_nonneg_right (by omega) (le_of_lt hP2_pos)
      _ = (L : ℤ) * (3 * P2) := by ring
      _ ≤ (L : ℤ) * ((2 * (n : ℤ) - 2) * t) :=
          mul_le_mul_of_nonneg_left hbig (by omega)
      _ = 2 * (L : ℤ) * ((n : ℤ) - 1) * t := by ring
  · push Not at hbig
    -- Exponential dominance `4 * L * (n + 1) ≤ 2^n`
    have hquad_nat : 4 * n ^ 2 ≤ 2 ^ n := four_mul_sq_le_two_pow hn8
    have hdom_nat : 4 * L * (n + 1) ≤ 4 * n ^ 2 := by
      have h1 : 4 * L ≤ n := by omega
      have h2 : n + 1 ≤ 4 * n := by omega
      calc 4 * L * (n + 1) ≤ n * (4 * n) := Nat.mul_le_mul h1 h2
        _ = 4 * n ^ 2 := by ring
    have hdom : 4 * (L : ℤ) * ((n : ℤ) + 1) ≤ P2 := by
      have h : 4 * L * (n + 1) ≤ 2 ^ n := le_trans hdom_nat hquad_nat
      dsimp only [P2]; exact_mod_cast h
    -- Theorem 1 slack and bounds on t and s = 2 + 2t
    have ht1 : P2 - 2 * (n : ℤ) ≤ ((n : ℤ) - 1) * t := theorem1_slack_bound hn2 hV
    have hge := two_pow_le_edgeSet_ncard hn2 hV
    have ht_ge_2L : 2 * (L : ℤ) ≤ t := by
      by_contra hlt
      have hle_t : t ≤ 2 * (L : ℤ) := by omega
      have hm1 : ((n : ℤ) - 1) * t ≤ ((n : ℤ) - 1) * (2 * (L : ℤ)) :=
        mul_le_mul_of_nonneg_left hle_t (by omega)
      have hLn : 2 * (n : ℤ) ≤ 2 * (L : ℤ) * (n : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by omega)
      have hL40Z : (40 : ℤ) ≤ (L : ℤ) := by omega
      have he1 : ((n : ℤ) - 1) * (2 * (L : ℤ)) = 2 * (L : ℤ) * (n : ℤ) - 2 * (L : ℤ) := by ring
      have he2 : 4 * (L : ℤ) * ((n : ℤ) + 1) = 4 * (L : ℤ) * (n : ℤ) + 4 * (L : ℤ) := by ring
      linarith only [ht1, hm1, hLn, hL40Z, hdom, he1, he2]
    let s : ℕ := 2 + 2 * (G.edgeSet.ncard - 2 ^ n)
    have hs1 : 1 ≤ s := by omega
    have hs_eq : (s : ℤ) = 2 + 2 * t := by
      unfold s t edgeExcess
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hge]
      push_cast; ring
    have hs_up : ((n : ℤ) - 1) * (s : ℤ) ≤ 4 * P2 := by
      have h2n_le : 2 * (n : ℤ) ≤ P2 := by
        have h1 : 2 * n ≤ 4 * L * (n + 1) := by
          calc 2 * n ≤ 40 * (n + 1) := by omega
            _ ≤ 4 * L * (n + 1) := Nat.mul_le_mul_right (n + 1) (by omega)
        have h2 : 2 * (n : ℤ) ≤ 4 * (L : ℤ) * ((n : ℤ) + 1) := by exact_mod_cast h1
        linarith only [h2, hdom]
      have he : ((n : ℤ) - 1) * (s : ℤ) = 2 * (n : ℤ) - 2 + (2 * (n : ℤ) - 2) * t := by
        rw [hs_eq]; ring
      linarith only [he, hbig, h2n_le]
    have hs_dn : 2 * P2 - 2 * ((n : ℤ) + 1) ≤ ((n : ℤ) - 1) * (s : ℤ) := by
      have he : ((n : ℤ) - 1) * (s : ℤ) = 2 * (((n : ℤ) - 1) * t) + 2 * (n : ℤ) - 2 := by
        rw [hs_eq]; ring
      linarith only [he, ht1]
    -- Cut index j0 = n / 2 - n / L
    let M : ℕ := n / L
    have hdm : L * M + n % L = n := Nat.div_add_mod n L
    have hmlt : n % L < L := Nat.mod_lt n (by omega)
    have hLM_dn : n - L < L * M := by omega
    have hLM_up : L * M ≤ n := by omega
    have hM_ge64 : 64 ≤ M := by
      by_contra hlt
      have hm : L * M ≤ L * 63 := Nat.mul_le_mul_left L (by omega)
      omega
    have h40M_le : 40 * M ≤ L * M := Nat.mul_le_mul_right M hL40
    have hM_le : 2 * M < n / 2 := by omega
    let j0 : ℕ := n / 2 - M
    have hj0_lt : 2 * j0 < n := by omega
    have hj0_le : 2 * j0 ≤ n := by omega
    have hLM2 : (n : ℤ) ≤ 2 * (L : ℤ) * (M : ℤ) := by
      have hL_le_LM : L ≤ L * M := Nat.le_mul_of_pos_right L (by omega)
      have hnat : n ≤ 2 * (L * M) := by omega
      have hZ : (n : ℤ) ≤ ((2 * (L * M) : ℕ) : ℤ) := by exact_mod_cast hnat
      push_cast at hZ; linarith only [hZ]
    -- Chebyshev tail: 2 * L * B(n, j0) ≤ P2
    have hcheb : ((n : ℤ) - 2 * (j0 : ℤ)) ^ 2 * (hammingBallSize n j0 : ℤ) ≤ (n : ℤ) * P2 :=
      chebyshev_hammingBall_tail hj0_le
    have hgapZ : 2 * (M : ℤ) ≤ (n : ℤ) - 2 * (j0 : ℤ) := by omega
    have hn_le_Lgap : (n : ℤ) ≤ (L : ℤ) * ((n : ℤ) - 2 * (j0 : ℤ)) := by
      calc (n : ℤ) ≤ 2 * (L : ℤ) * (M : ℤ) := hLM2
        _ = (L : ℤ) * (2 * (M : ℤ)) := by ring
        _ ≤ (L : ℤ) * ((n : ℤ) - 2 * (j0 : ℤ)) :=
            mul_le_mul_of_nonneg_left hgapZ (by omega)
    have hsq_ge : (n : ℤ) ^ 2 ≤ (L : ℤ) ^ 2 * ((n : ℤ) - 2 * (j0 : ℤ)) ^ 2 := by
      have hmul := mul_le_mul hn_le_Lgap hn_le_Lgap (by omega)
        (le_trans (by omega : (0 : ℤ) ≤ n) hn_le_Lgap)
      have he1 : (n : ℤ) * (n : ℤ) = (n : ℤ) ^ 2 := by ring
      have he2 : ((L : ℤ) * ((n : ℤ) - 2 * (j0 : ℤ))) * ((L : ℤ) * ((n : ℤ) - 2 * (j0 : ℤ))) =
          (L : ℤ) ^ 2 * ((n : ℤ) - 2 * (j0 : ℤ)) ^ 2 := by ring
      linarith only [hmul, he1, he2]
    have hB_nn : 0 ≤ (hammingBallSize n j0 : ℤ) := Nat.cast_nonneg _
    have hn2B : (n : ℤ) ^ 2 * (hammingBallSize n j0 : ℤ) ≤
        (L : ℤ) ^ 2 * ((n : ℤ) * P2) := by
      calc (n : ℤ) ^ 2 * (hammingBallSize n j0 : ℤ)
          ≤ (L : ℤ) ^ 2 * ((n : ℤ) - 2 * (j0 : ℤ)) ^ 2 *
              (hammingBallSize n j0 : ℤ) := mul_le_mul_of_nonneg_right hsq_ge hB_nn
        _ = (L : ℤ) ^ 2 * (((n : ℤ) - 2 * (j0 : ℤ)) ^ 2 *
              (hammingBallSize n j0 : ℤ)) := by ring
        _ ≤ (L : ℤ) ^ 2 * ((n : ℤ) * P2) :=
            mul_le_mul_of_nonneg_left hcheb (sq_nonneg _)
    have hnB : (n : ℤ) * (hammingBallSize n j0 : ℤ) ≤ (L : ℤ) ^ 2 * P2 := by
      apply le_of_mul_le_mul_left _ (show (0 : ℤ) < n by omega)
      have he1 : (n : ℤ) * ((n : ℤ) * (hammingBallSize n j0 : ℤ)) =
          (n : ℤ) ^ 2 * (hammingBallSize n j0 : ℤ) := by ring
      have he2 : (n : ℤ) * ((L : ℤ) ^ 2 * P2) = (L : ℤ) ^ 2 * ((n : ℤ) * P2) := by ring
      linarith only [hn2B, he1, he2]
    have h2L3 : 2 * (L : ℤ) ^ 3 ≤ (n : ℤ) := by
      have h64 : 64 * (L : ℤ) ^ 3 ≤ (n : ℤ) := by exact_mod_cast hn
      have hL3_nn : (0 : ℤ) ≤ (L : ℤ) ^ 3 := by positivity
      linarith only [h64, hL3_nn]
    have h2LB : 2 * (L : ℤ) * (hammingBallSize n j0 : ℤ) ≤ P2 := by
      apply le_of_mul_le_mul_left _ (show (0 : ℤ) < (L : ℤ) ^ 2 by positivity)
      have hm := mul_le_mul_of_nonneg_right h2L3 hB_nn
      have he1 : (L : ℤ) ^ 2 * (2 * (L : ℤ) * (hammingBallSize n j0 : ℤ)) =
          2 * (L : ℤ) ^ 3 * (hammingBallSize n j0 : ℤ) := by ring
      linarith only [hm, hnB, he1]
    -- Window width i1 = n - 1 - 2 * j0
    let i1 : ℕ := n - 1 - 2 * j0
    have h2LM_3 : 2 * (L : ℤ) * (M : ℤ) + (L : ℤ) ≤ 3 * ((n : ℤ) - 1) := by
      have h1 : L ≤ L * M := Nat.le_mul_of_pos_right L (by omega)
      have h2 : 2 * (L * M) + L ≤ 3 * (n - 1) := by omega
      have hZ : ((2 * (L * M) + L : ℕ) : ℤ) ≤ ((3 * (n - 1) : ℕ) : ℤ) := by exact_mod_cast h2
      have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (by omega)
      push_cast at hZ; rw [hn1] at hZ; linarith only [hZ]
    have hLi1s : (L : ℤ) * (i1 : ℤ) * (s : ℤ) ≤ 12 * P2 := by
      apply le_of_mul_le_mul_left _ (show (0 : ℤ) < (n : ℤ) - 1 by omega)
      have hi1Z : (i1 : ℤ) ≤ 2 * (M : ℤ) + 1 := by omega
      have hLi : (L : ℤ) * (i1 : ℤ) ≤ 2 * (L : ℤ) * (M : ℤ) + (L : ℤ) := by
        have hm := mul_le_mul_of_nonneg_left hi1Z (show (0 : ℤ) ≤ L by omega)
        have he : (L : ℤ) * (2 * (M : ℤ) + 1) = 2 * (L : ℤ) * (M : ℤ) + (L : ℤ) := by ring
        linarith only [hm, he]
      have hLi3 : (L : ℤ) * (i1 : ℤ) ≤ 3 * ((n : ℤ) - 1) := le_trans hLi h2LM_3
      have hm := mul_le_mul hLi3 hs_up (mul_nonneg (by omega) (by omega)) (by omega)
      have he1 : ((n : ℤ) - 1) * ((L : ℤ) * (i1 : ℤ) * (s : ℤ)) =
          ((L : ℤ) * (i1 : ℤ)) * (((n : ℤ) - 1) * (s : ℤ)) := by ring
      have he2 : ((n : ℤ) - 1) * (12 * P2) = (3 * ((n : ℤ) - 1)) * (4 * P2) := by ring
      linarith only [hm, he1, he2]
    -- Lower bound on A and upper bound on D
    let A : ℤ := P2 - 2 * (hammingBallSize n j0 : ℤ) - (i1 : ℤ) * (s : ℤ)
    have hLA : ((L : ℤ) - 13) * P2 ≤ (L : ℤ) * A := by
      have he1 : (L : ℤ) * A = (L : ℤ) * P2 -
          (2 * (L : ℤ) * (hammingBallSize n j0 : ℤ)) - ((L : ℤ) * (i1 : ℤ) * (s : ℤ)) := by
        dsimp only [A]; ring
      have he2 : ((L : ℤ) - 13) * P2 = (L : ℤ) * P2 - P2 - 12 * P2 := by ring
      linarith only [he1, he2, h2LB, hLi1s]
    have hL13_pos : 0 ≤ ((L : ℤ) - 13) * P2 := mul_nonneg (by omega) (le_of_lt hP2_pos)
    have hA_nn : 0 ≤ A := by
      apply le_of_mul_le_mul_left _ (show (0 : ℤ) < L by omega)
      linarith only [hLA, hL13_pos, mul_zero (L : ℤ)]
    have h2LMs : 2 * (L : ℤ) * (M : ℤ) * (s : ℤ) ≤ 12 * P2 := by
      apply le_of_mul_le_mul_left _ (show (0 : ℤ) < (n : ℤ) - 1 by omega)
      have hL0 : (0 : ℤ) ≤ L := by omega
      have hLM3 : 2 * (L : ℤ) * (M : ℤ) ≤ 3 * ((n : ℤ) - 1) := by linarith only [h2LM_3, hL0]
      have hm := mul_le_mul hLM3 hs_up (mul_nonneg (by omega) (by omega)) (by omega)
      have he1 : ((n : ℤ) - 1) * (2 * (L : ℤ) * (M : ℤ) * (s : ℤ)) =
          (2 * (L : ℤ) * (M : ℤ)) * (((n : ℤ) - 1) * (s : ℤ)) := by ring
      have he2 : ((n : ℤ) - 1) * (12 * P2) = (3 * ((n : ℤ) - 1)) * (4 * P2) := by ring
      linarith only [hm, he1, he2]
    have hLj0s : ((L : ℤ) - 7) * P2 ≤ (L : ℤ) * (j0 : ℤ) * (s : ℤ) := by
      have h2j0_ge : (n : ℤ) - 1 - 2 * (M : ℤ) ≤ 2 * (j0 : ℤ) := by omega
      have h1 := mul_le_mul_of_nonneg_right h2j0_ge (show 0 ≤ (L : ℤ) * (s : ℤ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left hs_dn (show (0 : ℤ) ≤ L by omega)
      have h3 : (0 : ℤ) ≤ 2 * (L : ℤ) * ((n : ℤ) + 1) := by positivity
      have he1 : ((n : ℤ) - 1 - 2 * (M : ℤ)) * ((L : ℤ) * (s : ℤ)) =
          (L : ℤ) * (((n : ℤ) - 1) * (s : ℤ)) - 2 * (L : ℤ) * (M : ℤ) * (s : ℤ) := by ring
      have he2 : 2 * (j0 : ℤ) * ((L : ℤ) * (s : ℤ)) = 2 * ((L : ℤ) * (j0 : ℤ) * (s : ℤ)) := by ring
      have he3 : (L : ℤ) * (2 * P2 - 2 * ((n : ℤ) + 1)) =
          2 * (L : ℤ) * P2 - 2 * (L : ℤ) * ((n : ℤ) + 1) := by ring
      have he4 : 2 * (((L : ℤ) - 7) * P2) = 2 * (L : ℤ) * P2 - 14 * P2 := by ring
      have hdom' : 4 * (L : ℤ) * ((n : ℤ) + 1) = 2 * (2 * (L : ℤ) * ((n : ℤ) + 1)) := by ring
      linarith only [h1, h2, h3, h2LMs, hdom, hP2_pos, he1, he2, he3, he4, hdom']
    let D : ℤ := max 0 (A - (j0 : ℤ) * (s : ℤ))
    have hA_le_P2 : A ≤ P2 := by
      dsimp only [A]
      have h1 : 0 ≤ 2 * (hammingBallSize n j0 : ℤ) := by positivity
      have h2 : 0 ≤ (i1 : ℤ) * (s : ℤ) := by positivity
      linarith only [h1, h2]
    have hLD : (L : ℤ) * D ≤ 7 * P2 := by
      dsimp only [D]
      rcases le_total 0 (A - (j0 : ℤ) * (s : ℤ)) with hle | hle
      · rw [max_eq_right hle]
        have hm := mul_le_mul_of_nonneg_left hA_le_P2 (show (0 : ℤ) ≤ L by omega)
        have he1 : (L : ℤ) * (A - (j0 : ℤ) * (s : ℤ)) =
            (L : ℤ) * A - (L : ℤ) * (j0 : ℤ) * (s : ℤ) := by ring
        have he2 : ((L : ℤ) - 7) * P2 = (L : ℤ) * P2 - 7 * P2 := by ring
        linarith only [hm, hLj0s, he1, he2]
      · rw [max_eq_left hle, mul_zero]
        positivity
    -- Combine with ballCapDelta_lower_of_j0 and Theorem 4
    have hdelta : A ^ 2 - D ^ 2 ≤ 2 * (s : ℤ) * ballCapDelta n s :=
      ballCapDelta_lower_of_j0 (n := n) (s := s) (j0 := j0) hs1 hj0_lt hA_nn
    have hL2delta : ((L : ℤ) - 26) * P2 ^ 2 ≤ (L : ℤ) * (2 * (s : ℤ) * ballCapDelta n s) := by
      apply le_of_mul_le_mul_left _ (show (0 : ℤ) < L by omega)
      have hsqA := mul_le_mul hLA hLA hL13_pos (le_trans hL13_pos hLA)
      have hLD_nn : 0 ≤ (L : ℤ) * D := mul_nonneg (by omega) (le_max_left _ _)
      have hsqD := mul_le_mul hLD hLD hLD_nn (by positivity)
      have hmulL2 := mul_le_mul_of_nonneg_left hdelta (sq_nonneg (L : ℤ))
      have h120 : (0 : ℤ) ≤ 120 * P2 ^ 2 := by positivity
      have he1 : (((L : ℤ) - 13) * P2) * (((L : ℤ) - 13) * P2) =
          (L : ℤ) * (((L : ℤ) - 26) * P2 ^ 2) + 49 * P2 ^ 2 + 120 * P2 ^ 2 := by ring
      have he2 : ((L : ℤ) * A) * ((L : ℤ) * A) = (L : ℤ) ^ 2 * A ^ 2 := by ring
      have he3 : ((L : ℤ) * D) * ((L : ℤ) * D) = (L : ℤ) ^ 2 * D ^ 2 := by ring
      have he4 : (7 * P2) * (7 * P2) = 49 * P2 ^ 2 := by ring
      have he5 : (L : ℤ) ^ 2 * (A ^ 2 - D ^ 2) = (L : ℤ) ^ 2 * A ^ 2 - (L : ℤ) ^ 2 * D ^ 2 := by
        ring
      have he6 : (L : ℤ) * ((L : ℤ) * (2 * (s : ℤ) * ballCapDelta n s)) =
          (L : ℤ) ^ 2 * (2 * (s : ℤ) * ballCapDelta n s) := by ring
      linarith only [hsqA, hsqD, hmulL2, h120, he1, he2, he3, he4, he5, he6]
    have ht4 : 2 * t * ballCapDelta n s ≤ P2 * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ))) :=
      theorem4_thin_levels hn2 hV
    have ht_nn : 0 ≤ 2 * t := by
      have : (0 : ℤ) ≤ 2 * L := by omega
      linarith only [ht_ge_2L, this]
    have hstep_t : 2 * t * (((L : ℤ) - 26) * P2 ^ 2) ≤
        2 * (L : ℤ) * (s : ℤ) * P2 * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ))) := by
      have hm1 := mul_le_mul_of_nonneg_left ht4 (show 0 ≤ 2 * (L : ℤ) * (s : ℤ) by positivity)
      have hm2 := mul_le_mul_of_nonneg_left hL2delta ht_nn
      have he1 : 2 * (L : ℤ) * (s : ℤ) * (2 * t * ballCapDelta n s) =
          2 * t * ((L : ℤ) * (2 * (s : ℤ) * ballCapDelta n s)) := by ring
      have he2 : 2 * (L : ℤ) * (s : ℤ) * (P2 * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ)))) =
          2 * (L : ℤ) * (s : ℤ) * P2 * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ))) := by ring
      linarith only [hm1, hm2, he1, he2]
    have hcancelP2' : 2 * t * ((L : ℤ) - 26) * P2 ≤
        2 * (L : ℤ) * (s : ℤ) * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ))) := by
      apply le_of_mul_le_mul_left _ hP2_pos
      have he1 : P2 * (2 * t * ((L : ℤ) - 26) * P2) =
          2 * t * (((L : ℤ) - 26) * P2 ^ 2) := by ring
      have he2 : P2 * (2 * (L : ℤ) * (s : ℤ) * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ)))) =
          2 * (L : ℤ) * (s : ℤ) * P2 * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ))) := by ring
      linarith only [hstep_t, he1, he2]
    have hts_cmp : ((L : ℤ) - 28) * (s : ℤ) ≤ 2 * t * ((L : ℤ) - 26) := by
      have hL0 : (0 : ℤ) ≤ L := by omega
      have he : 2 * t * ((L : ℤ) - 26) - ((L : ℤ) - 28) * (2 + 2 * t) =
          4 * t - 2 * (L : ℤ) + 56 := by ring
      rw [hs_eq]
      linarith only [ht_ge_2L, hL0, he]
    have hstep_s : ((L : ℤ) - 28) * P2 ≤
        2 * (L : ℤ) * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ))) := by
      apply le_of_mul_le_mul_left _ (show (0 : ℤ) < s by omega)
      have hm := mul_le_mul_of_nonneg_right hts_cmp (le_of_lt hP2_pos)
      have he1 : (s : ℤ) * (((L : ℤ) - 28) * P2) = ((L : ℤ) - 28) * (s : ℤ) * P2 := by ring
      have he2 : (s : ℤ) * (2 * (L : ℤ) * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ)))) =
          2 * (L : ℤ) * (s : ℤ) * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ))) := by ring
      linarith only [hm, hcancelP2', he1, he2]
    have h4Ln : 4 * (L : ℤ) * (n : ℤ) ≤ P2 := by
      have h4L0 : (0 : ℤ) ≤ 4 * L := by omega
      have he : 4 * (L : ℤ) * ((n : ℤ) + 1) = 4 * (L : ℤ) * (n : ℤ) + 4 * (L : ℤ) := by ring
      linarith only [hdom, h4L0, he]
    have he_final : 2 * (L : ℤ) * (((n : ℤ) - 1) * t - (P2 - 2 * (n : ℤ))) =
        2 * (L : ℤ) * ((n : ℤ) - 1) * t - 2 * (L : ℤ) * P2 + 4 * (L : ℤ) * (n : ℤ) := by ring
    have he_lhs : (3 * (L : ℤ) - 30) * P2 = ((L : ℤ) - 28) * P2 + 2 * (L : ℤ) * P2 - 2 * P2 := by
      ring
    linarith only [hstep_s, h4Ln, hP2_pos, he_final, he_lhs]

/-- **Theorem 5 (`bound-2.md` Steps 28–30, Asymptotic Second-Term Coefficient `3/2`)**:
`liminf_{n → ∞} (f(n) - 2^n)(n - 1) / 2^n ≥ 3/2`, formalized unconditionally over `ℚ`:
for every `ε > 0`, there exists `N` such that for all `n ≥ N`,
`(3/2 - ε) * 2^n ≤ (f n - 2^n) * (n - 1)`. -/
theorem theorem5_asymptotic_three_halves :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((3 : ℚ) / 2 - ε) * (2 : ℚ) ^ n ≤ ((f n : ℚ) - (2 : ℚ) ^ n) * ((n : ℚ) - 1) := by
  intro ε hε
  let L : ℕ := max 40 (⌈(15 : ℚ) / ε⌉.toNat + 1)
  have hL40 : 40 ≤ L := Nat.le_max_left _ _
  have hL_gt : (15 : ℚ) / ε < (L : ℚ) := by
    have hpos : (0 : ℚ) < (15 : ℚ) / ε := div_pos (by norm_num) hε
    have hc0 : (0 : ℤ) ≤ ⌈(15 : ℚ) / ε⌉ := Int.ceil_nonneg (le_of_lt hpos)
    have hle : ⌈(15 : ℚ) / ε⌉.toNat + 1 ≤ L := Nat.le_max_right _ _
    have h1 : (15 : ℚ) / ε ≤ (⌈(15 : ℚ) / ε⌉ : ℚ) := Int.le_ceil _
    have h2 : (⌈(15 : ℚ) / ε⌉ : ℚ) = (⌈(15 : ℚ) / ε⌉.toNat : ℚ) := by
      exact_mod_cast (Int.toNat_of_nonneg hc0).symm
    have h3 : (⌈(15 : ℚ) / ε⌉.toNat : ℚ) + 1 ≤ (L : ℚ) := by exact_mod_cast hle
    linarith
  have h15_le : (15 : ℚ) / (L : ℚ) ≤ ε := by
    have hLpos : (0 : ℚ) < (L : ℚ) := by exact_mod_cast (show 0 < L by omega)
    rw [div_le_iff₀ hLpos]
    have hdiv := (div_lt_iff₀ hε).1 hL_gt
    linarith
  refine ⟨64 * L ^ 3, fun n hn => ?_⟩
  obtain ⟨G, hDec, hV, he⟩ := Nat.sInf_mem (f_set_nonempty n)
  let _ := hDec
  rw [edgeCount_eq_ncard] at he
  have hZ := theorem5_int_step hL40 hn hV
  unfold edgeExcess at hZ
  rw [he] at hZ
  have hQ : (((3 * (L : ℤ) - 30) * (2 : ℤ) ^ n : ℤ) : ℚ) ≤
      ((2 * (L : ℤ) * ((n : ℤ) - 1) * ((f n : ℤ) - (2 : ℤ) ^ n) : ℤ) : ℚ) := by
    exact_mod_cast hZ
  push_cast at hQ
  have hL_posQ : (0 : ℚ) < 2 * (L : ℚ) := by
    have : (0 : ℚ) < (L : ℚ) := by exact_mod_cast (show 0 < L by omega)
    linarith
  have hdiv : ((3 : ℚ) / 2 - (15 : ℚ) / (L : ℚ)) * (2 : ℚ) ^ n ≤
      ((f n : ℚ) - (2 : ℚ) ^ n) * ((n : ℚ) - 1) := by
    apply le_of_mul_le_mul_left _ hL_posQ
    have h1 : (2 * (L : ℚ)) * (((3 : ℚ) / 2 - (15 : ℚ) / (L : ℚ)) * (2 : ℚ) ^ n) =
        (3 * (L : ℚ) - 30) * (2 : ℚ) ^ n := by
      have hLne : (L : ℚ) ≠ 0 := by linarith only [hL_posQ]
      field_simp [hLne]
      ring
    have h2 : (2 * (L : ℚ)) * (((f n : ℚ) - (2 : ℚ) ^ n) * ((n : ℚ) - 1)) =
        2 * (L : ℚ) * ((n : ℚ) - 1) * ((f n : ℚ) - (2 : ℚ) ^ n) := by ring
    linarith only [h1, h2, hQ]
  have hpow_nn : (0 : ℚ) ≤ (2 : ℚ) ^ n := by positivity
  have heps : ((3 : ℚ) / 2 - ε) * (2 : ℚ) ^ n ≤
      ((3 : ℚ) / 2 - (15 : ℚ) / (L : ℚ)) * (2 : ℚ) ^ n :=
    mul_le_mul_of_nonneg_right (by linarith only [h15_le]) hpow_nn
  linarith only [heps, hdiv]

end


/-! ## Section 5: Parity Balls, Half-Step Chain, and Antipodal Cap (`bound-4..9`) -/

/-- Multiplicative O(k) binomial coefficient evaluator for fast kernel reduction. -/
def fastChoose (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => fastChoose n k * (n - k) / (k + 1)

theorem fastChoose_eq_choose (n k : ℕ) : fastChoose n k = n.choose k := by
  induction k with
  | zero => simp [fastChoose]
  | succ k ih =>
    simp only [fastChoose, ih]
    have h := Nat.choose_succ_right_eq n k
    have hdiv := congrArg (· / (k + 1)) h
    simpa [Nat.mul_div_cancel _ (Nat.succ_pos k)] using hdiv.symm

noncomputable section

/-- `P_k(w)`: number of vertices at distance `j ≤ k` from `w` in `G` with `j ≡ k (mod 2)`
(`bound-4.md` Lemma 7). -/
def parityBallCard {n : ℕ} (G : SimpleGraph (CubeVertex n)) (w : CubeVertex n) (k : ℕ) : ℕ :=
  ∑ j ∈ range (k + 1), if j % 2 = k % 2 then (levelSet G w j).card else 0

/-- `Bp(n, k)`: number of cube strings within Hamming distance `k` of `w` with distance `≡ k (mod 2)`
(`bound-4.md` Lemma 7). -/
def hammingParityBall (n k : ℕ) : ℕ :=
  ∑ j ∈ range (k + 1), if j % 2 = k % 2 then n.choose j else 0

/-- `pg_k(w) = Bp(n, k) - P_k(w)`: parity-ball deficit at radius `k` (`bound-4.md` Lemma 8). -/
def parityGap {n : ℕ} (G : SimpleGraph (CubeVertex n)) (w : CubeVertex n) (k : ℕ) : ℤ :=
  (hammingParityBall n k : ℤ) - (parityBallCard G w k : ℤ)

theorem parityBallCard_eq_filter {n : ℕ} (G : SimpleGraph (CubeVertex n))
    (w : CubeVertex n) (k : ℕ) :
    parityBallCard G w k =
      (univ.filter fun u => G.dist w u < k + 1 ∧ G.dist w u % 2 = k % 2).card := by
  have h1 : ∀ j, (if j % 2 = k % 2 then ((levelSet G w j).card : ℤ) else 0) =
      ∑ u ∈ levelSet G w j, (if G.dist w u % 2 = k % 2 then (1 : ℤ) else 0) := by
    intro j
    have he : ∑ u ∈ levelSet G w j, (if G.dist w u % 2 = k % 2 then (1 : ℤ) else 0) =
        ∑ _u ∈ levelSet G w j, (if j % 2 = k % 2 then (1 : ℤ) else 0) :=
      Finset.sum_congr rfl fun u hu => by rw [mem_levelSet.1 hu]
    rw [he]
    by_cases hj : j % 2 = k % 2 <;> simp [hj]
  have hZ : ((parityBallCard G w k : ℕ) : ℤ) =
      (((univ.filter fun u => G.dist w u < k + 1 ∧ G.dist w u % 2 = k % 2).card : ℕ) : ℤ) := by
    unfold parityBallCard
    rw [Nat.cast_sum, Finset.sum_congr rfl fun j _ => by push_cast; exact h1 j, levels_sum]
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hlt : G.dist w u < k + 1 <;> by_cases hp : G.dist w u % 2 = k % 2 <;> simp [hlt, hp]
  exact_mod_cast hZ

theorem hammingParityBall_eq_filter {n : ℕ} (w : CubeVertex n) (k : ℕ) :
    hammingParityBall n k =
      (univ.filter fun u => hammingDist w u < k + 1 ∧ hammingDist w u % 2 = k % 2).card := by
  have h := parityBallCard_eq_filter (Q n) w k
  have hd : ∀ u, (Q n).dist w u = hammingDist w u := Q_dist_eq_hammingDist w
  simp_rw [hd] at h
  rw [← h]
  unfold hammingParityBall parityBallCard
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : (levelSet (Q n) w j).card = n.choose j := by
    rw [← card_hamming_sphere w j]
    congr 1; ext u
    simp [levelSet, hd]
  rw [hs]

/-- **Lemma 7 (`bound-4.md` Step 37, Parity-Ball Bound)**:
For every vertex `w` and radius `k`, `P_k(w) ≤ Bp(n, k)` (equivalently `0 ≤ pg_k(w)`). -/
theorem lemma7_parityBall_le {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (w : CubeVertex n) (k : ℕ) :
    parityBallCard G w k ≤ hammingParityBall n k := by
  rw [parityBallCard_eq_filter, hammingParityBall_eq_filter w k]
  refine Finset.card_le_card fun u hu => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  have hd := dist_hamming hG hc w u
  omega

theorem parityGap_nonneg {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (w : CubeVertex n) (k : ℕ) :
    0 ≤ parityGap G w k := by
  unfold parityGap
  have h := lemma7_parityBall_le hG hc w k
  omega

/-- **Lemma 7 (`bound-4.md` Step 37, Equality at Top Radii `n - 1` and `n`)**:
For `n ≥ 1` and `k ∈ {n - 1, n}`, `P_k(w) = Bp(n, k) = 2^(n-1)`, so `pg_k(w) = 0`. -/
theorem lemma7_parityBall_eq_top {n : ℕ} (hn : 1 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (w : CubeVertex n) {k : ℕ}
    (hk : k = n - 1 ∨ k = n) :
    parityBallCard G w k = 2 ^ (n - 1) ∧
      hammingParityBall n k = 2 ^ (n - 1) ∧
      parityGap G w k = 0 := by
  have hc := connected_of_ediam hD
  have hP : parityBallCard G w k = 2 ^ (n - 1) := by
    rw [parityBallCard_eq_filter]
    have heq : (univ.filter fun u => G.dist w u < k + 1 ∧ G.dist w u % 2 = k % 2) =
        univ.filter (fun u => hammingDist w u % 2 = k % 2) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hd := dist_hamming hG hc w u
      have hle := dist_le_of_ediam hD w u
      rcases hk with rfl | rfl <;> omega
    rw [heq]
    exact card_hamming_parity hn w (k % 2) (Nat.mod_lt _ (by norm_num))
  have hB : hammingParityBall n k = 2 ^ (n - 1) := by
    rw [hammingParityBall_eq_filter w k]
    have heq : (univ.filter fun u => hammingDist w u < k + 1 ∧ hammingDist w u % 2 = k % 2) =
        univ.filter (fun u => hammingDist w u % 2 = k % 2) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hle := hammingDist_le_n w u
      rcases hk with rfl | rfl <;> omega
    rw [heq]
    exact card_hamming_parity hn w (k % 2) (Nat.mod_lt _ (by norm_num))
  refine ⟨hP, hB, ?_⟩
  unfold parityGap
  rw [hP, hB, sub_self]

theorem parityGap_zero {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hc : G.Connected) (w : CubeVertex n) :
    parityGap G w 0 = 0 := by
  unfold parityGap hammingParityBall parityBallCard
  simp [card_levelSet_zero hc w]

theorem parityGap_one {n : ℕ} {G : SimpleGraph (CubeVertex n)} (w : CubeVertex n) :
    parityGap G w 1 = (n : ℤ) - 2 - excess G w := by
  unfold parityGap hammingParityBall parityBallCard
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have h0 : ¬(0 % 2 = 1 % 2) := by decide
  simp only [h0, ↓reduceIte, Nat.choose_one_right]
  push_cast
  rw [card_levelSet_one w]
  ring

theorem ballGap_eq_parityGap_add {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (w : CubeVertex n) {k : ℕ} (hk : 1 ≤ k) :
    ballGap G w k = parityGap G w k + parityGap G w (k - 1) := by
  have hgb : graphBallCard G w k = parityBallCard G w k + parityBallCard G w (k - 1) := by
    unfold graphBallCard parityBallCard
    have he : k - 1 + 1 = k := by omega
    rw [he]
    have hsplit : ∑ j ∈ range k,
        ((if j % 2 = k % 2 then (levelSet G w j).card else 0) +
          (if j % 2 = (k - 1) % 2 then (levelSet G w j).card else 0)) =
        ∑ j ∈ range k, (levelSet G w j).card := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> omega
    rw [Finset.sum_range_succ _ k, Finset.sum_range_succ (fun j => if j % 2 = k % 2 then
      (levelSet G w j).card else 0) k]
    simp only [↓reduceIte]
    rw [← hsplit, Finset.sum_add_distrib]
    omega
  have hhb : hammingBallSize n k = hammingParityBall n k + hammingParityBall n (k - 1) := by
    unfold hammingBallSize hammingParityBall
    have he : k - 1 + 1 = k := by omega
    rw [he]
    have hsplit : ∑ j ∈ range k,
        ((if j % 2 = k % 2 then n.choose j else 0) +
          (if j % 2 = (k - 1) % 2 then n.choose j else 0)) =
        ∑ j ∈ range k, n.choose j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> omega
    rw [Finset.sum_range_succ _ k, Finset.sum_range_succ (fun j => if j % 2 = k % 2 then
      n.choose j else 0) k]
    simp only [↓reduceIte]
    rw [← hsplit, Finset.sum_add_distrib]
    omega
  unfold ballGap parityGap
  rw [hgb, hhb]
  push_cast
  ring

/-- Step 38 (`bound-4.md`):
`δ(w) = 2 (n - 2 - x_w) + 2 ∑_{k=2}^{n-2} pg_k(w)` for `n ≥ 3`. -/
theorem distGap_eq_sum_parityGap {n : ℕ} (hn : 3 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (w : CubeVertex n) :
    distGap G w =
      2 * ((n : ℤ) - 2 - excess G w) + 2 * ∑ k ∈ Ico 2 (n - 1), parityGap G w k := by
  have hc := connected_of_ediam hD
  rw [distGap_eq_sum_ballGap (by omega) hD w]
  have hg0 : ballGap G w 0 = 0 := by
    unfold ballGap hammingBallSize graphBallCard
    simp [card_levelSet_zero hc w]
  have hpg0 := parityGap_zero hc w
  have hpg1 := parityGap_one (G := G) w
  have hpg_top := (lemma7_parityBall_eq_top (by omega) hG hD w (Or.inl rfl)).2.2
  have hsplit0 := Finset.sum_range_add_sum_Ico (fun k => ballGap G w k) (show 1 ≤ n by omega)
  simp only [Finset.range_one, Finset.sum_singleton, hg0, zero_add] at hsplit0
  rw [← hsplit0]
  have hsum_ico : ∑ k ∈ Ico 1 n, ballGap G w k =
      ∑ k ∈ Ico 1 n, parityGap G w k + ∑ k ∈ Ico 1 n, parityGap G w (k - 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k hk =>
      ballGap_eq_parityGap_add w (by simp only [Finset.mem_Ico] at hk; omega)
  rw [hsum_ico]
  have h1 : ∑ k ∈ Ico 1 n, parityGap G w k =
      parityGap G w 1 + ∑ k ∈ Ico 2 (n - 1), parityGap G w k + parityGap G w (n - 1) := by
    have e1 := Finset.sum_eq_sum_Ico_succ_bot (show 1 < n by omega) (fun k => parityGap G w k)
    have e2 := Finset.sum_Ico_succ_top (show 2 ≤ n - 1 by omega) (fun k => parityGap G w k)
    have en : n - 1 + 1 = n := by omega
    rw [en] at e2
    linarith
  have h2 : ∑ k ∈ Ico 1 n, parityGap G w (k - 1) =
      parityGap G w 0 + parityGap G w 1 + ∑ k ∈ Ico 2 (n - 1), parityGap G w k := by
    have hbij : ∑ k ∈ Ico 1 n, parityGap G w (k - 1) = ∑ j ∈ Ico 0 (n - 1), parityGap G w j := by
      refine Finset.sum_nbij' (fun k => k - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro k hk; simp only [Finset.mem_Ico] at hk; omega
      · intro j _; omega
      · intro _ _; rfl
    rw [hbij]
    have e1 := Finset.sum_eq_sum_Ico_succ_bot (show 0 < n - 1 by omega) (fun j => parityGap G w j)
    have e2 := Finset.sum_eq_sum_Ico_succ_bot (show 1 < n - 1 by omega) (fun j => parityGap G w j)
    linarith
  rw [h1, h2, hpg0, hpg1, hpg_top]
  ring

/-- Step 38 (`bound-4.md`): for `k ≥ 2`,
`|S_k(w)| = C(n, k) - pg_k(w) + pg_{k-2}(w)`. -/
theorem levelSet_card_eq_parityGap {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (w : CubeVertex n) {k : ℕ} (hk : 2 ≤ k) :
    ((levelSet G w k).card : ℤ) =
      (n.choose k : ℤ) - parityGap G w k + parityGap G w (k - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hmod : (m + 2) % 2 = m % 2 := by omega
  have hmod1 : ¬((m + 1) % 2 = m % 2) := by omega
  have hP : parityBallCard G w (m + 2) = parityBallCard G w m + (levelSet G w (m + 2)).card := by
    unfold parityBallCard
    simp only [hmod]
    rw [Finset.sum_range_succ _ (m + 2), Finset.sum_range_succ _ (m + 1)]
    simp [hmod, hmod1]
  have hB : hammingParityBall n (m + 2) = hammingParityBall n m + n.choose (m + 2) := by
    unfold hammingParityBall
    simp only [hmod]
    rw [Finset.sum_range_succ _ (m + 2), Finset.sum_range_succ _ (m + 1)]
    simp [hmod, hmod1]
  unfold parityGap
  have he : m + 2 - 2 = m := by omega
  rw [he, hP, hB]
  push_cast
  ring

private theorem hammingDist_add_weights_even {n : ℕ} (w u : CubeVertex n) :
    (hammingDist w u + hammingWeight w + hammingWeight u) % 2 = 0 := by
  have h1 : hammingDist w u = ∑ i : Fin n, (if w i ≠ u i then 1 else 0) :=
    hammingDist_eq_sum w u
  have h2 : hammingWeight w = ∑ i : Fin n, (if w i = true then 1 else 0) := by
    unfold hammingWeight; rw [Finset.card_filter]
  have h3 : hammingWeight u = ∑ i : Fin n, (if u i = true then 1 else 0) := by
    unfold hammingWeight; rw [Finset.card_filter]
  have hsum : hammingDist w u + hammingWeight w + hammingWeight u =
      2 * ∑ i : Fin n,
        (((if w i ≠ u i then 1 else 0) + (if w i = true then 1 else 0) +
          (if u i = true then 1 else 0)) / 2) := by
    rw [h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases w i <;> cases u i <;> decide
  omega

/-- **Lemma 17 (`bound-8.md` Step 70, Bipartite Distance-Parity Excess Conservation)**:
For every `n ≥ 1`, every valid spanning subgraph `G` of `Q_n`, every vertex `w`, and each
parity `r < 2`, the sum of degree excesses `x_u` at distance `≡ r (mod 2)` from `w` equals
`edgeExcess G = |E(G)| - 2^n`. -/
theorem lemma17_dist_parity_excess {n : ℕ} (hn : 1 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (w : CubeVertex n) (r : ℕ) (hr : r < 2) :
    ∑ u ∈ univ.filter (fun u : CubeVertex n => G.dist w u % 2 = r), excess G u =
      edgeExcess G := by
  let target := (hammingWeight w + r) % 2
  have ht : target < 2 := Nat.mod_lt _ (by norm_num)
  rw [← sum_excess_part hn hG target ht]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, target]
  have hd := (dist_hamming hG hc w u).2
  have hev := hammingDist_add_weights_even w u
  omega

theorem lemma17_levelExcess_parity {n : ℕ} (hn : 1 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hD : G.ediam = (n : ℕ∞)) (w : CubeVertex n) (r : ℕ) (hr : r < 2) :
    ∑ k ∈ range (n + 1), (if k % 2 = r then levelExcess G w k else 0) = edgeExcess G := by
  have hc := connected_of_ediam hD
  have h1 : ∀ k, (if k % 2 = r then levelExcess G w k else 0) =
      ∑ u ∈ levelSet G w k, (if G.dist w u % 2 = r then excess G u else 0) := by
    intro k
    have he : ∑ u ∈ levelSet G w k, (if G.dist w u % 2 = r then excess G u else 0) =
        ∑ u ∈ levelSet G w k, (if k % 2 = r then excess G u else 0) :=
      Finset.sum_congr rfl fun u hu => by rw [mem_levelSet.1 hu]
    rw [he]
    by_cases hk : k % 2 = r <;> simp [hk, levelExcess]
  rw [Finset.sum_congr rfl fun k _ => h1 k, levels_sum, ← lemma17_dist_parity_excess hn hG hc w r hr,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hlt : G.dist w u < n + 1 := Nat.lt_succ_of_le (dist_le_of_ediam hD w u)
  simp [hlt]

private theorem half_step_partial {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (w : CubeVertex n) :
    ∀ k : ℕ,
      ((parityBallCard G w (k + 1) : ℤ) - (parityBallCard G w k : ℤ) ≤
        1 + ∑ j ∈ range (k + 1), (if j % 2 = k % 2 then levelExcess G w j else 0)) ∧
      ((parityBallCard G w (k + 2) : ℤ) - (parityBallCard G w (k + 1) : ℤ) ≤
        1 + ∑ j ∈ range (k + 2), (if j % 2 = (k + 1) % 2 then levelExcess G w j else 0)) := by
  have hstep_ge1 : ∀ m : ℕ, 1 ≤ m →
      ((levelSet G w (m + 1)).card : ℤ) - (levelSet G w m).card ≤ levelExcess G w m := by
    intro m hm
    have hl := level_step hG hc w m
    have hm0 := extraParents_nonneg hc w hm
    have hm1 := extraParents_nonneg hc w (show 1 ≤ m + 1 by omega)
    linarith
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · unfold parityBallCard
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      have h01 : ¬(0 % 2 = 1 % 2) := by decide
      simp only [h01, ↓reduceIte]
      rw [card_levelSet_zero hc w]
      push_cast
      rw [card_levelSet_one w, levelExcess_zero hc w]
      linarith
    · unfold parityBallCard
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      have h02 : 0 % 2 = 2 % 2 := rfl
      have h12 : ¬(1 % 2 = 2 % 2) := by decide
      have h01 : ¬(0 % 2 = 1 % 2) := by decide
      simp only [h02, h12, h01, ↓reduceIte]
      rw [card_levelSet_zero hc w]
      push_cast
      have hs : ((levelSet G w 2).card : ℤ) - (levelSet G w 1).card ≤ levelExcess G w 1 :=
        hstep_ge1 1 le_rfl
      linarith
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hmod : (k + 3) % 2 = (k + 1) % 2 := by omega
    have hmod_ne : ¬((k + 2) % 2 = (k + 1) % 2) := by omega
    have hm2 : (k + 2) % 2 = k % 2 := by omega
    have hm1 : ¬((k + 1) % 2 = k % 2) := by omega
    have hP3 : parityBallCard G w (k + 3) =
        parityBallCard G w (k + 1) + (levelSet G w (k + 3)).card := by
      unfold parityBallCard
      have hk11 : k + 1 + 1 = k + 2 := rfl
      rw [hk11, Finset.sum_range_succ _ (k + 3), Finset.sum_range_succ _ (k + 2)]
      simp_rw [hmod]
      split_ifs; omega
    have hP2 : parityBallCard G w (k + 2) =
        parityBallCard G w k + (levelSet G w (k + 2)).card := by
      unfold parityBallCard
      rw [Finset.sum_range_succ _ (k + 2), Finset.sum_range_succ _ (k + 1)]
      simp_rw [hm2]
      split_ifs; omega
    have hsumX : ∑ j ∈ range (k + 3), (if j % 2 = (k + 2) % 2 then levelExcess G w j else 0) =
        ∑ j ∈ range (k + 1), (if j % 2 = k % 2 then levelExcess G w j else 0) +
          levelExcess G w (k + 2) := by
      rw [Finset.sum_range_succ _ (k + 2), Finset.sum_range_succ _ (k + 1)]
      simp_rw [hm2]
      split_ifs; ring
    have hs : ((levelSet G w (k + 3)).card : ℤ) - (levelSet G w (k + 2)).card ≤
        levelExcess G w (k + 2) := hstep_ge1 (k + 2) (by omega)
    have hprev := ih.1
    have ek2 : k + 1 + 1 = k + 2 := rfl
    have ek3 : k + 1 + 2 = k + 3 := rfl
    rw [ek2, ek3, hP3, hP2, hsumX]
    push_cast
    linarith

/-- **Lemma 18 (`bound-8.md` Step 71, The Half-Step Bound)**:
For `n ≥ 2`, every valid spanning subgraph `G` of `Q_n`, every vertex `w`, and `1 ≤ k ≤ n`,
`P_k(w) - P_{k-1}(w) ≤ t + 1`. -/
theorem lemma18_half_step {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hV : IsValidSpanningSubgraph n G) (w : CubeVertex n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (parityBallCard G w k : ℤ) - (parityBallCard G w (k - 1) : ℤ) ≤ edgeExcess G + 1 := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hp := (half_step_partial hG hc w m).1
  simp only [Nat.add_sub_cancel]
  have hsub : range (m + 1) ⊆ range (n + 1) := by
    intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
  have hle : ∑ j ∈ range (m + 1), (if j % 2 = m % 2 then levelExcess G w j else 0) ≤
      ∑ j ∈ range (n + 1), (if j % 2 = m % 2 then levelExcess G w j else 0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => ?_
    split_ifs
    · exact Finset.sum_nonneg fun u _ => excess_nonneg hn hG hD u
    · exact le_rfl
  rw [lemma17_levelExcess_parity (by omega) hG hD w (m % 2) (Nat.mod_lt _ (by norm_num))] at hle
  linarith

theorem hammingParityBall_sub {n : ℕ} (hn : 1 ≤ n) :
    ∀ k : ℕ,
      ((hammingParityBall n (k + 1) : ℤ) - (hammingParityBall n k : ℤ) =
        ((n - 1).choose (k + 1) : ℤ)) ∧
      ((hammingParityBall n (k + 2) : ℤ) - (hammingParityBall n (k + 1) : ℤ) =
        ((n - 1).choose (k + 2) : ℤ)) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · unfold hammingParityBall
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      have h01 : ¬(0 % 2 = 1 % 2) := by decide
      simp only [h01, ↓reduceIte, Nat.choose_zero_right, Nat.choose_one_right]
      push_cast; ring
    · unfold hammingParityBall
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      have h02 : 0 % 2 = 2 % 2 := rfl
      have h12 : ¬(1 % 2 = 2 % 2) := by decide
      have h01 : ¬(0 % 2 = 1 % 2) := by decide
      simp only [h02, h12, h01, ↓reduceIte, Nat.choose_zero_right, Nat.choose_one_right,
        Nat.choose_succ_succ]
      push_cast; ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hmod : (k + 3) % 2 = (k + 1) % 2 := by omega
    have hmod_ne : ¬((k + 2) % 2 = (k + 1) % 2) := by omega
    have hB3 : hammingParityBall (d + 1) (k + 3) =
        hammingParityBall (d + 1) (k + 1) + (d + 1).choose (k + 3) := by
      unfold hammingParityBall
      have hk11 : k + 1 + 1 = k + 2 := rfl
      rw [hk11, Finset.sum_range_succ _ (k + 3), Finset.sum_range_succ _ (k + 2)]
      simp_rw [hmod]
      split_ifs; omega
    have hpasc : (d + 1).choose (k + 3) = d.choose (k + 2) + d.choose (k + 3) :=
      Nat.choose_succ_succ d (k + 2)
    have hprev := ih.1
    have ek2 : k + 1 + 1 = k + 2 := rfl
    have ek3 : k + 1 + 2 = k + 3 := rfl
    rw [ek2, ek3, hB3, hpasc]
    push_cast
    linarith

/-- **Lemma 18 (`bound-8.md` Step 71, Parity-Gap Half-Step)**:
For `n ≥ 2` and `1 ≤ k ≤ n`, `pg_k(w) - pg_{k-1}(w) ≥ C(n - 1, k) - (t + 1)`. -/
theorem lemma18_parityGap_step {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hV : IsValidSpanningSubgraph n G) (w : CubeVertex n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((n - 1).choose k : ℤ) - (edgeExcess G + 1) ≤ parityGap G w k - parityGap G w (k - 1) := by
  have hs := lemma18_half_step hn hV w hk1 hkn
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hb := (hammingParityBall_sub (n := n) (by omega) m).1
  simp only [Nat.add_sub_cancel] at hs ⊢
  unfold parityGap
  linarith

/-- `p_k` (`bound-8.md` Lemma 19): the recursive half-step lower-bound chain on `pg_k(w)`. -/
def halfStepChain (n : ℕ) (x t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => (n : ℤ) - 2 - x
  | k + 2 => max 0 (halfStepChain n x t (k + 1) + (fastChoose (n - 1) (k + 2) : ℤ) - (t + 1))

/-- **Lemma 19 (`bound-8.md` Step 72)**:
At every vertex `w` of every valid spanning subgraph `G` of `Q_n` (`n ≥ 2`),
`halfStepChain n (excess G w) (edgeExcess G) k ≤ pg_k(w)` for all `k ≤ n`. -/
theorem lemma19_halfStepChain_le {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hV : IsValidSpanningSubgraph n G) (w : CubeVertex n) :
    ∀ k : ℕ, k ≤ n → halfStepChain n (excess G w) (edgeExcess G) k ≤ parityGap G w k := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  intro k
  induction k with
  | zero =>
    intro _
    simp [halfStepChain, parityGap_zero hc w]
  | succ k ih =>
    cases k with
    | zero =>
      intro _
      simp [halfStepChain, parityGap_one]
    | succ k =>
      intro hkn
      simp only [halfStepChain, fastChoose_eq_choose, max_le_iff]
      refine ⟨parityGap_nonneg hG hc w (k + 2), ?_⟩
      have hprev := ih (by omega)
      have hstep := lemma18_parityGap_step hn hV w (k := k + 2) (by omega) hkn
      have he : k + 2 - 1 = k + 1 := rfl
      rw [he] at hstep
      linarith

theorem halfStepChain_antitone_t (n : ℕ) (x : ℤ) {t1 t2 : ℤ} (ht : t1 ≤ t2) :
    ∀ k : ℕ, halfStepChain n x t2 k ≤ halfStepChain n x t1 k := by
  intro k
  induction k with
  | zero => simp [halfStepChain]
  | succ k ih =>
    cases k with
    | zero => simp [halfStepChain]
    | succ k =>
      simp only [halfStepChain]
      exact max_le_max le_rfl (by linarith)

/-- `μ = (n - 1) t - (2^n - 2n)`: mean value of `ψ` across the `2^n` vertices (`bound-9.md`). -/
def meanPsi (n : ℕ) (G : SimpleGraph (CubeVertex n)) : ℤ :=
  ((n : ℤ) - 1) * edgeExcess G - ((2 : ℤ) ^ n - 2 * (n : ℤ))

/-- `η_w(v) = d_G(v, w) + d_G(v, w̄) - n`: antipodal triangle detour (`bound-9.md` Lemma 20). -/
def antipodalDetour {n : ℕ} (G : SimpleGraph (CubeVertex n)) (w v : CubeVertex n) : ℤ :=
  (G.dist v w : ℤ) + (G.dist v (antipode w) : ℤ) - (n : ℤ)

theorem antipodalDetour_nonneg_and_even {n : ℕ} {G : SimpleGraph (CubeVertex n)}
    (hG : G ≤ Q n) (hc : G.Connected) (w v : CubeVertex n) :
    0 ≤ antipodalDetour G w v ∧ 2 ∣ antipodalDetour G w v := by
  have hd1 := dist_hamming hG hc v w
  have hd2 := dist_hamming hG hc v (antipode w)
  have hsum := hammingDist_antipode_right v w
  unfold antipodalDetour
  refine ⟨by omega, ?_⟩
  refine ⟨(((G.dist v w + G.dist v (antipode w) - n) / 2 : ℕ) : ℤ), ?_⟩
  omega

/-- **Lemma 20 (`bound-9.md` Step 75, Antipodal Pair Conservation Identity)**:
For every `n ≥ 2`, every valid spanning subgraph `G` of `Q_n`, and every vertex `w`,
`2 (M(w) + M(w̄)) + ∑_v x_v η_w(v) = 2 μ`, and in halved integer form
`M(w) + M(w̄) + ∑_v x_v (η_w(v) / 2) = μ`. -/
theorem lemma20_antipodal_identity {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hV : IsValidSpanningSubgraph n G) (w : CubeVertex n) :
    2 * (weightedExtra G w + weightedExtra G (antipode w)) +
        ∑ v : CubeVertex n, excess G v * antipodalDetour G w v =
      2 * meanPsi n G := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hpc1 := part_c hn hG hD w
  have hpc2 := part_c hn hG hD (antipode w)
  have hl1 := lSum_eq hD w
  have hl2 := lSum_eq hD (antipode w)
  have hpt : ∀ v : CubeVertex n,
      2 * ((((n - G.dist w v) / 2 : ℕ) : ℤ) + (((n - G.dist (antipode w) v) / 2 : ℕ) : ℤ)) =
        (n : ℤ) - antipodalDetour G w v -
          (if n % 2 = 1 then 1 else if G.dist w v % 2 = 1 then 2 else 0) := by
    intro v
    have hd1 := dist_le_of_ediam hD w v
    have hd2 := dist_le_of_ediam hD (antipode w) v
    have hp1 := (dist_hamming hG hc w v).2
    have hp2 := (dist_hamming hG hc (antipode w) v).2
    have hanti := hammingDist_antipode_left w v
    unfold antipodalDetour
    rw [@SimpleGraph.dist_comm _ G v w, @SimpleGraph.dist_comm _ G v (antipode w)]
    split_ifs <;> omega
  have h2L : 2 * (lSum G w + lSum G (antipode w)) =
      2 * ((n : ℤ) - 1) * edgeExcess G -
        ∑ v : CubeVertex n, excess G v * antipodalDetour G w v := by
    rw [hl1, hl2, ← Finset.sum_add_distrib, Finset.mul_sum]
    have hmul : ∀ v : CubeVertex n,
        2 * ((((n - G.dist w v) / 2 : ℕ) : ℤ) * excess G v +
          (((n - G.dist (antipode w) v) / 2 : ℕ) : ℤ) * excess G v) =
        excess G v * (n : ℤ) - excess G v * antipodalDetour G w v -
          excess G v * (if n % 2 = 1 then 1 else if G.dist w v % 2 = 1 then 2 else 0) := by
      intro v
      have hp := hpt v
      linear_combination excess G v * hp
    rw [Finset.sum_congr rfl fun v _ => hmul v, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_excess]
    have hpar_term : ∑ v : CubeVertex n,
        excess G v * (if n % 2 = 1 then (1 : ℤ) else if G.dist w v % 2 = 1 then 2 else 0) =
        2 * edgeExcess G := by
      by_cases hodd : n % 2 = 1
      · simp only [hodd, ↓reduceIte, mul_one]
        exact sum_excess
      · simp only [hodd, ↓reduceIte]
        have heq : ∑ v : CubeVertex n, excess G v * (if G.dist w v % 2 = 1 then (2 : ℤ) else 0) =
            2 * ∑ v ∈ univ.filter (fun v : CubeVertex n => G.dist w v % 2 = 1), excess G v := by
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          split_ifs <;> ring
        rw [heq, lemma17_dist_parity_excess (by omega) hG hc w 1 (by norm_num)]
    rw [hpar_term]
    ring
  have hpow := pow_eq_two_mul (show 1 ≤ n by omega)
  unfold meanPsi
  linarith

theorem lemma20_antipodal_identity_div2 {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hV : IsValidSpanningSubgraph n G) (w : CubeVertex n) :
    weightedExtra G w + weightedExtra G (antipode w) +
        ∑ v : CubeVertex n, excess G v * (antipodalDetour G w v / 2) =
      meanPsi n G := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hid := lemma20_antipodal_identity hn hV w
  have hev : ∑ v : CubeVertex n, excess G v * antipodalDetour G w v =
      2 * ∑ v : CubeVertex n, excess G v * (antipodalDetour G w v / 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨k, hk⟩ := (antipodalDetour_nonneg_and_even hG hc w v).2
    rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
    ring
  linarith

/-- **Antipodal Cap (`bound-9.md` Lemma 20)**:
At every vertex `w` of every valid spanning subgraph `G` of `Q_n` (`n ≥ 2`),
`0 ≤ M(w) ≤ μ` and `M(w) + M(w̄) ≤ μ`. -/
theorem antipodal_cap {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (CubeVertex n)}
    (hV : IsValidSpanningSubgraph n G) (w : CubeVertex n) :
    0 ≤ weightedExtra G w ∧
      weightedExtra G w ≤ meanPsi n G ∧
      weightedExtra G w + weightedExtra G (antipode w) ≤ meanPsi n G := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hMw := weightedExtra_nonneg hc w
  have hMa := weightedExtra_nonneg hc (antipode w)
  have hid := lemma20_antipodal_identity hn hV w
  have hsum_nn : 0 ≤ ∑ v : CubeVertex n, excess G v * antipodalDetour G w v :=
    Finset.sum_nonneg fun v _ =>
      mul_nonneg (excess_nonneg hn hG hD v) (antipodalDetour_nonneg_and_even hG hc w v).1
  refine ⟨hMw, by linarith, by linarith⟩

/-- `R'_n`: positive radii in `R_n` (`1 ≤ m ≤ n - 2` with `m ≡ n (mod 2)`). -/
def rSetPos (n : ℕ) : Finset ℕ :=
  (rSet n).filter fun m => 1 ≤ m

/-- Contract for a level-assignment recipe `κ : ℕ → ℕ` (`bound-5.md` Lemma 10). -/
def IsValidRecipe (n : ℕ) (κ : ℕ → ℕ) : Prop :=
  ∀ m ∈ rSetPos n, 2 ≤ κ m ∧ κ m ≤ m + 1

/-- `u_k`: number of radii `m ∈ R'_n` assigned to level `k` by recipe `κ`. -/
def recipeCount (n : ℕ) (κ : ℕ → ℕ) (k : ℕ) : ℤ :=
  ((rSetPos n).filter fun m => κ m = k).card

/-- `K / 2` (`bound-9.md` Step 76): constant term of `M(w)` under recipe `κ` at excess `x`. -/
def recipeHalfK (n : ℕ) (κ : ℕ → ℕ) (x : ℤ) : ℤ :=
  (if n % 2 = 0 then x else 0) +
    (∑ m ∈ rSetPos n, ((fastChoose n (κ m) : ℤ) - 2)) +
    recipeCount n κ 3 * ((n : ℤ) - 2 - x) -
    ((2 : ℤ) ^ (n - 1) - (n : ℤ))

/-- **Step 76 (`bound-9.md`, Lower Bound on `M(w)` from Any Valid Recipe `κ`)**:
For `n ≥ 4`, every valid spanning subgraph `G` of `Q_n`, every vertex `w`, and any valid
recipe `κ`,
`K/2 + ∑_{k=2}^{n-2} (u_{k+2} - u_k) pg_k(w) ≤ M(w)`. -/
theorem recipe_weightedExtra_lower_bound {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (CubeVertex n)} (hV : IsValidSpanningSubgraph n G)
    (w : CubeVertex n) (κ : ℕ → ℕ) (hκ : IsValidRecipe n κ) :
    recipeHalfK n κ (excess G w) +
        ∑ k ∈ Ico 2 (n - 1),
          (recipeCount n κ (k + 2) - recipeCount n κ k) * parityGap G w k ≤
      weightedExtra G w := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hc := connected_of_ediam hD
  have hpc := part_c (by omega) hG hD w
  -- Split lSum G w into m = 0 (when n even) and rSetPos n
  have hl_split : lSum G w =
      (if n % 2 = 0 then excess G w else 0) + ∑ m ∈ rSetPos n, ballExcess G w m := by
    unfold lSum rSetPos
    have hsplit := Finset.sum_filter_add_sum_filter_not (rSet n) (fun m => 1 ≤ m)
      (fun m => ballExcess G w m)
    rw [← hsplit]
    have h0set : (rSet n).filter (fun m => ¬1 ≤ m) = if n % 2 = 0 then {0} else ∅ := by
      ext m
      simp only [Finset.mem_filter, rSet, Finset.mem_range]
      by_cases hev : n % 2 = 0
      · simp only [hev, ↓reduceIte, Finset.mem_singleton]
        omega
      · simp only [hev, ↓reduceIte, Finset.notMem_empty, iff_false]
        omega
    rw [h0set]
    by_cases hev : n % 2 = 0
    · simp [hev, ballExcess, levelExcess_zero hc w, add_comm]
    · simp [hev]
  -- Lower bound each ballExcess G w m by s_{κ m} - 2
  have hterm : ∀ m ∈ rSetPos n,
      ((fastChoose n (κ m) : ℤ) - 2) - parityGap G w (κ m) + parityGap G w (κ m - 2) ≤
        ballExcess G w m := by
    intro m hm
    obtain ⟨h2, hle⟩ := hκ m hm
    have hcap := level_growth_bound hV w (k := κ m) (by omega)
    have hmon := ballExcess_mono (by omega) hG hD w (show κ m - 1 ≤ m by omega)
    have hlev := levelSet_card_eq_parityGap (G := G) w h2
    rw [← fastChoose_eq_choose] at hlev
    linarith
  have hsum_le : ∑ m ∈ rSetPos n,
      (((fastChoose n (κ m) : ℤ) - 2) - parityGap G w (κ m) + parityGap G w (κ m - 2)) ≤
      ∑ m ∈ rSetPos n, ballExcess G w m :=
    Finset.sum_le_sum hterm
  -- Group parityGap terms by fiber k = κ m ∈ Ico 2 n
  have hfib : ∀ f : ℕ → ℤ,
      ∑ m ∈ rSetPos n, f (κ m) = ∑ k ∈ Ico 2 n, recipeCount n κ k * f k := by
    intro f
    have hmaps : ∀ m ∈ rSetPos n, κ m ∈ Ico 2 n := by
      intro m hm
      obtain ⟨h2, hle⟩ := hκ m hm
      simp only [rSetPos, Finset.mem_filter, rSet, Finset.mem_range] at hm
      simp only [Finset.mem_Ico]
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]]
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  have hA : ∑ m ∈ rSetPos n, parityGap G w (κ m) =
      ∑ k ∈ Ico 2 (n - 1), recipeCount n κ k * parityGap G w k := by
    rw [hfib (fun k => parityGap G w k)]
    have he := Finset.sum_Ico_succ_top (show 2 ≤ n - 1 by omega)
      (fun k => recipeCount n κ k * parityGap G w k)
    have en : n - 1 + 1 = n := by omega
    rw [en] at he
    have htop := (lemma7_parityBall_eq_top (by omega) hG hD w (Or.inl rfl)).2.2
    rw [he, htop, mul_zero, add_zero]
  have hB : ∑ m ∈ rSetPos n, parityGap G w (κ m - 2) =
      recipeCount n κ 3 * ((n : ℤ) - 2 - excess G w) +
        ∑ k ∈ Ico 2 (n - 1), recipeCount n κ (k + 2) * parityGap G w k := by
    rw [hfib (fun k => parityGap G w (k - 2))]
    have e1 := Finset.sum_eq_sum_Ico_succ_bot (show 2 < n by omega)
      (fun k => recipeCount n κ k * parityGap G w (k - 2))
    have e2 := Finset.sum_eq_sum_Ico_succ_bot (show 3 < n by omega)
      (fun k => recipeCount n κ k * parityGap G w (k - 2))
    rw [e1, e2]
    simp only [Nat.sub_self, show 3 - 2 = 1 by rfl, parityGap_zero hc w,
      parityGap_one (G := G) w, mul_zero, zero_add]
    have hshift : ∑ k ∈ Ico 4 n, recipeCount n κ k * parityGap G w (k - 2) =
        ∑ j ∈ Ico 2 (n - 2), recipeCount n κ (j + 2) * parityGap G w j := by
      refine Finset.sum_nbij' (fun k => k - 2) (fun j => j + 2) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro k hk; simp only [Finset.mem_Ico] at hk; omega
      · intro j _; omega
      · intro k hk
        simp only [Finset.mem_Ico] at hk
        have : k - 2 + 2 = k := by omega
        rw [this]
    have hrc_n : recipeCount n κ n = 0 := by
      unfold recipeCount
      suffices h : ((rSetPos n).filter fun m => κ m = n) = ∅ by simp [h]
      rw [Finset.filter_eq_empty_iff]
      intro m hm hkm
      have hle := (hκ m hm).2
      simp only [rSetPos, Finset.mem_filter, rSet, Finset.mem_range] at hm
      omega
    have etop := Finset.sum_Ico_succ_top (show 2 ≤ n - 2 by omega)
      (fun j => recipeCount n κ (j + 2) * parityGap G w j)
    have en1 : n - 2 + 1 = n - 1 := by omega
    have en2 : n - 2 + 2 = n := by omega
    rw [en1] at etop
    rw [hshift, etop, en2, hrc_n, zero_mul, add_zero]
  have hsplit_sum : ∑ m ∈ rSetPos n,
      (((fastChoose n (κ m) : ℤ) - 2) - parityGap G w (κ m) + parityGap G w (κ m - 2)) =
      (∑ m ∈ rSetPos n, ((fastChoose n (κ m) : ℤ) - 2)) -
        (∑ m ∈ rSetPos n, parityGap G w (κ m)) +
        (∑ m ∈ rSetPos n, parityGap G w (κ m - 2)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hcomb : ∑ k ∈ Ico 2 (n - 1),
      (recipeCount n κ (k + 2) - recipeCount n κ k) * parityGap G w k =
      (∑ k ∈ Ico 2 (n - 1), recipeCount n κ (k + 2) * parityGap G w k) -
        (∑ k ∈ Ico 2 (n - 1), recipeCount n κ k * parityGap G w k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => sub_mul _ _ _
  unfold recipeHalfK
  linarith

/-- Theorem 13's antipodal-capped floor (`bound-9.md` Theorem 13). -/
def cappedFloor (n : ℕ) (κ : ℕ → ℕ) (α x t : ℤ) : ℤ :=
  2 * x * ((n : ℤ) - 2 - x) + α * recipeHalfK n κ x -
    max 0 (α - 2) * (((n : ℤ) - 1) * t - ((2 : ℤ) ^ n - 2 * (n : ℤ))) +
    ∑ k ∈ Ico 2 (n - 1),
      (2 * x + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) * halfStepChain n x t k

/-- **Theorem 13 (`bound-9.md` Step 77, Antipodal-Capped Recipe Floor)**:
For `n ≥ 4`, any valid recipe `κ`, and any `α ≥ 0` whose parity-gap weights
`a_k = 2x + α (u_{k+2} - u_k)` are nonnegative for `2 ≤ k ≤ n - 2`, every vertex `w` of
excess `x` in a valid spanning subgraph `G` of `Q_n` satisfies
`cappedFloor n κ α x (edgeExcess G) ≤ ψ(w)`. -/
theorem theorem13_capped_floor {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (CubeVertex n)} (hV : IsValidSpanningSubgraph n G)
    (w : CubeVertex n) (κ : ℕ → ℕ) (hκ : IsValidRecipe n κ) {α : ℤ} (hα : 0 ≤ α)
    (hw : ∀ k ∈ Ico 2 (n - 1),
      0 ≤ 2 * excess G w + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) :
    cappedFloor n κ α (excess G w) (edgeExcess G) ≤ psi G w := by
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  have hM := recipe_weightedExtra_lower_bound hn hV w κ hκ
  have hcap := antipodal_cap (by omega) hV w
  have hδ := distGap_eq_sum_parityGap (by omega) hG hD w
  -- (2 - α) M(w) ≥ - max 0 (α - 2) μ
  have h2α : -max 0 (α - 2) * meanPsi n G ≤ (2 - α) * weightedExtra G w := by
    by_cases hle : α ≤ 2
    · have hm0 : max 0 (α - 2) = 0 := max_eq_left (by omega)
      rw [hm0, neg_zero, zero_mul]
      exact mul_nonneg (by omega) hcap.1
    · have hm1 : max 0 (α - 2) = α - 2 := max_eq_right (by omega)
      rw [hm1]
      have hmul := mul_le_mul_of_nonneg_left hcap.2.1 (show 0 ≤ α - 2 by omega)
      linarith
  have hαM : α * (recipeHalfK n κ (excess G w) +
      ∑ k ∈ Ico 2 (n - 1),
        (recipeCount n κ (k + 2) - recipeCount n κ k) * parityGap G w k) ≤
      α * weightedExtra G w :=
    mul_le_mul_of_nonneg_left hM hα
  -- Lower bound weighted parityGap sum by halfStepChain sum using Lemma 19
  have hchain : ∑ k ∈ Ico 2 (n - 1),
      (2 * excess G w + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) *
        halfStepChain n (excess G w) (edgeExcess G) k ≤
      ∑ k ∈ Ico 2 (n - 1),
        (2 * excess G w + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) *
          parityGap G w k := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_le : k ≤ n := by simp only [Finset.mem_Ico] at hk; omega
    exact mul_le_mul_of_nonneg_left (lemma19_halfStepChain_le (by omega) hV w k hk_le) (hw k hk)
  have hlin : excess G w * distGap G w +
      α * ∑ k ∈ Ico 2 (n - 1),
        (recipeCount n κ (k + 2) - recipeCount n κ k) * parityGap G w k =
      2 * excess G w * ((n : ℤ) - 2 - excess G w) +
        ∑ k ∈ Ico 2 (n - 1),
          (2 * excess G w + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) *
            parityGap G w k := by
    rw [hδ, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, add_assoc,
      ← Finset.sum_add_distrib]
    have hcongr : ∑ k ∈ Ico 2 (n - 1),
        (excess G w * (2 * parityGap G w k) +
          α * ((recipeCount n κ (k + 2) - recipeCount n κ k) * parityGap G w k)) =
        ∑ k ∈ Ico 2 (n - 1),
          (2 * excess G w + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) *
            parityGap G w k :=
      Finset.sum_congr rfl fun k _ => by ring
    linarith
  unfold cappedFloor psi meanPsi at *
  linarith

theorem cappedFloor_antitone_t (n : ℕ) (κ : ℕ → ℕ) (α x : ℤ) {t1 t2 : ℤ}
    (hn : 4 ≤ n) (ht : t1 ≤ t2)
    (hw : ∀ k ∈ Ico 2 (n - 1), 0 ≤ 2 * x + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) :
    cappedFloor n κ α x t2 ≤ cappedFloor n κ α x t1 := by
  unfold cappedFloor
  have hmu : max 0 (α - 2) * (((n : ℤ) - 1) * t1 - ((2 : ℤ) ^ n - 2 * (n : ℤ))) ≤
      max 0 (α - 2) * (((n : ℤ) - 1) * t2 - ((2 : ℤ) ^ n - 2 * (n : ℤ))) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_max_left 0 _)
    have hn1 : (0 : ℤ) ≤ (n : ℤ) - 1 := by omega
    nlinarith
  have hsum : ∑ k ∈ Ico 2 (n - 1),
      (2 * x + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) * halfStepChain n x t2 k ≤
      ∑ k ∈ Ico 2 (n - 1),
        (2 * x + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) * halfStepChain n x t1 k :=
    Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_left (halfStepChain_antitone_t n x ht k) (hw k hk)
  linarith

end

/-- Closed-form recipe `(F)` (`bound-5.md` Lemma 11). -/
def recipeF (n m : ℕ) : ℕ :=
  if n % 2 = 1 then
    if m ≤ 1 then 2 else (m - 1) / 2 + 3
  else
    m / 2 + 2

/-- Closed-form recipe `H = (G)|_{x=1}` (`bound-6.md` Lemma 14 / `bound-9.md` Theorem 14). -/
def recipeH (n m : ℕ) : ℕ :=
  let top := (n + 1) / 2
  if m + 1 < top then
    m + 1
  else
    let m0 := if (top - 1) % 2 = n % 2 then top - 1 else top
    top + (m - m0) / 2

theorem recipeF_valid (n : ℕ) : IsValidRecipe n (recipeF n) := by
  intro m hm
  simp only [rSetPos, Finset.mem_filter, rSet, Finset.mem_range] at hm
  unfold recipeF
  split_ifs <;> omega

theorem recipeH_valid {n : ℕ} (hn : 4 ≤ n) : IsValidRecipe n (recipeH n) := by
  intro m hm
  simp only [rSetPos, Finset.mem_filter, rSet, Finset.mem_range] at hm
  unfold recipeH
  dsimp only
  split_ifs <;> omega

def sumFilterRange (p : ℕ → Bool) (g : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => sumFilterRange p g m + if p m then g m else 0

private theorem sumFilterRange_eq (p : ℕ → Prop) [DecidablePred p] (g : ℕ → ℤ) (m : ℕ) :
    sumFilterRange (fun x => decide (p x)) g m =
      ∑ x ∈ (range m).filter p, g x := by
  rw [Finset.sum_filter]
  induction m with
  | zero => simp [sumFilterRange]
  | succ m ih =>
    rw [Finset.sum_range_succ, sumFilterRange, ih]
    by_cases hp : p m <;> simp [hp]

def allRange (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | m + 1 => allRange p m && p m

private theorem allRange_eq_true (p : ℕ → Bool) (m : ℕ) :
    allRange p m = true ↔ ∀ k < m, p k = true := by
  induction m with
  | zero => simp [allRange]
  | succ m ih =>
    simp only [allRange, Bool.and_eq_true, ih]
    constructor
    · intro ⟨h1, h2⟩ k hk
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hk) with rfl | hlt
      · exact h2
      · exact h1 k hlt
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h m (Nat.lt_succ_self m)⟩

def recipeCountFast (n : ℕ) (κ : ℕ → ℕ) (k : ℕ) : ℤ :=
  sumFilterRange (fun m => decide ((m % 2 = n % 2 ∧ 1 ≤ m) ∧ κ m = k)) (fun _ => 1) (n - 1)

private theorem recipeCountFast_eq (n : ℕ) (κ : ℕ → ℕ) (k : ℕ) :
    recipeCountFast n κ k = recipeCount n κ k := by
  unfold recipeCountFast recipeCount rSetPos rSet
  rw [sumFilterRange_eq (fun m => (m % 2 = n % 2 ∧ 1 ≤ m) ∧ κ m = k)]
  have hf : (range (n - 1)).filter (fun m => (m % 2 = n % 2 ∧ 1 ≤ m) ∧ κ m = k) =
      (((range (n - 1)).filter fun m => m % 2 = n % 2).filter fun m => 1 ≤ m).filter
        (fun m => κ m = k) := by
    ext m; simp only [Finset.mem_filter]; tauto
  rw [hf, Finset.card_eq_sum_ones]
  push_cast; rfl

def recipeHalfKFast (n : ℕ) (κ : ℕ → ℕ) (x : ℤ) : ℤ :=
  (if n % 2 = 0 then x else 0) +
    sumFilterRange (fun m => decide (m % 2 = n % 2 ∧ 1 ≤ m))
      (fun m => (fastChoose n (κ m) : ℤ) - 2) (n - 1) +
    recipeCountFast n κ 3 * ((n : ℤ) - 2 - x) -
    ((2 : ℤ) ^ (n - 1) - (n : ℤ))

private theorem recipeHalfKFast_eq (n : ℕ) (κ : ℕ → ℕ) (x : ℤ) :
    recipeHalfKFast n κ x = recipeHalfK n κ x := by
  unfold recipeHalfKFast recipeHalfK rSetPos rSet
  rw [sumFilterRange_eq (fun m => m % 2 = n % 2 ∧ 1 ≤ m), recipeCountFast_eq]
  have hf : (range (n - 1)).filter (fun m => m % 2 = n % 2 ∧ 1 ≤ m) =
      ((range (n - 1)).filter fun m => m % 2 = n % 2).filter fun m => 1 ≤ m := by
    ext m; simp only [Finset.mem_filter]; tauto
  rw [hf]

def sumWeightedChainAux (n : ℕ) (t : ℤ) (wt : ℕ → ℤ) : ℕ → ℕ → ℤ → ℤ
  | 0, _, _ => 0
  | r + 1, k, pPrev =>
    let pCur := max 0 (pPrev + (fastChoose (n - 1) k : ℤ) - (t + 1))
    wt k * pCur + sumWeightedChainAux n t wt r (k + 1) pCur

private theorem sumWeightedChainAux_eq (n : ℕ) (x t : ℤ) (wt : ℕ → ℤ) :
    ∀ (r k : ℕ), 2 ≤ k →
      sumWeightedChainAux n t wt r k (halfStepChain n x t (k - 1)) =
        ∑ i ∈ range r, wt (k + i) * halfStepChain n x t (k + i) := by
  intro r
  induction r with
  | zero =>
    intro _ _
    simp [sumWeightedChainAux]
  | succ r ih =>
    intro k hk
    simp only [sumWeightedChainAux]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hp : max 0 (halfStepChain n x t (m + 2 - 1) + (fastChoose (n - 1) (m + 2) : ℤ) - (t + 1)) =
        halfStepChain n x t (m + 2) := by
      have e : m + 2 - 1 = m + 1 := by omega
      rw [e]; rfl
    rw [hp]
    have hrec := ih (m + 3) (by omega)
    have e3 : m + 3 - 1 = m + 2 := by omega
    rw [e3] at hrec
    rw [hrec, Finset.sum_range_succ' (fun i => wt (m + 2 + i) * halfStepChain n x t (m + 2 + i)) r]
    simp only [Nat.add_zero]
    have hshift : ∑ i ∈ range r, wt (m + 3 + i) * halfStepChain n x t (m + 3 + i) =
        ∑ i ∈ range r, wt (m + 2 + (i + 1)) * halfStepChain n x t (m + 2 + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => by
        have e : m + 3 + i = m + 2 + (i + 1) := by omega
        rw [e]
    rw [hshift]
    ring

def cappedFloorFast (n : ℕ) (κ : ℕ → ℕ) (α x t : ℤ) : ℤ :=
  2 * x * ((n : ℤ) - 2 - x) + α * recipeHalfKFast n κ x -
    max 0 (α - 2) * (((n : ℤ) - 1) * t - ((2 : ℤ) ^ n - 2 * (n : ℤ))) +
    sumWeightedChainAux n t
      (fun k => 2 * x + α * (recipeCountFast n κ (k + 2) - recipeCountFast n κ k))
      (n - 3) 2 ((n : ℤ) - 2 - x)

private theorem cappedFloorFast_eq {n : ℕ} (hn : 4 ≤ n) (κ : ℕ → ℕ) (α x t : ℤ) :
    cappedFloorFast n κ α x t = cappedFloor n κ α x t := by
  unfold cappedFloorFast cappedFloor
  simp_rw [recipeHalfKFast_eq, recipeCountFast_eq]
  have hp1 : ((n : ℤ) - 2 - x) = halfStepChain n x t (2 - 1) := rfl
  rw [hp1, sumWeightedChainAux_eq n x t _ (n - 3) 2 le_rfl]
  have hico : ∑ i ∈ range (n - 3),
      (2 * x + α * (recipeCount n κ (2 + i + 2) - recipeCount n κ (2 + i))) *
        halfStepChain n x t (2 + i) =
      ∑ k ∈ Ico 2 (n - 1),
        (2 * x + α * (recipeCount n κ (k + 2) - recipeCount n κ k)) * halfStepChain n x t k := by
    refine Finset.sum_nbij' (fun i => 2 + i) (fun k => k - 2) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range, Finset.mem_Ico] at hi ⊢; omega
    · intro k hk; simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
    · intro i _; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk; omega
    · intro _ _; rfl
  rw [hico]

def weightsNonnegBool (n : ℕ) (κ : ℕ → ℕ) (α x : ℤ) : Bool :=
  allRange (fun k =>
    if 2 ≤ k then
      decide (0 ≤ 2 * x + α * (recipeCountFast n κ (k + 2) - recipeCountFast n κ k))
    else true) (n - 1)

def candidateOk (n : ℕ) (κ : ℕ → ℕ) (α x t3 P : ℤ) : Bool :=
  decide (0 ≤ α) &&
    decide (x * P ≤ ((n : ℤ) - 2) * cappedFloorFast n κ α x t3) &&
    weightsNonnegBool n κ α x

def excessCoveredBool (n t3 : ℕ) (P : ℤ) (x : ℕ) : Bool :=
  let xZ : ℤ := x
  let tZ : ℤ := t3
  candidateOk n (recipeH n) (2 * xZ) xZ tZ P ||
    candidateOk n (recipeF n) (2 * xZ) xZ tZ P ||
    candidateOk n (recipeH n) 2 xZ tZ P ||
    candidateOk n (recipeF n) 2 xZ tZ P ||
    candidateOk n (recipeH n) 0 xZ tZ P ||
    candidateOk n (recipeF n) 0 xZ tZ P

/-- Kernel-decidable certificate predicate for Theorem 14 (`bound-9.md` Step 78):
verifies at excess threshold `t3` and slope numerator `P` (`ρ = P / (n - 2)`) that
every excess `1 ≤ x ≤ n - 2` achieves `(n - 2) ψ(w) ≥ x P` via `(F)` or `H` at integer
`α ∈ {0, 2, 2x}`, and that `2 t3 P > (n - 2) 2^n μ(t3)` with negative slope up to `t3`. -/
def capCertOk (n t3 : ℕ) (P : ℤ) : Bool :=
  decide (4 ≤ n) &&
    decide (0 ≤ P) &&
    decide (2 * P < ((n : ℤ) - 2) * (2 : ℤ) ^ n * ((n : ℤ) - 1)) &&
    decide (((n : ℤ) - 2) * (2 : ℤ) ^ n *
      (((n : ℤ) - 1) * (t3 : ℤ) - ((2 : ℤ) ^ n - 2 * (n : ℤ))) < 2 * (t3 : ℤ) * P) &&
    allRange (fun x => if 1 ≤ x then excessCoveredBool n t3 P x else true) (n - 1)

private theorem candidateOk_sound {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (CubeVertex n)} (hV : IsValidSpanningSubgraph n G)
    (w : CubeVertex n) (κ : ℕ → ℕ) (hκ : IsValidRecipe n κ)
    {α t3 P : ℤ} (ht : edgeExcess G ≤ t3)
    (hok : candidateOk n κ α (excess G w) t3 P = true) :
    excess G w * P ≤ ((n : ℤ) - 2) * psi G w := by
  unfold candidateOk weightsNonnegBool at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, allRange_eq_true] at hok
  obtain ⟨⟨hα, hfl⟩, hw_raw⟩ := hok
  have hw : ∀ k ∈ Ico 2 (n - 1),
      0 ≤ 2 * excess G w + α * (recipeCount n κ (k + 2) - recipeCount n κ k) := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have h1 := hw_raw k hk.2
    simp only [hk.1, ↓reduceIte, decide_eq_true_eq, recipeCountFast_eq] at h1
    exact h1
  rw [cappedFloorFast_eq hn] at hfl
  have hanti := cappedFloor_antitone_t n κ α (excess G w) hn ht hw
  have h13 := theorem13_capped_floor hn hV w κ hκ hα hw
  have hn2 : (0 : ℤ) ≤ (n : ℤ) - 2 := by omega
  have hstep1 : ((n : ℤ) - 2) * cappedFloor n κ α (excess G w) t3 ≤
      ((n : ℤ) - 2) * cappedFloor n κ α (excess G w) (edgeExcess G) :=
    mul_le_mul_of_nonneg_left hanti hn2
  have hstep2 : ((n : ℤ) - 2) * cappedFloor n κ α (excess G w) (edgeExcess G) ≤
      ((n : ℤ) - 2) * psi G w :=
    mul_le_mul_of_nonneg_left h13 hn2
  linarith

/-- Soundness of `capCertOk` (`bound-9.md` Step 78): whenever `capCertOk n t3 P = true`,
every valid spanning subgraph of `Q_n` has at least `2^n + t3 + 1` edges, so
`2^n + t3 + 1 ≤ f n`. -/
theorem theorem14_from_cert (n t3 : ℕ) (P : ℤ) (hcert : capCertOk n t3 P = true) :
    2 ^ n + t3 + 1 ≤ f n := by
  unfold capCertOk at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq, allRange_eq_true] at hcert
  obtain ⟨⟨⟨⟨hn4, hP0⟩, hslope⟩, hexcl⟩, hcov⟩ := hcert
  apply le_f_of_forall_valid
  intro G hV
  have ⟨hG, hD⟩ := (isValidSpanningSubgraph_iff_ediam G).1 hV
  by_contra hlt
  have ht_le : edgeExcess G ≤ (t3 : ℤ) := by
    unfold edgeExcess
    have : G.edgeSet.ncard ≤ 2 ^ n + t3 := by omega
    have hcast : (G.edgeSet.ncard : ℤ) ≤ ((2 ^ n + t3 : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  have hpt : ∀ w : CubeVertex n, excess G w * P ≤ ((n : ℤ) - 2) * psi G w := by
    intro w
    have hx0 := excess_nonneg (by omega) hG hD w
    have hx_le := excess_le hG w
    by_cases hx1 : 1 ≤ excess G w
    · let xNat : ℕ := (excess G w).toNat
      have hx_cast : (xNat : ℤ) = excess G w := Int.toNat_of_nonneg hx0
      have hx1_nat : 1 ≤ xNat := by omega
      have hc_x := hcov xNat (by omega)
      simp only [hx1_nat, ↓reduceIte] at hc_x
      unfold excessCoveredBool at hc_x
      dsimp only at hc_x
      rw [hx_cast] at hc_x
      simp only [Bool.or_eq_true] at hc_x
      have hF := recipeF_valid n
      have hH := recipeH_valid hn4
      rcases hc_x with ((((h1 | h2) | h3) | h4) | h5) | h6
      · exact candidateOk_sound hn4 hV w (recipeH n) hH ht_le h1
      · exact candidateOk_sound hn4 hV w (recipeF n) hF ht_le h2
      · exact candidateOk_sound hn4 hV w (recipeH n) hH ht_le h3
      · exact candidateOk_sound hn4 hV w (recipeF n) hF ht_le h4
      · exact candidateOk_sound hn4 hV w (recipeH n) hH ht_le h5
      · exact candidateOk_sound hn4 hV w (recipeF n) hF ht_le h6
    · have hxz : excess G w = 0 := by omega
      have hp0 := psi_nonneg (by omega) hV w
      have hn2 : (0 : ℤ) ≤ (n : ℤ) - 2 := by omega
      rw [hxz, zero_mul]
      exact mul_nonneg hn2 hp0
  have hsum : (∑ w : CubeVertex n, excess G w) * P ≤
      ((n : ℤ) - 2) * ∑ w : CubeVertex n, psi G w := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hpt w
  rw [sum_excess, sum_psi (by omega) hV] at hsum
  nlinarith

/-! ### Theorem 14 Concrete Antipodal-Cap Lower Bounds (`n = 9..32`, `bound-9.md` Table) -/

/-- `f 9 ≥ 580` (`bound-9.md` Theorem 14; beats Theorem 1's `574` and `bound-8`'s `576`). -/
theorem f_nine_ge_580 : 580 ≤ f 9 := by
  simpa using theorem14_from_cert 9 67 1162 (by decide)

/-- `f 10 ≥ 1147` (`bound-9.md` Theorem 14; beats Theorem 1's `1136` and `bound-8`'s `1140`). -/
theorem f_ten_ge_1147 : 1147 ≤ f 10 := by
  simpa using theorem14_from_cert 10 122 3372 (by decide)

/-- `f 11 ≥ 2271` (`bound-9.md` Theorem 14; beats Theorem 1's `2251` and `bound-8`'s `2257`). -/
theorem f_eleven_ge_2271 : 2271 ≤ f 11 := by
  simpa using theorem14_from_cert 11 222 8506 (by decide)

/-- `f 12 ≥ 4503` (`bound-9.md` Theorem 14; beats Theorem 1's `4467` and `bound-8`'s `4482`). -/
theorem f_twelve_ge_4503 : 4503 ≤ f 12 := by
  simpa using theorem14_from_cert 12 406 19948 (by decide)

/-- `f 13 ≥ 8941` (`bound-9.md` Theorem 14; beats Theorem 1's `8873` and `bound-8`'s `8905`). -/
theorem f_thirteen_ge_8941 : 8941 ≤ f 13 := by
  simpa using theorem14_from_cert 13 748 49030 (by decide)

/-- `f 14 ≥ 17753` (`bound-9.md` Theorem 14; beats Theorem 1's `17643` and `bound-8`'s `17704`). -/
theorem f_fourteen_ge_17753 : 17753 ≤ f 14 := by
  simpa using theorem14_from_cert 14 1368 103608 (by decide)

/-- `f 15 ≥ 35327` (`bound-9.md` Theorem 14; beats Theorem 1's `35107` and `bound-8`'s `35244`). -/
theorem f_fifteen_ge_35327 : 35327 ≤ f 15 := by
  simpa using theorem14_from_cert 15 2558 257230 (by decide)

/-- `f 16 ≥ 70357` (`bound-9.md` Theorem 14; beats Theorem 1's `69903` and `bound-8`'s `70182`). -/
theorem f_sixteen_ge_70357 : 70357 ≤ f 16 := by
  simpa using theorem14_from_cert 16 4820 648632 (by decide)

theorem f_seventeen_ge_140128 : 140128 ≤ f 17 := by
  simpa using theorem14_from_cert 17 9055 1504554 (by decide)

theorem f_eighteen_ge_279210 : 279210 ≤ f 18 := by
  simpa using theorem14_from_cert 18 17065 3441882 (by decide)

theorem f_nineteen_ge_556449 : 556449 ≤ f 19 := by
  simpa using theorem14_from_cert 19 32160 7572022 (by decide)

theorem f_twenty_ge_1110320 : 1110320 ≤ f 20 := by
  simpa using theorem14_from_cert 20 61743 19042134 (by decide)

theorem f_twentyone_ge_2214490 : 2214490 ≤ f 21 := by
  simpa using theorem14_from_cert 21 117337 42385900 (by decide)

theorem f_twentytwo_ge_4418155 : 4418155 ≤ f 22 := by
  simpa using theorem14_from_cert 22 223850 94920780 (by decide)

theorem f_twentythree_ge_8816922 : 8816922 ≤ f 23 := by
  simpa using theorem14_from_cert 23 428313 212708224 (by decide)

theorem f_twentyfour_ge_17599972 : 17599972 ≤ f 24 := by
  simpa using theorem14_from_cert 24 822755 481408946 (by decide)

theorem f_twentyfive_ge_35138325 : 35138325 ≤ f 25 := by
  simpa using theorem14_from_cert 25 1583892 1086331110 (by decide)

theorem f_twentysix_ge_70152107 : 70152107 ≤ f 26 := by
  simpa using theorem14_from_cert 26 3043242 2374246908 (by decide)

theorem f_twentyseven_ge_140081100 : 140081100 ≤ f 27 := by
  simpa using theorem14_from_cert 27 5863371 5216260844 (by decide)

theorem f_twentyeight_ge_279786071 : 279786071 ≤ f 28 := by
  simpa using theorem14_from_cert 28 11350614 11692402312 (by decide)

theorem f_twentynine_ge_558766740 : 558766740 ≤ f 29 := by
  simpa using theorem14_from_cert 29 21895827 25227109738 (by decide)

theorem f_thirty_ge_1116183007 : 1116183007 ≤ f 30 := by
  simpa using theorem14_from_cert 30 42441182 55626961564 (by decide)

set_option maxRecDepth 16384 in
theorem f_thirtyone_ge_2229577178 : 2229577178 ≤ f 31 := by
  simpa using theorem14_from_cert 31 82093529 119603426680 (by decide)

set_option maxRecDepth 16384 in
theorem f_thirtytwo_ge_4454492243 : 4454492243 ≤ f 32 := by
  simpa using theorem14_from_cert 32 159524946 262627585068 (by decide)

/-- Complete Theorem 14 antipodal-cap lower-bound ladder for `n = 17..32` (`bound-9.md` Table):
`f 17 ≥ 140128`, ..., `f 32 ≥ 4454492243`. -/
theorem theorem14_bounds_17_to_32 :
    140128 ≤ f 17 ∧ 279210 ≤ f 18 ∧ 556449 ≤ f 19 ∧ 1110320 ≤ f 20 ∧
    2214490 ≤ f 21 ∧ 4418155 ≤ f 22 ∧ 8816922 ≤ f 23 ∧ 17599972 ≤ f 24 ∧
    35138325 ≤ f 25 ∧ 70152107 ≤ f 26 ∧ 140081100 ≤ f 27 ∧ 279786071 ≤ f 28 ∧
    558766740 ≤ f 29 ∧ 1116183007 ≤ f 30 ∧ 2229577178 ≤ f 31 ∧ 4454492243 ≤ f 32 :=
  ⟨f_seventeen_ge_140128, f_eighteen_ge_279210, f_nineteen_ge_556449,
   f_twenty_ge_1110320, f_twentyone_ge_2214490, f_twentytwo_ge_4418155,
   f_twentythree_ge_8816922, f_twentyfour_ge_17599972, f_twentyfive_ge_35138325,
   f_twentysix_ge_70152107, f_twentyseven_ge_140081100, f_twentyeight_ge_279786071,
   f_twentynine_ge_558766740, f_thirty_ge_1116183007, f_thirtyone_ge_2229577178,
   f_thirtytwo_ge_4454492243⟩

end Hypercube

end
