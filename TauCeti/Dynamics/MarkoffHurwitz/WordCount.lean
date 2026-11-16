/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import TauCeti.Dynamics.MarkoffHurwitz.Branches
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Data.List.Finite

/-!
# Chronological words, delays, the renewal count, and freeness of `Γ'`

Finite words `u : List (ℕ × Fin d)` over the accelerated Markoff–Hurwitz alphabet act
chronologically on chart coordinates (`TauCeti.MarkoffHurwitz.wordMap`), accumulate logarithmic
denominators (`TauCeti.MarkoffHurwitz.wordDelay`), and lift to endomorphisms of `Fin (d + 2) → ℝ`
(`TauCeti.MarkoffHurwitz.wordLinearMap`). At each chart point `x` and cutoff `r : ℝ`,
`TauCeti.MarkoffHurwitz.wordCount d x r` counts the finite words `u` (including the empty word)
satisfying `wordDelay u x ≤ r`.

This file establishes the algebraic, analytic, and combinatorial API of words and their count:

* concatenation laws for `wordMap`, `wordDelay`, and `wordLinearMap`, simplex invariance of
  `wordMap`, and the homogeneous cocycle identity
  `wordDelay u (orderedConeProject y) = log (wordLinearMap u y (Fin.last (d + 1)) / y_{d+1})` on
  `orderedCone d`;
* the linear delay floor `|u| * log (3 / 2) ≤ wordDelay u x`, the per-letter bound
  `a.1 ≤ 2 * exp r - 3`, and finiteness of `{u | wordDelay u x ≤ r}` at every
  `x ∈ orderedSimplex d`;
* monotonicity, local constancy from the right, right-continuity, Borel measurability, and initial
  values (`r < 0` and `0 ≤ r < log (3 / 2)`) of `wordCount d x`;
* the renewal equation
  `wordCount d x r = (if 0 ≤ r then 1 else 0) +
    ∑' a, wordCount d (branchMap a x) (r - branchDelay a x)`
  together with finite support of its summand;
* freeness of the accelerated Markoff–Hurwitz semigroup `Γ'`: `Function.Injective wordLinearMap` in
  every chart dimension `d`.

## References

* A. Gamburd, M. Magee, and R. Ronan, *An asymptotic formula for integer points on
  Markoff–Hurwitz varieties*, Annals of Mathematics 190 (2019), 751–809, p. 756 (footnote 5),
  (1.7), and §4.1 (4.1).
-/

public noncomputable section

open Filter Set Topology

namespace TauCeti.MarkoffHurwitz

/-! ### Chronological word map, delay cocycle, and homogeneous linear action -/

/-- The map `F_u` of a finite word read chronologically: the first letter acts first,
`wordMap (a :: u) x = wordMap u (branchMap a x)`, and `[]` acts as the identity. -/
def wordMap {d : ℕ} : List (ℕ × Fin d) → (Fin d → ℝ) → (Fin d → ℝ)
  | [], x => x
  | a :: u, x => wordMap u (branchMap a x)

/-- `wordMap` of the empty word is the identity. -/
@[simp]
theorem wordMap_nil {d : ℕ} (x : Fin d → ℝ) : wordMap ([] : List (ℕ × Fin d)) x = x :=
  (rfl)

/-- `wordMap` on a cons word applies `branchMap a` first, then `wordMap u`. -/
@[simp]
theorem wordMap_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordMap (a :: u) x = wordMap u (branchMap a x) :=
  (rfl)

/-- `wordMap` of a single-letter word `[a]` is `branchMap a`. -/
theorem wordMap_singleton {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    wordMap [a] x = branchMap a x :=
  (rfl)

/-- Chronological concatenation law for `wordMap`: `F_{u ++ v} = F_v ∘ F_u`. -/
@[simp]
theorem wordMap_append {d : ℕ} (u v : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordMap (u ++ v) x = wordMap v (wordMap u x) := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih => simp [ih]

/-- Every chronological word map preserves `orderedSimplex d`. -/
theorem mapsTo_wordMap_orderedSimplex {d : ℕ} (u : List (ℕ × Fin d)) :
    MapsTo (wordMap u) (orderedSimplex d) (orderedSimplex d) := by
  intro x hx
  induction u generalizing x with
  | nil => exact hx
  | cons a _ ih => exact ih (branchMap_mem_orderedSimplex a hx)

/-- Pointwise form of `mapsTo_wordMap_orderedSimplex`. -/
theorem wordMap_mem_orderedSimplex {d : ℕ} (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : wordMap u x ∈ orderedSimplex d :=
  mapsTo_wordMap_orderedSimplex u hx

/-- The delay `T_u(w)` of a finite word read chronologically: `[]` has delay `0` and
`wordDelay (a :: u) x = log (branchDenom a x) + wordDelay u (branchMap a x)`. -/
def wordDelay {d : ℕ} : List (ℕ × Fin d) → (Fin d → ℝ) → ℝ
  | [], _ => 0
  | a :: u, x => Real.log (branchDenom a x) + wordDelay u (branchMap a x)

/-- The empty word has delay `0`. -/
@[simp]
theorem wordDelay_nil {d : ℕ} (x : Fin d → ℝ) : wordDelay ([] : List (ℕ × Fin d)) x = 0 :=
  (rfl)

/-- `wordDelay` on `a :: u` splits into `branchDelay a x + wordDelay u (branchMap a x)`. -/
@[simp]
theorem wordDelay_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordDelay (a :: u) x = branchDelay a x + wordDelay u (branchMap a x) := by
  rw [branchDelay_apply]
  rfl

/-- `wordDelay` of a single-letter word `[a]` is `branchDelay a`. -/
theorem wordDelay_singleton {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    wordDelay [a] x = branchDelay a x := by
  simp

/-- Chronological cocycle identity for `wordDelay`:
`wordDelay (u ++ v) x = wordDelay u x + wordDelay v (wordMap u x)`. -/
@[simp]
theorem wordDelay_append {d : ℕ} (u v : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordDelay (u ++ v) x = wordDelay u x + wordDelay v (wordMap u x) := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    simp only [List.cons_append, wordDelay_cons, ih, wordMap_cons]
    ring

/-- The homogeneous linear endomorphism `γ_u` of a chronological word `u : List (ℕ × Fin d)`:
`[]` acts as `LinearMap.id` and `a :: u` acts as `wordLinearMap u ∘ₗ branchLinearMap a`. -/
def wordLinearMap {d : ℕ} : List (ℕ × Fin d) → ((Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ))
  | [] => LinearMap.id
  | a :: u => wordLinearMap u ∘ₗ branchLinearMap a

/-- `wordLinearMap []` is the identity linear map. -/
@[simp]
theorem wordLinearMap_nil {d : ℕ} :
    wordLinearMap ([] : List (ℕ × Fin d)) = LinearMap.id :=
  (rfl)

/-- `wordLinearMap (a :: u)` composes `wordLinearMap u` after `branchLinearMap a`. -/
@[simp]
theorem wordLinearMap_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) :
    wordLinearMap (a :: u) = wordLinearMap u ∘ₗ branchLinearMap a :=
  (rfl)

/-- `wordLinearMap [a]` is `branchLinearMap a`. -/
theorem wordLinearMap_singleton {d : ℕ} (a : ℕ × Fin d) :
    wordLinearMap [a] = branchLinearMap a := by
  simp

/-- Chronological concatenation law for `wordLinearMap`:
`wordLinearMap (u ++ v) = wordLinearMap v ∘ₗ wordLinearMap u`. -/
@[simp]
theorem wordLinearMap_append {d : ℕ} (u v : List (ℕ × Fin d)) :
    wordLinearMap (u ++ v) = wordLinearMap v ∘ₗ wordLinearMap u := by
  induction u with
  | nil =>
    ext y i
    simp
  | cons a u ih =>
    rw [List.cons_append, wordLinearMap_cons, ih, wordLinearMap_cons, LinearMap.comp_assoc]

/-- Every `wordLinearMap u` maps `orderedCone d` into itself. -/
theorem wordLinearMap_mem_orderedCone {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : wordLinearMap u y ∈ orderedCone d := by
  induction u generalizing y with
  | nil => simpa using hy
  | cons a _ ih => exact ih (branchLinearMap_mem_orderedCone a hy)

/-- Homogeneous cocycle relation for words on `orderedCone d`:
`wordLinearMap u y = (y_{d+1} * exp (wordDelay u (orderedConeProject y))) •
  orderedSimplexLift (wordMap u (orderedConeProject y))`. -/
theorem wordLinearMap_eq_smul_orderedSimplexLift {d : ℕ} (u : List (ℕ × Fin d))
    {y : Fin (d + 2) → ℝ} (hy : y ∈ orderedCone d) :
    wordLinearMap u y =
      (y (Fin.last (d + 1)) * Real.exp (wordDelay u (orderedConeProject y))) •
        orderedSimplexLift (wordMap u (orderedConeProject y)) := by
  induction u generalizing y with
  | nil =>
    simp [last_smul_orderedSimplexLift_orderedConeProject hy]
  | cons a u ih =>
    have hay : branchLinearMap a y ∈ orderedCone d := branchLinearMap_mem_orderedCone a hy
    have hx : orderedConeProject y ∈ orderedSimplex d := orderedConeProject_mem_orderedSimplex hy
    have hq : 0 < branchDenom a (orderedConeProject y) :=
      branchDenom_pos_of_mem_orderedSimplex a hx
    rw [wordLinearMap_cons, LinearMap.comp_apply, ih hay,
      branchLinearMap_last_of_mem_orderedCone a hy, orderedConeProject_branchLinearMap a hy,
      wordDelay_cons, Real.exp_add, exp_branchDelay a hq, wordMap_cons]
    simp [mul_assoc]

/-- Projective equivariance of `wordLinearMap` and `wordMap` on `orderedCone d`. -/
theorem orderedConeProject_wordLinearMap {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    orderedConeProject (wordLinearMap u y) = wordMap u (orderedConeProject y) := by
  have hypos := last_pos_of_mem_orderedCone hy
  have hexp := Real.exp_pos (wordDelay u (orderedConeProject y))
  rw [wordLinearMap_eq_smul_orderedSimplexLift u hy,
    orderedConeProject_smul (mul_pos hypos hexp).ne', orderedConeProject_orderedSimplexLift]

/-- Homogeneous delay formula on `orderedCone d`:
`wordDelay u (orderedConeProject y) = log (wordLinearMap u y (Fin.last (d + 1)) / y_{d+1})`. -/
theorem wordDelay_orderedConeProject {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    wordDelay u (orderedConeProject y) =
      Real.log (wordLinearMap u y (Fin.last (d + 1)) / y (Fin.last (d + 1))) := by
  have hypos := last_pos_of_mem_orderedCone hy
  rw [wordLinearMap_eq_smul_orderedSimplexLift u hy]
  simp [mul_div_cancel_left₀ _ hypos.ne']

/-! ### Delay lower bounds and finiteness of sublevel sets -/

/-- Linear lower bound on `orderedSimplex d`:
`(u.length : ℝ) * log (3 / 2) ≤ wordDelay u x`. -/
theorem length_mul_log_three_div_two_le_wordDelay {d : ℕ} (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    (u.length : ℝ) * Real.log (3 / 2) ≤ wordDelay u x := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    have ha := log_three_div_two_le_branchDelay_of_mem_orderedSimplex a hx
    have hu := ih (branchMap_mem_orderedSimplex a hx)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, wordDelay_cons]
    linarith

/-- On `orderedSimplex d`, every word has nonnegative delay. -/
theorem wordDelay_nonneg_of_mem_orderedSimplex {d : ℕ} (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 0 ≤ wordDelay u x := by
  refine le_trans ?_ (length_mul_log_three_div_two_le_wordDelay u hx)
  exact mul_nonneg u.length.cast_nonneg (Real.log_nonneg (by norm_num))

/-- Every nonempty word has delay at least `log (3 / 2)` on `orderedSimplex d`. -/
theorem log_three_div_two_le_wordDelay_of_ne_nil {d : ℕ} {u : List (ℕ × Fin d)} (hu : u ≠ [])
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Real.log (3 / 2) ≤ wordDelay u x := by
  cases u with
  | nil => contradiction
  | cons a v =>
    rw [wordDelay_cons]
    linarith [log_three_div_two_le_branchDelay_of_mem_orderedSimplex a hx,
      wordDelay_nonneg_of_mem_orderedSimplex v (branchMap_mem_orderedSimplex a hx)]

/-- Every letter `a` occurring in `u` contributes at least `log ((a.1 + 3) / 2)` to
`wordDelay u x` on `orderedSimplex d`. -/
theorem log_add_three_div_two_le_wordDelay_of_mem {d : ℕ} {a : ℕ × Fin d} {u : List (ℕ × Fin d)}
    (ha : a ∈ u) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Real.log (((a.1 : ℝ) + 3) / 2) ≤ wordDelay u x := by
  induction u generalizing x with
  | nil => cases ha
  | cons b v ih =>
    rw [wordDelay_cons]
    rcases List.mem_cons.mp ha with rfl | hav
    · linarith [log_add_three_div_two_le_branchDelay_of_mem_orderedSimplex a hx,
        wordDelay_nonneg_of_mem_orderedSimplex v (branchMap_mem_orderedSimplex a hx)]
    · linarith [branchDelay_pos_of_mem_orderedSimplex b hx,
        ih hav (branchMap_mem_orderedSimplex b hx)]

/-- Per-letter bound on `orderedSimplex d`: if `wordDelay u x ≤ r` and `a ∈ u`, then
`(a.1 : ℝ) ≤ 2 * exp r - 3`. -/
theorem fst_le_two_mul_exp_sub_three_of_wordDelay_le {d : ℕ} {a : ℕ × Fin d}
    {u : List (ℕ × Fin d)} (ha : a ∈ u) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) {r : ℝ}
    (hr : wordDelay u x ≤ r) : (a.1 : ℝ) ≤ 2 * Real.exp r - 3 := by
  have hlog : Real.log (((a.1 : ℝ) + 3) / 2) ≤ r :=
    (log_add_three_div_two_le_wordDelay_of_mem ha hx).trans hr
  have hexp : ((a.1 : ℝ) + 3) / 2 ≤ Real.exp r := by
    have hpos : (0 : ℝ) < ((a.1 : ℝ) + 3) / 2 := by positivity
    simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog
  linarith

/-- For every `x ∈ orderedSimplex d` and `r : ℝ`, only finitely many words satisfy
`wordDelay u x ≤ r`. -/
theorem finite_setOf_wordDelay_le {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.Finite := by
  let L : ℕ := ⌊r / Real.log (3 / 2)⌋₊
  let M : ℕ := ⌊2 * Real.exp r⌋₊ + 1
  have hlog_pos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hfin := (List.finite_setOf_sum_map_snd_add_one_le (Fin d) (L * M)).image
    (List.map Prod.swap)
  refine hfin.subset fun u hu => ?_
  rw [mem_ofPred_eq] at hu
  refine ⟨u.map Prod.swap, ?_, by simp [Function.comp_def]⟩
  rw [mem_ofPred_eq, List.map_map]
  have hlen : u.length ≤ L := by
    by_cases hr0 : 0 ≤ r
    · refine Nat.le_floor ?_
      rw [le_div_iff₀ hlog_pos]
      exact (length_mul_log_three_div_two_le_wordDelay u hx).trans hu
    · have h0 : 0 ≤ wordDelay u x := wordDelay_nonneg_of_mem_orderedSimplex u hx
      linarith
  have hbound : ∀ b ∈ (u.map fun p : ℕ × Fin d => p.1 + 1), b ≤ M := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
    have ha_le : (a.1 : ℝ) ≤ 2 * Real.exp r - 3 :=
      fst_le_two_mul_exp_sub_three_of_wordDelay_le ha hx hu
    have ha_lt : a.1 ≤ ⌊2 * Real.exp r⌋₊ :=
      Nat.le_floor (by linarith)
    exact Nat.succ_le_succ ha_lt
  have hsum : (u.map fun p : ℕ × Fin d => p.1 + 1).sum ≤ u.length * M := by
    simpa using List.sum_le_length_nsmul (u.map fun p : ℕ × Fin d => p.1 + 1) M hbound
  exact le_trans (by simpa [Function.comp_def] using hsum) (Nat.mul_le_mul_right M hlen)

/-! ### The renewal word count, regularity, and the renewal equation -/

/-- The renewal count `N(w, r)`: the number of words `u` (including `[]`) satisfying
`wordDelay u x ≤ r` (Gamburd–Magee–Ronan 2019, (1.7)). -/
def wordCount (d : ℕ) (x : Fin d → ℝ) (r : ℝ) : ℕ :=
  {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.ncard

/-- Unfolded formula for `wordCount d x r`. -/
theorem wordCount_apply (d : ℕ) (x : Fin d → ℝ) (r : ℝ) :
    wordCount d x r = {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.ncard :=
  (rfl)

/-- Scaling invariance of `wordCount` on `orderedCone d`: positive collinearity preserves the
projected renewal count. -/
theorem wordCount_orderedConeProject_smul (d : ℕ) {c : ℝ} (hc : 0 < c) (y : Fin (d + 2) → ℝ)
    (r : ℝ) :
    wordCount d (orderedConeProject (c • y)) r = wordCount d (orderedConeProject y) r := by
  rw [orderedConeProject_smul hc.ne']

/-- For `r < 0` and `x ∈ orderedSimplex d`, `wordCount d x r = 0`. -/
theorem wordCount_eq_zero_of_lt_zero {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    {r : ℝ} (hr : r < 0) : wordCount d x r = 0 := by
  have hemp : {u : List (ℕ × Fin d) | wordDelay u x ≤ r} = ∅ := by
    ext u
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact hr.trans_le (wordDelay_nonneg_of_mem_orderedSimplex u hx)
  rw [wordCount_apply, hemp, Set.ncard_empty]

/-- For `0 ≤ r < log (3 / 2)` and `x ∈ orderedSimplex d`, only the empty word contributes, so
`wordCount d x r = 1`. -/
theorem wordCount_eq_one_of_lt_log_three_div_two {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < Real.log (3 / 2)) :
    wordCount d x r = 1 := by
  rw [wordCount_apply]
  have hset : {u : List (ℕ × Fin d) | wordDelay u x ≤ r} = {[]} := by
    ext u
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro hu
      by_contra hne
      linarith [log_three_div_two_le_wordDelay_of_ne_nil hne hx]
    · rintro rfl
      simpa using hr0
  rw [hset, Set.ncard_singleton]

/-- At `r = 0` on `orderedSimplex d`, `wordCount d x 0 = 1`. -/
@[simp]
theorem wordCount_zero_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : wordCount d x 0 = 1 :=
  wordCount_eq_one_of_lt_log_three_div_two hx le_rfl (Real.log_pos (by norm_num))

/-- `wordCount d x` is monotone in `r` at every `x ∈ orderedSimplex d`. -/
theorem monotone_wordCount {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Monotone (wordCount d x) := by
  intro r₁ r₂ hr
  exact Set.ncard_le_ncard (fun u hu => le_trans hu hr) (finite_setOf_wordDelay_le hx r₂)

/-- Local constancy of `wordCount d x` from the right at every `r₀ : ℝ` when
`x ∈ orderedSimplex d`. -/
theorem exists_Ico_wordCount_eq {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r₀ : ℝ) :
    ∃ δ > 0, ∀ r ∈ Ico r₀ (r₀ + δ), wordCount d x r = wordCount d x r₀ := by
  have hT : {u : List (ℕ × Fin d) | wordDelay u x ≤ r₀ + 1 ∧ r₀ < wordDelay u x}.Finite :=
    (finite_setOf_wordDelay_le hx (r₀ + 1)).subset fun _ hu => hu.1
  by_cases hne : {u : List (ℕ × Fin d) | wordDelay u x ≤ r₀ + 1 ∧ r₀ < wordDelay u x}.Nonempty
  · let F := hT.toFinset.image fun u => wordDelay u x
    have hFne : F.Nonempty := (hT.toFinset_nonempty.mpr hne).image _
    let m := F.min' hFne
    have hm : r₀ < m := by
      obtain ⟨t, ht, htm⟩ := Finset.mem_image.mp (Finset.min'_mem F hFne)
      have ht' := (hT.mem_toFinset.mp ht).2
      dsimp only [m]
      linarith
    refine ⟨min 1 (m - r₀), lt_min zero_lt_one (sub_pos.mpr hm), fun r hr => ?_⟩
    rw [wordCount_apply, wordCount_apply]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    refine ⟨fun hu => ?_, fun hu => hu.trans hr.1⟩
    by_contra hgt
    have hlt1 : wordDelay u x ≤ r₀ + 1 :=
      hu.trans (hr.2.le.trans (add_le_add_right (min_le_left _ _) _))
    have hu_mem : u ∈ hT.toFinset := hT.mem_toFinset.mpr ⟨hlt1, not_le.mp hgt⟩
    have hm_le : m ≤ wordDelay u x := Finset.min'_le F _ (Finset.mem_image_of_mem _ hu_mem)
    have hr_lt : r < m := by
      have : r < r₀ + (m - r₀) := lt_of_lt_of_le hr.2 (add_le_add_right (min_le_right _ _) _)
      linarith
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, zero_lt_one, fun r hr => ?_⟩
    rw [wordCount_apply, wordCount_apply]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    refine ⟨fun hu => ?_, fun hu => hu.trans hr.1⟩
    by_contra hgt
    have : u ∈ ({u : List (ℕ × Fin d) | wordDelay u x ≤ r₀ + 1 ∧ r₀ < wordDelay u x}) :=
      ⟨hu.trans hr.2.le, not_le.mp hgt⟩
    rw [hne] at this
    exact this

/-- `wordCount d x` is right-continuous at every `r₀ : ℝ` when `x ∈ orderedSimplex d`. -/
theorem continuousWithinAt_wordCount_Ici {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (r₀ : ℝ) : ContinuousWithinAt (wordCount d x) (Ici r₀) r₀ := by
  obtain ⟨δ, hδ, hconst⟩ := exists_Ico_wordCount_eq hx r₀
  have hev : wordCount d x =ᶠ[𝓝[≥] r₀] fun _ => wordCount d x r₀ :=
    Filter.eventually_of_mem (Ico_mem_nhdsGE (lt_add_of_pos_right r₀ hδ)) hconst
  exact continuousWithinAt_const.congr_of_eventuallyEq hev rfl

/-- `r ↦ (wordCount d x r : ℝ)` is right-continuous at every `r₀ : ℝ` when
`x ∈ orderedSimplex d`. -/
theorem continuousWithinAt_natCast_wordCount_Ici {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) (r₀ : ℝ) :
    ContinuousWithinAt (fun r => (wordCount d x r : ℝ)) (Ici r₀) r₀ := by
  have hcont : Continuous (Nat.cast : ℕ → ℝ) := continuous_of_discreteTopology
  exact hcont.continuousAt.comp_continuousWithinAt (continuousWithinAt_wordCount_Ici hx r₀)

/-- `wordCount d x : ℝ → ℕ` is Borel measurable for every `x ∈ orderedSimplex d`. -/
theorem measurable_wordCount {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Measurable (wordCount d x) :=
  (monotone_wordCount hx).measurable

/-- `r ↦ (wordCount d x r : ℝ)` is Borel measurable for every `x ∈ orderedSimplex d`. -/
theorem measurable_natCast_wordCount {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Measurable fun r => (wordCount d x r : ℝ) :=
  (continuous_of_discreteTopology : Continuous (Nat.cast : ℕ → ℝ)).measurable.comp
    (measurable_wordCount hx)

/-- At each `x ∈ orderedSimplex d` and `r : ℝ`, only finitely many letters `a` satisfy
`branchDelay a x ≤ r`. -/
theorem finite_setOf_branchDelay_le {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    {a : ℕ × Fin d | branchDelay a x ≤ r}.Finite := by
  refine ((Set.finite_Iio (⌊2 * Real.exp r⌋₊ + 1)).prod Set.finite_univ).subset fun a ha => ?_
  refine ⟨?_, trivial⟩
  have hlog : Real.log (((a.1 : ℝ) + 3) / 2) ≤ r :=
    (log_add_three_div_two_le_branchDelay_of_mem_orderedSimplex a hx).trans ha
  have hexp : ((a.1 : ℝ) + 3) / 2 ≤ Real.exp r := by
    have hpos : (0 : ℝ) < ((a.1 : ℝ) + 3) / 2 := by positivity
    simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog
  have hle : a.1 ≤ ⌊2 * Real.exp r⌋₊ := Nat.le_floor (by linarith)
  exact Nat.lt_succ_of_le hle

/-- At each `x ∈ orderedSimplex d` and `r : ℝ`, the renewal summand
`a ↦ wordCount d (branchMap a x) (r - branchDelay a x)` has finite support. -/
theorem finite_support_wordCount_sub_branchDelay {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) (r : ℝ) :
    (Function.support fun a : ℕ × Fin d =>
      wordCount d (branchMap a x) (r - branchDelay a x)).Finite := by
  refine (finite_setOf_branchDelay_le hx r).subset fun a ha => ?_
  by_contra hgt
  apply ha
  exact wordCount_eq_zero_of_lt_zero (branchMap_mem_orderedSimplex a hx)
    (sub_neg.mpr (not_le.mp hgt))

/-- **Renewal equation** for `wordCount` on `orderedSimplex d`
(Gamburd–Magee–Ronan 2019, (4.1)): partitioning words by whether they are empty or start with a
first letter `a` yields
`wordCount d x r = (if 0 ≤ r then 1 else 0) +
  ∑' a, wordCount d (branchMap a x) (r - branchDelay a x)`. -/
theorem wordCount_renewal {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    wordCount d x r =
      (if 0 ≤ r then 1 else 0) +
        ∑' a : ℕ × Fin d, wordCount d (branchMap a x) (r - branchDelay a x) := by
  by_cases hr : 0 ≤ r
  · -- Partition `{u | wordDelay u x ≤ r}` into `[]` and nonempty words grouped by first letter.
    have hS := finite_setOf_wordDelay_le hx r
    have hB := finite_setOf_branchDelay_le hx r
    let F : Finset (ℕ × Fin d) := hB.toFinset
    let G : (ℕ × Fin d) → Finset (List (ℕ × Fin d)) := fun a =>
      (finite_setOf_wordDelay_le (branchMap_mem_orderedSimplex a hx)
        (r - branchDelay a x)).toFinset
    let emb : (ℕ × Fin d) → List (ℕ × Fin d) ↪ List (ℕ × Fin d) := fun a =>
      ⟨List.cons a, fun _ _ h => (List.cons.inj h).2⟩
    have hpart : hS.toFinset = insert [] (F.biUnion fun a => (G a).map (emb a)) := by
      ext u
      cases u with
      | nil =>
        simp [hS.mem_toFinset, hr]
      | cons a v =>
        simp only [hS.mem_toFinset, mem_ofPred_eq, wordDelay_cons, Finset.mem_insert,
          reduceCtorEq, false_or, Finset.mem_biUnion, Finset.mem_map]
        constructor
        · intro huv
          have hv0 : 0 ≤ wordDelay v (branchMap a x) :=
            wordDelay_nonneg_of_mem_orderedSimplex v (branchMap_mem_orderedSimplex a hx)
          have haB : a ∈ {b : ℕ × Fin d | branchDelay b x ≤ r} := by
            rw [mem_ofPred_eq]
            linarith
          refine ⟨a, hB.mem_toFinset.mpr haB, v, ?_, rfl⟩
          rw [Set.Finite.mem_toFinset]
          exact le_sub_iff_add_le'.mpr huv
        · rintro ⟨a', _, v', hv', heq⟩
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          rw [Set.Finite.mem_toFinset] at hv'
          exact le_sub_iff_add_le'.mp hv'
    -- The first-letter fibers are pairwise disjoint and do not contain `[]`.
    have hnotMem : ([] : List (ℕ × Fin d)) ∉ F.biUnion fun a => (G a).map (emb a) := by
      simp [emb]
    have hdisj : (F : Set (ℕ × Fin d)).PairwiseDisjoint fun a => (G a).map (emb a) := by
      intro a₁ _ a₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu₁ hu₂
      rcases Finset.mem_map.mp hu₁ with ⟨v₁, _, rfl⟩
      rcases Finset.mem_map.mp hu₂ with ⟨v₂, _, heq⟩
      exact hne (List.cons.inj heq).1.symm
    have hcard_G : ∀ a, ((G a).map (emb a)).card =
        wordCount d (branchMap a x) (r - branchDelay a x) := by
      intro a
      rw [Finset.card_map, wordCount_apply,
        Set.ncard_eq_toFinset_card _
          (finite_setOf_wordDelay_le (branchMap_mem_orderedSimplex a hx) (r - branchDelay a x))]
    -- Collapse the `tsum` to the finite set `F` where `branchDelay a x ≤ r`.
    have htsum : (∑' a : ℕ × Fin d, wordCount d (branchMap a x) (r - branchDelay a x)) =
        ∑ a ∈ F, wordCount d (branchMap a x) (r - branchDelay a x) := by
      refine tsum_eq_sum fun a ha => ?_
      have hgt : r < branchDelay a x := not_le.mp fun hle => ha (hB.mem_toFinset.mpr hle)
      exact wordCount_eq_zero_of_lt_zero (branchMap_mem_orderedSimplex a hx) (sub_neg.mpr hgt)
    simp only [hr, ↓reduceIte]
    rw [htsum, wordCount_apply, Set.ncard_eq_toFinset_card _ hS, hpart,
      Finset.card_insert_of_notMem hnotMem, Finset.card_biUnion hdisj, add_comm 1]
    simp [hcard_G]
  · -- For `r < 0`, both the total count and every shifted branch count vanish.
    have hlt : r < 0 := not_le.mp hr
    have hzero : ∀ a : ℕ × Fin d, wordCount d (branchMap a x) (r - branchDelay a x) = 0 := by
      intro a
      have hpos := branchDelay_pos_of_mem_orderedSimplex a hx
      exact wordCount_eq_zero_of_lt_zero (branchMap_mem_orderedSimplex a hx) (by linarith)
    simp [hr, wordCount_eq_zero_of_lt_zero hx hlt, hzero]

/-! ### Freeness of the accelerated Markoff–Hurwitz semigroup `Γ'` -/

/-- The open positive strictly increasing subcone of `orderedConeHyperplane d`: positive strictly
increasing homogeneous tuples satisfying `y₀ + ⋯ + y_d = y_{d+1}`. -/
def strictOrderedCone (d : ℕ) : Set (Fin (d + 2) → ℝ) :=
  {y | (∀ i, 0 < y i) ∧ StrictMono y ∧ y ∈ orderedConeHyperplane d}

/-- Membership in `strictOrderedCone d` unfolded. -/
@[simp]
theorem mem_strictOrderedCone_iff {d : ℕ} {y : Fin (d + 2) → ℝ} :
    y ∈ strictOrderedCone d ↔
      (∀ i, 0 < y i) ∧ StrictMono y ∧ y ∈ orderedConeHyperplane d :=
  Iff.rfl

/-- Every point of `strictOrderedCone d` belongs to `orderedCone d`. -/
theorem strictOrderedCone_subset_orderedCone (d : ℕ) :
    strictOrderedCone d ⊆ orderedCone d := by
  rintro y ⟨hypos, hystrict, hyhyp⟩
  rw [mem_orderedCone_iff]
  refine ⟨fun h0 => ?_, fun i => (hypos i).le, hystrict.monotone,
    mem_orderedConeHyperplane_iff.mp hyhyp⟩
  have : y 0 = 0 := congrFun h0 0
  linarith [hypos 0]

/-- For `1 ≤ d`, `orderedSimplexLift (orderedSimplexInteriorPoint d)` belongs to
`strictOrderedCone d`. -/
theorem orderedSimplexLift_interiorPoint_mem_strictOrderedCone {d : ℕ} (hd : 1 ≤ d) :
    orderedSimplexLift (orderedSimplexInteriorPoint d) ∈ strictOrderedCone d := by
  refine ⟨?_, ?_, mem_orderedConeHyperplane_iff.mpr (sum_castSucc_orderedSimplexLift _)⟩
  · refine Fin.lastCases (by simp) (Fin.lastCases ?_ fun i => ?_)
    · simp only [orderedSimplexLift_castSucc, chartToSimplex_last,
        one_sub_sum_orderedSimplexInteriorPoint]
      positivity
    · simp only [orderedSimplexLift_castSucc, chartToSimplex_castSucc]
      exact orderedSimplexInteriorPoint_pos i
  · intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast a' =>
        induction a' using Fin.lastCases with
        | last =>
          simp only [orderedSimplexLift_castSucc, chartToSimplex_last, orderedSimplexLift_last,
            one_sub_sum_orderedSimplexInteriorPoint]
          rw [div_lt_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr hd
          linarith
        | cast i =>
          have h1 := orderedSimplexInteriorPoint_lt_one_sub_sum i
          have h2 : 1 - ∑ k : Fin d, orderedSimplexInteriorPoint d k < 1 := by
            rw [one_sub_sum_orderedSimplexInteriorPoint, div_lt_iff₀ (by positivity)]
            have : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr hd
            linarith
          simpa using h1.trans h2
    | cast b' =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (not_lt_of_ge (Fin.le_last _))
      | cast a' =>
        have hab' : a' < b' := Fin.castSucc_lt_castSucc_iff.mp hab
        induction b' using Fin.lastCases with
        | last =>
          induction a' using Fin.lastCases with
          | last => exact absurd hab' (lt_irrefl _)
          | cast i => simpa using orderedSimplexInteriorPoint_lt_one_sub_sum i
        | cast j =>
          induction a' using Fin.lastCases with
          | last => exact absurd hab' (not_lt_of_ge (Fin.le_last _))
          | cast i =>
            simpa using strictMono_orderedSimplexInteriorPoint d
              (Fin.castSucc_lt_castSucc_iff.mp hab')

/-- Every unaccelerated generator `hurwitzGen j` strictly increases `y_{d+1}` on
`strictOrderedCone d`. -/
theorem last_lt_hurwitzGen_last_of_mem_strictOrderedCone {d : ℕ} (j : Fin (d + 1))
    {y : Fin (d + 2) → ℝ} (hy : y ∈ strictOrderedCone d) :
    y (Fin.last (d + 1)) < hurwitzGen j y (Fin.last (d + 1)) := by
  rw [hurwitzGen_last_of_mem_hyperplane j hy.2.2]
  linarith [hy.2.1 (Fin.castSucc_lt_last j)]

/-- For `1 ≤ d`, every unaccelerated generator `hurwitzGen j` maps `strictOrderedCone d` into
itself. -/
theorem hurwitzGen_mem_strictOrderedCone {d : ℕ} (hd : 1 ≤ d) (j : Fin (d + 1))
    {y : Fin (d + 2) → ℝ} (hy : y ∈ strictOrderedCone d) :
    hurwitzGen j y ∈ strictOrderedCone d := by
  have hlast_gt := last_lt_hurwitzGen_last_of_mem_strictOrderedCone j hy
  rcases hy with ⟨hypos, hystrict, _⟩
  refine ⟨?_, ?_, hurwitzGen_mem_hyperplane j y⟩
  · refine Fin.lastCases ?_ fun k => ?_
    · exact lt_trans (hypos _) hlast_gt
    · rw [hurwitzGen_castSucc]
      exact hypos _
  · intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast k =>
        rw [hurwitzGen_castSucc, hurwitzGen_last]
        have hexists : ∃ m : Fin (d + 1), m ≠ k := by
          by_cases hk0 : k = 0
          · refine ⟨Fin.last d, ?_⟩
            rw [hk0, ne_eq, Fin.ext_iff]
            simp
            omega
          · exact ⟨0, Ne.symm hk0⟩
        obtain ⟨m, hmk⟩ := hexists
        have hsum_erase : y ((Fin.castSucc j).succAbove k) + y ((Fin.castSucc j).succAbove m) ≤
            ∑ r : Fin (d + 1), y ((Fin.castSucc j).succAbove r) := by
          have hpair : ({k, m} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
          have hle := Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun r : Fin (d + 1) => y ((Fin.castSucc j).succAbove r)) hpair
            fun r _ _ => (hypos ((Fin.castSucc j).succAbove r)).le
          rwa [Finset.sum_pair hmk.symm] at hle
        linarith [hypos ((Fin.castSucc j).succAbove m)]
    | cast b' =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (not_lt_of_ge (Fin.le_last _))
      | cast a' =>
        rw [hurwitzGen_castSucc, hurwitzGen_castSucc]
        exact hystrict ((Fin.strictMono_succAbove (Fin.castSucc j))
          (Fin.castSucc_lt_castSucc_iff.mp hab))

/-- One-step unique recovery on `strictOrderedCone d`: if `hurwitzGen j₁ y₁ = hurwitzGen j₂ y₂`
for `y₁, y₂ ∈ strictOrderedCone d`, then `j₁ = j₂` and `y₁ = y₂`
(Gamburd–Magee–Ronan 2019, p. 756, footnote 5). -/
theorem hurwitzGen_inj_on_strictOrderedCone {d : ℕ} {j₁ j₂ : Fin (d + 1)}
    {y₁ y₂ : Fin (d + 2) → ℝ} (hy₁ : y₁ ∈ strictOrderedCone d) (hy₂ : y₂ ∈ strictOrderedCone d)
    (heq : hurwitzGen j₁ y₁ = hurwitzGen j₂ y₂) : j₁ = j₂ ∧ y₁ = y₂ := by
  have hlast : y₁ (Fin.last (d + 1)) = y₂ (Fin.last (d + 1)) := by
    simpa using congrFun heq (Fin.castSucc (Fin.last d))
  have hdel : y₁ (Fin.castSucc j₁) = y₂ (Fin.castSucc j₂) := by
    have hlast_img := congrFun heq (Fin.last (d + 1))
    rw [hurwitzGen_last_of_mem_hyperplane j₁ hy₁.2.2,
      hurwitzGen_last_of_mem_hyperplane j₂ hy₂.2.2, hlast] at hlast_img
    linarith
  have hj : j₁ = j₂ := by
    have hnotlt : ∀ {p q : Fin (d + 1)} {u v : Fin (d + 2) → ℝ},
        u ∈ strictOrderedCone d → v ∈ strictOrderedCone d →
        hurwitzGen p u = hurwitzGen q v → u (Fin.castSucc p) = v (Fin.castSucc q) →
        ¬ p < q := by
      intro p q u v hu hv hpq hdel_uv hlt
      have hp_ne : p ≠ Fin.last d := ne_of_lt (lt_of_lt_of_le hlt (Fin.le_last q))
      let i : Fin d := p.castPred hp_ne
      have hi : Fin.castSucc i = p := Fin.castSucc_castPred p hp_ne
      have himg := congrFun hpq (Fin.castSucc (Fin.castSucc i))
      rw [hurwitzGen_castSucc_castSucc, hurwitzGen_castSucc_castSucc] at himg
      have h_p : p.succAbove i = i.succ := Fin.succAbove_of_le_castSucc p i (le_of_eq hi.symm)
      have h_q : q.succAbove i = p := by
        rw [Fin.succAbove_of_castSucc_lt q i (hi.symm ▸ hlt), hi]
      rw [h_p, h_q] at himg
      have hi_lt : p < i.succ := hi ▸ Fin.castSucc_lt_succ
      have hu_lt : u (Fin.castSucc p) < u (Fin.castSucc i.succ) :=
        hu.2.1 (Fin.castSucc_lt_castSucc_iff.mpr hi_lt)
      have hv_lt : v (Fin.castSucc p) < v (Fin.castSucc q) :=
        hv.2.1 (Fin.castSucc_lt_castSucc_iff.mpr hlt)
      linarith
    rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
    · exact absurd hlt (hnotlt hy₁ hy₂ heq hdel)
    · rfl
    · exact absurd hgt (hnotlt hy₂ hy₁ heq.symm hdel.symm)
  subst hj
  refine ⟨rfl, ?_⟩
  ext m
  by_cases hm : m = Fin.castSucc j₁
  · rwa [hm]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hm
    simpa using congrFun heq (Fin.castSucc k)

/-- Unaccelerated chronological word action on `Fin (d + 2) → ℝ` over `Fin (d + 1)`. -/
def unaccelWordLinearMap {d : ℕ} :
    List (Fin (d + 1)) → ((Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ))
  | [] => LinearMap.id
  | j :: w => unaccelWordLinearMap w ∘ₗ hurwitzGen j

/-- `unaccelWordLinearMap []` is the identity linear map. -/
@[simp]
theorem unaccelWordLinearMap_nil {d : ℕ} :
    unaccelWordLinearMap ([] : List (Fin (d + 1))) = LinearMap.id :=
  (rfl)

/-- `unaccelWordLinearMap (j :: w)` composes `unaccelWordLinearMap w` after `hurwitzGen j`. -/
@[simp]
theorem unaccelWordLinearMap_cons {d : ℕ} (j : Fin (d + 1)) (w : List (Fin (d + 1))) :
    unaccelWordLinearMap (j :: w) = unaccelWordLinearMap w ∘ₗ hurwitzGen j :=
  (rfl)

/-- Chronological concatenation law for `unaccelWordLinearMap`. -/
@[simp]
theorem unaccelWordLinearMap_append {d : ℕ} (w₁ w₂ : List (Fin (d + 1))) :
    unaccelWordLinearMap (w₁ ++ w₂) = unaccelWordLinearMap w₂ ∘ₗ unaccelWordLinearMap w₁ := by
  induction w₁ with
  | nil =>
    ext y i
    simp
  | cons j w₁ ih =>
    simp only [List.cons_append, unaccelWordLinearMap_cons, ih, LinearMap.comp_assoc]

/-- For `1 ≤ d`, the unaccelerated Markoff–Hurwitz generators `hurwitzGen j` (`j : Fin (d + 1)`)
freely generate their linear semigroup: `unaccelWordLinearMap` is injective. -/
theorem unaccelWordLinearMap_injective {d : ℕ} (hd : 1 ≤ d) :
    Function.Injective (unaccelWordLinearMap (d := d)) := by
  let y₀ := orderedSimplexLift (orderedSimplexInteriorPoint d)
  have hy₀ : y₀ ∈ strictOrderedCone d := orderedSimplexLift_interiorPoint_mem_strictOrderedCone hd
  have hmem : ∀ w : List (Fin (d + 1)), unaccelWordLinearMap w y₀ ∈ strictOrderedCone d ∧
      (w ≠ [] → 1 < unaccelWordLinearMap w y₀ (Fin.last (d + 1))) := by
    intro w
    induction w using List.reverseRecOn with
    | nil =>
      exact ⟨hy₀, fun h => absurd rfl h⟩
    | append_singleton u j ih =>
      have hmem_next := hurwitzGen_mem_strictOrderedCone hd j ih.1
      have hlt_next := last_lt_hurwitzGen_last_of_mem_strictOrderedCone j ih.1
      have hge1 : 1 ≤ unaccelWordLinearMap u y₀ (Fin.last (d + 1)) := by
        by_cases hu : u = []
        · subst hu
          simp [y₀]
        · exact (ih.2 hu).le
      have heval :
          unaccelWordLinearMap (u ++ [j]) y₀ = hurwitzGen j (unaccelWordLinearMap u y₀) := by
        simp
      rw [heval]
      exact ⟨hmem_next, fun _ => lt_of_le_of_lt hge1 hlt_next⟩
  suffices ∀ w₁ w₂ : List (Fin (d + 1)),
      unaccelWordLinearMap w₁ y₀ = unaccelWordLinearMap w₂ y₀ → w₁ = w₂ by
    intro w₁ w₂ hmap
    exact this w₁ w₂ (congrFun (congrArg DFunLike.coe hmap) y₀)
  intro w₁
  induction w₁ using List.reverseRecOn with
  | nil =>
    intro w₂ heq
    by_contra hw₂
    have hgt := (hmem w₂).2 (Ne.symm hw₂)
    rw [← heq] at hgt
    simp [y₀] at hgt
  | append_singleton u₁ j₁ ih =>
    intro w₂ heq
    induction w₂ using List.reverseRecOn with
    | nil =>
      have hgt := (hmem (u₁ ++ [j₁])).2 (by simp)
      rw [heq] at hgt
      simp [y₀] at hgt
    | append_singleton u₂ j₂ _ =>
      have heq' : hurwitzGen j₁ (unaccelWordLinearMap u₁ y₀) =
          hurwitzGen j₂ (unaccelWordLinearMap u₂ y₀) := by
        simpa using heq
      obtain ⟨rfl, hu_eq⟩ :=
        hurwitzGen_inj_on_strictOrderedCone (hmem u₁).1 (hmem u₂).1 heq'
      rw [ih u₂ hu_eq]

/-- Chronological expansion of an accelerated word `u : List (ℕ × Fin d)` into an unaccelerated
word in `List (Fin (d + 1))`: each letter `(A, j)` expands to `j :: replicate A d`. -/
def expandWord {d : ℕ} : List (ℕ × Fin d) → List (Fin (d + 1))
  | [] => []
  | a :: u => Fin.castSucc a.2 :: (List.replicate a.1 (Fin.last d) ++ expandWord u)

/-- `expandWord` of the empty word is `[]`. -/
@[simp]
theorem expandWord_nil {d : ℕ} : expandWord ([] : List (ℕ × Fin d)) = [] :=
  (rfl)

/-- `expandWord` on `a :: u` prepends `Fin.castSucc a.2` and `a.1` copies of `Fin.last d`. -/
@[simp]
theorem expandWord_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) :
    expandWord (a :: u) = Fin.castSucc a.2 :: (List.replicate a.1 (Fin.last d) ++ expandWord u) :=
  (rfl)

/-- `expandWord` commutes with word concatenation. -/
@[simp]
theorem expandWord_append {d : ℕ} (u v : List (ℕ × Fin d)) :
    expandWord (u ++ v) = expandWord u ++ expandWord v := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih, List.append_assoc]

/-- `unaccelWordLinearMap (expandWord u)` agrees with `wordLinearMap u` for every word `u`. -/
theorem unaccelWordLinearMap_expandWord {d : ℕ} (u : List (ℕ × Fin d)) :
    unaccelWordLinearMap (expandWord u) = wordLinearMap u := by
  have hrep : ∀ A : ℕ,
      unaccelWordLinearMap (List.replicate A (Fin.last d)) = hurwitzGen (Fin.last d) ^ A := by
    intro A
    induction A with
    | zero => rfl
    | succ A ih =>
      rw [List.replicate_succ, unaccelWordLinearMap_cons, ih, pow_succ]
      rfl
  induction u with
  | nil => rfl
  | cons a u ih =>
    have hexp : expandWord (a :: u) =
        (Fin.castSucc a.2 :: List.replicate a.1 (Fin.last d)) ++ expandWord u :=
      rfl
    rw [hexp, unaccelWordLinearMap_append, ih, unaccelWordLinearMap_cons, hrep, wordLinearMap_cons]
    ext y m
    simp [branchLinearMap_apply]

/-- `expandWord` is injective: the maximal runs of `Fin.last d` uniquely delimit accelerated
letters. -/
theorem expandWord_injective {d : ℕ} : Function.Injective (expandWord (d := d)) := by
  have hnot_last : ∀ u : List (ℕ × Fin d), ∀ rest : List (Fin (d + 1)),
      expandWord u ≠ Fin.last d :: rest := by
    intro u rest h
    cases u with
    | nil => simp at h
    | cons c v =>
      simp only [expandWord_cons, List.cons.injEq] at h
      exact (Fin.castSucc_lt_last c.2).ne h.1
  have hrep_inj : ∀ (A B : ℕ) (u₁ u₂ : List (ℕ × Fin d)),
      List.replicate A (Fin.last d) ++ expandWord u₁ =
        List.replicate B (Fin.last d) ++ expandWord u₂ →
      A = B ∧ expandWord u₁ = expandWord u₂ := by
    intro A
    induction A with
    | zero =>
      intro B u₁ u₂ h
      cases B with
      | zero => exact ⟨rfl, by simpa using h⟩
      | succ B =>
        simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
        exact absurd h (hnot_last u₁ _)
    | succ A ih =>
      intro B u₁ u₂ h
      cases B with
      | zero =>
        simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
        exact absurd h.symm (hnot_last u₂ _)
      | succ B =>
        simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨rfl, hu⟩ := ih B u₁ u₂ h
        exact ⟨rfl, hu⟩
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ h
    cases u₂ with
    | nil => rfl
    | cons b v => simp at h
  | cons a u₁ ih =>
    intro u₂ h
    cases u₂ with
    | nil => simp at h
    | cons b u₂ =>
      simp only [expandWord_cons, List.cons.injEq] at h
      obtain ⟨ha1, hexp⟩ := hrep_inj a.1 b.1 u₁ u₂ h.2
      rw [Prod.ext ha1 (Fin.castSucc_inj.mp h.1), ih hexp]

/-- **Freeness of the accelerated Markoff–Hurwitz linear semigroup `Γ'`**
(Gamburd–Magee–Ronan 2019, p. 756, footnote 5): distinct words over `ℕ × Fin d` induce distinct
linear endomorphisms of `Fin (d + 2) → ℝ`. -/
theorem wordLinearMap_injective (d : ℕ) : Function.Injective (wordLinearMap (d := d)) := by
  cases d with
  | zero =>
    intro u₁ u₂ _
    cases u₁ with
    | nil =>
      cases u₂ with
      | nil => rfl
      | cons b _ => exact Fin.elim0 b.2
    | cons a _ => exact Fin.elim0 a.2
  | succ m =>
    intro u₁ u₂ h
    rw [← unaccelWordLinearMap_expandWord, ← unaccelWordLinearMap_expandWord] at h
    exact expandWord_injective (unaccelWordLinearMap_injective (Nat.succ_pos m) h)

end TauCeti.MarkoffHurwitz
