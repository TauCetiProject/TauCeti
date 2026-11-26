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
  `wordMap`, and the homogeneous delay cocycle identity on `orderedCone d`;
* the linear delay floor `|u| * log (3 / 2) ≤ wordDelay u x`, the per-letter bound
  `a.1 ≤ 2 * exp r - 3`, and finiteness of `{u | wordDelay u x ≤ r}` on `orderedSimplex d`;
* monotonicity, local constancy from the right, right-continuity, Borel measurability, and initial
  values of `wordCount d x`;
* the renewal equation `wordCount d x r = (if 0 ≤ r then 1 else 0) +
  ∑' a, wordCount d (branchMap a x) (r - branchDelay a x)` and finite support of its summand;
* freeness of the accelerated Markoff–Hurwitz semigroup `Γ'`: `Function.Injective wordLinearMap`.

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
theorem wordMap_nil {d : ℕ} (x : Fin d → ℝ) : wordMap ([] : List (ℕ × Fin d)) x = x := (rfl)

/-- `wordMap` on a cons word applies `branchMap a` first, then `wordMap u`. -/
@[simp]
theorem wordMap_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordMap (a :: u) x = wordMap u (branchMap a x) := (rfl)

/-- `wordMap` of a single-letter word `[a]` is `branchMap a`. -/
theorem wordMap_singleton {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    wordMap [a] x = branchMap a x := (rfl)

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
theorem wordDelay_nil {d : ℕ} (x : Fin d → ℝ) : wordDelay ([] : List (ℕ × Fin d)) x = 0 := (rfl)

/-- `wordDelay` on `a :: u` splits into `branchDelay a x + wordDelay u (branchMap a x)`. -/
@[simp]
theorem wordDelay_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordDelay (a :: u) x = branchDelay a x + wordDelay u (branchMap a x) := by
  rw [branchDelay_apply]; rfl

/-- `wordDelay` of a single-letter word `[a]` is `branchDelay a`. -/
theorem wordDelay_singleton {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    wordDelay [a] x = branchDelay a x := by simp

/-- Chronological cocycle identity for `wordDelay`:
`wordDelay (u ++ v) x = wordDelay u x + wordDelay v (wordMap u x)`. -/
@[simp]
theorem wordDelay_append {d : ℕ} (u v : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordDelay (u ++ v) x = wordDelay u x + wordDelay v (wordMap u x) := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih => simp only [List.cons_append, wordDelay_cons, ih, wordMap_cons]; ring

/-- The homogeneous linear endomorphism `γ_u` of a chronological word `u : List (ℕ × Fin d)`:
`[]` acts as `LinearMap.id` and `a :: u` acts as `wordLinearMap u ∘ₗ branchLinearMap a`. -/
def wordLinearMap {d : ℕ} : List (ℕ × Fin d) → ((Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ))
  | [] => LinearMap.id
  | a :: u => wordLinearMap u ∘ₗ branchLinearMap a

/-- `wordLinearMap []` is the identity linear map. -/
@[simp]
theorem wordLinearMap_nil {d : ℕ} :
    wordLinearMap ([] : List (ℕ × Fin d)) = LinearMap.id := (rfl)

/-- `wordLinearMap (a :: u)` composes `wordLinearMap u` after `branchLinearMap a`. -/
@[simp]
theorem wordLinearMap_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) :
    wordLinearMap (a :: u) = wordLinearMap u ∘ₗ branchLinearMap a := (rfl)

/-- `wordLinearMap [a]` is `branchLinearMap a`. -/
theorem wordLinearMap_singleton {d : ℕ} (a : ℕ × Fin d) :
    wordLinearMap [a] = branchLinearMap a := by simp

/-- Chronological concatenation law for `wordLinearMap`:
`wordLinearMap (u ++ v) = wordLinearMap v ∘ₗ wordLinearMap u`. -/
@[simp]
theorem wordLinearMap_append {d : ℕ} (u v : List (ℕ × Fin d)) :
    wordLinearMap (u ++ v) = wordLinearMap v ∘ₗ wordLinearMap u := by
  induction u with
  | nil => ext; simp
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
  | nil => simp [last_smul_orderedSimplexLift_orderedConeProject hy]
  | cons a u ih =>
    have hq := branchDenom_pos_of_mem_orderedSimplex a (orderedConeProject_mem_orderedSimplex hy)
    rw [wordLinearMap_cons, LinearMap.comp_apply, ih (branchLinearMap_mem_orderedCone a hy),
      branchLinearMap_last_of_mem_orderedCone a hy, orderedConeProject_branchLinearMap a hy,
      wordDelay_cons, Real.exp_add, exp_branchDelay a hq, wordMap_cons]
    simp [mul_assoc]

/-- Projective equivariance of `wordLinearMap` and `wordMap` on `orderedCone d`. -/
theorem orderedConeProject_wordLinearMap {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    orderedConeProject (wordLinearMap u y) = wordMap u (orderedConeProject y) := by
  rw [wordLinearMap_eq_smul_orderedSimplexLift u hy,
    orderedConeProject_smul (mul_pos (last_pos_of_mem_orderedCone hy) (Real.exp_pos _)).ne',
    orderedConeProject_orderedSimplexLift]

/-- Homogeneous delay formula on `orderedCone d`:
`wordDelay u (orderedConeProject y) = log (wordLinearMap u y (Fin.last (d + 1)) / y_{d+1})`. -/
theorem wordDelay_orderedConeProject {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    wordDelay u (orderedConeProject y) =
      Real.log (wordLinearMap u y (Fin.last (d + 1)) / y (Fin.last (d + 1))) := by
  rw [wordLinearMap_eq_smul_orderedSimplexLift u hy]
  simp [mul_div_cancel_left₀ _ (last_pos_of_mem_orderedCone hy).ne']

/-! ### Delay lower bounds and finiteness of sublevel sets -/

/-- Linear lower bound on `orderedSimplex d`:
`(u.length : ℝ) * log (3 / 2) ≤ wordDelay u x`. -/
theorem length_mul_log_three_div_two_le_wordDelay {d : ℕ} (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    (u.length : ℝ) * Real.log (3 / 2) ≤ wordDelay u x := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, wordDelay_cons]
    linarith [log_three_div_two_le_branchDelay_of_mem_orderedSimplex a hx,
      ih (branchMap_mem_orderedSimplex a hx)]

/-- On `orderedSimplex d`, every word has nonnegative delay. -/
theorem wordDelay_nonneg_of_mem_orderedSimplex {d : ℕ} (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 0 ≤ wordDelay u x :=
  (mul_nonneg u.length.cast_nonneg (Real.log_nonneg (by norm_num))).trans
    (length_mul_log_three_div_two_le_wordDelay u hx)

/-- Every nonempty word has delay at least `log (3 / 2)` on `orderedSimplex d`. -/
theorem log_three_div_two_le_wordDelay_of_ne_nil {d : ℕ} {u : List (ℕ × Fin d)} (hu : u ≠ [])
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Real.log (3 / 2) ≤ wordDelay u x := by
  rcases u with _ | ⟨a, v⟩; · contradiction
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
  have hpos : (0 : ℝ) < ((a.1 : ℝ) + 3) / 2 := by positivity
  have hexp : ((a.1 : ℝ) + 3) / 2 ≤ Real.exp r := by
    simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr
      ((log_add_three_div_two_le_wordDelay_of_mem ha hx).trans hr)
  linarith

/-- For every `x ∈ orderedSimplex d` and `r : ℝ`, only finitely many words satisfy
`wordDelay u x ≤ r`. -/
theorem finite_setOf_wordDelay_le {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.Finite := by
  let L : ℕ := ⌊r / Real.log (3 / 2)⌋₊
  let M : ℕ := ⌊2 * Real.exp r⌋₊ + 1
  refine ((List.finite_setOf_sum_map_snd_add_one_le (Fin d) (L * M)).image
    (List.map Prod.swap)).subset fun u hu => ⟨u.map Prod.swap, ?_, by simp [Function.comp_def]⟩
  rw [mem_ofPred_eq] at hu
  rw [mem_ofPred_eq, List.map_map]
  have hlen : u.length ≤ L := by
    by_cases hr0 : 0 ≤ r
    · exact Nat.le_floor ((le_div_iff₀ (Real.log_pos (by norm_num))).mpr
        ((length_mul_log_three_div_two_le_wordDelay u hx).trans hu))
    · linarith [wordDelay_nonneg_of_mem_orderedSimplex u hx]
  have hbound : ∀ b ∈ (u.map fun p : ℕ × Fin d => p.1 + 1), b ≤ M := fun b hb => by
    rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
    exact Nat.succ_le_succ (Nat.le_floor
      (by linarith [fst_le_two_mul_exp_sub_three_of_wordDelay_le ha hx hu]))
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
    wordCount d x r = {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.ncard := (rfl)

/-- Scaling invariance of `wordCount` under `orderedConeProject`: nonzero scalar multiplication on
`y` preserves the projected renewal count. -/
theorem wordCount_orderedConeProject_smul (d : ℕ) {c : ℝ} (hc : c ≠ 0) (y : Fin (d + 2) → ℝ)
    (r : ℝ) :
    wordCount d (orderedConeProject (c • y)) r = wordCount d (orderedConeProject y) r := by
  rw [orderedConeProject_smul hc]

/-- For `r < 0` and `x ∈ orderedSimplex d`, `wordCount d x r = 0`. -/
theorem wordCount_eq_zero_of_lt_zero {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    {r : ℝ} (hr : r < 0) : wordCount d x r = 0 := by
  rw [wordCount_apply, show {u : List (ℕ × Fin d) | wordDelay u x ≤ r} = ∅ from
    eq_empty_of_forall_notMem fun u hu => not_le_of_gt
      (hr.trans_le (wordDelay_nonneg_of_mem_orderedSimplex u hx)) hu, Set.ncard_empty]

/-- For `0 ≤ r < log (3 / 2)` and `x ∈ orderedSimplex d`, only the empty word contributes, so
`wordCount d x r = 1`. -/
theorem wordCount_eq_one_of_lt_log_three_div_two {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < Real.log (3 / 2)) :
    wordCount d x r = 1 := by
  have hset : {u : List (ℕ × Fin d) | wordDelay u x ≤ r} = {[]} := by
    ext u; simp only [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun hu => by by_contra hne; linarith [log_three_div_two_le_wordDelay_of_ne_nil hne hx],
      fun h => h ▸ by simpa using hr0⟩
  rw [wordCount_apply, hset, Set.ncard_singleton]

/-- At `r = 0` on `orderedSimplex d`, `wordCount d x 0 = 1`. -/
@[simp]
theorem wordCount_zero_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : wordCount d x 0 = 1 :=
  wordCount_eq_one_of_lt_log_three_div_two hx le_rfl (Real.log_pos (by norm_num))

/-- `wordCount d x` is monotone in `r` at every `x ∈ orderedSimplex d`. -/
theorem monotone_wordCount {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Monotone (wordCount d x) := fun _ r₂ hr =>
  Set.ncard_le_ncard (fun _ hu => le_trans hu hr) (finite_setOf_wordDelay_le hx r₂)

/-- Local constancy of `wordCount d x` from the right at every `r₀ : ℝ` when
`x ∈ orderedSimplex d`. -/
theorem exists_Ico_wordCount_eq {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r₀ : ℝ) :
    ∃ δ > 0, ∀ r ∈ Ico r₀ (r₀ + δ), wordCount d x r = wordCount d x r₀ := by
  have hT : {u : List (ℕ × Fin d) | wordDelay u x ≤ r₀ + 1 ∧ r₀ < wordDelay u x}.Finite :=
    (finite_setOf_wordDelay_le hx (r₀ + 1)).subset fun _ hu => hu.1
  let F : Finset ℝ := insert (r₀ + 1) (hT.toFinset.image fun u => wordDelay u x)
  let m := F.min' (Finset.insert_nonempty _ _)
  have hm : r₀ < m := (Finset.lt_min'_iff _ _).mpr fun y hy => by
    rcases Finset.mem_insert.mp hy with rfl | hy
    · linarith
    · rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
      exact (hT.mem_toFinset.mp hu).2
  refine ⟨m - r₀, sub_pos.mpr hm, fun r hr => ?_⟩
  have hm1 : m ≤ r₀ + 1 := Finset.min'_le F _ (Finset.mem_insert_self _ _)
  rcases mem_Ico.mp hr with ⟨hr1, hr2⟩
  rw [wordCount_apply, wordCount_apply]; congr 1; ext u; simp only [mem_ofPred_eq]
  refine ⟨fun hu => ?_, fun hu => hu.trans hr1⟩
  by_contra hgt
  have hu_mem : u ∈ hT.toFinset :=
    hT.mem_toFinset.mpr ⟨hu.trans (hr2.le.trans (by linarith)), not_le.mp hgt⟩
  have hm_le : m ≤ wordDelay u x :=
    Finset.min'_le F _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hu_mem))
  linarith

/-- `wordCount d x` is right-continuous at every `r₀ : ℝ` when `x ∈ orderedSimplex d`. -/
theorem continuousWithinAt_wordCount_Ici {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (r₀ : ℝ) : ContinuousWithinAt (wordCount d x) (Ici r₀) r₀ := by
  obtain ⟨δ, hδ, hconst⟩ := exists_Ico_wordCount_eq hx r₀
  exact continuousWithinAt_const.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ico_mem_nhdsGE (lt_add_of_pos_right r₀ hδ)) hconst) rfl

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
  have hpos : (0 : ℝ) < ((a.1 : ℝ) + 3) / 2 := by positivity
  have hexp : ((a.1 : ℝ) + 3) / 2 ≤ Real.exp r := by
    simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr
      ((log_add_three_div_two_le_branchDelay_of_mem_orderedSimplex a hx).trans ha)
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor (by linarith)), trivial⟩

/-- At each `x ∈ orderedSimplex d` and `r : ℝ`, the renewal summand
`a ↦ wordCount d (branchMap a x) (r - branchDelay a x)` has finite support. -/
theorem finite_support_wordCount_sub_branchDelay {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) (r : ℝ) :
    (Function.support fun a : ℕ × Fin d =>
      wordCount d (branchMap a x) (r - branchDelay a x)).Finite := by
  refine (finite_setOf_branchDelay_le hx r).subset fun a ha => ?_
  by_contra hgt
  exact ha (wordCount_eq_zero_of_lt_zero (branchMap_mem_orderedSimplex a hx)
    (sub_neg.mpr (not_le.mp hgt)))

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
  · have hS := finite_setOf_wordDelay_le hx r
    have hB := finite_setOf_branchDelay_le hx r
    let F : Finset (ℕ × Fin d) := hB.toFinset
    let G : (ℕ × Fin d) → Finset (List (ℕ × Fin d)) := fun a =>
      (finite_setOf_wordDelay_le (branchMap_mem_orderedSimplex a hx)
        (r - branchDelay a x)).toFinset
    let emb : (ℕ × Fin d) → List (ℕ × Fin d) ↪ List (ℕ × Fin d) := fun a =>
      ⟨List.cons a, fun _ _ h => (List.cons.inj h).2⟩
    have hpart : hS.toFinset = insert [] (F.biUnion fun a => (G a).map (emb a)) := by
      ext u; rcases u with _ | ⟨a, v⟩
      · simp [hS.mem_toFinset, hr]
      · simp only [hS.mem_toFinset, mem_ofPred_eq, wordDelay_cons, Finset.mem_insert,
          reduceCtorEq, false_or, Finset.mem_biUnion, Finset.mem_map]
        refine ⟨fun huv => ⟨a, hB.mem_toFinset.mpr ?_, v, ?_, rfl⟩, ?_⟩
        · rw [mem_ofPred_eq]
          linarith [wordDelay_nonneg_of_mem_orderedSimplex v (branchMap_mem_orderedSimplex a hx)]
        · exact (Set.Finite.mem_toFinset _).mpr (le_sub_iff_add_le'.mpr huv)
        · rintro ⟨_, _, _, hv', heq⟩
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          exact le_sub_iff_add_le'.mp ((Set.Finite.mem_toFinset _).mp hv')
    have hdisj : (F : Set (ℕ × Fin d)).PairwiseDisjoint fun a => (G a).map (emb a) := by
      intro a₁ _ a₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      rintro _ hu₁ hu₂
      rcases Finset.mem_map.mp hu₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_map.mp hu₂ with ⟨_, _, heq⟩
      exact hne (List.cons.inj heq).1.symm
    have hcard_G : ∀ a, ((G a).map (emb a)).card =
        wordCount d (branchMap a x) (r - branchDelay a x) := fun a => by
      rw [Finset.card_map, wordCount_apply,
        Set.ncard_eq_toFinset_card _
          (finite_setOf_wordDelay_le (branchMap_mem_orderedSimplex a hx) (r - branchDelay a x))]
    have htsum : (∑' a : ℕ × Fin d, wordCount d (branchMap a x) (r - branchDelay a x)) =
        ∑ a ∈ F, wordCount d (branchMap a x) (r - branchDelay a x) :=
      tsum_eq_sum fun a ha => wordCount_eq_zero_of_lt_zero (branchMap_mem_orderedSimplex a hx)
        (sub_neg.mpr (not_le.mp fun hle => ha (hB.mem_toFinset.mpr hle)))
    simp only [hr, ↓reduceIte]
    rw [htsum, wordCount_apply, Set.ncard_eq_toFinset_card _ hS, hpart,
      Finset.card_insert_of_notMem (by simp [emb]), Finset.card_biUnion hdisj, add_comm 1]
    simp [hcard_G]
  · have hzero : ∀ a : ℕ × Fin d, wordCount d (branchMap a x) (r - branchDelay a x) = 0 := fun a =>
      wordCount_eq_zero_of_lt_zero (branchMap_mem_orderedSimplex a hx)
        (by linarith [branchDelay_pos_of_mem_orderedSimplex a hx])
    simp [hr, wordCount_eq_zero_of_lt_zero hx (not_le.mp hr), hzero]

/-! ### Freeness of the accelerated Markoff–Hurwitz semigroup `Γ'` -/

/-- Unaccelerated chronological word action on `Fin (d + 2) → ℝ` over `Fin (d + 1)`. -/
def unaccelWordLinearMap {d : ℕ} :
    List (Fin (d + 1)) → ((Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ))
  | [] => LinearMap.id
  | j :: w => unaccelWordLinearMap w ∘ₗ hurwitzGen j

/-- `unaccelWordLinearMap []` is the identity linear map. -/
@[simp]
theorem unaccelWordLinearMap_nil {d : ℕ} :
    unaccelWordLinearMap ([] : List (Fin (d + 1))) = LinearMap.id := (rfl)

/-- `unaccelWordLinearMap (j :: w)` composes `unaccelWordLinearMap w` after `hurwitzGen j`. -/
@[simp]
theorem unaccelWordLinearMap_cons {d : ℕ} (j : Fin (d + 1)) (w : List (Fin (d + 1))) :
    unaccelWordLinearMap (j :: w) = unaccelWordLinearMap w ∘ₗ hurwitzGen j := (rfl)

/-- Chronological concatenation law for `unaccelWordLinearMap`. -/
@[simp]
theorem unaccelWordLinearMap_append {d : ℕ} (w₁ w₂ : List (Fin (d + 1))) :
    unaccelWordLinearMap (w₁ ++ w₂) = unaccelWordLinearMap w₂ ∘ₗ unaccelWordLinearMap w₁ := by
  induction w₁ with
  | nil => ext; simp
  | cons j w₁ ih =>
    simp only [List.cons_append, unaccelWordLinearMap_cons, ih, LinearMap.comp_assoc]

/-- For `1 ≤ d`, the unaccelerated Markoff–Hurwitz generators `hurwitzGen j` (`j : Fin (d + 1)`)
freely generate their linear semigroup: `unaccelWordLinearMap` is injective. -/
theorem unaccelWordLinearMap_injective {d : ℕ} (hd : 1 ≤ d) :
    Function.Injective (unaccelWordLinearMap (d := d)) := by
  let y₀ := orderedSimplexLift (orderedSimplexInteriorPoint d)
  have hy₀ : y₀ ∈ strictOrderedCone d := orderedSimplexLift_interiorPoint_mem_strictOrderedCone hd
  have hmem : ∀ w : List (Fin (d + 1)), unaccelWordLinearMap w y₀ ∈ strictOrderedCone d ∧
      (w ≠ [] → 1 < unaccelWordLinearMap w y₀ (Fin.last (d + 1))) := fun w => by
    induction w using List.reverseRecOn with
    | nil => exact ⟨hy₀, fun h => absurd rfl h⟩
    | append_singleton u j ih =>
      have hge1 : 1 ≤ unaccelWordLinearMap u y₀ (Fin.last (d + 1)) := by
        by_cases hu : u = []
        · subst hu; simp [y₀]
        · exact (ih.2 hu).le
      simp only [unaccelWordLinearMap_append, unaccelWordLinearMap_cons, unaccelWordLinearMap_nil,
        LinearMap.id_comp, LinearMap.comp_apply]
      exact ⟨hurwitzGen_mem_strictOrderedCone hd j ih.1,
        fun _ => lt_of_le_of_lt hge1 (last_lt_hurwitzGen_last_of_mem_strictOrderedCone j ih.1)⟩
  suffices ∀ w₁ w₂ : List (Fin (d + 1)),
      unaccelWordLinearMap w₁ y₀ = unaccelWordLinearMap w₂ y₀ → w₁ = w₂ from
    fun w₁ w₂ hmap => this w₁ w₂ (congrFun (congrArg DFunLike.coe hmap) y₀)
  intro w₁
  induction w₁ using List.reverseRecOn with
  | nil =>
    intro w₂ heq; by_contra hw₂
    have hgt := (hmem w₂).2 (Ne.symm hw₂); rw [← heq] at hgt; simp [y₀] at hgt
  | append_singleton u₁ j₁ ih =>
    intro w₂ heq
    induction w₂ using List.reverseRecOn with
    | nil =>
      have hgt := (hmem (u₁ ++ [j₁])).2 (by simp); rw [heq] at hgt; simp [y₀] at hgt
    | append_singleton u₂ j₂ _ =>
      obtain ⟨rfl, hu_eq⟩ :=
        hurwitzGen_inj_on_strictOrderedCone (hmem u₁).1 (hmem u₂).1 (by simpa using heq)
      rw [ih u₂ hu_eq]

/-- Chronological expansion of an accelerated word `u : List (ℕ × Fin d)` into an unaccelerated
word in `List (Fin (d + 1))`: each letter `(A, j)` expands to `j :: replicate A d`. -/
def expandWord {d : ℕ} : List (ℕ × Fin d) → List (Fin (d + 1))
  | [] => []
  | a :: u => Fin.castSucc a.2 :: (List.replicate a.1 (Fin.last d) ++ expandWord u)

/-- `expandWord` of the empty word is `[]`. -/
@[simp]
theorem expandWord_nil {d : ℕ} : expandWord ([] : List (ℕ × Fin d)) = [] := (rfl)

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
    intro A; induction A with
    | zero => rfl
    | succ A ih => rw [List.replicate_succ, unaccelWordLinearMap_cons, ih, pow_succ]; rfl
  induction u with
  | nil => rfl
  | cons a u ih =>
    rw [expandWord_cons, ← List.cons_append, unaccelWordLinearMap_append, ih,
      unaccelWordLinearMap_cons, hrep, wordLinearMap_cons]
    ext y m; simp [branchLinearMap_apply]

/-- `expandWord` is injective: the maximal runs of `Fin.last d` uniquely delimit accelerated
letters. -/
theorem expandWord_injective {d : ℕ} : Function.Injective (expandWord (d := d)) := by
  have hnot_last : ∀ (u : List (ℕ × Fin d)) (rest : List (Fin (d + 1))),
      expandWord u ≠ Fin.last d :: rest := by
    rintro (_ | ⟨c, v⟩) rest h
    · simp at h
    · exact (Fin.castSucc_lt_last c.2).ne (List.cons.inj h).1
  have hrep_inj : ∀ (A B : ℕ) (u₁ u₂ : List (ℕ × Fin d)),
      List.replicate A (Fin.last d) ++ expandWord u₁ =
        List.replicate B (Fin.last d) ++ expandWord u₂ →
      A = B ∧ expandWord u₁ = expandWord u₂ := by
    intro A; induction A with
    | zero =>
      rintro (_ | B) u₁ u₂ h
      · exact ⟨rfl, by simpa using h⟩
      · exact absurd (by simpa [List.replicate_succ] using h) (hnot_last u₁ _)
    | succ A ih =>
      rintro (_ | B) u₁ u₂ h
      · exact absurd (by simpa [List.replicate_succ] using h.symm) (hnot_last u₂ _)
      · obtain ⟨rfl, hu⟩ := ih B u₁ u₂ (by simpa [List.replicate_succ] using h)
        exact ⟨rfl, hu⟩
  intro u₁
  induction u₁ with
  | nil =>
    rintro (_ | ⟨b, v⟩) h
    · rfl
    · simp at h
  | cons a u₁ ih =>
    rintro (_ | ⟨b, u₂⟩) h
    · simp at h
    · obtain ⟨ha1, hexp⟩ := hrep_inj a.1 b.1 u₁ u₂ (List.cons.inj h).2
      rw [Prod.ext ha1 (Fin.castSucc_inj.mp (List.cons.inj h).1), ih hexp]

/-- **Freeness of the accelerated Markoff–Hurwitz linear semigroup `Γ'`**
(Gamburd–Magee–Ronan 2019, p. 756, footnote 5): distinct words over `ℕ × Fin d` induce distinct
linear endomorphisms of `Fin (d + 2) → ℝ`. -/
theorem wordLinearMap_injective (d : ℕ) : Function.Injective (wordLinearMap (d := d)) := by
  rcases d with _ | m
  · rintro (_ | ⟨a, _⟩) (_ | ⟨b, _⟩) _
    · rfl
    · exact Fin.elim0 b.2
    · exact Fin.elim0 a.2
    · exact Fin.elim0 a.2
  · intro u₁ u₂ h
    rw [← unaccelWordLinearMap_expandWord, ← unaccelWordLinearMap_expandWord] at h
    exact expandWord_injective (unaccelWordLinearMap_injective (Nat.succ_pos m) h)

end TauCeti.MarkoffHurwitz
