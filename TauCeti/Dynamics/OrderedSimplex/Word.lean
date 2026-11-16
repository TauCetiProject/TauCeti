/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import TauCeti.Dynamics.OrderedSimplex.Branch

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Chronological words, delays, renewal counting, and semigroup freeness

This file develops finite words in the accelerated alphabet `ℕ × Fin d` acting chronologically on
`orderedSimplex d` (`n = d + 2`): the empty word acts as the identity and `a :: u` applies `a`
first and then `u`.

* `TauCeti.OrderedSimplex.wordMap`: the branch composition `F_u`, with `F_{a :: u} = F_u ∘ F_a`.
* `TauCeti.OrderedSimplex.wordDelay`: the cumulative logarithmic delay `T_u`, with
  `T_{a :: u}(w) = log q_a(w) + T_u(F_a w)`.
* `TauCeti.OrderedSimplex.wordCount`: the renewal counting function
  `N(w, r) = #{u | T_u(w) ≤ r}` over the accelerated semigroup with identity.
* `TauCeti.OrderedSimplex.wordMove` and `TauCeti.OrderedSimplex.unaccelWordMove`: the
  corresponding chronological compositions of linear moves on `Fin (d + 2) → ℝ`.

On `orderedSimplex d` (and `orderedCone d`), we prove:
* concatenation laws for `wordMap`, `wordDelay`, and `wordMove`, plus invariance and smoothness;
* the homogeneous delay identity `T_u(w) = log ((γ_u y)_n / y_n)` and scale invariance of `N`;
* lower bounds `T_u(w) ≥ |u| log (3 / 2)` and `A ≤ 2 e^r - 3` for every letter `(A, j) ∈ u` with
  `T_u(w) ≤ r`, yielding finiteness of `{u | T_u(w) ≤ r}`;
* monotonicity, small-`r` values (`0` for `r < 0` and `1` for `0 ≤ r < log (3 / 2)`), indicator-sum
  representation, local right-constancy (hence right-continuity), and Borel measurability of `N`;
* the renewal equation `N(w, r) = 1{r ≥ 0} + ∑_a N(F_a w, r - τ_a(w))` with finite support;
* freeness of the unaccelerated semigroup (for `1 ≤ d`) and of the accelerated semigroup
  `wordMove` (for every `d : ℕ`) as linear maps on `Fin (d + 2) → ℝ`.

## References

* A. Gamburd, M. Magee and R. Ronan, *An asymptotic formula for integer points on Markoff–Hurwitz
  varieties*, Ann. of Math. (2) 190 (2019), no. 3, 751–809, (1.7), (4.1), p. 756 and footnote 5.
-/

public section

noncomputable section

open Filter Finset Set Topology
open scoped ContDiff

namespace TauCeti.OrderedSimplex

/-! ### Chronological words, delays, and linear moves -/

/-- The map `F_u` of a word read chronologically: the first letter acts first,
`F_{a :: u} = F_u ∘ F_a`, and the empty word acts as the identity. -/
def wordMap {d : ℕ} : List (ℕ × Fin d) → (Fin d → ℝ) → (Fin d → ℝ)
  | [], x => x
  | a :: u, x => wordMap u (branchMap a x)

/-- The delay of a word read chronologically: the first letter acts first, and
`T_{a :: u}(w) = log q_a(w) + T_u(F_a w)`; the empty word has delay `0`. -/
def wordDelay {d : ℕ} : List (ℕ × Fin d) → (Fin d → ℝ) → ℝ
  | [], _ => 0
  | a :: u, x => Real.log (branchDenom a x) + wordDelay u (branchMap a x)

/-- The renewal count `N(w, r)`: the number of words, the empty word included, whose delay
at `w` is at most `r`. -/
def wordCount (d : ℕ) (x : Fin d → ℝ) (r : ℝ) : ℕ :=
  {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.ncard

/-- The chronological linear move `γ_{a_m} ⋯ γ_{a_1}` of an accelerated word. -/
def wordMove {d : ℕ} : List (ℕ × Fin d) → (Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ)
  | [] => LinearMap.id
  | a :: u => (wordMove u).comp (accelMove a)

/-- The chronological linear move of an unaccelerated word in `Fin (d + 1)`. -/
def unaccelWordMove {d : ℕ} : List (Fin (d + 1)) → (Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ)
  | [] => LinearMap.id
  | j :: js => (unaccelWordMove js).comp (unaccelMove j)

@[simp]
theorem wordMap_nil {d : ℕ} (x : Fin d → ℝ) : wordMap [] x = x :=
  (rfl)

@[simp]
theorem wordMap_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordMap (a :: u) x = wordMap u (branchMap a x) :=
  (rfl)

theorem wordMap_singleton {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    wordMap [a] x = branchMap a x :=
  (rfl)

@[simp]
theorem wordDelay_nil {d : ℕ} (x : Fin d → ℝ) : wordDelay [] x = 0 :=
  (rfl)

@[simp]
theorem wordDelay_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordDelay (a :: u) x = branchDelay a x + wordDelay u (branchMap a x) := by
  rw [wordDelay, branchDelay_def]

theorem wordDelay_singleton {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    wordDelay [a] x = branchDelay a x := by
  simp

theorem wordCount_def (d : ℕ) (x : Fin d → ℝ) (r : ℝ) :
    wordCount d x r = {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.ncard :=
  (rfl)

@[simp]
theorem wordMove_nil {d : ℕ} : wordMove (d := d) [] = LinearMap.id :=
  (rfl)

@[simp]
theorem wordMove_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) :
    wordMove (a :: u) = (wordMove u).comp (accelMove a) :=
  (rfl)

theorem wordMove_singleton {d : ℕ} (a : ℕ × Fin d) : wordMove [a] = accelMove a := by
  simp

@[simp]
theorem unaccelWordMove_nil {d : ℕ} : unaccelWordMove (d := d) [] = LinearMap.id :=
  (rfl)

@[simp]
theorem unaccelWordMove_cons {d : ℕ} (j : Fin (d + 1)) (js : List (Fin (d + 1))) :
    unaccelWordMove (j :: js) = (unaccelWordMove js).comp (unaccelMove j) :=
  (rfl)

theorem unaccelWordMove_singleton {d : ℕ} (j : Fin (d + 1)) :
    unaccelWordMove [j] = unaccelMove j := by
  simp

/-- Concatenation law for branch maps: `F_{u ++ v} = F_v ∘ F_u`. -/
theorem wordMap_append {d : ℕ} (u v : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordMap (u ++ v) x = wordMap v (wordMap u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => simp [ih]

/-- Concatenation law for word delays: `T_{u ++ v}(w) = T_u(w) + T_v(F_u w)`. -/
theorem wordDelay_append {d : ℕ} (u v : List (ℕ × Fin d)) (x : Fin d → ℝ) :
    wordDelay (u ++ v) x = wordDelay u x + wordDelay v (wordMap u x) := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    simp [ih, add_assoc]

/-- Concatenation law for accelerated linear word moves. -/
theorem wordMove_append {d : ℕ} (u v : List (ℕ × Fin d)) :
    wordMove (u ++ v) = (wordMove v).comp (wordMove u) := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih, LinearMap.comp_assoc]

/-- Concatenation law for unaccelerated linear word moves. -/
theorem unaccelWordMove_append {d : ℕ} (js₁ js₂ : List (Fin (d + 1))) :
    unaccelWordMove (js₁ ++ js₂) = (unaccelWordMove js₂).comp (unaccelWordMove js₁) := by
  induction js₁ with
  | nil => simp
  | cons j js₁ ih => simp [ih, LinearMap.comp_assoc]

/-- Every word map preserves `orderedSimplex d`. -/
theorem wordMap_mapsTo {d : ℕ} (u : List (ℕ × Fin d)) :
    MapsTo (wordMap u) (orderedSimplex d) (orderedSimplex d) := by
  induction u with
  | nil => exact mapsTo_id _
  | cons a u ih => exact ih.comp (branchMap_mapsTo a)

/-- Every word map is smooth on `orderedSimplex d`. -/
theorem contDiffOn_wordMap {d : ℕ} (u : List (ℕ × Fin d)) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (wordMap u) (orderedSimplex d) := by
  induction u with
  | nil => exact contDiffOn_id
  | cons a u ih =>
    exact ih.comp (contDiffOn_branchMap_orderedSimplex a n) (branchMap_mapsTo a)

/-- Every word delay is smooth on `orderedSimplex d`. -/
theorem contDiffOn_wordDelay {d : ℕ} (u : List (ℕ × Fin d)) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (wordDelay u) (orderedSimplex d) := by
  induction u with
  | nil => exact contDiffOn_const
  | cons a u ih =>
    have hcomp : ContDiffOn ℝ n (fun x => wordDelay u (branchMap a x)) (orderedSimplex d) :=
      ih.comp (contDiffOn_branchMap_orderedSimplex a n) (branchMap_mapsTo a)
    exact ((contDiffOn_branchDelay_orderedSimplex a n).add hcomp).congr fun x _ =>
      wordDelay_cons a u x

/-- Every accelerated linear word move preserves `orderedCone d`. -/
theorem wordMove_mapsTo_orderedCone {d : ℕ} (u : List (ℕ × Fin d)) :
    MapsTo (wordMove u) (orderedCone d) (orderedCone d) := by
  induction u with
  | nil => exact mapsTo_id _
  | cons a u ih => exact ih.comp (accelMove_mapsTo_orderedCone a)

/-- Every unaccelerated linear word move preserves `orderedCone d`. -/
theorem unaccelWordMove_mapsTo_orderedCone {d : ℕ} (js : List (Fin (d + 1))) :
    MapsTo (unaccelWordMove js) (orderedCone d) (orderedCone d) := by
  induction js with
  | nil => exact mapsTo_id _
  | cons j js ih => exact ih.comp (unaccelMove_mapsTo_orderedCone j)

/-! ### Homogeneous meaning and scale invariance -/

/-- Homogeneous intertwining identity for chronological words on `orderedCone d`:
`γ_u y = y_n exp(T_u(w)) (F_u(w), 1)` where `w = normalizeCone y`. -/
theorem wordMove_eq_smul_toHomogeneous {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    wordMove u y =
      (y (Fin.last (d + 1)) * Real.exp (wordDelay u (normalizeCone y))) •
        toHomogeneous (wordMap u (normalizeCone y)) := by
  induction u generalizing y with
  | nil =>
    simp [smul_toHomogeneous_normalizeCone (orderedCone_subset_coneSpan d hy)
      (last_pos_of_mem_orderedCone hy).ne']
  | cons a u ih =>
    have hy' : accelMove a y ∈ orderedCone d := accelMove_mapsTo_orderedCone a hy
    have hq : 0 < branchDenom a (normalizeCone y) :=
      branchDenom_pos a (normalizeCone_mem_orderedSimplex hy)
    rw [wordMove_cons, LinearMap.comp_apply, ih hy', normalizeCone_accelMove a hy,
      accelMove_last_eq_mul_branchDenom a hy, wordDelay_cons, wordMap_cons, Real.exp_add,
      branchDelay_def, Real.exp_log hq, mul_assoc]

/-- The last coordinate of `γ_u y` on `orderedCone d` equals `y_n exp(T_u(normalizeCone y))`. -/
theorem wordMove_last_eq {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    wordMove u y (Fin.last (d + 1)) =
      y (Fin.last (d + 1)) * Real.exp (wordDelay u (normalizeCone y)) := by
  rw [wordMove_eq_smul_toHomogeneous u hy]
  simp

/-- Projective normalisation intertwines `wordMove u` and `wordMap u` on `orderedCone d`. -/
theorem normalizeCone_wordMove {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    normalizeCone (wordMove u y) = wordMap u (normalizeCone y) := by
  have hpos : 0 < y (Fin.last (d + 1)) * Real.exp (wordDelay u (normalizeCone y)) :=
    mul_pos (last_pos_of_mem_orderedCone hy) (Real.exp_pos _)
  rw [wordMove_eq_smul_toHomogeneous u hy, normalizeCone_smul hpos.ne',
    normalizeCone_toHomogeneous]

/-- Homogeneous formula for the word delay: `T_u(normalizeCone y) = log ((γ_u y)_n / y_n)`. -/
theorem wordDelay_normalizeCone {d : ℕ} (u : List (ℕ × Fin d)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    wordDelay u (normalizeCone y) =
      Real.log (wordMove u y (Fin.last (d + 1)) / y (Fin.last (d + 1))) := by
  rw [wordMove_last_eq u hy, mul_div_cancel_left₀ _ (last_pos_of_mem_orderedCone hy).ne',
    Real.log_exp]

/-- Homogeneous description of the renewal count on `orderedCone d`. -/
theorem wordCount_normalizeCone_eq {d : ℕ} {y : Fin (d + 2) → ℝ} (hy : y ∈ orderedCone d)
    (r : ℝ) :
    wordCount d (normalizeCone y) r =
      {u : List (ℕ × Fin d) |
        Real.log (wordMove u y (Fin.last (d + 1)) / y (Fin.last (d + 1))) ≤ r}.ncard := by
  rw [wordCount_def]
  congr 1
  ext u
  simp [wordDelay_normalizeCone u hy]

/-- Scale invariance of the renewal count under nonzero scaling of a homogeneous vector. -/
theorem wordCount_normalizeCone_smul {d : ℕ} {c : ℝ} (hc : c ≠ 0) (y : Fin (d + 2) → ℝ) (r : ℝ) :
    wordCount d (normalizeCone (c • y)) r = wordCount d (normalizeCone y) r := by
  rw [normalizeCone_smul hc]

/-! ### Lower bounds and finiteness of contributing words -/

/-- Linear lower bound `|u| log (3 / 2) ≤ T_u(w)` on `orderedSimplex d`. -/
theorem length_mul_log_le_wordDelay {d : ℕ} (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    (u.length : ℝ) * Real.log (3 / 2) ≤ wordDelay u x := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    have h1 := log_three_div_two_le_branchDelay a hx
    have h2 := ih (branchMap_mapsTo a hx)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, wordDelay_cons]
    linarith

/-- Every word delay is nonnegative on `orderedSimplex d`. -/
theorem wordDelay_nonneg {d : ℕ} (u : List (ℕ × Fin d)) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    0 ≤ wordDelay u x := by
  have hlog : 0 ≤ Real.log (3 / 2) := (Real.log_pos (by norm_num)).le
  exact (mul_nonneg (Nat.cast_nonneg u.length) hlog).trans (length_mul_log_le_wordDelay u hx)

/-- Every nonempty word has delay at least `log (3 / 2)` on `orderedSimplex d`. -/
theorem log_three_div_two_le_wordDelay_of_ne_nil {d : ℕ} {u : List (ℕ × Fin d)} (hu : u ≠ [])
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Real.log (3 / 2) ≤ wordDelay u x := by
  have hlen : (1 : ℝ) ≤ (u.length : ℝ) := by
    exact_mod_cast List.length_pos_iff.2 hu
  have hlog : 0 ≤ Real.log (3 / 2) := (Real.log_pos (by norm_num)).le
  calc Real.log (3 / 2)
      = 1 * Real.log (3 / 2) := (one_mul _).symm
    _ ≤ (u.length : ℝ) * Real.log (3 / 2) := mul_le_mul_of_nonneg_right hlen hlog
    _ ≤ wordDelay u x := length_mul_log_le_wordDelay u hx

/-- Every nonempty word has strictly positive delay on `orderedSimplex d`. -/
theorem wordDelay_pos_of_ne_nil {d : ℕ} {u : List (ℕ × Fin d)} (hu : u ≠ [])
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    0 < wordDelay u x :=
  (Real.log_pos (by norm_num)).trans_le (log_three_div_two_le_wordDelay_of_ne_nil hu hx)

/-- Every letter `(A, j)` occurring in `u` satisfies `log ((A + 3) / 2) ≤ T_u(w)` on
`orderedSimplex d`. -/
theorem log_le_wordDelay_of_mem {d : ℕ} {u : List (ℕ × Fin d)} {a : ℕ × Fin d} (ha : a ∈ u)
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Real.log (((a.1 : ℝ) + 3) / 2) ≤ wordDelay u x := by
  induction u generalizing x with
  | nil => simp at ha
  | cons b v ih =>
    rw [wordDelay_cons]
    rcases List.mem_cons.1 ha with rfl | hv
    · linarith [log_le_branchDelay a hx, wordDelay_nonneg v (branchMap_mapsTo a hx)]
    · linarith [(branchDelay_pos b hx).le, ih hv (branchMap_mapsTo b hx)]

/-- Every letter `(A, j)` occurring in a word with `T_u(w) ≤ r` satisfies `A ≤ 2 e^r - 3`. -/
theorem letter_fst_le_of_wordDelay_le {d : ℕ} {u : List (ℕ × Fin d)} {a : ℕ × Fin d} (ha : a ∈ u)
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) {r : ℝ} (hr : wordDelay u x ≤ r) :
    (a.1 : ℝ) ≤ 2 * Real.exp r - 3 := by
  have hlog : Real.log (((a.1 : ℝ) + 3) / 2) ≤ r := (log_le_wordDelay_of_mem ha hx).trans hr
  have hexp := Real.exp_le_exp.2 hlog
  rw [Real.exp_log (by positivity)] at hexp
  linarith

/-- For every `x ∈ orderedSimplex d` and `r : ℝ`, only finitely many words satisfy
`wordDelay u x ≤ r`. -/
theorem finite_wordDelay_le {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    {u : List (ℕ × Fin d) | wordDelay u x ≤ r}.Finite := by
  let L : ℕ := Nat.ceil (r / Real.log (3 / 2))
  let M : ℕ := Nat.ceil (2 * Real.exp r)
  let embed : List (Fin (M + 1) × Fin d) → List (ℕ × Fin d) := List.map fun p => (p.1.1, p.2)
  have hfin : (embed '' {l : List (Fin (M + 1) × Fin d) | l.length ≤ L}).Finite :=
    (List.finite_length_le (α := Fin (M + 1) × Fin d) (n := L)).image embed
  refine hfin.subset fun u hu => ?_
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hlen : u.length ≤ L := by
    have h1 : (u.length : ℝ) ≤ r / Real.log (3 / 2) :=
      (le_div_iff₀ hlog).2 ((length_mul_log_le_wordDelay u hx).trans hu)
    exact Nat.cast_le.1 (h1.trans (Nat.le_ceil _))
  let lift : List (Fin (M + 1) × Fin d) :=
    u.map fun a => (⟨min a.1 M, Nat.lt_succ_of_le (min_le_right _ _)⟩, a.2)
  refine ⟨lift, by simpa [lift] using hlen, ?_⟩
  simp only [embed, lift, List.map_map]
  rw [List.map_congr_left (g := id) fun a ha => ?_, List.map_id]
  have haM : a.1 ≤ M := by
    have h1 : (a.1 : ℝ) ≤ 2 * Real.exp r := by
      linarith [letter_fst_le_of_wordDelay_le ha hx hu]
    exact Nat.cast_le.1 (h1.trans (Nat.le_ceil _))
  exact Prod.ext (min_eq_left haM) rfl

/-! ### Monotonicity, small-`r` values, right-continuity, and measurability -/

/-- The renewal count `r ↦ wordCount d x r` is nondecreasing on `orderedSimplex d`. -/
theorem wordCount_mono {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Monotone (wordCount d x) := by
  intro r₁ r₂ hr
  exact Set.ncard_le_ncard (fun _ hu => le_trans hu hr) (finite_wordDelay_le hx r₂)

/-- For `r < 0`, no word contributes to `wordCount d x r`. -/
theorem wordCount_eq_zero_of_neg {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) {r : ℝ}
    (hr : r < 0) :
    wordCount d x r = 0 := by
  rw [wordCount_def]
  have hempty : {u : List (ℕ × Fin d) | wordDelay u x ≤ r} = ∅ := by
    ext u
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact hr.trans_le (wordDelay_nonneg u hx)
  rw [hempty, Set.ncard_empty]

/-- For `0 ≤ r < log (3 / 2)`, only the empty word contributes to `wordCount d x r`. -/
theorem wordCount_eq_one_of_lt_log {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < Real.log (3 / 2)) :
    wordCount d x r = 1 := by
  rw [wordCount_def]
  have hsing : {u : List (ℕ × Fin d) | wordDelay u x ≤ r} = {[]} := by
    ext u
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro hu
      by_contra hne
      have hge := log_three_div_two_le_wordDelay_of_ne_nil hne hx
      linarith
    · rintro rfl
      simpa using hr0
  rw [hsing, Set.ncard_singleton]

/-- At `r = 0`, `wordCount d x 0 = 1` on `orderedSimplex d`. -/
theorem wordCount_zero {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    wordCount d x 0 = 1 :=
  wordCount_eq_one_of_lt_log hx le_rfl (Real.log_pos (by norm_num))

/-- Below any cutoff `R`, `wordCount d x r` is a finite sum of indicators of `[T_u(w), ∞)`. -/
theorem wordCount_eq_sum_indicator {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    {R r : ℝ} (hr : r ≤ R) :
    wordCount d x r =
      ∑ u ∈ (finite_wordDelay_le hx R).toFinset, if wordDelay u x ≤ r then 1 else 0 := by
  classical
  rw [wordCount_def, Set.ncard_eq_toFinset_card _ (finite_wordDelay_le hx r),
    ← Finset.card_filter]
  congr 1
  ext u
  simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, Finset.mem_filter]
  exact ⟨fun h => ⟨h.trans hr, h⟩, fun h => h.2⟩

/-- The renewal count `r ↦ wordCount d x r` is locally constant on the right at every `r : ℝ`. -/
theorem eventually_wordCount_eq_of_Ici {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (r : ℝ) :
    ∃ δ > 0, ∀ r' ∈ Ico r (r + δ), wordCount d x r' = wordCount d x r := by
  let S : Set (List (ℕ × Fin d)) := {u | r < wordDelay u x ∧ wordDelay u x ≤ r + 1}
  have hSfin : S.Finite := (finite_wordDelay_le hx (r + 1)).subset fun _ hu => hu.2
  by_cases hS : S.Nonempty
  · classical
    let T : Finset ℝ := hSfin.toFinset.image fun u => wordDelay u x
    have hT : T.Nonempty := by
      rcases hS with ⟨u, hu⟩
      exact ⟨wordDelay u x, Finset.mem_image_of_mem _ (hSfin.mem_toFinset.2 hu)⟩
    let m : ℝ := T.min' hT
    have hm_gt : r < m := by
      rcases Finset.mem_image.1 (Finset.min'_mem T hT) with ⟨u, hu, hmu⟩
      dsimp only [m]
      rw [← hmu]
      exact (hSfin.mem_toFinset.1 hu).1
    refine ⟨min 1 (m - r), lt_min zero_lt_one (sub_pos.2 hm_gt), fun r' hr' => ?_⟩
    rw [wordCount_def, wordCount_def]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    refine ⟨fun hu => ?_, fun hu => hu.trans hr'.1⟩
    by_contra hlt
    have huS : u ∈ S := ⟨not_le.1 hlt, hu.trans (by linarith [hr'.2, min_le_left 1 (m - r)])⟩
    have hm_le : m ≤ wordDelay u x :=
      Finset.min'_le T _ (Finset.mem_image_of_mem _ (hSfin.mem_toFinset.2 huS))
    linarith [hr'.2, min_le_right 1 (m - r)]
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    refine ⟨1, zero_lt_one, fun r' hr' => ?_⟩
    rw [wordCount_def, wordCount_def]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    refine ⟨fun hu => ?_, fun hu => hu.trans hr'.1⟩
    by_contra hlt
    have huS : u ∈ S := ⟨not_le.1 hlt, hu.trans hr'.2.le⟩
    rw [hS] at huS
    exact huS

/-- The renewal count `r ↦ (wordCount d x r : ℝ)` is right-continuous at every `r : ℝ`. -/
theorem continuousWithinAt_wordCount_Ici {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (r : ℝ) :
    ContinuousWithinAt (fun t => (wordCount d x t : ℝ)) (Ici r) r := by
  rcases eventually_wordCount_eq_of_Ici hx r with ⟨δ, hδ, hconst⟩
  rw [ContinuousWithinAt]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ico_mem_nhdsGE (lt_add_of_pos_right r hδ)] with t ht
  exact congrArg Nat.cast (hconst t ht).symm

/-- The renewal count `r ↦ (wordCount d x r : ℝ)` is Borel measurable on `ℝ`. -/
theorem measurable_wordCount_real {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Measurable fun r => (wordCount d x r : ℝ) :=
  (Nat.mono_cast.comp (wordCount_mono hx)).measurable

/-- The `ℕ`-valued renewal count `r ↦ wordCount d x r` is Borel measurable on `ℝ`. -/
theorem measurable_wordCount {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Measurable (wordCount d x) :=
  (wordCount_mono hx).measurable

/-! ### Renewal equation -/

/-- Only finitely many first letters `a` contribute nonzero terms to the renewal sum at `(x, r)`. -/
theorem finite_support_wordCount_branch {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (r : ℝ) :
    (Function.support fun a : ℕ × Fin d =>
      wordCount d (branchMap a x) (r - branchDelay a x)).Finite := by
  have hpre : ((fun a : ℕ × Fin d => [a]) ⁻¹' {u | wordDelay u x ≤ r}).Finite :=
    (finite_wordDelay_le hx r).preimage fun a _ b _ h => by simpa using h
  refine hpre.subset fun a ha => ?_
  simp only [Function.mem_support, ne_eq] at ha
  simp only [Set.mem_preimage, mem_ofPred_eq, wordDelay_singleton]
  by_contra hlt
  exact ha (wordCount_eq_zero_of_neg (branchMap_mapsTo a hx) (sub_neg.2 (not_le.1 hlt)))

private theorem ncard_nonempty_wordDelay_le {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (r : ℝ) :
    {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u ≠ []}.ncard =
      ∑ᶠ a : ℕ × Fin d, wordCount d (branchMap a x) (r - branchDelay a x) := by
  let f : ℕ × Fin d → ℕ := fun a => wordCount d (branchMap a x) (r - branchDelay a x)
  let T : Set (ℕ × Fin d) := Function.support f
  have hTfin : T.Finite := finite_support_wordCount_branch hx r
  let B : ℕ × Fin d → Set (List (ℕ × Fin d)) :=
    fun a => (a :: ·) '' {v : List (ℕ × Fin d) | wordDelay v (branchMap a x) ≤ r - branchDelay a x}
  have hS₁_eq : {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u ≠ []} = ⋃ a ∈ T, B a := by
    ext u
    simp only [B, T, f, mem_ofPred_eq, mem_iUnion, mem_image, Function.mem_support, ne_eq]
    constructor
    · rintro ⟨hu, hne⟩
      cases u with
      | nil => exact absurd rfl hne
      | cons a v =>
        have hv : wordDelay v (branchMap a x) ≤ r - branchDelay a x := by
          rw [wordDelay_cons] at hu
          linarith
        have hpos : wordCount d (branchMap a x) (r - branchDelay a x) ≠ 0 := by
          rw [wordCount_def, ne_eq,
            Set.ncard_eq_zero (finite_wordDelay_le (branchMap_mapsTo a hx) _)]
          exact Set.Nonempty.ne_empty ⟨v, hv⟩
        exact ⟨a, hpos, v, hv, rfl⟩
    · rintro ⟨a, _, v, hv, rfl⟩
      refine ⟨?_, List.cons_ne_nil _ _⟩
      rw [wordDelay_cons]
      linarith
  have hBfin : ∀ a ∈ T, (B a).Finite := fun a _ =>
    (finite_wordDelay_le (branchMap_mapsTo a hx) _).image _
  have hBdisj : T.PairwiseDisjoint B := by
    intro a₁ _ a₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨v₁, _, rfl⟩ ⟨v₂, _, hEq⟩
    exact hne (List.cons.inj hEq).1.symm
  have hBcard : ∀ a, (B a).ncard = f a := fun a =>
    Set.ncard_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
  rw [hS₁_eq, hTfin.ncard_biUnion hBfin hBdisj]
  simp_rw [hBcard]
  rw [finsum_mem_eq_finite_toFinset_sum f hTfin, finsum_eq_sum f hTfin]

/-- The renewal equation for `wordCount`:
`N(w, r) = 1{r ≥ 0} + ∑ᶠ a, N(F_a w, r - τ_a(w))`. -/
theorem wordCount_renewal {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    wordCount d x r =
      (if 0 ≤ r then 1 else 0) +
        ∑ᶠ a : ℕ × Fin d, wordCount d (branchMap a x) (r - branchDelay a x) := by
  have hSfin := finite_wordDelay_le hx r
  have hSunion : {u : List (ℕ × Fin d) | wordDelay u x ≤ r} =
      {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u = []} ∪
        {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u ≠ []} := by
    ext u
    simp only [mem_union, mem_ofPred_eq]
    tauto
  have hSdisj : Disjoint {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u = []}
      {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u ≠ []} := by
    rw [Set.disjoint_left]
    intro u h0 h1
    exact h1.2 h0.2
  have hS₀_card :
      {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u = []}.ncard = if 0 ≤ r then 1 else 0 := by
    split_ifs with hr
    · have hEq : {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u = []} = {[]} := by
        ext u
        simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => h.2, fun h => ⟨by simp [h, hr], h⟩⟩
      rw [hEq, Set.ncard_singleton]
    · have hEq : {u : List (ℕ × Fin d) | wordDelay u x ≤ r ∧ u = []} = ∅ := by
        ext u
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hu, rfl⟩
        exact hr (by simpa using hu)
      rw [hEq, Set.ncard_empty]
  rw [wordCount_def, hSunion,
    Set.ncard_union_eq hSdisj (hSfin.subset fun _ h => h.1) (hSfin.subset fun _ h => h.1),
    hS₀_card, ncard_nonempty_wordDelay_le hx r]

/-- The real-valued terms of the renewal sum are summable (in fact finitely supported). -/
theorem summable_wordCount_branch {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    Summable fun a : ℕ × Fin d => (wordCount d (branchMap a x) (r - branchDelay a x) : ℝ) := by
  have hfin := finite_support_wordCount_branch hx r
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun a ha => ?_
  have h0 : wordCount d (branchMap a x) (r - branchDelay a x) = 0 := by
    by_contra hne
    exact ha (hfin.mem_toFinset.2 hne)
  simp [h0]

/-- Real-valued `tsum` form of the renewal equation:
`(N(w, r) : ℝ) = 1{r ≥ 0} + ∑' a, (N(F_a w, r - τ_a(w)) : ℝ)`. -/
theorem wordCount_renewal_tsum {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) (r : ℝ) :
    (wordCount d x r : ℝ) =
      (if 0 ≤ r then (1 : ℝ) else 0) +
        ∑' a : ℕ × Fin d, (wordCount d (branchMap a x) (r - branchDelay a x) : ℝ) := by
  have hfin := finite_support_wordCount_branch hx r
  have hnat := wordCount_renewal hx r
  rw [finsum_eq_sum _ hfin] at hnat
  have htsum :
      (∑' a : ℕ × Fin d, (wordCount d (branchMap a x) (r - branchDelay a x) : ℝ)) =
        ∑ a ∈ hfin.toFinset, (wordCount d (branchMap a x) (r - branchDelay a x) : ℝ) := by
    refine tsum_eq_sum fun a ha => ?_
    have h0 : wordCount d (branchMap a x) (r - branchDelay a x) = 0 := by
      by_contra hne
      exact ha (hfin.mem_toFinset.2 hne)
    simp [h0]
  rw [htsum, ← Nat.cast_sum, hnat]
  split_ifs <;> simp

/-! ### Freeness of the unaccelerated and accelerated semigroups -/

/-- Strictly positive, strictly increasing vectors in the hyperplane `coneSpan d`. -/
private def IsStrictOrderedCone {d : ℕ} (y : Fin (d + 2) → ℝ) : Prop :=
  (∀ k, 0 < y k) ∧ StrictMono y ∧ y ∈ coneSpan d

/-- A canonical witness in `IsStrictOrderedCone` for `1 ≤ d`: `(1, 2, …, d + 1, ∑ (i + 1))`. -/
private def strictOrderedConePoint (d : ℕ) : Fin (d + 2) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (fun i : Fin (d + 1) => (i.1 : ℝ) + 1)
    (∑ i : Fin (d + 1), ((i.1 : ℝ) + 1))

private theorem strictOrderedConePoint_mem {d : ℕ} (hd : 1 ≤ d) :
    IsStrictOrderedCone (strictOrderedConePoint d) := by
  have : Nontrivial (Fin (d + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [strictOrderedConePoint, Fin.snoc_last]
      exact Finset.sum_pos (fun i _ => by positivity) Finset.univ_nonempty
    · simp only [strictOrderedConePoint, Fin.snoc_castSucc]
      positivity
  · intro k₁ k₂ hlt
    refine Fin.lastCases ?_ (fun i₂ => ?_) k₂ hlt
    · refine Fin.lastCases (fun h => absurd h (lt_irrefl _)) (fun i₁ _ => ?_) k₁
      simp only [strictOrderedConePoint, Fin.snoc_castSucc, Fin.snoc_last]
      rcases exists_ne i₁ with ⟨i', hi'⟩
      have hpair : ((i₁.1 : ℝ) + 1) + ((i'.1 : ℝ) + 1) ≤
          ∑ i : Fin (d + 1), ((i.1 : ℝ) + 1) := by
        have hsub : ({i₁, i'} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
        have hle := Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun i : Fin (d + 1) => (i.1 : ℝ) + 1) hsub fun i _ _ => by positivity
        rwa [Finset.sum_pair hi'.symm] at hle
      linarith [Nat.cast_nonneg (α := ℝ) i'.1]
    · refine Fin.lastCases (fun h => absurd h (not_lt.2 (Fin.castSucc_lt_last i₂).le))
        (fun i₁ h => ?_) k₁
      simp only [strictOrderedConePoint, Fin.snoc_castSucc]
      have hi : i₁.1 < i₂.1 := Fin.castSucc_lt_castSucc_iff.1 h
      have : (i₁.1 : ℝ) < (i₂.1 : ℝ) := Nat.cast_lt.2 hi
      linarith
  · rw [mem_coneSpan_iff]
    simp [strictOrderedConePoint]

private theorem unaccelMove_preserves_strict {d : ℕ} (hd : 1 ≤ d) (j : Fin (d + 1))
    {y : Fin (d + 2) → ℝ} (hy : IsStrictOrderedCone y) :
    IsStrictOrderedCone (unaccelMove j y) := by
  have : Nontrivial (Fin (d + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  refine ⟨?_, ?_, unaccelMove_mem_coneSpan j y⟩
  · intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · rw [unaccelMove_last]
      exact Finset.sum_pos (fun i _ => hy.1 _) Finset.univ_nonempty
    · rw [unaccelMove_castSucc]
      exact hy.1 _
  · intro k₁ k₂ hlt
    refine Fin.lastCases ?_ (fun i₂ => ?_) k₂ hlt
    · refine Fin.lastCases (fun h => absurd h (lt_irrefl _)) (fun i₁ _ => ?_) k₁
      rw [unaccelMove_castSucc, unaccelMove_last]
      rcases exists_ne i₁ with ⟨i', hi'⟩
      have hpair : y (j.castSucc.succAbove i₁) + y (j.castSucc.succAbove i') ≤
          ∑ i : Fin (d + 1), y (j.castSucc.succAbove i) := by
        have hsub : ({i₁, i'} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
        have hle := Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun i : Fin (d + 1) => y (j.castSucc.succAbove i)) hsub fun i _ _ => (hy.1 _).le
        rwa [Finset.sum_pair hi'.symm] at hle
      linarith [hy.1 (j.castSucc.succAbove i')]
    · refine Fin.lastCases (fun h => absurd h (not_lt.2 (Fin.castSucc_lt_last i₂).le))
        (fun i₁ h => ?_) k₁
      rw [unaccelMove_castSucc, unaccelMove_castSucc]
      exact hy.2.1 ((Fin.strictMono_succAbove _) (Fin.castSucc_lt_castSucc_iff.1 h))

private theorem unaccelWordMove_preserves_strict {d : ℕ} (hd : 1 ≤ d) (js : List (Fin (d + 1)))
    {y : Fin (d + 2) → ℝ} (hy : IsStrictOrderedCone y) :
    IsStrictOrderedCone (unaccelWordMove js y) := by
  induction js generalizing y with
  | nil => exact hy
  | cons j _ ih => exact ih (unaccelMove_preserves_strict hd j hy)

private theorem unaccelMove_last_gt {d : ℕ} (j : Fin (d + 1)) {y : Fin (d + 2) → ℝ}
    (hy : IsStrictOrderedCone y) :
    y (Fin.last (d + 1)) < unaccelMove j y (Fin.last (d + 1)) := by
  rw [unaccelMove_last_of_mem_coneSpan j hy.2.2]
  linarith [hy.2.1 (Fin.castSucc_lt_last j)]

private theorem unaccelWordMove_last_ge {d : ℕ} (hd : 1 ≤ d) (js : List (Fin (d + 1)))
    {y : Fin (d + 2) → ℝ} (hy : IsStrictOrderedCone y) :
    y (Fin.last (d + 1)) ≤ unaccelWordMove js y (Fin.last (d + 1)) := by
  induction js generalizing y with
  | nil => exact le_rfl
  | cons j _ ih =>
    exact (unaccelMove_last_gt j hy).le.trans (ih (unaccelMove_preserves_strict hd j hy))

/-- On strictly ordered cone vectors, `unaccelMove j y` uniquely determines both `j` and `y`. -/
private theorem unaccelMove_inj_strict {d : ℕ} {j₁ j₂ : Fin (d + 1)}
    {y₁ y₂ : Fin (d + 2) → ℝ} (hy₁ : IsStrictOrderedCone y₁) (hy₂ : IsStrictOrderedCone y₂)
    (heq : unaccelMove j₁ y₁ = unaccelMove j₂ y₂) :
    j₁ = j₂ ∧ y₁ = y₂ := by
  have hlast : y₁ (Fin.last (d + 1)) = y₂ (Fin.last (d + 1)) := by
    have hpen := congrFun heq (Fin.last d).castSucc
    simpa [unaccelMove_penultimate] using hpen
  have hdel : y₁ j₁.castSucc = y₂ j₂.castSucc := by
    have htop := congrFun heq (Fin.last (d + 1))
    rw [unaccelMove_last_of_mem_coneSpan j₁ hy₁.2.2,
      unaccelMove_last_of_mem_coneSpan j₂ hy₂.2.2] at htop
    linarith
  have hnotlt : ∀ {a b : Fin (d + 1)} {u v : Fin (d + 2) → ℝ},
      IsStrictOrderedCone u → IsStrictOrderedCone v →
      unaccelMove a u = unaccelMove b v → u a.castSucc = v b.castSucc → ¬ a < b := by
    intro a b u v hu hv hab huv hlt
    have hcoord := congrFun hab a.castSucc
    rw [unaccelMove_castSucc, unaccelMove_castSucc] at hcoord
    have hs1 : a.castSucc.succAbove a = a.succ :=
      Fin.succAbove_of_le_castSucc a.castSucc a le_rfl
    have hs2 : b.castSucc.succAbove a = a.castSucc :=
      Fin.succAbove_of_castSucc_lt b.castSucc a (Fin.castSucc_lt_castSucc_iff.2 hlt)
    rw [hs1, hs2] at hcoord
    have h1 : u a.castSucc < u a.succ := hu.2.1 (Fin.castSucc_lt_succ (i := a))
    have h2 : v a.castSucc < v b.castSucc := hv.2.1 (Fin.castSucc_lt_castSucc_iff.2 hlt)
    linarith
  have hj : j₁ = j₂ := le_antisymm
    (not_lt.1 (hnotlt hy₂ hy₁ heq.symm hdel.symm))
    (not_lt.1 (hnotlt hy₁ hy₂ heq hdel))
  subst hj
  refine ⟨rfl, ?_⟩
  ext k
  by_cases hk : k = j₁.castSucc
  · rw [hk, hdel]
  · rcases Fin.exists_succAbove_eq hk with ⟨i, rfl⟩
    have hi := congrFun heq i.castSucc
    simpa [unaccelMove_castSucc] using hi

private theorem unaccelWordMove_apply_injective {d : ℕ} (hd : 1 ≤ d) {y : Fin (d + 2) → ℝ}
    (hy : IsStrictOrderedCone y) :
    Function.Injective fun js : List (Fin (d + 1)) => unaccelWordMove js y := by
  intro js₁
  refine List.reverseRecOn js₁ ?_ ?_
  · intro js₂ hEq
    refine List.reverseRecOn js₂ (fun _ => rfl) (fun l₂ j₂ _ hEq => ?_) hEq
    dsimp only at hEq
    rw [unaccelWordMove_nil, LinearMap.id_apply, unaccelWordMove_append, LinearMap.comp_apply,
      unaccelWordMove_singleton] at hEq
    have hlt := unaccelMove_last_gt j₂ (unaccelWordMove_preserves_strict hd l₂ hy)
    have hge := unaccelWordMove_last_ge hd l₂ hy
    have htop := congrFun hEq (Fin.last (d + 1))
    linarith
  · intro l₁ j₁ ih js₂ hEq
    refine List.reverseRecOn js₂ (fun hEq => ?_) (fun l₂ j₂ _ hEq => ?_) hEq
    · dsimp only at hEq
      rw [unaccelWordMove_nil, LinearMap.id_apply, unaccelWordMove_append, LinearMap.comp_apply,
        unaccelWordMove_singleton] at hEq
      have hlt := unaccelMove_last_gt j₁ (unaccelWordMove_preserves_strict hd l₁ hy)
      have hge := unaccelWordMove_last_ge hd l₁ hy
      have htop := congrFun hEq (Fin.last (d + 1))
      linarith
    · dsimp only at hEq
      rw [unaccelWordMove_append, unaccelWordMove_append, LinearMap.comp_apply,
        LinearMap.comp_apply, unaccelWordMove_singleton, unaccelWordMove_singleton] at hEq
      rcases unaccelMove_inj_strict (unaccelWordMove_preserves_strict hd l₁ hy)
        (unaccelWordMove_preserves_strict hd l₂ hy) hEq with ⟨hj, hl⟩
      rw [ih hl, hj]

/-- For `1 ≤ d`, distinct unaccelerated words induce distinct linear maps on `Fin (d + 2) → ℝ`
(freeness of the unaccelerated semigroup). -/
theorem unaccelWordMove_injective {d : ℕ} (hd : 1 ≤ d) :
    Function.Injective (unaccelWordMove (d := d)) := by
  intro js₁ js₂ hEq
  exact unaccelWordMove_apply_injective hd (strictOrderedConePoint_mem hd) (by dsimp only; rw [hEq])

/-- Expansion of an accelerated word into its underlying unaccelerated word in `Fin (d + 1)`. -/
def expandWord {d : ℕ} : List (ℕ × Fin d) → List (Fin (d + 1))
  | [] => []
  | a :: u => a.2.castSucc :: List.replicate a.1 (Fin.last d) ++ expandWord u

@[simp]
theorem expandWord_nil {d : ℕ} : expandWord (d := d) [] = [] :=
  (rfl)

@[simp]
theorem expandWord_cons {d : ℕ} (a : ℕ × Fin d) (u : List (ℕ × Fin d)) :
    expandWord (a :: u) = a.2.castSucc :: List.replicate a.1 (Fin.last d) ++ expandWord u :=
  (rfl)

theorem expandWord_singleton {d : ℕ} (a : ℕ × Fin d) :
    expandWord [a] = a.2.castSucc :: List.replicate a.1 (Fin.last d) := by
  simp

private theorem unaccelWordMove_replicate {d : ℕ} (A : ℕ) (j : Fin (d + 1)) :
    unaccelWordMove (List.replicate A j) = unaccelMove j ^ A := by
  induction A with
  | zero =>
    simp [Module.End.one_eq_id]
  | succ A ih =>
    rw [List.replicate_succ, unaccelWordMove_cons, ih, pow_succ]
    rfl

/-- Expanding an accelerated word preserves its linear move. -/
theorem unaccelWordMove_expandWord {d : ℕ} (u : List (ℕ × Fin d)) :
    unaccelWordMove (expandWord u) = wordMove u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    rw [expandWord, List.cons_append, unaccelWordMove_cons, unaccelWordMove_append,
      unaccelWordMove_replicate, ih, wordMove_cons, LinearMap.comp_assoc, accelMove_def]

private theorem expandWord_ne_last_cons {d : ℕ} (u : List (ℕ × Fin d)) (t : List (Fin (d + 1))) :
    expandWord u ≠ Fin.last d :: t := by
  cases u with
  | nil => simp
  | cons a u =>
    simp only [expandWord_cons, List.cons_append, ne_eq, List.cons.injEq, not_and]
    intro h
    exact absurd h (Fin.castSucc_ne_last a.2)

private theorem replicate_append_expandWord_inj {d : ℕ} {A₁ A₂ : ℕ} {v₁ v₂ : List (ℕ × Fin d)}
    (h : List.replicate A₁ (Fin.last d) ++ expandWord v₁ =
      List.replicate A₂ (Fin.last d) ++ expandWord v₂) :
    A₁ = A₂ ∧ expandWord v₁ = expandWord v₂ := by
  induction A₁ generalizing A₂ with
  | zero =>
    cases A₂ with
    | zero => simpa using h
    | succ A₂ =>
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
      exact absurd h (expandWord_ne_last_cons v₁ _)
  | succ A₁ ih =>
    cases A₂ with
    | zero =>
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
      exact absurd h.symm (expandWord_ne_last_cons v₂ _)
    | succ A₂ =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      rcases ih h with ⟨hA, hv⟩
      exact ⟨congrArg Nat.succ hA, hv⟩

/-- The expansion from accelerated words to unaccelerated words is injective. -/
theorem expandWord_injective {d : ℕ} : Function.Injective (expandWord (d := d)) := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ h
    cases u₂ with
    | nil => rfl
    | cons a v => simp at h
  | cons a₁ v₁ ih =>
    intro u₂ h
    cases u₂ with
    | nil => simp at h
    | cons a₂ v₂ =>
      simp only [expandWord_cons, List.cons_append, List.cons.injEq] at h
      rcases h with ⟨hj, htail⟩
      rcases replicate_append_expandWord_inj htail with ⟨hA, hv⟩
      have ha : a₁ = a₂ := Prod.ext hA (Fin.castSucc_injective d hj)
      rw [ha, ih hv]

/-- Distinct accelerated words induce distinct linear maps on `Fin (d + 2) → ℝ` for every `d : ℕ`
(freeness of the accelerated semigroup). -/
theorem wordMove_injective (d : ℕ) : Function.Injective (wordMove (d := d)) := by
  cases d with
  | zero =>
    intro u₁ u₂ _
    cases u₁ with
    | nil =>
      cases u₂ with
      | nil => rfl
      | cons a _ => exact Fin.elim0 a.2
    | cons a _ => exact Fin.elim0 a.2
  | succ d =>
    intro u₁ u₂ h
    apply expandWord_injective
    apply unaccelWordMove_injective (Nat.succ_pos d)
    rw [unaccelWordMove_expandWord, unaccelWordMove_expandWord, h]

end TauCeti.OrderedSimplex
