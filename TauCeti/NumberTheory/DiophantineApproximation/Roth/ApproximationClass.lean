/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# Approximation classes

Mahler's reduction sorts the solutions of a Diophantine inequality by where they are well
approximated, so that the solutions in one class behave alike at every place. Nothing in it is
about places, heights or number fields: a family of maps `φ a : X → ℝ` with nonnegative values
summing to at most `1` sends each point of `X` to a point of the standard simplex, for `0 < N`
the unit cube is cut into half-open cells of side `1 / N`, and two points lie in the same class
when they land in the same cell.

For `0 < N` and a point with nonnegative coordinates, a cell is labelled by its scaled south-west
corner `cellIndex N y a = ⌊N * y a⌋₊`, a tuple of natural numbers. The definition makes sense for
every `y : A → ℝ` and `N : ℕ`, but outside this range it loses its geometric meaning: negative
coordinates are truncated to `0`, and `N = 0` gives the constant label `0`. Three facts come out
of this.

* The classes are finitely many. The label of a point of the simplex satisfies
  `∑ a, c a ≤ N`, and there are `(N + card A).choose (card A)` such labels
  (`TauCeti.ncard_setOf_sum_le`). Without the simplex condition the labels are the
  `(N + 1) ^ card A` cells of the cube; the rejection test at the end of the file shows the
  difference.
* An infinite set has an infinite class, by the pigeonhole principle.
* A class pins every coordinate at once. For `f : A → ℝ` with values in `(0, 1]` and product
  `Λ = ∏ b, f b < 1`, the profile `logProfile f a = log (f a) / log Λ` is a point of the simplex
  lying on the hyperplane `∑ a, y a = 1`, and its cell traps each `f a` between two powers of
  `Λ`: `Λ ^ ((c a + 1) / N) < f a ≤ Λ ^ (c a / N)`. Since the profile lies on the hyperplane, its
  label sums to more than `N - card A`.

## Main results

* `TauCeti.cellIndex`: the label of the cell of side `1 / N` containing a point with nonnegative
  coordinates, for `0 < N`.
* `TauCeti.sum_cellIndex_le`: a point of the simplex has a label with `∑ a, c a ≤ N`.
* `TauCeti.ncard_image_cellIndex_le`: at most `(N + card A).choose (card A)` classes are nonempty.
* `Set.Infinite.exists_cellIndex_eq`: an infinite set has an infinite class.
* `TauCeti.logProfile`, with `TauCeti.logProfile_nonneg` and `TauCeti.sum_logProfile`.
* `TauCeti.le_rpow_cellIndex_div` and `TauCeti.rpow_cellIndex_add_one_div_lt`: the two halves of
  Bombieri–Gubler's (6.9); the first is attained.
* `TauCeti.one_sub_card_div_lt_sum_cellIndex_div`: Bombieri–Gubler's (6.10), the label of a point
  on the hyperplane `∑ a, y a = 1` sums to more than `N - card A`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), 6.4.2–6.4.4.
* The statements follow Ralf Stephan's formalization
  `DiophantineApproximation/ApproximationClass.lean` in `rwst/Subspace-Theorems` (Apache 2.0).
-/

public section

open Finset Real

namespace TauCeti

variable {A : Type*}

/-- The tuple `⌊N * y a⌋₊` of natural numbers. For `0 < N` and `y : A → ℝ` with nonnegative
coordinates, it labels the half-open cell of side `1 / N` containing `y` by its south-west corner
scaled by `N`. Negative coordinates are truncated to `0`, and for `N = 0` the label is constantly
`0`. -/
noncomputable def cellIndex (N : ℕ) (y : A → ℝ) (a : A) : ℕ := ⌊(N : ℝ) * y a⌋₊

theorem cellIndex_apply (N : ℕ) (y : A → ℝ) (a : A) : cellIndex N y a = ⌊(N : ℝ) * y a⌋₊ :=
  (rfl)

/-- The south-west corner of the cell of a point is below the point. -/
theorem cellIndex_div_le (N : ℕ) {y : A → ℝ} {a : A} (hy : 0 ≤ y a) :
    (cellIndex N y a : ℝ) / N ≤ y a := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simpa using hy
  rw [div_le_iff₀ (by exact_mod_cast hN), mul_comm, cellIndex_apply]
  exact Nat.floor_le (by positivity)

/-- A point is strictly below the north-east corner of its cell. -/
theorem lt_cellIndex_add_one_div {N : ℕ} (hN : 0 < N) (y : A → ℝ) (a : A) :
    y a < ((cellIndex N y a : ℝ) + 1) / N := by
  rw [lt_div_iff₀ (by exact_mod_cast hN), mul_comm, cellIndex_apply]
  exact Nat.lt_floor_add_one _

/-- The label of a point of the standard simplex satisfies `∑ a, c a ≤ N`. -/
theorem sum_cellIndex_le [Fintype A] (N : ℕ) {y : A → ℝ} (hy : ∀ a, 0 ≤ y a)
    (hsum : ∑ a, y a ≤ 1) : ∑ a, cellIndex N y a ≤ N := by
  have key : ∑ a, (cellIndex N y a : ℝ) ≤ N := calc
    ∑ a, (cellIndex N y a : ℝ) ≤ ∑ a, (N : ℝ) * y a :=
      sum_le_sum fun a _ ↦ Nat.floor_le (mul_nonneg N.cast_nonneg (hy a))
    _ = N * ∑ a, y a := (mul_sum ..).symm
    _ ≤ N := mul_le_of_le_one_right N.cast_nonneg hsum
  exact_mod_cast key

/-- **Bombieri–Gubler (6.10).** The label of a point on the hyperplane `∑ a, y a = 1` sums to
more than `N - card A`, after division by `N`. -/
theorem one_sub_card_div_lt_sum_cellIndex_div [Fintype A] {N : ℕ} (hN : 0 < N) {y : A → ℝ}
    (hsum : ∑ a, y a = 1) :
    1 - (Fintype.card A : ℝ) / N < ∑ a, (cellIndex N y a : ℝ) / N := by
  have hA : (univ : Finset A).Nonempty := by
    by_contra h
    simp [not_nonempty_iff_eq_empty.mp h] at hsum
  have hlt : ∑ a, y a < ∑ a, ((cellIndex N y a : ℝ) + 1) / N :=
    sum_lt_sum_of_nonempty hA fun a _ ↦ lt_cellIndex_add_one_div hN y a
  simp only [add_div, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one_div,
    hsum] at hlt
  linarith

variable [Fintype A]

/-- The logarithmic profile of `f : A → ℝ`, the tuple `log (f a) / log (∏ b, f b)`. For `f` with
values in `(0, 1]` and product less than `1` it is a point of the standard simplex lying on the
hyperplane `∑ a, y a = 1`. When the product is `1` the profile is `0`. -/
noncomputable def logProfile (f : A → ℝ) (a : A) : ℝ := log (f a) / log (∏ b, f b)

theorem logProfile_apply (f : A → ℝ) (a : A) : logProfile f a = log (f a) / log (∏ b, f b) :=
  (rfl)

/-- The logarithmic profile of a family in `(0, 1]` is nonnegative. -/
theorem logProfile_nonneg {f : A → ℝ} (hpos : ∀ a, 0 < f a) (hf : ∀ a, f a ≤ 1) (a : A) :
    0 ≤ logProfile f a :=
  div_nonneg_of_nonpos (log_nonpos (hpos a).le (hf a))
    (log_nonpos (prod_nonneg fun b _ ↦ (hpos b).le) (prod_le_one₀ (fun b _ ↦ (hpos b).le)
      fun b _ ↦ hf b))

/-- The logarithmic profile of a positive family with product different from `1` sums to `1`. -/
@[simp]
theorem sum_logProfile {f : A → ℝ} (hpos : ∀ a, 0 < f a) (hprod : ∏ b, f b ≠ 1) :
    ∑ a, logProfile f a = 1 := by
  have hlog : log (∏ b, f b) = ∑ a, log (f a) := log_prod fun a _ ↦ (hpos a).ne'
  simp_rw [logProfile_apply, ← Finset.sum_div, ← hlog]
  exact div_self (log_ne_zero_of_pos_of_ne_one (prod_pos fun b _ ↦ hpos b) hprod)

/-- **The upper half of Bombieri–Gubler (6.9).** For `f` with values in `(0, 1]` and product
`Λ`, each `f a` is at most `Λ ^ (c a / N)`, where `c` labels the cell of the logarithmic
profile of `f`. -/
theorem le_rpow_cellIndex_div (N : ℕ) {f : A → ℝ} (hpos : ∀ a, 0 < f a)
    (hf : ∀ a, f a ≤ 1) (a : A) :
    f a ≤ (∏ b, f b) ^ ((cellIndex N (logProfile f) a : ℝ) / N) := by
  have hprod₀ : 0 < ∏ b, f b := prod_pos fun b _ ↦ hpos b
  rcases (prod_le_one₀ (fun b _ ↦ (hpos b).le) fun b _ ↦ hf b).lt_or_eq with hprod | hprod
  swap
  · rw [hprod, one_rpow]
    exact hf a
  rw [← log_le_log_iff (hpos a) (rpow_pos_of_pos hprod₀ _), log_rpow hprod₀,
    ← le_div_iff_of_neg (log_neg hprod₀ hprod), ← logProfile_apply]
  exact cellIndex_div_le N (logProfile_nonneg hpos hf a)

/-- **The lower half of Bombieri–Gubler (6.9).** For a positive family `f` with product `Λ < 1`,
each `f a` exceeds `Λ ^ ((c a + 1) / N)`, where `c` labels the cell of the logarithmic profile
of `f`. -/
theorem rpow_cellIndex_add_one_div_lt {N : ℕ} (hN : 0 < N) {f : A → ℝ} (hpos : ∀ a, 0 < f a)
    (hprod : ∏ b, f b < 1) (a : A) :
    (∏ b, f b) ^ (((cellIndex N (logProfile f) a : ℝ) + 1) / N) < f a := by
  have hprod₀ : 0 < ∏ b, f b := prod_pos fun b _ ↦ hpos b
  rw [← log_lt_log_iff (rpow_pos_of_pos hprod₀ _) (hpos a), log_rpow hprod₀,
    ← div_lt_iff_of_neg (log_neg hprod₀ hprod), ← logProfile_apply]
  exact lt_cellIndex_add_one_div hN _ a

/-- The classes of a family of maps into the standard simplex, which for `0 < N` are the cells of
side `1 / N`: at most `(N + card A).choose (card A)` labels occur. -/
theorem ncard_image_cellIndex_le {ι : Type*} {X : Set ι} (φ : A → ι → ℝ)
    (hφ₀ : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ₁ : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
    ((fun x ↦ cellIndex N fun a ↦ φ a x) '' X).ncard ≤
      (N + Fintype.card A).choose (Fintype.card A) := by
  rw [← ncard_setOf_sum_le A N]
  refine Set.ncard_le_ncard ?_ (finite_setOf_sum_le A N)
  rintro _ ⟨x, hx, rfl⟩
  exact sum_cellIndex_le N (fun a ↦ hφ₀ a x hx) (hφ₁ x hx)

end TauCeti

namespace Set

open TauCeti

/-- **An infinite set has an infinite approximation class.** For a family of maps from an infinite
set `X` into the standard simplex and every `N`, some label `c` with `∑ a, c a ≤ N` is shared by
infinitely many points of `X`; for `0 < N` it labels a cell of side `1 / N`. -/
theorem Infinite.exists_cellIndex_eq {ι A : Type*} [Fintype A] {X : Set ι} (hX : X.Infinite)
    (φ : A → ι → ℝ) (hφ₀ : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ₁ : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
    ∃ c : A → ℕ, ∑ a, c a ≤ N ∧ {x ∈ X | cellIndex N (fun a ↦ φ a x) = c}.Infinite := by
  by_contra! h
  refine hX (((finite_setOf_sum_le A N).biUnion h).subset fun x hx ↦ ?_)
  exact mem_biUnion (sum_cellIndex_le N (fun a ↦ hφ₀ a x hx) (hφ₁ x hx)) ⟨hx, rfl⟩

end Set

/-! ### Tests -/

/-- The classes are cells of the simplex, not of the cube: the constant point `1` of the unit
square has a label summing to `2` at `N = 1`. Without `∑ a, y a ≤ 1` the labels are the
`(N + 1) ^ card A` cells of the cube, `4` against `3` at `N = 1` and `card A = 2`. -/
example : ¬ ∑ a, TauCeti.cellIndex 1 (fun _ : Fin 2 ↦ (1 : ℝ)) a ≤ 1 := by
  norm_num [TauCeti.cellIndex_apply, Fin.sum_univ_two]

/-- The count of labels at `N = 1` and `card A = 2`. -/
example : {c : Fin 2 → ℕ | ∑ a, c a ≤ 1}.ncard = 3 := by
  rw [TauCeti.ncard_setOf_sum_le]
  decide

/-- The upper half of (6.9) is attained, so its exponent is not off by one: for the single value
`f = 1 / 4` the profile is `1`, the label at `N = 2` is `2`, and the bound is an equality. -/
example : (∏ _b : Fin 1, (1 / 4 : ℝ)) ^
    ((TauCeti.cellIndex 2 (TauCeti.logProfile fun _ : Fin 1 ↦ (1 / 4 : ℝ)) 0 : ℝ) / 2) = 1 / 4 := by
  have hprof : TauCeti.logProfile (fun _ : Fin 1 ↦ (1 / 4 : ℝ)) 0 = 1 := by
    rw [TauCeti.logProfile_apply, Fin.prod_univ_one]
    exact div_self (Real.log_neg (by norm_num) (by norm_num)).ne
  rw [TauCeti.cellIndex_apply, hprof]
  norm_num
