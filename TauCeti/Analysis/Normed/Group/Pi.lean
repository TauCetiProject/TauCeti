/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real

/-!
# Norms on products

The norm on a nonempty finite product of seminormed groups is the maximum of the coordinate norms,
so it is attained at some coordinate (`Pi.exists_norm_apply_eq_norm`). Hence for every positive
exponent `n` its `n`-th power is at most the sum of the `n`-th powers of the coordinate norms
(`Pi.norm_pow_le_sum_norm_pow`). Replacing a coordinate of a point of the closed ball of radius `R`
about `0` by an element of norm at most `R` stays in that ball (`Pi.norm_update_le`).

Over an arbitrary index type, every coordinate of `Pi.single i c` has norm at most `‖c‖`
(`Pi.norm_single_apply_le`).

In a finite product of copies of one seminormed group, a difference of two coordinates has norm at
most twice the norm (`Pi.norm_sub_le_two_mul_norm`). For real coordinates this is
`|v i - v j| ≤ 2 * ‖v‖` (`Pi.abs_sub_le_two_mul_norm`), with equality at `v = eᵢ - eⱼ`
(`Pi.abs_sub_eq_two_mul_norm_single_sub_single`).
-/

public section

/-- The norm on a nonempty finite product of seminormed groups is attained at some coordinate. -/
theorem Pi.exists_norm_apply_eq_norm {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (f : ∀ i, E i) : ∃ i, ‖f i‖ = ‖f‖ := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun i ↦ ‖f i‖₊
  exact ⟨i, by rw [Pi.norm_def, hi, coe_nnNorm]⟩

/-- The `n`-th power of the norm on a finite product is at most the sum of the `n`-th powers of
the coordinate norms, for every positive exponent `n`. -/
theorem Pi.norm_pow_le_sum_norm_pow {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (f : ∀ i, E i) {n : ℕ} (hn : n ≠ 0) :
    ‖f‖ ^ n ≤ ∑ i, ‖f i‖ ^ n := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim f 0, hn]
  obtain ⟨i, hi⟩ := Pi.exists_norm_apply_eq_norm f
  rw [← hi]
  exact Finset.single_le_sum (f := fun i ↦ ‖f i‖ ^ n) (fun _ _ ↦ by positivity)
    (Finset.mem_univ i)

/-- Every coordinate of `Pi.single i c` has norm at most `‖c‖`, over any index type. -/
theorem Pi.norm_single_apply_le {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (i j : ι) (c : E i) :
    ‖(Pi.single i c : ∀ j, E j) j‖ ≤ ‖c‖ := by
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

/-- Replacing a coordinate of a point of norm at most `R` in a finite product by an element of norm
at most `R` gives a point of norm at most `R`. -/
theorem Pi.norm_update_le {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] {x : ∀ i, E i} {i : ι} {y : E i} {R : ℝ} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) : ‖Function.update x i y‖ ≤ R :=
  (pi_norm_le_iff_of_nonneg ((norm_nonneg y).trans hy)).2 fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simpa using hy
    · simpa [Function.update_of_ne hj] using (norm_le_pi_norm x j).trans hx

/-- In the sup norm, a difference of two coordinates has norm at most twice the norm. -/
theorem Pi.norm_sub_le_two_mul_norm {ι : Type*} [Fintype ι] {E : Type*} [SeminormedAddGroup E]
    (v : ι → E) (i j : ι) : ‖v i - v j‖ ≤ 2 * ‖v‖ := by
  linarith [norm_sub_le (v i) (v j), norm_le_pi_norm v i, norm_le_pi_norm v j]

/-- In the sup norm, a difference of two real coordinates is at most twice the norm. -/
theorem Pi.abs_sub_le_two_mul_norm {ι : Type*} [Fintype ι] (v : ι → ℝ) (i j : ι) :
    |v i - v j| ≤ 2 * ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact Pi.norm_sub_le_two_mul_norm v i j

/-- The vector `eᵢ - eⱼ` attains the bound `Pi.abs_sub_le_two_mul_norm`. -/
theorem Pi.abs_sub_eq_two_mul_norm_single_sub_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    |(Pi.single i 1 - Pi.single j 1 : ι → ℝ) i - (Pi.single i 1 - Pi.single j 1 : ι → ℝ) j| =
      2 * ‖(Pi.single i 1 - Pi.single j 1 : ι → ℝ)‖ := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  rw [← dist_eq_norm, dist_single_single i j _ _ hij]
  norm_num [hij, hij.symm]
