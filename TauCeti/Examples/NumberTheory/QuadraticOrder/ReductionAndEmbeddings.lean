/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.NormNum.RealSqrt
import TauCeti.NumberTheory.NumberField.Quadratic.EmbeddingBound
import TauCeti.NumberTheory.QuadraticOrder.CoordinateReduction
import TauCeti.NumberTheory.QuadraticOrder.Reduction

/-!
# Boundary cases for reduction and embeddings of quadratic orders

These examples distinguish scalar divisibility from norm divisibility, injective coordinate
rectangles from endpoint collisions, and bounds under complex algebra maps from injectivity.
The square-root parameters include the nonsquare, non-squarefree integer `20`, the square `4`
and the repeated-root case `0`. Reduction is also checked at moduli `0` and `1`.
-/

open QuadraticAlgebra

namespace TauCeti.QuadraticOrderExamples

/-- Reduction modulo zero has zero kernel, with no positive-modulus hypothesis. -/
example : RingHom.ker (mapRingHom (Int.castRingHom (ZMod 0)) (5 : ℤ) 0) = ⊥ := by
  simpa using ker_mapRingHom_intCastRingHom (5 : ℤ) 0 0

/-- The quotient modulo zero is infinite; `Nat.card` must not be read as a finite size. -/
example : ¬Finite (QuadraticAlgebra ℤ 5 0 ⧸ Ideal.span {(0 : QuadraticAlgebra ℤ 5 0)}) := by
  simpa using (finite_quotient_span_natCast_iff (a := 5) (b := 0) (m := 0))

/-- The one-element quotient has the advertised cardinality at modulus one. -/
example : Nat.card (QuadraticAlgebra ℤ 5 0 ⧸ Ideal.span {(1 : QuadraticAlgebra ℤ 5 0)}) = 1 := by
  simp

/-- Divisibility of the Gaussian norm does not imply scalar divisibility in the order. -/
example : (2 : ℤ) ∣ norm (⟨1, 1⟩ : QuadraticAlgebra ℤ (-1) 0) ∧
    (⟨1, 1⟩ : QuadraticAlgebra ℤ (-1) 0) ∉ Ideal.span {(2 : QuadraticAlgebra ℤ (-1) 0)} := by
  exact ⟨by norm_num [norm_def], fun h ↦ by simpa using (mem_span_natCast_iff (m := 2)).mp h⟩

/-- The non-squarefree parameter `20` permits a full half-open coordinate rectangle modulo `3`.
-/
example : Set.InjOn (mapRingHom (Int.castRingHom (ZMod 3)) (20 : ℤ) 0)
    {z : QuadraticAlgebra ℤ 20 0 | z.re ∈ Set.Ico 0 3 ∧ z.im ∈ Set.Ico 0 3} := by
  exact injOn_mapRingHom_setOf_re_mem_Ico_im_mem_Ico 20 0 3 0 3 0 3 (by norm_num) (by norm_num)

/-- Keeping both endpoints of a full period loses injectivity: `0` and `3` reduce together. -/
example : ¬Set.InjOn (mapRingHom (Int.castRingHom (ZMod 3)) (20 : ℤ) 0)
    {z : QuadraticAlgebra ℤ 20 0 | z.re ∈ Set.Icc 0 3 ∧ z.im ∈ Set.Icc 0 2} := by
  intro h
  simpa using h (x₁ := 0) (x₂ := 3) (by norm_num) (by norm_num) (by decide)

/-- The singleton rectangle shows why the ambient `m²` bound needs a positive modulus. -/
example : Set.InjOn (Int.cast : ℤ → ZMod 0) ({0} : Set ℤ) ∧
    Set.InjOn (Int.cast : ℤ → ZMod 0) ({0} : Set ℤ) ∧
    (0 : ℕ) ^ 2 <
      {z : QuadraticAlgebra ℤ 20 0 | z.re ∈ ({0} : Set ℤ) ∧ z.im ∈ ({0} : Set ℤ)}.ncard := by
  refine ⟨Set.injOn_singleton _ _, Set.injOn_singleton _ _, ?_⟩
  rw [ncard_setOf_re_mem_im_mem]
  norm_num

/-- The Gaussian embedding has the Euclidean squared norm, including arbitrary rational
coordinates. -/
example (u v : ℚ) : ‖sqrtEmbedding (-1) (⟨u, v⟩ : QuadraticAlgebra ℚ (-1) 0)‖ ^ 2 =
    (u : ℝ) ^ 2 + (v : ℝ) ^ 2 := by
  simpa [norm_def, sq] using
    ((forall_norm_sq_sqrtEmbedding_eq_norm_iff (r := -1)).mpr (by norm_num)) ⟨u, v⟩

/-- At the non-squarefree parameter `20` the positive coordinate bound is attained. -/
example : ‖sqrtEmbedding 20 (⟨1, 1⟩ : QuadraticAlgebra ℚ 20 0)‖ = 1 + Real.sqrt 20 := by
  open scoped ComplexOrder in
  norm_num [sqrtEmbedding_apply,
    Complex.sqrt_of_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 20)]
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

/-- Changing the sign of the second coordinate makes that bound strict. -/
example : ‖sqrtEmbedding 20 (⟨1, -1⟩ : QuadraticAlgebra ℚ 20 0)‖ < 1 + Real.sqrt 20 := by
  open scoped ComplexOrder in
  norm_num [sqrtEmbedding_apply,
    Complex.sqrt_of_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 20)]
  rw [← sub_eq_add_neg, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_lt]
  exact ⟨by linarith, by linarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 20)]⟩

/-- For a square parameter the coordinate bound still holds while a nonzero element is killed.
-/
example : (⟨-2, 1⟩ : QuadraticAlgebra ℚ 4 0) ≠ 0 ∧
    sqrtEmbedding 4 (⟨-2, 1⟩ : QuadraticAlgebra ℚ 4 0) = 0 ∧
    ‖sqrtEmbedding 4 (⟨-2, 1⟩ : QuadraticAlgebra ℚ 4 0)‖ ≤ 4 := by
  open scoped ComplexOrder in
  norm_num [sqrtEmbedding_apply,
    Complex.sqrt_of_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 4),
    QuadraticAlgebra.ext_iff]

/-- At the repeated-root parameter zero the two complex algebra maps coincide. -/
example : sqrtEmbedding 0 = negSqrtEmbedding 0 := by
  exact algHom_ext (by norm_num [Complex.sqrt_zero])

/-- The second coordinate cannot be bounded by the divided recovery formula at `r = 0`:
the nonzero generator has both complex images zero. -/
example : ¬ |((ω : QuadraticAlgebra ℚ 0 0).im : ℝ)| ≤
    (‖sqrtEmbedding 0 (ω : QuadraticAlgebra ℚ 0 0)‖ +
      ‖negSqrtEmbedding 0 (ω : QuadraticAlgebra ℚ 0 0)‖) / (2 * Real.sqrt |(0 : ℝ)|) := by
  norm_num [Complex.sqrt_zero]

/-- The coordinate estimate specializes to the Gaussian triangle bound for both embeddings. -/
example (σ : QuadraticAlgebra ℚ (-1) 0 →ₐ[ℚ] ℂ) (u v : ℚ) :
    ‖σ ⟨u, v⟩‖ ≤ |(u : ℝ)| + |(v : ℝ)| := by
  simpa using norm_embedding_le σ ⟨u, v⟩

/-- Equality in the Gaussian coordinate bound occurs exactly on a coordinate axis. -/
example (u v : ℚ) :
    ‖sqrtEmbedding (-1) (⟨u, v⟩ : QuadraticAlgebra ℚ (-1) 0)‖ =
      |(u : ℝ)| + |(v : ℝ)| ↔ u * v = 0 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  norm_num [sqrtEmbedding_apply, Complex.sqrt_neg_one]
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), add_sq, sq_abs, sq_abs]
  simp only [add_right_cancel_iff]
  constructor <;> grind [abs_eq_zero, Rat.cast_eq_zero, Rat.cast_zero]

end TauCeti.QuadraticOrderExamples
