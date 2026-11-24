/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.RealSqrt
import TauCeti.NumberTheory.NumberField.Quadratic.EmbeddingBound
import TauCeti.NumberTheory.QuadraticOrder.CoordinateReduction
import TauCeti.NumberTheory.QuadraticOrder.Reduction

/-!
# Boundary cases for reduction and embeddings of quadratic orders

These examples distinguish scalar divisibility from norm divisibility, injective coordinate
rectangles from endpoint collisions, and bounds under complex algebra maps from injectivity.
The square-root parameters include the nonsquare, non-squarefree integer `20`, the square `4`
and the repeated-root case `0`. Reduction is also checked at moduli `0` and `1`, the quotient
sizes `4` and `9` of `ℤ[√5]/(2)` and `ℤ[√20]/(3)` are exhibited, the latter a field, and the empty
coordinate set gives the empty rectangle.
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

/-- Modulo `2` the order `ℤ[√5]` has four classes, those of `0`, `1`, `ω` and `1 + ω`. -/
example :
    let I := Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ 5 0)}
    Nat.card (QuadraticAlgebra ℤ 5 0 ⧸ I) = 4 ∧
      ({0, 1, Ideal.Quotient.mk I ω, Ideal.Quotient.mk I (1 + ω)} :
        Set (QuadraticAlgebra ℤ 5 0 ⧸ I)) = Set.univ := by
  intro I
  refine ⟨card_quotient_span_natCast 5 0 2, Set.eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hz : Ideal.Quotient.mk I z = Ideal.Quotient.mk I ⟨z.re % 2, z.im % 2⟩ :=
    mk_eq_mk_span_natCast_iff.mpr ⟨(Int.mod_modEq _ _).symm, (Int.mod_modEq _ _).symm⟩
  have h0 : (⟨0, 0⟩ : QuadraticAlgebra ℤ 5 0) = 0 := by ext <;> simp
  have h1 : (⟨1, 0⟩ : QuadraticAlgebra ℤ 5 0) = 1 := by ext <;> simp
  have hω : (⟨0, 1⟩ : QuadraticAlgebra ℤ 5 0) = ω := by ext <;> simp
  have h1ω : (⟨1, 1⟩ : QuadraticAlgebra ℤ 5 0) = 1 + ω := by ext <;> simp
  rw [hz]
  rcases Int.emod_two_eq z.re with h | h <;> rcases Int.emod_two_eq z.im with h' | h' <;>
    simp [h, h', h0, h1, hω, h1ω]

/-- Modulo `3` the order `ℤ[√20]` has nine classes; `20 ≡ 2` is not a square modulo `3`, so the
quotient is the field with nine elements. -/
example :
    Nat.card (QuadraticAlgebra ℤ 20 0 ⧸ Ideal.span {((3 : ℕ) : QuadraticAlgebra ℤ 20 0)}) = 9 ∧
      ¬IsSquare ((20 : ℤ) : ZMod 3) ∧
      IsField (QuadraticAlgebra ℤ 20 0 ⧸ Ideal.span {((3 : ℕ) : QuadraticAlgebra ℤ 20 0)}) := by
  refine ⟨card_quotient_span_natCast 20 0 3, by decide, ?_⟩
  have : Fact (∀ r : ZMod 3, r ^ 2 ≠ ((20 : ℤ) : ZMod 3) + ((0 : ℤ) : ZMod 3) * r) :=
    ⟨by decide⟩
  exact (quotientSpanNatCastEquiv 20 0 3).toMulEquiv.isField_congr.mpr (Field.toIsField _)

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

/-- The empty coordinate set gives the empty rectangle, with `0 · #V = 0` elements. -/
example (V : Set ℤ) :
    {z : QuadraticAlgebra ℤ 20 0 | z.re ∈ (∅ : Set ℤ) ∧ z.im ∈ V} = ∅ ∧
      {z : QuadraticAlgebra ℤ 20 0 | z.re ∈ (∅ : Set ℤ) ∧ z.im ∈ V}.ncard = 0 * V.ncard := by
  refine ⟨by simp, ?_⟩
  rw [ncard_setOf_re_mem_im_mem, Set.ncard_empty]

/-- The Gaussian embedding has the Euclidean squared norm, including arbitrary rational
coordinates. -/
example (u v : ℚ) : ‖sqrtEmbedding (-1) (⟨u, v⟩ : QuadraticAlgebra ℚ (-1) 0)‖ ^ 2 =
    (u : ℝ) ^ 2 + (v : ℝ) ^ 2 := by
  simpa [norm_def, sq] using
    ((forall_norm_sq_sqrtEmbedding_eq_norm_iff (r := -1)).mpr (by norm_num)) ⟨u, v⟩

/-- At the non-squarefree parameter `20` the positive coordinate bound is attained. -/
example : ‖sqrtEmbedding 20 (⟨1, 1⟩ : QuadraticAlgebra ℚ 20 0)‖ = 1 + Real.sqrt 20 := by
  norm_num [sqrtEmbedding_apply, sqrtRadicand_of_nonneg (by norm_num : (0 : ℚ) ≤ 20)]
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

/-- Changing the sign of the second coordinate makes that bound strict. -/
example : ‖sqrtEmbedding 20 (⟨1, -1⟩ : QuadraticAlgebra ℚ 20 0)‖ < 1 + Real.sqrt 20 := by
  norm_num [sqrtEmbedding_apply, sqrtRadicand_of_nonneg (by norm_num : (0 : ℚ) ≤ 20)]
  rw [← sub_eq_add_neg, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_lt]
  exact ⟨by linarith, by linarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 20)]⟩

/-- For a square parameter the coordinate bound still holds while a nonzero element is killed.
-/
example : (⟨-2, 1⟩ : QuadraticAlgebra ℚ 4 0) ≠ 0 ∧
    sqrtEmbedding 4 (⟨-2, 1⟩ : QuadraticAlgebra ℚ 4 0) = 0 ∧
    ‖sqrtEmbedding 4 (⟨-2, 1⟩ : QuadraticAlgebra ℚ 4 0)‖ ≤ 4 := by
  norm_num [sqrtEmbedding_apply, sqrtRadicand_of_nonneg (by norm_num : (0 : ℚ) ≤ 4),
    QuadraticAlgebra.ext_iff]

/-- At the repeated-root parameter zero the two complex algebra maps coincide. -/
example : sqrtEmbedding 0 = negSqrtEmbedding 0 := by
  exact algHom_ext (by norm_num [sqrtRadicand_of_nonneg (by norm_num : (0 : ℚ) ≤ 0)])

/-- The second coordinate cannot be bounded by the divided recovery formula at `r = 0`:
the nonzero generator has both complex images zero. -/
example : ¬ |((ω : QuadraticAlgebra ℚ 0 0).im : ℝ)| ≤
    (‖sqrtEmbedding 0 (ω : QuadraticAlgebra ℚ 0 0)‖ +
      ‖negSqrtEmbedding 0 (ω : QuadraticAlgebra ℚ 0 0)‖) / (2 * Real.sqrt |(0 : ℝ)|) := by
  norm_num [sqrtRadicand_of_nonneg (by norm_num : (0 : ℚ) ≤ 0)]

/-- The coordinate estimate specializes to the Gaussian triangle bound for both embeddings. -/
example (σ : QuadraticAlgebra ℚ (-1) 0 →ₐ[ℚ] ℂ) (u v : ℚ) :
    ‖σ ⟨u, v⟩‖ ≤ |(u : ℝ)| + |(v : ℝ)| := by
  simpa using norm_embedding_le σ ⟨u, v⟩

/-- Equality in the Gaussian coordinate bound occurs exactly on a coordinate axis. -/
example (u v : ℚ) :
    ‖sqrtEmbedding (-1) (⟨u, v⟩ : QuadraticAlgebra ℚ (-1) 0)‖ =
      |(u : ℝ)| + |(v : ℝ)| ↔ u * v = 0 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  norm_num [sqrtEmbedding_apply, sqrtRadicand_of_nonpos (by norm_num : (-1 : ℚ) ≤ 0)]
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), add_sq, sq_abs, sq_abs]
  simp only [add_right_cancel_iff]
  constructor <;> grind [abs_eq_zero, Rat.cast_eq_zero, Rat.cast_zero]

end TauCeti.QuadraticOrderExamples
