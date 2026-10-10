/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.Square
public import TauCeti.Algebra.Ring.Semireal
public import Mathlib.Analysis.RCLike.Sqrt
public import TauCeti.FieldTheory.IsRealClosed.Real
import TauCeti.FieldTheory.RealClosure.Sqrt
import TauCeti.Algebra.Order.Ring.Ordering.Semireal

/-! # Square roots in the complexification of a real closed field

`QuadraticAlgebra.isSquare` specializes the algebraic square-root construction to a real
closed field, without requiring an order on that field as a hypothesis. This square-closure
property is used to prove algebraic closedness of the complexification.

## Main results

* `QuadraticAlgebra.sqrt` constructs a square root in `R[i]` over an ordered real closed field,
  deriving the scalar root existence it needs. `sq_sqrt`, `sqrt_coordinates`, and the sign lemmas
  characterize this root.
* `QuadraticAlgebra.isSquare` shows every element of `R[i]` is a square when `R` is real closed,
  without choosing an order.
* `QuadraticAlgebra.equivComplex` identifies `ℝ[i]` with `ℂ`, and
  `equivComplex_sqrt` identifies the constructed root with `Complex.sqrt`.

The semireal square obstruction supplies the field instance on
`QuadraticAlgebra R (-1) 0`.
-/

public section

namespace QuadraticAlgebra

open TauCeti.RealClosure

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [IsRealClosed R]

private noncomputable def complex_sqrt_magnitude
    (a b : R) : R :=
  nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))

private theorem complex_sqrt_magnitude_ge_abs
    (a b : R) :
    |a| ≤ complex_sqrt_magnitude a b := by
  have hm0 : 0 ≤ complex_sqrt_magnitude a b :=
    nonnegSqrt_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have hm : (complex_sqrt_magnitude a b) ^ 2 = a ^ 2 + b ^ 2 :=
    sq_nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
  apply (sq_le_sq₀ (abs_nonneg a) hm0).mp
  rw [sq_abs, hm]
  nlinarith [sq_nonneg b]

private theorem complex_sqrt_radicands_nonneg
    (a b : R) :
    0 ≤ (complex_sqrt_magnitude a b + a) / 2 ∧
      0 ≤ (complex_sqrt_magnitude a b - a) / 2 := by
  have h' := complex_sqrt_magnitude_ge_abs a b
  constructor <;> apply div_nonneg (by linarith [neg_abs_le a, le_abs_self a]) (by norm_num)

private noncomputable def complex_sqrt_real_part
    (a b : R) : R :=
  nonnegSqrt (complex_sqrt_radicands_nonneg a b).1

private noncomputable def complex_sqrt_imag_part
    (a b : R) : R :=
  nonnegSqrt (complex_sqrt_radicands_nonneg a b).2

/-- The square root in `R[i]` whose real part is nonnegative and whose imaginary part is
nonnegative when the input's imaginary part is nonnegative, and nonpositive otherwise. -/
noncomputable def _root_.QuadraticAlgebra.sqrt
    (z : QuadraticAlgebra R (-1) 0) : QuadraticAlgebra R (-1) 0 := by
  exact ⟨complex_sqrt_real_part z.re z.im,
    if 0 ≤ z.im then complex_sqrt_imag_part z.re z.im
    else -complex_sqrt_imag_part z.re z.im⟩

/-- The coordinates of the chosen square root satisfy the equations obtained by squaring. -/
theorem _root_.QuadraticAlgebra.sqrt_coordinates
    (z : QuadraticAlgebra R (-1) 0) :
    (QuadraticAlgebra.sqrt z).re ^ 2 - (QuadraticAlgebra.sqrt z).im ^ 2 = z.re ∧
      2 * (QuadraticAlgebra.sqrt z).re * (QuadraticAlgebra.sqrt z).im = z.im := by
  let a := z.re
  let b := z.im
  let m := complex_sqrt_magnitude a b
  let s := complex_sqrt_real_part a b
  let q := complex_sqrt_imag_part a b
  have hm : m ^ 2 = a ^ 2 + b ^ 2 :=
    sq_nonnegSqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have hs0 : 0 ≤ s := nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg a b).1
  have hs : s ^ 2 = (m + a) / 2 :=
    sq_nonnegSqrt (complex_sqrt_radicands_nonneg a b).1
  have hq0 : 0 ≤ q := nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg a b).2
  have hq : q ^ 2 = (m - a) / 2 :=
    sq_nonnegSqrt (complex_sqrt_radicands_nonneg a b).2
  have hreal : s ^ 2 - q ^ 2 = a := by
    rw [hs, hq]
    ring
  have hprod_sq : (2 * s * q) ^ 2 = |b| ^ 2 := by
    calc
      (2 * s * q) ^ 2 = 4 * s ^ 2 * q ^ 2 := by ring
      _ = 4 * ((m + a) / 2) * ((m - a) / 2) := by rw [hs, hq]
      _ = b ^ 2 := by nlinarith [hm]
      _ = |b| ^ 2 := by rw [sq_abs]
  have hprod_nonneg : 0 ≤ 2 * s * q := mul_nonneg (mul_nonneg (by norm_num) hs0) hq0
  have hprod : 2 * s * q = |b| :=
    (sq_eq_sq₀ hprod_nonneg (abs_nonneg b)).mp hprod_sq
  have himag : 2 * s * (if 0 ≤ b then q else -q) = b := by
    by_cases hb : 0 ≤ b
    · simpa [hb, abs_of_nonneg hb] using hprod
    · have hbneg : b < 0 := lt_of_not_ge hb
      rw [ite_eq_right hb]
      calc
        2 * s * -q = -(2 * s * q) := by ring
        _ = -|b| := by rw [hprod]
        _ = b := by simp [abs_of_neg hbneg]
  change s ^ 2 - (if 0 ≤ b then q else -q) ^ 2 = a ∧
    2 * s * (if 0 ≤ b then q else -q) = b
  constructor
  · by_cases hb : 0 ≤ b <;> simp [hb, hreal]
  · exact himag

/-- The chosen square root squares to its input. -/
@[simp]
theorem _root_.QuadraticAlgebra.sq_sqrt
    (z : QuadraticAlgebra R (-1) 0) : (QuadraticAlgebra.sqrt z) ^ 2 = z := by
  rw [pow_two]
  obtain ⟨hre, him⟩ := QuadraticAlgebra.sqrt_coordinates z
  have hmul : z = QuadraticAlgebra.sqrt z * QuadraticAlgebra.sqrt z := by
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      linear_combination -hre
    · simp only [QuadraticAlgebra.im_mul]
      linear_combination -him
  exact hmul.symm

private theorem complex_sqrt_magnitude_eq_norm (a b : ℝ) :
    complex_sqrt_magnitude a b =
      ‖(a : ℂ) + (b : ℂ) * Complex.I‖ := by
  rw [Complex.norm_add_mul_I]
  simpa [complex_sqrt_magnitude] using
    nonnegSqrt_real_eq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))

private theorem complex_sqrt_real_part_eq_mathlib (a b : ℝ) :
    complex_sqrt_real_part a b =
      Real.sqrt ((‖(a : ℂ) + (b : ℂ) * Complex.I‖ + a) / 2) := by
  rw [← complex_sqrt_magnitude_eq_norm]
  exact nonnegSqrt_real_eq_sqrt (complex_sqrt_radicands_nonneg a b).1

private theorem complex_sqrt_imag_part_eq_mathlib (a b : ℝ) :
    complex_sqrt_imag_part a b =
      Real.sqrt ((‖(a : ℂ) + (b : ℂ) * Complex.I‖ - a) / 2) := by
  rw [← complex_sqrt_magnitude_eq_norm]
  exact nonnegSqrt_real_eq_sqrt (complex_sqrt_radicands_nonneg a b).2

private noncomputable def quadratic_to_complex_hom : QuadraticAlgebra ℝ (-1) 0 →ₐ[ℝ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I, by simp⟩

private theorem quadratic_to_complex_hom_apply (z : QuadraticAlgebra ℝ (-1) 0) :
    quadratic_to_complex_hom z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
  simp [quadratic_to_complex_hom, QuadraticAlgebra.lift]

/-- The real part of the chosen square root is nonnegative. -/
theorem _root_.QuadraticAlgebra.re_sqrt_nonneg
    (z : QuadraticAlgebra R (-1) 0) :
    0 ≤ (QuadraticAlgebra.sqrt z).re :=
  nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg z.re z.im).1

/-- If the input has nonnegative imaginary part, so does its chosen square root. -/
theorem _root_.QuadraticAlgebra.im_sqrt_nonneg_of_im_nonneg
    (z : QuadraticAlgebra R (-1) 0) (hz : 0 ≤ z.im) :
    0 ≤ (QuadraticAlgebra.sqrt z).im := by
  simpa only [QuadraticAlgebra.sqrt, ite_eq_left hz, complex_sqrt_imag_part] using
    (nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg z.re z.im).2)

/-- If the input has negative imaginary part, its chosen square root has nonpositive
imaginary part. -/
theorem _root_.QuadraticAlgebra.im_sqrt_nonpos_of_im_neg
    (z : QuadraticAlgebra R (-1) 0) (hz : z.im < 0) :
    (QuadraticAlgebra.sqrt z).im ≤ 0 := by
  simpa only [QuadraticAlgebra.sqrt, ite_eq_right (not_le_of_gt hz), complex_sqrt_imag_part] using
    (neg_nonpos.mpr (nonnegSqrt_nonneg (complex_sqrt_radicands_nonneg z.re z.im).2))

/-- The canonical real-algebra equivalence from `ℝ[i]` to `ℂ`. -/
noncomputable def _root_.QuadraticAlgebra.equivComplex :
    QuadraticAlgebra ℝ (-1) 0 ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofBijective quadratic_to_complex_hom (by
    constructor
    · intro z w h
      apply QuadraticAlgebra.ext
      · have hr := congrArg Complex.re h
        simpa [quadratic_to_complex_hom_apply] using hr
      · have hi := congrArg Complex.im h
        simpa [quadratic_to_complex_hom_apply] using hi
    · intro z
      refine ⟨⟨z.re, z.im⟩, ?_⟩
      rw [quadratic_to_complex_hom_apply]
      apply Complex.ext <;> simp)

/-- The real coordinate of `QuadraticAlgebra.equivComplex` is unchanged. -/
@[simp]
theorem _root_.QuadraticAlgebra.re_equivComplex (z : QuadraticAlgebra ℝ (-1) 0) :
    (QuadraticAlgebra.equivComplex z).re = z.re := by
  -- Expose the algebra hom underlying the equivalence.
  change (quadratic_to_complex_hom z).re = z.re
  rw [quadratic_to_complex_hom_apply]
  simp

/-- The imaginary coordinate of `QuadraticAlgebra.equivComplex` is unchanged. -/
@[simp]
theorem _root_.QuadraticAlgebra.im_equivComplex (z : QuadraticAlgebra ℝ (-1) 0) :
    (QuadraticAlgebra.equivComplex z).im = z.im := by
  -- Expose the algebra hom underlying the equivalence.
  change (quadratic_to_complex_hom z).im = z.im
  rw [quadratic_to_complex_hom_apply]
  simp

/-- `QuadraticAlgebra.sqrt` agrees with Mathlib's principal complex square root over `ℝ`. -/
theorem _root_.QuadraticAlgebra.equivComplex_sqrt (z : QuadraticAlgebra ℝ (-1) 0) :
    QuadraticAlgebra.equivComplex (QuadraticAlgebra.sqrt z) =
      Complex.sqrt (QuadraticAlgebra.equivComplex z) := by
  -- Expose the algebra hom underlying the equivalence to apply the complex comparison.
  change quadratic_to_complex_hom (QuadraticAlgebra.sqrt z) =
    Complex.sqrt (quadratic_to_complex_hom z)
  rw [quadratic_to_complex_hom_apply, quadratic_to_complex_hom_apply,
    Complex.sqrt_eq_real_add_ite]
  apply Complex.ext
  · simp [QuadraticAlgebra.sqrt, complex_sqrt_real_part_eq_mathlib, Complex.mul_re, apply_ite]
  · simp [QuadraticAlgebra.sqrt, complex_sqrt_imag_part_eq_mathlib, Complex.mul_im, apply_ite]
    by_cases hb : 0 ≤ z.im <;> simp [hb]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Every element of `R[i]` is a square when `R` is real closed, without choosing an order. -/
theorem isSquare (z : QuadraticAlgebra R (-1) 0) : IsSquare z := by
  obtain ⟨o, ho⟩ := IsSemireal.exists_linearOrder (K := R)
  let := o
  have := ho
  refine ⟨QuadraticAlgebra.sqrt z, ?_⟩
  simpa [pow_two] using
    (QuadraticAlgebra.sq_sqrt z).symm

end QuadraticAlgebra
