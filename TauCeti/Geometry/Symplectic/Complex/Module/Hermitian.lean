/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.LinearCombination

/-!
# The Hermitian form with a given imaginary part

Let `J` be an almost complex structure on a real module `U` and `B` a real bilinear form on `U`.
The form

`H (v, w) = B (J v) w + i B v w`

is real bilinear, has imaginary part `B`, and is complex linear in the first variable for the
complex structure `J.complexModule` in which `i` acts by `J`. When `B` is alternating and
`J`-invariant, `H` is conjugate symmetric, and it is positive definite exactly when
`0 < B (J v) v` for `v ≠ 0`. This is the classical correspondence between Hermitian forms on
`(U, J)` and `J`-invariant alternating real forms (Birkenhake–Lange, *Complex Abelian Varieties*,
Lemma 2.1.7), in the convention linear in the first variable.

`TauCeti.SymplecticForm.complexAssociatedForm` is the form `ω (v, J w) + i ω (v, w)` of a symplectic
form, linear in the second variable; for `J`-invariant `ω` its real part is the negative of the
real part of `H` here.

## Main declarations

* `TauCeti.AlmostComplexStructure.hermitianOfIm`: the form `H` of `(J, B)`.
* `TauCeti.AlmostComplexStructure.re_hermitianOfIm`,
  `TauCeti.AlmostComplexStructure.im_hermitianOfIm`: `Re H = B (J ·) ·` and `Im H = B`.
* `TauCeti.AlmostComplexStructure.hermitianOfIm_smul_left`: `H` is complex linear in the first
  variable for `J.complexModule`.
* `TauCeti.AlmostComplexStructure.hermitianOfIm_conj_symm`: for alternating `J`-invariant `B`,
  `H` is conjugate symmetric.
* `TauCeti.AlmostComplexStructure.hermitianOfIm_self_pos`: `0 < H (v, v)` when `B` is alternating
  and `0 < B (J v) v`.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped ComplexOrder ComplexConjugate

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

/-- An alternating bilinear form preserved by `J` satisfies `B (J v) w = B (J w) v`. -/
theorem bilinForm_apply_left_comm (J : AlmostComplexStructure U) {B : LinearMap.BilinForm ℝ U}
    (hB : B.IsAlt) (hBJ : ∀ v w, B (J v) (J w) = B v w) (v w : U) :
    B (J v) w = B (J w) v := by
  rw [J.bilinForm_apply_left_eq_neg_apply_right hBJ, hB.neg_eq]

variable (J : AlmostComplexStructure U) (B : LinearMap.BilinForm ℝ U)

/-- The **Hermitian form** `H (v, w) = B (J v) w + i B v w` with imaginary part a real bilinear
form `B`, for an almost complex structure `J`, as a real bilinear map. It is complex linear in the
first variable for `J.complexModule` (`hermitianOfIm_smul_left`); when `B` is alternating and
`J`-invariant it is conjugate symmetric (`hermitianOfIm_conj_symm`). -/
noncomputable def hermitianOfIm : U →ₗ[ℝ] U →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun v w ↦ (B (J v) w : ℂ) + Complex.I * B v w)
    (fun v v' w ↦ by simp only [map_add, LinearMap.add_apply]; push_cast; ring)
    (fun c v w ↦ by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.real_smul]
      push_cast; ring)
    (fun v w w' ↦ by simp only [map_add]; push_cast; ring)
    (fun c v w ↦ by
      simp only [map_smul, smul_eq_mul, Complex.real_smul]
      push_cast; ring)

/-- The defining formula `H (v, w) = B (J v) w + i B v w`. -/
@[simp]
theorem hermitianOfIm_apply (v w : U) :
    J.hermitianOfIm B v w = (B (J v) w : ℂ) + Complex.I * B v w := by
  simp [hermitianOfIm]

/-- The real part of the Hermitian form is `B (J v) w`. -/
theorem re_hermitianOfIm (v w : U) : (J.hermitianOfIm B v w).re = B (J v) w := by
  simp

/-- **The imaginary part of the Hermitian form is `B`.** -/
theorem im_hermitianOfIm (v w : U) : (J.hermitianOfIm B v w).im = B v w := by
  simp

/-- The Hermitian form turns `J` in the first variable into multiplication by `i`. -/
theorem hermitianOfIm_apply_left (v w : U) :
    J.hermitianOfIm B (J v) w = Complex.I * J.hermitianOfIm B v w := by
  simp only [hermitianOfIm_apply, apply_apply, map_neg, LinearMap.neg_apply]
  push_cast
  linear_combination (-(B v w : ℂ)) * Complex.I_sq

/-- The Hermitian form is complex linear in the first variable for the complex structure
`J.complexModule`, in which `i` acts by `J`. -/
theorem hermitianOfIm_smul_left (z : ℂ) (v w : U) :
    letI := J.complexModule
    J.hermitianOfIm B (z • v) w = z * J.hermitianOfIm B v w := by
  let := J.complexModule
  rw [J.complexModule_smul_def, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, hermitianOfIm_apply_left, Complex.real_smul,
    Complex.real_smul, ← mul_assoc, ← add_mul]
  conv_rhs => rw [← Complex.re_add_im z]

variable {J B}

/-- On the diagonal, the Hermitian form of an alternating form is real, equal to `B (J v) v`. -/
theorem hermitianOfIm_self (hB : B.IsAlt) (v : U) :
    J.hermitianOfIm B v v = (B (J v) v : ℂ) := by
  simp [hB v]

/-- **The Hermitian form of an alternating `J`-invariant form is conjugate symmetric**:
`conj (H (w, v)) = H (v, w)`. -/
theorem hermitianOfIm_conj_symm (hB : B.IsAlt) (hBJ : ∀ v w, B (J v) (J w) = B v w) (v w : U) :
    conj (J.hermitianOfIm B w v) = J.hermitianOfIm B v w := by
  apply Complex.ext
  · simp [J.bilinForm_apply_left_comm hB hBJ v w]
  · simp [← hB.neg_eq v w]

/-- **Positivity of the Hermitian form**: if `B` is alternating and `0 < B (J v) v`, then
`0 < H (v, v)`. -/
theorem hermitianOfIm_self_pos (hB : B.IsAlt) {v : U} (hv : 0 < B (J v) v) :
    0 < J.hermitianOfIm B v v := by
  rw [hermitianOfIm_self hB]
  exact Complex.zero_lt_real.mpr hv

end TauCeti.AlmostComplexStructure
