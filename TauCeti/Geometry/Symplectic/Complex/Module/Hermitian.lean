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
# The complex-valued form with a given imaginary part

Let `J` be an almost complex structure on a real module `U` and `B` a real bilinear form on `U`.
The associated complex-valued real bilinear map

`H (v, w) = B (J v) w + i B v w`

has imaginary part `B` and is complex linear in the first variable for the complex structure
`J.complexModule` in which `i` acts by `J`; it is the only such map (`complexFormOfIm_unique`).
When `B` is `J`-invariant, `H` is conjugate linear in the second variable. When `B` is moreover
alternating, `H` is a Hermitian form: it is conjugate symmetric, and it is positive definite
exactly when `0 < B (J v) v` for `v ≠ 0`. This is the classical correspondence between Hermitian
forms on `(U, J)` and `J`-invariant alternating real forms (Birkenhake–Lange, *Complex Abelian
Varieties*, Lemma 2.1.7), in the convention linear in the first variable.

`TauCeti.SymplecticForm.complexAssociatedForm` is the form `ω (v, J w) + i ω (v, w)` of a symplectic
form, linear in the second variable; for `J`-invariant `ω` its real part is the negative of the
real part of `H` here.

## Main declarations

* `TauCeti.AlmostComplexStructure.complexFormOfIm`: the map `H` of `(J, B)`, characterized by
  `TauCeti.AlmostComplexStructure.complexFormOfIm_unique`.
* `TauCeti.AlmostComplexStructure.re_complexFormOfIm`,
  `TauCeti.AlmostComplexStructure.im_complexFormOfIm`: `Re H = B (J ·) ·` and `Im H = B`.
* `TauCeti.AlmostComplexStructure.complexFormOfIm_smul_left`: `H` is complex linear in the first
  variable for `J.complexModule`, and `TauCeti.AlmostComplexStructure.complexFormOfIm_smul_right`:
  for `J`-invariant `B` it is conjugate linear in the second.
* `TauCeti.AlmostComplexStructure.complexFormOfIm_conj_symm`: for alternating `J`-invariant `B`,
  `H` is conjugate symmetric.
* `TauCeti.AlmostComplexStructure.complexFormOfIm_self_pos`: `0 < H (v, v)` when `B v v = 0` (for
  instance for alternating `B`) and `0 < B (J v) v`.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped ComplexOrder ComplexConjugate

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

variable (J : AlmostComplexStructure U) (B : LinearMap.BilinForm ℝ U)

/-- The complex-valued real bilinear map `H (v, w) = B (J v) w + i B v w` with imaginary part a
real bilinear form `B`, for an almost complex structure `J`. It is complex linear in the first
variable for `J.complexModule` (`complexFormOfIm_smul_left`); when `B` is alternating and
`J`-invariant it is a Hermitian form (`complexFormOfIm_conj_symm`). -/
noncomputable def complexFormOfIm : U →ₗ[ℝ] U →ₗ[ℝ] ℂ :=
  (B.compLeft J.toLinearMap).compr₂ Complex.ofRealAm.toLinearMap +
    Complex.I • B.compr₂ Complex.ofRealAm.toLinearMap

/-- The defining formula `H (v, w) = B (J v) w + i B v w`. -/
@[simp]
theorem complexFormOfIm_apply (v w : U) :
    J.complexFormOfIm B v w = (B (J v) w : ℂ) + Complex.I * B v w := by
  simp [complexFormOfIm]

/-- The real part of `H` is `B (J v) w`. -/
theorem re_complexFormOfIm (v w : U) : (J.complexFormOfIm B v w).re = B (J v) w := by
  simp

/-- **The imaginary part of `H` is `B`.** -/
theorem im_complexFormOfIm (v w : U) : (J.complexFormOfIm B v w).im = B v w := by
  simp

/-- `H` turns `J` in the first variable into multiplication by `i`. -/
theorem complexFormOfIm_apply_left (v w : U) :
    J.complexFormOfIm B (J v) w = Complex.I * J.complexFormOfIm B v w := by
  simp only [complexFormOfIm_apply, apply_apply, map_neg, LinearMap.neg_apply]
  push_cast
  linear_combination (-(B v w : ℂ)) * Complex.I_sq

/-- `H` is complex linear in the first variable for the complex structure `J.complexModule`, in
which `i` acts by `J`. -/
theorem complexFormOfIm_smul_left (z : ℂ) (v w : U) :
    letI := J.complexModule
    J.complexFormOfIm B (z • v) w = z * J.complexFormOfIm B v w := by
  let := J.complexModule
  rw [J.complexModule_smul_def]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    complexFormOfIm_apply_left, Complex.real_smul]
  ring

/-- **Uniqueness of `H`**: a real bilinear map with imaginary part `B` that turns `J` in the first
variable into multiplication by `i` is `J.complexFormOfIm B`. -/
theorem complexFormOfIm_unique {F : U →ₗ[ℝ] U →ₗ[ℝ] ℂ} (hIm : ∀ v w, (F v w).im = B v w)
    (hJ : ∀ v w, F (J v) w = Complex.I * F v w) : F = J.complexFormOfIm B := by
  refine LinearMap.ext₂ fun v w ↦ Complex.ext ?_ ?_
  · rw [re_complexFormOfIm, ← hIm, hJ]
    simp
  · rw [im_complexFormOfIm, hIm]

variable {J B}

/-- For `J`-invariant `B`, `H` turns `J` in the second variable into multiplication by `-i`. -/
theorem complexFormOfIm_apply_right (hBJ : ∀ v w, B (J v) (J w) = B v w) (v w : U) :
    J.complexFormOfIm B v (J w) = -Complex.I * J.complexFormOfIm B v w := by
  rw [complexFormOfIm_apply, complexFormOfIm_apply, hBJ,
    J.bilinForm_apply_left_eq_neg_apply_right hBJ v w]
  push_cast
  linear_combination (B v w : ℂ) * Complex.I_sq

/-- For `J`-invariant `B`, `H` is conjugate linear in the second variable for the complex structure
`J.complexModule`. -/
theorem complexFormOfIm_smul_right (hBJ : ∀ v w, B (J v) (J w) = B v w) (z : ℂ) (v w : U) :
    letI := J.complexModule
    J.complexFormOfIm B v (z • w) = conj z * J.complexFormOfIm B v w := by
  let := J.complexModule
  rw [J.complexModule_smul_def]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add, map_smul, map_mul, complexFormOfIm_apply_right hBJ, Complex.real_smul,
    Complex.conj_ofReal, Complex.conj_I]
  ring

/-- On the diagonal, `H (v, v)` is real when `B v v = 0` (for instance for alternating `B`), equal
to `B (J v) v`. -/
theorem complexFormOfIm_self {v : U} (hv : B v v = 0) :
    J.complexFormOfIm B v v = (B (J v) v : ℂ) := by
  simp [hv]

/-- **For an alternating `J`-invariant form, `H` is conjugate symmetric**:
`conj (H (w, v)) = H (v, w)`. -/
theorem complexFormOfIm_conj_symm (hB : B.IsAlt) (hBJ : ∀ v w, B (J v) (J w) = B v w) (v w : U) :
    conj (J.complexFormOfIm B w v) = J.complexFormOfIm B v w := by
  apply Complex.ext
  · simp [J.bilinForm_apply_left_symm hB hBJ v w]
  · simp [← hB.neg_eq v w]

/-- **Positivity of `H`**: if `B v v = 0` (for instance for alternating `B`) and `0 < B (J v) v`,
then `0 < H (v, v)`. -/
theorem complexFormOfIm_self_pos {v : U} (hvv : B v v = 0) (hv : 0 < B (J v) v) :
    0 < J.complexFormOfIm B v v := by
  rw [complexFormOfIm_self hvv]
  exact Complex.zero_lt_real.mpr hv

end TauCeti.AlmostComplexStructure
