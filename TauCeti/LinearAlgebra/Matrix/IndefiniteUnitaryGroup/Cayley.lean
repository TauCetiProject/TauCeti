/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.CayleyChart
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import Mathlib.Tactic.NoncommRing

/-!
# The Cayley transform of the unitary group of a sesquilinear form

Let `R` be a commutative ring with an involution `star` and `A` a square matrix over `R`, the Gram
matrix of the form `⟨z, w⟩ = star z ⬝ᵥ A *ᵥ w`. The **Cayley transform** of a square matrix `X` is

`c(X) = (1 - X) (1 + X)⁻¹` (`Matrix.cayleyTransform`).

If `X` is skew-adjoint for the form, `star X * A + A * X = 0`, and `1 + X` is invertible, then
`c(X)` preserves the form, because `⟨(1 - X) u, (1 - X) w⟩ = ⟨(1 + X) u, (1 + X) w⟩`. Conversely, if
`g` preserves the form and `1 + g` is invertible, then `c(g)` is skew-adjoint for the form. When `2`
is a unit, `1 + c(X) = 2 (1 + X)⁻¹` is invertible as soon as `1 + X` is, and `c` is its own inverse.
So for an invertible Gram matrix `A` and `2` a unit, `c` is a bijection from the skew-adjoint `X`
with `1 + X` invertible onto the elements `g` of `Matrix.unitaryGroupOf A` with `1 + g` invertible,
with inverse `c` again (`Matrix.unitaryGroupOf.cayleyEquiv`). The skew-adjoint matrices are the Lie
algebra of the unitary group, and the Cayley transform is a rational chart of the group around the
identity, defined over the base ring.

The same expression is the Cayley coordinate `TauCeti.cayleyCoord 1 X` relative to `1`
(`Matrix.cayleyTransform_eq_cayleyCoord_one`), whose API concerns square roots of `-1` instead.
Over `ℂ` and for `A = 1`, the transform `Matrix.cayley H = (1 + i H) (1 - i H)⁻¹` of a Hermitian
matrix `H` is `c(-i H)` (`Matrix.cayley_eq_cayleyTransform`). The differential calculus of the
Cayley chart over `ℂ` is in `TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Cayley`.

## Main definitions

* `Matrix.cayleyTransform X`: the Cayley transform `(1 - X) (1 + X)⁻¹`.
* `Matrix.unitaryGroupOf.cayleyEquiv`: the bijection between the skew-adjoint `X` with `1 + X`
  invertible and the elements `g` of the unitary group with `1 + g` invertible.

## Main results

* `Matrix.star_cayleyTransform_mul_mul_cayleyTransform`: the Cayley transform of a skew-adjoint
  matrix preserves the form.
* `Matrix.star_cayleyTransform_mul_add_mul_cayleyTransform`: the Cayley transform of a
  form-preserving matrix is skew-adjoint.
* `Matrix.cayleyTransform_cayleyTransform`: the Cayley transform is an involution where `1 + X` is
  invertible.
* `Matrix.star_cayleyTransform_mul_mul_inv`: `star c(X) * A * (1 + X)⁻¹ = star (1 + X)⁻¹ * A` for
  skew-adjoint `X`.

## Provenance

`Matrix.star_cayleyTransform_mul_mul_cayleyTransform`,
`Matrix.star_cayleyTransform_mul_add_mul_cayleyTransform`,
`Matrix.star_cayleyTransform_mul_mul_inv` and `Matrix.unitaryGroupOf.cayleyEquiv` are adapted from
`New.gram_two_smul_inv_cayleyDenom_sub_one`, `New.cayleyChart_cayleyChartInv`,
`New.cayleyChart_injOn` and the identity `h_swap` in the proof of `New.logDerivU_cayleyChart` (file
`src/Lib/DiscreteSeries/Haar/CayleyChart.lean`) in grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC), which treat complex matrices and a Hermitian
involution. The statement over a commutative ring with involution,
for an arbitrary Gram matrix, and the bijection with the skew-adjoint matrices are new here.

## References

* A. Cayley, *Sur quelques propriétés des déterminants gauches*, J. Reine Angew. Math. **32**
  (1846), 119–123.
* H. Weyl, *The Classical Groups*, Princeton University Press, 1939, Chapter II, §10 (Cayley's
  rational parametrization).
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The **Cayley transform** `(1 - X) (1 + X)⁻¹` of a square matrix `X`. It maps the matrices
skew-adjoint for a form, with `1 + X` invertible, to the matrices preserving the form
(`Matrix.unitaryGroupOf.cayleyEquiv`). Where `1 + X` is singular its value is `0`. -/
noncomputable def cayleyTransform (X : Matrix n n R) : Matrix n n R :=
  (1 - X) * (1 + X)⁻¹

/-- The definition of the Cayley transform. -/
theorem cayleyTransform_def (X : Matrix n n R) : cayleyTransform X = (1 - X) * (1 + X)⁻¹ :=
  (rfl)

/-- The Cayley transform is the Cayley coordinate `TauCeti.cayleyCoord 1 X = (1 - X) (1 + X)⁻¹`
relative to `1`, with Mathlib's matrix inverse in place of `Ring.inverse`. The API of
`TauCeti.cayleyCoord` concerns square roots of `-1` and does not apply to the base point `1`. -/
theorem cayleyTransform_eq_cayleyCoord_one (X : Matrix n n R) :
    cayleyTransform X = TauCeti.cayleyCoord 1 X := by
  rw [cayleyTransform_def, TauCeti.cayleyCoord_def, nonsing_inv_eq_ringInverse]

/-- The Cayley transform of `0` is the identity. -/
@[simp]
theorem cayleyTransform_zero : cayleyTransform (0 : Matrix n n R) = 1 := by
  simp [cayleyTransform]

variable {X : Matrix n n R}

/-- Where `1 + X` is singular, the Cayley transform is `0`. -/
theorem cayleyTransform_of_not_isUnit (hX : ¬IsUnit (1 + X)) : cayleyTransform X = 0 := by
  rw [cayleyTransform, nonsing_inv_apply_not_isUnit _ fun h ↦ hX ((isUnit_iff_isUnit_det _).2 h),
    Matrix.mul_zero]

/-- The factors of the Cayley transform commute: `(1 - X) (1 + X)⁻¹ = (1 + X)⁻¹ (1 - X)`. -/
theorem cayleyTransform_eq_inv_mul (X : Matrix n n R) :
    cayleyTransform X = (1 + X)⁻¹ * (1 - X) := by
  by_cases hX : IsUnit (1 + X)
  swap
  · rw [cayleyTransform_of_not_isUnit hX,
      nonsing_inv_apply_not_isUnit _ fun h ↦ hX ((isUnit_iff_isUnit_det _).2 h), Matrix.zero_mul]
  have hd : IsUnit (1 + X).det := (isUnit_iff_isUnit_det _).1 hX
  have h : (1 + X) * (1 - X) = (1 - X) * (1 + X) := by noncomm_ring
  calc cayleyTransform X = (1 + X)⁻¹ * ((1 + X) * (1 - X)) * (1 + X)⁻¹ := by
        rw [nonsing_inv_mul_cancel_left _ _ hd, cayleyTransform]
    _ = (1 + X)⁻¹ * (1 - X) := by
        rw [h, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]

/-- The characterization `c(X) (1 + X) = 1 - X` of the Cayley transform. -/
theorem cayleyTransform_mul_one_add (hX : IsUnit (1 + X)) :
    cayleyTransform X * (1 + X) = 1 - X :=
  nonsing_inv_mul_cancel_right _ _ ((isUnit_iff_isUnit_det _).1 hX)

/-- The characterization `(1 + X) c(X) = 1 - X` of the Cayley transform. -/
theorem one_add_mul_cayleyTransform (hX : IsUnit (1 + X)) :
    (1 + X) * cayleyTransform X = 1 - X := by
  rw [cayleyTransform_eq_inv_mul, mul_nonsing_inv_cancel_left _ _
    ((isUnit_iff_isUnit_det _).1 hX)]

/-- `(1 + c(X)) (1 + X) = 2`: the denominator of the Cayley transform of `c(X)` is `2 (1 + X)⁻¹`. -/
theorem one_add_cayleyTransform_mul_one_add (hX : IsUnit (1 + X)) :
    (1 + cayleyTransform X) * (1 + X) = 2 := by
  rw [add_mul, one_mul, cayleyTransform_mul_one_add hX, add_add_sub_cancel, one_add_one_eq_two]

/-- The denominator of the Cayley transform of `c(X)`: `1 + c(X) = 2 (1 + X)⁻¹`. -/
theorem one_add_cayleyTransform (hX : IsUnit (1 + X)) :
    1 + cayleyTransform X = 2 * (1 + X)⁻¹ := by
  rw [← one_add_cayleyTransform_mul_one_add hX, Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hX), Matrix.mul_one]

/-- When `2` is a unit, `1 + c(X)` is invertible: it is `2 (1 + X)⁻¹` when `1 + X` is invertible,
and `1` otherwise. -/
theorem isUnit_one_add_cayleyTransform (h2 : IsUnit (2 : R)) (X : Matrix n n R) :
    IsUnit (1 + cayleyTransform X) := by
  by_cases hX : IsUnit (1 + X)
  swap
  · simp [cayleyTransform_of_not_isUnit hX]
  have h2' := h2.map (algebraMap R (Matrix n n R))
  rw [map_ofNat] at h2'
  rw [← one_add_cayleyTransform_mul_one_add hX] at h2'
  exact isUnit_of_mul_isUnit_left h2'

/-- **The Cayley transform is an involution.** When `2` is a unit and `1 + X` is invertible,
`c(c(X)) = X`. -/
theorem cayleyTransform_cayleyTransform (h2 : IsUnit (2 : R)) (hX : IsUnit (1 + X)) :
    cayleyTransform (cayleyTransform X) = X := by
  have hc := isUnit_one_add_cayleyTransform h2 X
  -- `X (1 + c(X)) = 1 - c(X)`: times `1 + X` on the right, both sides are `2 X`.
  have hXc : X * (1 + cayleyTransform X) = 1 - cayleyTransform X := by
    rw [← hX.mul_left_inj, Matrix.mul_assoc, one_add_cayleyTransform_mul_one_add hX, sub_mul,
      cayleyTransform_mul_one_add hX]
    noncomm_ring
  rw [← hc.mul_left_inj, cayleyTransform_mul_one_add hc, hXc]

section Form

variable [StarRing R] {A : Matrix n n R}

/-- **The Cayley transform of a skew-adjoint matrix preserves the form.** If
`star X * A + A * X = 0` and `1 + X` is invertible, then `star c(X) * A * c(X) = A`: indeed
`star (1 - X) * A * (1 - X) = star (1 + X) * A * (1 + X)`. -/
theorem star_cayleyTransform_mul_mul_cayleyTransform (hXA : star X * A + A * X = 0)
    (hX : IsUnit (1 + X)) : star (cayleyTransform X) * A * cayleyTransform X = A := by
  have hP : (1 + X) * (1 + X)⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hX)
  have h : star (1 - X) * A * (1 - X) = star (1 + X) * A * (1 + X) := by
    simp only [star_sub, star_add, star_one]
    linear_combination (norm := noncomm_ring) (-2 : Matrix n n R) * hXA
  calc star (cayleyTransform X) * A * cayleyTransform X
      = star (1 + X)⁻¹ * (star (1 - X) * A * (1 - X)) * (1 + X)⁻¹ := by
        simp only [cayleyTransform, star_mul, Matrix.mul_assoc]
    _ = star ((1 + X) * (1 + X)⁻¹) * A * ((1 + X) * (1 + X)⁻¹) := by
        rw [h]
        simp only [star_mul, Matrix.mul_assoc]
    _ = A := by simp [hP]

/-- For `X` skew-adjoint for the form, `star c(X) * A * (1 + X)⁻¹ = star (1 + X)⁻¹ * A`. This is the
identity that turns the derivative of the Cayley transform into a congruence
(`Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_fderiv_cayleyChart`). -/
theorem star_cayleyTransform_mul_mul_inv (hXA : star X * A + A * X = 0) :
    star (cayleyTransform X) * A * (1 + X)⁻¹ = star (1 + X)⁻¹ * A := by
  by_cases hX : IsUnit (1 + X)
  swap
  · simp [cayleyTransform_of_not_isUnit hX,
      nonsing_inv_apply_not_isUnit _ fun h ↦ hX ((isUnit_iff_isUnit_det _).2 h)]
  -- `star (1 - X) * A = A * (1 + X)`, since `star X * A = -(A * X)`.
  have h : star (1 - X) * A = A * (1 + X) := by
    rw [star_sub, star_one, Matrix.sub_mul, Matrix.one_mul, eq_neg_of_add_eq_zero_left hXA,
      Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]
  calc star (cayleyTransform X) * A * (1 + X)⁻¹
      = star (1 + X)⁻¹ * (star (1 - X) * A) * (1 + X)⁻¹ := by
        simp only [cayleyTransform, star_mul, Matrix.mul_assoc]
    _ = star (1 + X)⁻¹ * A * ((1 + X) * (1 + X)⁻¹) := by
        rw [h]
        simp only [Matrix.mul_assoc]
    _ = star (1 + X)⁻¹ * A := by
        rw [mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hX), Matrix.mul_one]

/-- **The Cayley transform of a form-preserving matrix is skew-adjoint.** If
`star g * A * g = A`, then `star c(g) * A + A * c(g) = 0`. -/
theorem star_cayleyTransform_mul_add_mul_cayleyTransform {g : Matrix n n R}
    (hg : star g * A * g = A) : star (cayleyTransform g) * A + A * cayleyTransform g = 0 := by
  by_cases h1 : IsUnit (1 + g)
  swap
  · simp [cayleyTransform_of_not_isUnit h1]
  rw [cayleyTransform_def]
  set P := (1 + g)⁻¹
  have hP : (1 + g) * P = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 h1)
  have hP' : star P * star (1 + g) = 1 := by rw [← star_mul, hP, star_one]
  have h : star (1 - g) * A * (1 + g) + star (1 + g) * A * (1 - g) = 0 := by
    simp only [star_sub, star_add, star_one]
    linear_combination (norm := noncomm_ring) (-2 : Matrix n n R) * hg
  calc star ((1 - g) * P) * A + A * ((1 - g) * P)
      = star P * star (1 - g) * A * ((1 + g) * P) + star P * star (1 + g) * A * ((1 - g) * P) := by
        simp only [star_mul, hP, hP', Matrix.mul_one, Matrix.one_mul]
    _ = star P * (star (1 - g) * A * (1 + g) + star (1 + g) * A * (1 - g)) * P := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

namespace unitaryGroupOf

/-- **The Cayley transform of the unitary group of a form.** For an invertible Gram matrix `A`
and `2` a unit, `X ↦ (1 - X) (1 + X)⁻¹` is a bijection from the matrices `X` skew-adjoint for the
form, `star X * A + A * X = 0`, with `1 + X` invertible, onto the elements `g` of
`Matrix.unitaryGroupOf A` with `1 + g` invertible. Its inverse is again the Cayley transform
`g ↦ (1 - g) (1 + g)⁻¹`. -/
noncomputable def cayleyEquiv (hA : IsUnit A) (h2 : IsUnit (2 : R)) :
    {X : Matrix n n R // star X * A + A * X = 0 ∧ IsUnit (1 + X)} ≃
      {g : unitaryGroupOf A // IsUnit (1 + ((g : GL n R) : Matrix n n R))} where
  toFun X := ⟨ofMatrix hA (cayleyTransform X.val)
      (star_cayleyTransform_mul_mul_cayleyTransform X.property.1 X.property.2), by
    simpa using isUnit_one_add_cayleyTransform h2 X.val⟩
  invFun g := ⟨cayleyTransform ((g.val : GL n R) : Matrix n n R),
    star_cayleyTransform_mul_add_mul_cayleyTransform (mem_unitaryGroupOf_iff.1 g.val.property),
    isUnit_one_add_cayleyTransform h2 _⟩
  left_inv X := Subtype.ext (by simpa using cayleyTransform_cayleyTransform h2 X.property.2)
  right_inv g := Subtype.ext (unitaryGroupOf.ext (by
    simpa using cayleyTransform_cayleyTransform h2 g.property))

/-- The matrix of the image of `X` under `Matrix.unitaryGroupOf.cayleyEquiv` is its Cayley
transform. -/
@[simp]
theorem coe_cayleyEquiv_apply (hA : IsUnit A) (h2 : IsUnit (2 : R))
    (X : {X : Matrix n n R // star X * A + A * X = 0 ∧ IsUnit (1 + X)}) :
    (((cayleyEquiv hA h2 X).val : GL n R) : Matrix n n R) = cayleyTransform X.val :=
  val_ofMatrix hA _ _

/-- The inverse of `Matrix.unitaryGroupOf.cayleyEquiv` is the Cayley transform. -/
@[simp]
theorem coe_cayleyEquiv_symm_apply (hA : IsUnit A) (h2 : IsUnit (2 : R))
    (g : {g : unitaryGroupOf A // IsUnit (1 + ((g : GL n R) : Matrix n n R))}) :
    ((cayleyEquiv hA h2).symm g : Matrix n n R) =
      cayleyTransform ((g.val : GL n R) : Matrix n n R) :=
  (rfl)

end unitaryGroupOf

end Form

end Matrix
