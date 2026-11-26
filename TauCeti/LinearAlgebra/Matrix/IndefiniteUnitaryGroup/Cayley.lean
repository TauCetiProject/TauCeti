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

`c(X) = (1 - X) (1 + X)⁻¹` (`TauCeti.cayleyCoord 1`).

If `X` is skew-adjoint for the form, `star X * A + A * X = 0`, and `1 + X` is invertible, then
`c(X)` preserves the form, because `⟨(1 - X) u, (1 - X) w⟩ = ⟨(1 + X) u, (1 + X) w⟩`. Conversely, if
`g` preserves the form and `1 + g` is invertible, then `c(g)` is skew-adjoint for the form. When `2`
is a unit, `1 + c(X) = 2 (1 + X)⁻¹` is invertible as soon as `1 + X` is, and `c` is its own inverse.
So for an invertible Gram matrix `A` and `2` a unit, `c` is a bijection from the skew-adjoint `X`
with `1 + X` invertible onto the elements `g` of `Matrix.unitaryGroupOf A` with `1 + g` invertible,
with inverse `c` again (`Matrix.unitaryGroupOf.cayleyEquiv`). The skew-adjoint matrices are the Lie
algebra of the unitary group, and the Cayley transform is a rational chart of the group around the
identity, defined over the base ring.

The transform uses the ring-level Cayley coordinate `TauCeti.cayleyCoord 1 X`; its
form-independent algebra is in `TauCeti.Algebra.Ring.CayleyChart`.
Over `ℂ` and for `A = 1`, the transform `Matrix.cayley H = (1 + i H) (1 - i H)⁻¹` of a Hermitian
matrix `H` is `c(-i H)` (`Matrix.cayley_eq_cayleyCoord_one`). The differential calculus of the
Cayley chart over `ℂ` is in `TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Cayley`.

## Main definitions

* `Matrix.unitaryGroupOf.cayleyEquiv`: the bijection between the skew-adjoint `X` with `1 + X`
  invertible and the elements `g` of the unitary group with `1 + g` invertible.

## Main results

* `Matrix.star_cayleyCoord_one_mul_mul_cayleyCoord_one`: the Cayley transform of a skew-adjoint
  matrix preserves the form.
* `Matrix.star_cayleyCoord_one_mul_add_mul_cayleyCoord_one`: the Cayley transform of a
  form-preserving matrix is skew-adjoint.
* `TauCeti.cayleyCoord_one_cayleyCoord_one`: the Cayley transform is an involution where `1 + X` is
  invertible.
* `Matrix.star_cayleyCoord_one_mul_mul_inv`: `star c(X) * A * (1 + X)⁻¹ = star (1 + X)⁻¹ * A` for
  skew-adjoint `X`.

## Provenance

`Matrix.star_cayleyCoord_one_mul_mul_cayleyCoord_one`,
`Matrix.star_cayleyCoord_one_mul_add_mul_cayleyCoord_one`,
`Matrix.star_cayleyCoord_one_mul_mul_inv` and `Matrix.unitaryGroupOf.cayleyEquiv` are adapted from
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

open TauCeti

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

variable {X : Matrix n n R}

section Form

variable [StarRing R] {A : Matrix n n R}

/-- **The Cayley transform of a skew-adjoint matrix preserves the form.** If
`star X * A + A * X = 0` and `1 + X` is invertible, then `star c(X) * A * c(X) = A`: indeed
`star (1 - X) * A * (1 - X) = star (1 + X) * A * (1 + X)`. -/
theorem star_cayleyCoord_one_mul_mul_cayleyCoord_one (hXA : star X * A + A * X = 0)
    (hX : IsUnit (1 + X)) : star (cayleyCoord 1 X) * A * cayleyCoord 1 X = A := by
  have hP : (1 + X) * (1 + X)⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hX)
  have h : star (1 - X) * A * (1 - X) = star (1 + X) * A * (1 + X) := by
    simp only [star_sub, star_add, star_one]
    linear_combination (norm := noncomm_ring) (-2 : Matrix n n R) * hXA
  calc star (cayleyCoord 1 X) * A * cayleyCoord 1 X
      = star (1 + X)⁻¹ * (star (1 - X) * A * (1 - X)) * (1 + X)⁻¹ := by
        simp only [cayleyCoord_def, ← nonsing_inv_eq_ringInverse, star_mul, Matrix.mul_assoc]
    _ = star ((1 + X) * (1 + X)⁻¹) * A * ((1 + X) * (1 + X)⁻¹) := by
        rw [h]
        simp only [star_mul, Matrix.mul_assoc]
    _ = A := by simp [hP]

/-- For `X` skew-adjoint for the form, `star c(X) * A * (1 + X)⁻¹ = star (1 + X)⁻¹ * A`. This is the
identity that turns the derivative of the Cayley transform into a congruence
(`Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_fderiv_cayleyChart`). -/
theorem star_cayleyCoord_one_mul_mul_inv (hXA : star X * A + A * X = 0) :
    star (cayleyCoord 1 X) * A * (1 + X)⁻¹ = star (1 + X)⁻¹ * A := by
  by_cases hX : IsUnit (1 + X)
  swap
  · simp [cayleyCoord_of_not_isUnit hX,
      nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ hX]
  -- `star (1 - X) * A = A * (1 + X)`, since `star X * A = -(A * X)`.
  have h : star (1 - X) * A = A * (1 + X) := by
    rw [star_sub, star_one, Matrix.sub_mul, Matrix.one_mul, eq_neg_of_add_eq_zero_left hXA,
      Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]
  calc star (cayleyCoord 1 X) * A * (1 + X)⁻¹
      = star (1 + X)⁻¹ * (star (1 - X) * A) * (1 + X)⁻¹ := by
        simp only [cayleyCoord_def, ← nonsing_inv_eq_ringInverse, star_mul, Matrix.mul_assoc]
    _ = star (1 + X)⁻¹ * A * ((1 + X) * (1 + X)⁻¹) := by
        rw [h]
        simp only [Matrix.mul_assoc]
    _ = star (1 + X)⁻¹ * A := by
        rw [mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hX), Matrix.mul_one]

/-- **The Cayley transform of a form-preserving matrix is skew-adjoint.** If
`star g * A * g = A`, then `star c(g) * A + A * c(g) = 0`. -/
theorem star_cayleyCoord_one_mul_add_mul_cayleyCoord_one {g : Matrix n n R}
    (hg : star g * A * g = A) : star (cayleyCoord 1 g) * A + A * cayleyCoord 1 g = 0 := by
  by_cases h1 : IsUnit (1 + g)
  swap
  · simp [cayleyCoord_of_not_isUnit h1]
  rw [cayleyCoord_def, ← nonsing_inv_eq_ringInverse]
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
      {g : unitaryGroupOf A // IsUnit (1 + ((g : GL n R) : Matrix n n R))} :=
  -- The matrix `2` is the image of `2 : R` under `algebraMap`, hence a unit.
  have h2' : IsUnit (2 : Matrix n n R) := by
    simpa only [map_ofNat] using h2.map (algebraMap R (Matrix n n R))
  { toFun := fun X ↦ ⟨ofMatrix hA (cayleyCoord 1 X.val)
        (star_cayleyCoord_one_mul_mul_cayleyCoord_one X.property.1 X.property.2), by
      simpa using isUnit_one_add_cayleyCoord_one h2' X.val⟩
    invFun := fun g ↦ ⟨cayleyCoord 1 ((g.val : GL n R) : Matrix n n R),
      star_cayleyCoord_one_mul_add_mul_cayleyCoord_one (mem_unitaryGroupOf_iff.1 g.val.property),
      isUnit_one_add_cayleyCoord_one h2' _⟩
    left_inv := fun X ↦ Subtype.ext (by
      simpa using cayleyCoord_one_cayleyCoord_one h2' X.property.2)
    right_inv := fun g ↦ Subtype.ext (unitaryGroupOf.ext (by
      simpa using cayleyCoord_one_cayleyCoord_one h2' g.property)) }

/-- The matrix of the image of `X` under `Matrix.unitaryGroupOf.cayleyEquiv` is its Cayley
transform. -/
@[simp]
theorem coe_cayleyEquiv_apply (hA : IsUnit A) (h2 : IsUnit (2 : R))
    (X : {X : Matrix n n R // star X * A + A * X = 0 ∧ IsUnit (1 + X)}) :
    (((cayleyEquiv hA h2 X).val : GL n R) : Matrix n n R) = cayleyCoord 1 X.val :=
  val_ofMatrix hA _ _

/-- The inverse of `Matrix.unitaryGroupOf.cayleyEquiv` is the Cayley transform. -/
@[simp]
theorem coe_cayleyEquiv_symm_apply (hA : IsUnit A) (h2 : IsUnit (2 : R))
    (g : {g : unitaryGroupOf A // IsUnit (1 + ((g : GL n R) : Matrix n n R))}) :
    ((cayleyEquiv hA h2).symm g : Matrix n n R) =
      cayleyCoord 1 ((g.val : GL n R) : Matrix n n R) :=
  (rfl)

end unitaryGroupOf

end Form

end Matrix
