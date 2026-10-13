/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
import TauCeti.Algebra.Group.Units.Basic

/-!
# Spinor norm of explicit equal-norm transport

`QuadraticMap.reflectionTransport` sends `x` to `y` by the reflection in `x - y` when that
vector is anisotropic, and otherwise by the reflections in `x + y` and `y`. Its spinor norm is
therefore the square class of `Q (x - y)` in the first branch. In the second branch it is trivial:
the equal-norm identity gives `Q (x + y) = 4 * Q y`, so the product of the two reflection norms
is `(2 * Q y)²`. This provides the spinor-norm information that an unspecified Witt isometry
does not determine.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III, for explicit reflection transport.
* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §55,
  for the spinor norm of a product of reflections.
-/

public section

namespace QuadraticMap

open TauCeti CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]
variable (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)

-- Branch normalization can erase the transport head before this spinor-norm equation matches.
/-- When the difference has zero norm, the specified equal-norm transport has trivial spinor
norm: its two reflection norms multiply to `(2 * Q y)²`. -/
@[simp↓]
theorem orthogonalSpinorNorm_reflectionTransport_of_sub_eq_zero (x y : V)
    (hxy : Q x = Q y) (hy : Q y ≠ 0) (hsub : Q (x - y) = 0) :
    orthogonalSpinorNorm Q hQ (Q.reflectionTransport x y hxy hy) = 1 := by
  have hadd := (TauCeti.QuadraticMap.isUnit_sub_or_add_of_map_eq Q x y hxy hy).resolve_left
    (by simp [hsub])
  let := hadd.invertible
  let := (isUnit_iff_ne_zero.mpr hy).invertible
  rw [reflectionTransport_eq_reflection_mul_reflection Q x y hxy hy hsub, map_mul,
    orthogonalSpinorNorm_reflectionOrthogonal, orthogonalSpinorNorm_reflectionOrthogonal,
    ← map_mul]
  have hsum : Q (x + y) = 4 * Q y := by
    have hdifference := hsub
    simp only [sub_eq_add_neg, QuadraticMap.map_add, QuadraticMap.map_neg,
      polar_neg_right, hxy] at hdifference ⊢
    linear_combination -hdifference
  have hsquare : IsSquare (unitOfInvertible (Q y) * unitOfInvertible (Q (x + y))) := by
    apply isSquare_units_val_iff.mp
    refine ⟨2 * Q y, ?_⟩
    simp only [Units.val_mul, val_unitOfInvertible, hsum]
    ring
  simpa only [squareClassHom_apply, ofAdd_eq_one, squareClass_eq_zero_iff]
    using hsquare

open Classical in
/-- The spinor norm of the specified transport is the square class of the difference norm
when it is nonzero, and is trivial when it is zero. -/
theorem orthogonalSpinorNorm_reflectionTransport (x y : V) (hxy : Q x = Q y)
    (hy : Q y ≠ 0) :
    orthogonalSpinorNorm Q hQ (Q.reflectionTransport x y hxy hy) =
      if hsub : Q (x - y) = 0 then 1
      else squareClassHom (Units.mk0 (Q (x - y)) hsub) := by
  classical
  split_ifs with hsub
  · exact Q.orthogonalSpinorNorm_reflectionTransport_of_sub_eq_zero hQ x y hxy hy hsub
  · let := (isUnit_iff_ne_zero.mpr hsub).invertible
    rw [reflectionTransport_eq_reflection, orthogonalSpinorNorm_reflectionOrthogonal]
    congr 1
    exact Units.ext (by simp)

end QuadraticMap
