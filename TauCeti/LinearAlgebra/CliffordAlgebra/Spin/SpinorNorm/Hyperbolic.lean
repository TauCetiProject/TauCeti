/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Hyperbolic

/-!
# The spinor norm on the diagonal torus of the hyperbolic plane

The special orthogonal group of the hyperbolic plane `H` is the diagonal torus `t ↦ diag(t, t⁻¹)`
(`TauCeti.hyperbolicTorusEquiv`). This file computes the spinor norm on it: `diag(t, t⁻¹)` is the
product of the reflections in vectors of norms `t` and `1`, so its spinor norm is the square class
of `t`. Thus the spinor norm, read through the torus, is the quotient map `Kˣ → Kˣ/(Kˣ)²`, and the
image of `Spin(H) → SO(H)`, which is the kernel of the spinor norm, is the torus at the square
parameters `(Kˣ)²`.

## Main results

* `CliffordAlgebra.spinorNorm_hyperbolicTorus`: the spinor norm of `diag(t, t⁻¹)` is `[t]`.
* `CliffordAlgebra.hyperbolicTorus_mem_range_spinToSpecialOrthogonal_iff`: `diag(t, t⁻¹)` lifts to
  `Spin(H)` exactly when `t` is a square.
* `CliffordAlgebra.range_spinToSpecialOrthogonal_hyperbolicPlane`: the image of `Spin(H)` is the
  image of the squares `(Kˣ)²` under the torus.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §55.
-/

public section

namespace CliffordAlgebra

open TauCeti QuadraticMap

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- The spinor norm of the diagonal torus element `diag(t, t⁻¹)` of the hyperbolic plane is the
square class of `t`. -/
@[simp high]
theorem spinorNorm_hyperbolicTorus (t : Kˣ) :
    spinorNorm (hyperbolicPlane K) nondegenerate_hyperbolicPlane (hyperbolicTorus K t) =
      squareClassHom t := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  -- `diag(t, t⁻¹)` is the reflection in `e` (of norm `1`) followed by the reflection in `w`
  -- (of norm `t`).
  set w : Fin 2 → K := ![⅟2 * (t + 1), ⅟2 * (t - 1)] with hw_def
  set e : Fin 2 → K := ![1, 0] with he_def
  have hw : hyperbolicPlane K w = t := by
    simp only [hw_def, hyperbolicPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [invOf_eq_inv]
    field_simp
    ring
  have he : hyperbolicPlane K e = 1 := by simp [he_def]
  let _ : Invertible (hyperbolicPlane K w) := invertibleOfNonzero (hw ▸ t.ne_zero)
  let _ : Invertible (hyperbolicPlane K e) := invertibleOfNonzero (he ▸ one_ne_zero)
  have hg : specialOrthogonalToOrthogonal _ (hyperbolicTorus K t) =
      reflectionOrthogonal _ w * reflectionOrthogonal _ e := by
    refine Subtype.ext (LinearEquiv.ext fun x ↦ ?_)
    ext i
    simp only [coe_specialOrthogonalToOrthogonal, Subgroup.coe_mul, coe_reflectionOrthogonal,
      LinearEquiv.mul_apply, hyperbolicTorus_apply, reflection_apply, invOf_eq_inv, hw, he,
      polar_hyperbolicPlane]
    fin_cases i <;> simp [hw_def, he_def, Matrix.vecHead, Matrix.vecTail] <;> field_simp <;> ring
  rw [spinorNorm_apply, hg, map_mul, orthogonalSpinorNorm_reflectionOrthogonal,
    orthogonalSpinorNorm_reflectionOrthogonal]
  -- The reflection formula records the norms as units `unitOfInvertible (Q v)`; identify them
  -- with `t` and `1` by comparing underlying values.
  have hwt : unitOfInvertible (hyperbolicPlane K w) = t := Units.ext hw
  have he1 : unitOfInvertible (hyperbolicPlane K e) = 1 := Units.ext he
  rw [hwt, he1, map_one]
  exact mul_one (squareClassHom t)

/-- A diagonal torus element `diag(t, t⁻¹)` of the hyperbolic plane lifts to `Spin` exactly when
`t` is a square. -/
theorem hyperbolicTorus_mem_range_spinToSpecialOrthogonal_iff (t : Kˣ) :
    hyperbolicTorus K t ∈ (spinToSpecialOrthogonal (hyperbolicPlane K)).range ↔ IsSquare t := by
  rw [range_spinToSpecialOrthogonal_eq_ker_spinorNorm _ nondegenerate_hyperbolicPlane,
    MonoidHom.mem_ker, spinorNorm_hyperbolicTorus, squareClassHom_apply, ofAdd_eq_one,
    squareClass_eq_zero_iff]

/-- The image of `Spin(H) → SO(H)` for the hyperbolic plane `H` is the diagonal torus at the square
parameters. -/
theorem range_spinToSpecialOrthogonal_hyperbolicPlane :
    (spinToSpecialOrthogonal (hyperbolicPlane K)).range =
      (Subgroup.square Kˣ).map (hyperbolicTorus K) := by
  ext g
  obtain ⟨t, rfl⟩ := hyperbolicTorus_surjective g
  rw [hyperbolicTorus_mem_range_spinToSpecialOrthogonal_iff,
    Subgroup.mem_map_iff_mem hyperbolicTorus_injective, Subgroup.mem_square]

end CliffordAlgebra
