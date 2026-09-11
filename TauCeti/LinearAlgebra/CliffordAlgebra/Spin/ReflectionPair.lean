/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal

/-!
# Normalized reflection-pair lifts in Spin groups

Two vectors of quadratic norm one determine a canonical element of the Spin group: the product of
their Clifford generators. Its orthogonal action is the ordered product of the two corresponding
reflections. This gives a concrete choice of lift for reflection products over positive-definite
real quadratic spaces, where anisotropic vectors can be normalized to unit norm.

## Main results

* `CliffordAlgebra.spinReflectionPair` bundles the product of two unit Clifford generators as a
  Spin element.
* `CliffordAlgebra.spinReflectionPair_self` identifies a repeated pair with the identity.
* `CliffordAlgebra.spinToOrthogonal_spinReflectionPair` computes the orthogonal action of a
  normalized reflection pair.
* `CliffordAlgebra.coe_spinToSpecialOrthogonal_spinReflectionPair` gives the same computation for
  the special-orthogonal projection.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

open TauCeti

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- The product of the Clifford generators of two unit vectors, as an element of the Spin group. -/
public def spinReflectionPair (Q : QuadraticForm R M) (v w : M) (hv : Q v = 1) (hw : Q w = 1) :
    spinGroup Q :=
  ⟨ι Q v * ι Q w,
    ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one v w (by rw [hv, hw, one_mul])⟩

@[simp]
theorem coe_spinReflectionPair (Q : QuadraticForm R M) (v w : M) (hv : Q v = 1)
    (hw : Q w = 1) :
    (spinReflectionPair Q v w hv hw : CliffordAlgebra Q) = ι Q v * ι Q w := by
  simp [spinReflectionPair]

/-- Repeating a unit vector in a reflection pair gives the identity Spin element. -/
@[simp]
theorem spinReflectionPair_self (Q : QuadraticForm R M) (v : M) (hv : Q v = 1) :
    spinReflectionPair Q v v hv hv = 1 := by
  apply Subtype.ext
  simp [spinReflectionPair, ι_sq_scalar, hv]

variable [Invertible (2 : R)]

/-- The orthogonal action of a normalized reflection-pair lift is the ordered product of the two
reflections. -/
@[simp]
theorem spinToOrthogonal_spinReflectionPair (Q : QuadraticForm R M) (v w : M)
    (hv : Q v = 1) (hw : Q w = 1) :
    let _ : Invertible (Q v) := hv.symm ▸ invertibleOne
    let _ : Invertible (Q w) := hw.symm ▸ invertibleOne
    spinToOrthogonal Q (spinReflectionPair Q v w hv hw) =
      QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w := by
  dsimp only
  let _ : Invertible (Q v) := hv.symm ▸ invertibleOne
  let _ : Invertible (Q w) := hw.symm ▸ invertibleOne
  exact spinToOrthogonal_eq_reflection_mul_reflection_of_coe_eq (Q := Q) _ v w
    (coe_spinReflectionPair Q v w hv hw)

/-- The special-orthogonal projection of a normalized reflection-pair lift has underlying action
the ordered product of the two orthogonal reflections. -/
@[simp]
theorem coe_spinToSpecialOrthogonal_spinReflectionPair (Q : QuadraticForm R M) (v w : M)
    (hv : Q v = 1) (hw : Q w = 1) :
    let _ : Invertible (Q v) := hv.symm ▸ invertibleOne
    let _ : Invertible (Q w) := hw.symm ▸ invertibleOne
    ((spinToSpecialOrthogonal Q (spinReflectionPair Q v w hv hw) :
        QuadraticMap.specialOrthogonalGroup Q) : M ≃ₗ[R] M) =
      ((QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w :
        QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) := by
  dsimp only
  let _ : Invertible (Q v) := hv.symm ▸ invertibleOne
  let _ : Invertible (Q w) := hw.symm ▸ invertibleOne
  apply LinearEquiv.ext
  intro m
  simpa only [coe_spinToSpecialOrthogonal_apply, coe_spinToOrthogonal_apply] using
    congrArg (fun y : QuadraticMap.orthogonalGroup Q => (y : M ≃ₗ[R] M) m)
      (spinToOrthogonal_spinReflectionPair Q v w hv hw)

end CliffordAlgebra
