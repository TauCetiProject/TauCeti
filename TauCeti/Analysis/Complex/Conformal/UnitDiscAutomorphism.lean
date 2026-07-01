/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Moebius

/-!
# Standard automorphisms of the complex unit disc

This file adds the rotation factor in the standard disc-automorphism formula
`z ↦ u * (z - a) / (1 - conj a * z)`, with `u` on the unit circle and `a` in the
unit disc.  The previous Moebius file supplies the factor sending `a` to `0`; this file
packages rotations as self-equivalences of `Complex.UnitDisc` and composes the two.

This advances the conformal-mapping roadmap's L2 disc-automorphism target.  It reuses
Mathlib's `Circle` action on `Complex.UnitDisc` and Tau Ceti's `unitDiscMoebiusEquiv`.
-/

public section

namespace TauCeti

open Complex
open scoped ComplexConjugate

/-- Rotation of the complex unit disc by a unit complex number. -/
noncomputable def unitDiscRotationEquiv (u : Circle) : Complex.UnitDisc ≃ Complex.UnitDisc where
  toFun z := u • z
  invFun z := u⁻¹ • z
  left_inv z := by
    simp [smul_smul]
  right_inv z := by
    simp [smul_smul]

/-- The rotation equivalence applies by the `Circle` action on the unit disc. -/
@[simp]
lemma unitDiscRotationEquiv_apply (u : Circle) (z : Complex.UnitDisc) :
    unitDiscRotationEquiv u z = u • z :=
  by simp [unitDiscRotationEquiv]

/-- The scalar formula for a unit-disc rotation. -/
@[simp, norm_cast]
lemma coe_unitDiscRotationEquiv_apply (u : Circle) (z : Complex.UnitDisc) :
    (unitDiscRotationEquiv u z : ℂ) = (u : ℂ) * (z : ℂ) := by
  simp [unitDiscRotationEquiv]

/-- Rotation by `1` is the identity equivalence of the unit disc. -/
@[simp]
lemma unitDiscRotationEquiv_one : unitDiscRotationEquiv 1 = Equiv.refl Complex.UnitDisc :=
  Equiv.ext fun z => by simp [unitDiscRotationEquiv]

/-- The inverse of a unit-disc rotation is rotation by the inverse circle element. -/
@[simp]
lemma unitDiscRotationEquiv_symm (u : Circle) :
    (unitDiscRotationEquiv u).symm = unitDiscRotationEquiv u⁻¹ :=
  Equiv.ext fun _ => rfl

/-- The inverse rotation followed by the original rotation is the identity. -/
@[simp]
lemma unitDiscRotationEquiv_inv_trans (u : Circle) :
    (unitDiscRotationEquiv u⁻¹).trans (unitDiscRotationEquiv u) = Equiv.refl Complex.UnitDisc := by
  ext z
  simp [unitDiscRotationEquiv]

/-- The original rotation followed by the inverse rotation is the identity. -/
@[simp]
lemma unitDiscRotationEquiv_trans_inv (u : Circle) :
    (unitDiscRotationEquiv u).trans (unitDiscRotationEquiv u⁻¹) = Equiv.refl Complex.UnitDisc := by
  ext z
  simp [unitDiscRotationEquiv]

/-- The norm of a rotated unit-disc point is unchanged. -/
@[simp]
lemma norm_unitDiscRotationEquiv (u : Circle) (z : Complex.UnitDisc) :
    ‖(unitDiscRotationEquiv u z : ℂ)‖ = ‖(z : ℂ)‖ := by
  simp [unitDiscRotationEquiv]

/-- A rotated unit-disc point is zero exactly when the original point is zero. -/
@[simp]
lemma unitDiscRotationEquiv_eq_zero_iff (u : Circle) (z : Complex.UnitDisc) :
    unitDiscRotationEquiv u z = 0 ↔ z = 0 := by
  rw [← Complex.UnitDisc.coe_inj, coe_unitDiscRotationEquiv_apply, Complex.UnitDisc.coe_zero,
    mul_eq_zero, Complex.UnitDisc.coe_eq_zero]
  simp

/-- Rotation by a circle element is holomorphic as a scalar map on the open unit disc. -/
lemma differentiableOn_unitDiscRotationFormula (u : Circle) :
    DifferentiableOn ℂ (fun z : ℂ => (u : ℂ) * z) (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_const (c := (u : ℂ))).mul differentiableOn_id

/--
The standard automorphism of the complex unit disc
`z ↦ u * (z - a) / (1 - conj a * z)`.

The center-removing factor is `unitDiscMoebiusEquiv a`; the circle element `u` supplies the
rotation factor in the usual classification formula for disc automorphisms.
-/
noncomputable def unitDiscStandardAutomorphEquiv (u : Circle) (a : Complex.UnitDisc) :
    Complex.UnitDisc ≃ Complex.UnitDisc :=
  (unitDiscMoebiusEquiv a).trans (unitDiscRotationEquiv u)

/-- The standard automorphism applies by first sending `a` to `0`, then rotating. -/
@[simp]
lemma unitDiscStandardAutomorphEquiv_apply (u : Circle) (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphEquiv u a z = unitDiscRotationEquiv u (unitDiscMoebius a z) :=
  by simp [unitDiscStandardAutomorphEquiv]

/-- The scalar formula for the standard disc automorphism. -/
@[simp, norm_cast]
lemma coe_unitDiscStandardAutomorphEquiv_apply (u : Circle) (a z : Complex.UnitDisc) :
    (unitDiscStandardAutomorphEquiv u a z : ℂ) =
      (u : ℂ) *
        (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ))) := by
  simp [unitDiscStandardAutomorphEquiv]

/-- With zero center, the standard automorphism is just rotation. -/
@[simp]
lemma unitDiscStandardAutomorphEquiv_zero (u : Circle) :
    unitDiscStandardAutomorphEquiv u 0 = unitDiscRotationEquiv u := by
  ext z
  simp [unitDiscStandardAutomorphEquiv]

/-- With unit rotation factor, the standard automorphism is the Moebius equivalence. -/
@[simp]
lemma unitDiscStandardAutomorphEquiv_one (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphEquiv 1 a = unitDiscMoebiusEquiv a := by
  ext z
  simp [unitDiscStandardAutomorphEquiv]

/-- The standard automorphism sends its center to zero. -/
@[simp]
lemma unitDiscStandardAutomorphEquiv_self (u : Circle) (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphEquiv u a a = 0 := by
  rw [unitDiscStandardAutomorphEquiv_apply, unitDiscMoebius_self]
  ext
  simp

/-- The standard automorphism sends zero to `-u * a`. -/
@[simp]
lemma unitDiscStandardAutomorphEquiv_apply_zero (u : Circle) (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphEquiv u a 0 = u • (-a) := by
  simp [unitDiscStandardAutomorphEquiv]

/-- The norm of a standard automorphism value is the pseudo-hyperbolic expression. -/
@[simp]
lemma norm_unitDiscStandardAutomorphEquiv (u : Circle) (a z : Complex.UnitDisc) :
    ‖(unitDiscStandardAutomorphEquiv u a z : ℂ)‖ = pseudoHyperbolicExpr (z : ℂ) (a : ℂ) := by
  rw [unitDiscStandardAutomorphEquiv_apply, norm_unitDiscRotationEquiv, norm_unitDiscMoebius]

/-- A standard disc automorphism vanishes exactly at its center. -/
@[simp]
lemma unitDiscStandardAutomorphEquiv_eq_zero_iff (u : Circle) (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphEquiv u a z = 0 ↔ z = a := by
  rw [unitDiscStandardAutomorphEquiv_apply, unitDiscRotationEquiv_eq_zero_iff,
    unitDiscMoebius_eq_zero_iff]

/-- The scalar formula of the standard automorphism is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscStandardAutomorphFormula (u : Circle) (a : Complex.UnitDisc) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        (u : ℂ) *
          ((z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * z)))
      (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_const (c := (u : ℂ))).mul (differentiableOn_unitDiscMoebiusFormula a)

/-- The inverse of a standard automorphism as a composition of the inverse rotation and
the inverse Moebius factor. -/
@[simp]
lemma unitDiscStandardAutomorphEquiv_symm (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphEquiv u a).symm =
      (unitDiscRotationEquiv u⁻¹).trans (unitDiscMoebiusEquiv (-a)) :=
  by simp [unitDiscStandardAutomorphEquiv]

end TauCeti
