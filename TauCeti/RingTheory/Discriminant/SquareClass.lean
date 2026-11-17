/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant
public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative

/-!
# The discriminant square class of a separable field extension

The discriminant of a field basis changes by the square of the change-of-basis determinant.
Consequently a finite separable extension has a well-defined discriminant in the multiplicative
square-class group of the base field. This retains the unit information lost by the discriminant
ideal and determines the quadratic field obtained by adjoining a square root of a discriminant.

`discriminantClass_eq` computes this invariant in any finite basis, including bases with a
different index type. `discriminantClass_eq_iff` tests a proposed representative without quotient
calculations, and `discriminantClass_eq_of_algEquiv` gives invariance under algebra equivalence.
No valuation or restriction on the characteristic is needed. The change-of-basis formula is
Mathlib's `Algebra.discr_of_matrix_vecMul`. For comparison,
`Algebra.discr_eq_zero_of_not_isSeparable` records why an inseparable extension cannot supply a
unit discriminant.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §3 (discriminants and change of basis).
-/

public section
noncomputable section

open Matrix

namespace Algebra

/-- Over an inseparable field extension every nonempty finite family's discriminant is zero,
since the trace pairing vanishes. -/
theorem discr_eq_zero_of_not_isSeparable (K L : Type*) [Field K] [Field L] [Algebra K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (b : ι → L)
    (h : ¬ Algebra.IsSeparable K L) : Algebra.discr K b = 0 := by
  rw [Algebra.discr_def]
  have hm : Algebra.traceMatrix K b = 0 := by
    ext i j
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Algebra.trace_eq_zero_of_not_isSeparable h]
  rw [hm, Matrix.det_zero]

end Algebra

namespace TauCeti

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [Module.Finite K L] [Algebra.IsSeparable K L]

/-- The square class of the discriminant of a finite separable field extension.
This is the unsigned discriminant of the trace pairing. -/
def discriminantClass : Kˣ ⧸ Subgroup.square Kˣ :=
  squareClassHom (Units.mk0 (Algebra.discr K (Module.finBasis K L))
    (Algebra.discr_not_zero_of_basis K _))

/-- Any finite field basis computes the discriminant square class. -/
theorem discriminantClass_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    discriminantClass K L =
      squareClassHom (Units.mk0 (Algebra.discr K b) (Algebra.discr_not_zero_of_basis K b)) := by
  classical
  let c := (Module.finBasis K L).reindex ((Module.finBasis K L).indexEquiv b)
  have hc : Algebra.discr K c = Algebra.discr K (Module.finBasis K L) := by
    simpa only [c, Module.Basis.coe_reindex] using
      Algebra.discr_reindex K (Module.finBasis K L) ((Module.finBasis K L).indexEquiv b)
  have hd : Algebra.discr K b = (c.toMatrix b).det ^ 2 * Algebra.discr K c := by
    calc
      Algebra.discr K b = Algebra.discr K
          (c ᵥ* (c.toMatrix b).map (algebraMap K L)) :=
        congrArg (Algebra.discr K) (c.toMatrix_map_vecMul b).symm
      _ = _ := Algebra.discr_of_matrix_vecMul _ _
  let u : Kˣ := (c.isUnit_det b).unit
  have hu : (u : K) = (c.toMatrix b).det := (c.isUnit_det b).unit_spec
  have he : Units.mk0 (Algebra.discr K b) (Algebra.discr_not_zero_of_basis K b) =
      u ^ 2 * Units.mk0 (Algebra.discr K (Module.finBasis K L))
        (Algebra.discr_not_zero_of_basis K _) := by
    apply Units.ext
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hu, ← hc] using hd
  rw [he, squareClassHom_sq_mul, discriminantClass]

/-- A proposed unit represents the discriminant class exactly when its product with a basis
discriminant is a square in the base field. -/
theorem discriminantClass_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (u : Kˣ) :
    discriminantClass K L = squareClassHom u ↔ IsSquare (Algebra.discr K b * (u : K)) := by
  rw [discriminantClass_eq K L b, squareClassHom_eq_iff, squareClass_eq_iff_isSquare_mul,
    ← Units.isSquare_coe_iff]
  rfl

/-- The discriminant class is trivial exactly when the discriminant of a field basis is a
square. This test does not depend on the basis. -/
theorem discriminantClass_eq_one_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    discriminantClass K L = 1 ↔ IsSquare (Algebra.discr K b) := by
  simpa using discriminantClass_eq_iff K L b 1

/-- Algebra-equivalent finite separable extensions have the same discriminant square class. -/
theorem discriminantClass_eq_of_algEquiv (M : Type*) [Field M] [Algebra K M]
    [Module.Finite K M] [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) :
    discriminantClass K L = discriminantClass K M := by
  classical
  let b := Module.finBasis K L
  rw [discriminantClass_eq K L b, discriminantClass_eq K M (b.map e.toLinearEquiv)]
  congr 1
  apply Units.ext
  exact Algebra.discr_eq_discr_of_algEquiv b e

/-- The identity extension has trivial discriminant square class. -/
@[simp]
theorem discriminantClass_self : discriminantClass K K = 1 := by
  rw [discriminantClass_eq_one_iff K K (Module.Basis.singleton Unit K)]
  have hd : Algebra.discr K (Module.Basis.singleton Unit K) = 1 := by
    simp [Algebra.discr_def, Matrix.det_unique, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]
  rw [hd]
  exact IsSquare.one

end TauCeti
