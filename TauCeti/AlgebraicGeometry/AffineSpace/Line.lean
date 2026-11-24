/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# The affine line over an affine base

For a commutative ring `R`, the affine line over `Spec R` is written here as
`Spec R[X] → Spec R`, the spectrum of the algebra map `R → R[X]`, rather than as Mathlib's
`𝔸(ULift (Fin 1); Spec R)`. This file records that this morphism is smooth of relative dimension
one, and that the origin, the spectrum of `Polynomial.constantCoeff`, is a section of it. These are
the facts needed to regard a scheme étale over `Spec k[T]` as a smooth curve over a field `k` with
the origin as a rational point.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]

/-- The affine line `Spec R[X] → Spec R` is smooth of relative dimension one. -/
instance smoothOfRelativeDimension_SpecMap_algebraMap_polynomial :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  rw [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact .of_algEquiv (n := 1) (e := MvPolynomial.uniqueAlgEquiv R (Fin 1))

/-- The origin `Spec R → Spec R[X]`, the spectrum of `Polynomial.constantCoeff`, is a section of
the affine line `Spec R[X] → Spec R`. -/
@[reassoc]
theorem SpecMap_constantCoeff_comp_SpecMap_algebraMap :
    Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := R))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) = 𝟙 _ := by
  have : (Polynomial.constantCoeff (R := R)).comp (algebraMap R (Polynomial R)) = RingHom.id R :=
    RingHom.ext fun _ ↦ Polynomial.coeff_C_zero
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, this, CommRingCat.ofHom_id, Spec.map_id]

end AlgebraicGeometry
