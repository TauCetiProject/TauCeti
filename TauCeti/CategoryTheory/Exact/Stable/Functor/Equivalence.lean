/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Functor.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Triangle equivalences of Frobenius stable categories

An additive equivalence preserving conflations in both directions preserves
projective-injectives between Frobenius exact categories. Its induced stable equivalence
is a triangle equivalence for Happel's triangulations.

Both directions of the induced equivalence commute with integral shifts, as do its unit
and counit. The identification of its forward functor with the descended exact functor
respects shifts. The theorem `stableEquivalenceIsTriangulated` expresses the triangle
equivalence through Mathlib's `Equivalence.IsTriangulated` interface.

## References

* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

universe v₁ v₂ u₁ u₂

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
variable {E : ExactStructure C} {E' : ExactStructure D}

namespace StableConflationExact

variable {e : C ≌ D} [e.functor.Additive]
variable (hF : StableConflationExact E E' e.functor)
variable (hG : StableConflationExact E' E e.inverse)
variable (hE : E.IsFrobenius) (hE' : E'.IsFrobenius)

/-- The forward functor of the induced stable equivalence has the shift comparison
constructed from the original exact functor's injective presentations. -/
@[instance_reducible]
noncomputable def stableEquivalenceFunctorCommShift :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    (stableEquivalence e hF hG hE hE').functor.CommShift ℤ := by
  letI := hE.stableHasShift
  letI := hE'.stableHasShift
  letI := hF.stableFunctorCommShift hE hE'
  exact Functor.CommShift.ofIso
    (eqToIso (stableEquivalence_functor e hF hG hE hE').symm) ℤ

/-- The forward stable equivalence's shift comparison is the descended functor's comparison
transported along their identification. -/
@[simp]
theorem stableEquivalenceFunctor_commShiftIso (n : ℤ) :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := hF.stableFunctorCommShift hE hE'
    letI := stableEquivalenceFunctorCommShift hF hG hE hE'
    (stableEquivalence e hF hG hE hE').functor.commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor E.ProjectiveStableCategory n)
        (eqToIso (stableEquivalence_functor e hF hG hE hE')) ≪≫
      (hF.stableFunctor hE).commShiftIso n ≪≫
      Functor.isoWhiskerRight (eqToIso (stableEquivalence_functor e hF hG hE hE')).symm
        (shiftFunctor E'.ProjectiveStableCategory n) :=
  (rfl)

/-- The inverse stable equivalence commutes with integral shifts via the canonical mate
of its forward comparison. -/
@[instance_reducible]
noncomputable def stableEquivalenceInverseCommShift :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    (stableEquivalence e hF hG hE hE').inverse.CommShift ℤ := by
  letI := hE.stableHasShift
  letI := hE'.stableHasShift
  letI := stableEquivalenceFunctorCommShift hF hG hE hE'
  exact (stableEquivalence e hF hG hE hE').commShiftInverse ℤ

/-- The identification of the stable equivalence's forward functor with the descended
exact functor is compatible with every integral shift. -/
theorem stableEquivalence_functor_commShift :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := hF.stableFunctorCommShift hE hE'
    letI := stableEquivalenceFunctorCommShift hF hG hE hE'
    (eqToIso (stableEquivalence_functor e hF hG hE hE')).hom.CommShift ℤ := by
  let := hE.stableHasShift
  let := hE'.stableHasShift
  let := hF.stableFunctorCommShift hE hE'
  let := stableEquivalenceFunctorCommShift hF hG hE hE'
  have := Functor.CommShift.ofIso_compatibility
    (eqToIso (stableEquivalence_functor e hF hG hE hE').symm) ℤ
  exact inferInstanceAs
    ((eqToIso (stableEquivalence_functor e hF hG hE hE').symm).inv.CommShift ℤ)

/-- An exact equivalence of Frobenius categories induces a triangle equivalence of stable
categories. The inverse shift comparison is determined by the forward comparison and the
unit and counit, so both directions and both equivalence isomorphisms respect the shifts. -/
theorem stableEquivalenceIsTriangulated :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := hE.stableShiftFunctor_additive
    letI := hE'.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := hE'.stablePretriangulated
    letI := stableEquivalenceFunctorCommShift hF hG hE hE'
    letI := stableEquivalenceInverseCommShift hF hG hE hE'
    letI := (stableEquivalence e hF hG hE hE').commShift_of_functor ℤ
    (stableEquivalence e hF hG hE hE').IsTriangulated := by
  let := hE.stableHasShift
  let := hE'.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE'.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE'.stablePretriangulated
  let := hF.stableFunctorCommShift hE hE'
  let := stableEquivalenceFunctorCommShift hF hG hE hE'
  let := stableEquivalenceInverseCommShift hF hG hE hE'
  let := (stableEquivalence e hF hG hE hE').commShift_of_functor ℤ
  have := hF.stableFunctorIsTriangulated hE hE'
  have := stableEquivalence_functor_commShift hF hG hE hE'
  exact Equivalence.IsTriangulated.mk' _
    (Functor.isTriangulated_of_iso (eqToIso (stableEquivalence_functor e hF hG hE hE')).symm)

end StableConflationExact

end TauCeti
