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

The forward shift comparison is transported from
`StableConflationExact.stableFunctorCommShift`. The inverse comparison is the one determined
by this forward comparison and the unit and counit of the existing stable equivalence,
using Mathlib's `Equivalence.commShiftInverse`. In particular both natural isomorphisms
commute with integral shifts. No new equivalence or choice of stable suspension is introduced.

Install `stableEquivalenceFunctorCommShift`, then the equivalence's `commShiftInverse`,
and `commShift_of_functor` locally. The theorem `stableEquivalenceIsTriangulated` then
supplies Mathlib's `Equivalence.IsTriangulated`, including triangle-functor structures
on both directions. The comparison with the original stable functor also respects shifts.

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

/-- An exact additive equivalence into a Frobenius category preserves projective-injectives.
Exactness of the inverse is sufficient for preservation of projectives; the target's
Frobenius property then gives injectivity. The source need not be Frobenius. -/
theorem ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    {e : C ≌ D} [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor)
    (hG : E'.IsConflationExact E e.inverse) (hE' : E'.IsFrobenius) :
    StableConflationExact E E' e.functor where
  isConflationExact := hF
  map_projectiveInjective {X} hX := by
    rw [ExactStructure.projectiveInjective_iff] at hX ⊢
    have hP := E.isProjective_map_adjoint E' e.toAdjunction hG hX.1
    exact ⟨hP, (hE'.projective_iff_injective _).mp hP⟩

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
    letI := (stableEquivalence e hF hG hE hE').commShiftInverse ℤ
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
  let := (stableEquivalence e hF hG hE hE').commShiftInverse ℤ
  let := (stableEquivalence e hF hG hE hE').commShift_of_functor ℤ
  have := hF.stableFunctorIsTriangulated hE hE'
  have := stableEquivalence_functor_commShift hF hG hE hE'
  exact Equivalence.IsTriangulated.mk' _
    (Functor.isTriangulated_of_iso (eqToIso (stableEquivalence_functor e hF hG hE hE')).symm)

end StableConflationExact

end TauCeti
