/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.Algebra.Ring.ULift

/-!
# The universe lift functor for commutative rings

`CommRingCat.uliftFunctor` sends a commutative ring `R` in universe `u` to `ULift R` in universe
`max u v`. It is fully faithful, and it preserves `u`-small limits and `u`-small filtered colimits.
The two preservation results are what is needed to transport a sheaf of rings, together with its
stalks, from universe `u` to universe `max u v`.

The proofs follow those for `GrpCat.uliftFunctor` in `Mathlib/Algebra/Category/Grp/Ulift.lean`
by Sophie Morel: the forgetful functor to types preserves and reflects the relevant limits and
colimits, and `CategoryTheory.uliftFunctor` on types preserves them.
-/

public section

universe v u

open CategoryTheory Limits

namespace CommRingCat

/-- The universe lift functor for commutative rings. -/
@[expose, pp_with_univ]
def uliftFunctor : CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  obj R := CommRingCat.of (ULift.{v} R)
  map f := CommRingCat.ofHom f.hom.ulift

/-- The universe lift of a commutative ring is `ULift` of it. -/
@[simp]
theorem uliftFunctor_obj (R : CommRingCat.{u}) :
    uliftFunctor.{v}.obj R = CommRingCat.of (ULift.{v} R) :=
  rfl

/-- The universe lift of a ring homomorphism is `RingHom.ulift` of it. -/
@[simp]
theorem uliftFunctor_map_hom {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (uliftFunctor.{v}.map f).hom = f.hom.ulift :=
  rfl

/-- The universe lift functor for commutative rings is fully faithful. -/
def uliftFunctorFullyFaithful : uliftFunctor.{v, u}.FullyFaithful where
  preimage f := CommRingCat.ofHom <|
    ULift.ringEquiv.toRingHom.comp (f.hom.comp ULift.ringEquiv.symm.toRingHom)

instance : uliftFunctor.{v, u}.Full := uliftFunctorFullyFaithful.full

instance : uliftFunctor.{v, u}.Faithful := uliftFunctorFullyFaithful.faithful

/-- The universe lift functor for commutative rings preserves `u`-small limits. -/
noncomputable instance uliftFunctor_preservesLimit {J : Type u} [Category.{u} J]
    (K : J ⥤ CommRingCat.{u}) : PreservesLimit K uliftFunctor.{v, u} where
  preserves lc := by
    have : ReflectsLimitsOfShape J (forget CommRingCat.{max u v}) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact ⟨isLimitOfReflects (forget CommRingCat) <|
      isLimitOfPreserves CategoryTheory.uliftFunctor.{v}
        (isLimitOfPreserves (forget CommRingCat) lc)⟩

noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type u} [Category.{u} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/-- The universe lift functor for commutative rings preserves `u`-small limits. -/
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{u, u} uliftFunctor.{v, u} where

/-- The universe lift functor for commutative rings preserves `u`-small filtered colimits. -/
noncomputable instance uliftFunctor_preservesColimit {J : Type u} [Category.{u} J] [IsFiltered J]
    (K : J ⥤ CommRingCat.{u}) : PreservesColimit K uliftFunctor.{v, u} where
  preserves lc := by
    have : ReflectsFilteredColimitsOfSize.{u, u} (forget CommRingCat.{max u v}) :=
      reflectsFilteredColimitsOfSize_shrink _
    have : PreservesFilteredColimitsOfSize.{u, u} (forget CommRingCat.{max u v}) :=
      preservesFilteredColimitsOfSize_shrink _
    exact ⟨isColimitOfReflects (forget CommRingCat) <|
      isColimitOfPreserves CategoryTheory.uliftFunctor.{v}
        (isColimitOfPreserves (forget CommRingCat) lc)⟩

/-- The universe lift functor for commutative rings preserves `u`-small filtered colimits. -/
noncomputable instance uliftFunctor_preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u, u} uliftFunctor.{v, u} where
  preserves_filtered_colimits _ _ _ := ⟨fun {_} ↦ inferInstance⟩

end CommRingCat
