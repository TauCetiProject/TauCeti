/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.RightMappingSpace
public import TauCeti.AlgebraicTopology.Quasicategory.LocallySmall

/-!
# Small mapping models for the differential graded nerve

The dg nerve of a category with objects in universe `u` and Hom complexes in universe `v`
is locally `v`-small, independently of `u`. Its right mapping space between `X` and `Y`
has the small Kan model obtained by applying good truncation and Dold–Kan to
`dgHomComplex R X Y`. Thus the object type need not be small in the universe of the
mapping homotopy types, as required when studying accessibility of derived enhancements.

`TauCeti.dgNerve.rightMappingSpaceSmallModel` retains this particular model and its
comparison maps, rather than making an unrelated choice of a small model at each pair.
It uses the existing normalized-chain comparison
`TauCeti.dgNerve.rightMappingSpaceIsoCochainToSSet`; the only additional universe
comparison inserts or removes an `ULift` wrapper. No smallness hypothesis on the
objects, boundedness hypothesis on the Hom complexes, or passage to the homotopy
category is used.

## References

* J. Lurie, *Higher Algebra*, Remark 1.3.1.12.
* J. Lurie, *Higher Topos Theory*, Corollary 5.4.1.5 and Proposition 5.4.1.7.
-/

public section

open CategoryTheory Simplicial

namespace TauCeti.dgNerve

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-- The Dold–Kan image of the good truncation of the Hom complex is a small Kan model
of the right mapping space of the dg nerve. The model lives in the Hom universe,
regardless of the universe of objects. -/
noncomputable def rightMappingSpaceSmallModel (X Y : C) :
    SmallSpaceModel.{v, max u v}
      ((dgNerve R C).rightMappingSpace ((dgNerveEquiv R C).symm X)
        ((dgNerveEquiv R C).symm Y) : SSet) :=
  (SSet.smallSpaceModelUlift.{v, u} ((cochainToSSet R).obj (dgHomComplex R X Y))).transport
    (rightMappingSpaceIsoCochainToSSet X Y).symm

/-- The chosen small model is the Dold–Kan construction on the good truncation of
`Hom(X, Y)`, with cycles in degree zero. -/
@[simp]
theorem rightMappingSpaceSmallModel_model (X Y : C) :
    (rightMappingSpaceSmallModel (R := R) X Y).model =
      (cochainToSSet R).obj (dgHomComplex R X Y) :=
  (rfl)

/-- The forward comparison is the inverse Dold–Kan mapping-space isomorphism,
after inserting the extra universe-lift wrapper. -/
theorem rightMappingSpaceSmallModel_hom (X Y : C) :
    (rightMappingSpaceSmallModel (R := R) X Y).hom =
      (by
        rw [rightMappingSpaceSmallModel_model]
        exact (SSet.smallSpaceModelUlift.{v, u}
          ((cochainToSSet R).obj (dgHomComplex R X Y))).hom ≫
          SSet.uliftFunctor.map (rightMappingSpaceIsoCochainToSSet X Y).inv) :=
  (rfl)

/-- The reverse comparison is the Dold–Kan mapping-space isomorphism,
followed by removal of the extra universe-lift wrapper. -/
theorem rightMappingSpaceSmallModel_inv (X Y : C) :
    (rightMappingSpaceSmallModel (R := R) X Y).inv =
      (by
        rw [rightMappingSpaceSmallModel_model]
        exact SSet.uliftFunctor.map (rightMappingSpaceIsoCochainToSSet X Y).hom ≫
          (SSet.smallSpaceModelUlift.{v, u}
            ((cochainToSSet R).obj (dgHomComplex R X Y))).inv) :=
  (rfl)

/-- A dg nerve is locally small in the universe of its Hom complexes, even when
its objects live in a larger universe. -/
instance : SSet.IsLocallySmall.{v} (dgNerve R C) where
  hasSmallSpaceModel x y := by
    obtain ⟨X, rfl⟩ := (dgNerveEquiv R C).symm.surjective x
    obtain ⟨Y, rfl⟩ := (dgNerveEquiv R C).symm.surjective y
    exact (hasSmallSpaceModel_iff_nonempty _).2 ⟨rightMappingSpaceSmallModel X Y⟩

end TauCeti.dgNerve
