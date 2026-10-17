/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Filtered
public import TauCeti.RingTheory.Henselization.SmallModel

/-!
# The underlying algebra of a henselization

The henselization of a ring along an ideal is constructed as the filtered colimit of its
étale neighbourhoods. This file forms the small diagram used for that colimit, defines the
resulting algebra, and provides the canonical map from every étale neighbourhood.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

/-- The small diagram of all étale neighbourhoods of `(R, I)`. -/
noncomputable abbrev diagram (I : Ideal R) :
    SmallModel (Neighbourhood.{u, u} I) ⥤ CommAlgCat.{u} R :=
  (equivSmallModel (Neighbourhood.{u, u} I)).inverse ⋙ (IsNeighbourhood I).ι

/-- The henselization algebra of `(R, I)`, constructed as the filtered colimit of its étale
neighbourhoods. -/
noncomputable def algebra (I : Ideal R) : CommAlgCat.{u} R :=
  colimit (diagram I)

/-- The ideal of the henselization algebra extended from `I`. -/
noncomputable abbrev extended (I : Ideal R) : Ideal (algebra I) :=
  I.map (algebraMap R (algebra I))

/-- The canonical map from an étale neighbourhood to the henselization algebra. -/
noncomputable def stage (I : Ideal R) (B : Neighbourhood.{u, u} I) : B.obj →ₐ[R] algebra I :=
  ((equivSmallModel (Neighbourhood.{u, u} I)).unitIso.hom.app B).hom ≫
    colimit.ι (diagram I) ((equivSmallModel (Neighbourhood.{u, u} I)).functor.obj B) |>.hom

/-- The stage maps form a cocone over the category of étale neighbourhoods. -/
@[simp]
theorem stage_naturality (I : Ideal R) {B C : Neighbourhood.{u, u} I} (f : B ⟶ C) :
    (stage I C).comp f.hom.hom = stage I B := by
  let E := equivSmallModel (Neighbourhood.{u, u} I)
  have hunit : (IsNeighbourhood I).ι.map f ≫
      (IsNeighbourhood I).ι.map (E.unitIso.hom.app C) =
      (IsNeighbourhood I).ι.map (E.unitIso.hom.app B) ≫
        (IsNeighbourhood I).ι.map (E.inverse.map (E.functor.map f)) := by
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp] using
      congrArg (IsNeighbourhood I).ι.map (E.unitIso.hom.naturality f)
  have hw : (IsNeighbourhood I).ι.map (E.inverse.map (E.functor.map f)) ≫
      colimit.ι (diagram I) (E.functor.obj C) =
      colimit.ι (diagram I) (E.functor.obj B) := by
    simpa only [diagram, Functor.comp_obj, Functor.comp_map] using
      colimit.w (diagram I) (E.functor.map f)
  have h' : (IsNeighbourhood I).ι.map f ≫
        (IsNeighbourhood I).ι.map (E.unitIso.hom.app C) ≫
        colimit.ι (diagram I) (E.functor.obj C) =
      (IsNeighbourhood I).ι.map (E.unitIso.hom.app B) ≫
        colimit.ι (diagram I) (E.functor.obj B) := by
    rw [← Category.assoc, hunit, Category.assoc, hw]
  exact congrArg CommAlgCat.Hom.hom h'

/-- Extending the ideal from a neighbourhood to the henselization agrees with extending it
directly from the base ring. -/
@[simp]
theorem map_extended_stage (I : Ideal R) (B : Neighbourhood.{u, u} I) :
    (I.map (algebraMap R B.obj)).map (↑(stage I B) : B.obj →+* algebra I) = extended I := by
  rw [Ideal.map_map]
  congr 1
  exact (stage I B).comp_algebraMap

end TauCeti.Henselization
