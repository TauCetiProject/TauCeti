/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Filtered
public import TauCeti.RingTheory.Henselization.SmallModel

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Over

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
  let c : Cocone (IsNeighbourhood I).ι :=
    (Cocone.whiskeringEquivalence E.symm).inverse.obj (colimit.cocone (diagram I))
  -- The component formula identifies each transported leg with our explicit stage map.
  have hstage (B : Neighbourhood.{u, u} I) : (c.ι.app B).hom = stage I B := by
    simp [c, Cocone.whiskeringEquivalence, Equivalence.invFunIdAssoc_inv_app,
      Equivalence.counitInv, diagram, stage, E]
    -- The inclusion is an induced functor: its map is the underlying neighbourhood morphism.
    dsimp only [ObjectProperty.ι, inducedFunctor]
  have hw := congrArg CommAlgCat.Hom.hom (c.w f)
  simp only [CommAlgCat.hom_comp, hstage] at hw
  exact hw

/-- Naturality of the stage maps, evaluated at an element. -/
@[simp]
theorem stage_hom_apply (I : Ideal R) {B C : Neighbourhood.{u, u} I} (f : B ⟶ C)
    (b : B.obj) : stage I C (f.hom.hom b) = stage I B b :=
  DFunLike.congr_fun (stage_naturality I f) b

/-- The map from the henselization algebra induced by a cocone on all étale neighbourhoods. -/
noncomputable def desc (I : Ideal R) (s : Cocone ((IsNeighbourhood I).ι)) :
    algebra I →ₐ[R] s.pt :=
  (colimit.desc (diagram I)
    (s.whisker (equivSmallModel (Neighbourhood.{u, u} I)).inverse)).hom

/-- The map induced by a cocone agrees with that cocone on every stage. -/
@[simp]
theorem desc_comp_stage (I : Ideal R) (s : Cocone ((IsNeighbourhood I).ι))
    (B : Neighbourhood.{u, u} I) :
    (desc I s).comp (stage I B) = (s.ι.app B).hom := by
  apply AlgHom.ext
  intro b
  -- The colimit equation is categorical, so expose `desc`, `stage`, and algebra-hom composition
  -- as the corresponding composite before evaluating it at `b`.
  change ((IsNeighbourhood I).ι.map
      ((equivSmallModel (Neighbourhood.{u, u} I)).unitIso.hom.app B) ≫
    colimit.ι (diagram I)
      ((equivSmallModel (Neighbourhood.{u, u} I)).functor.obj B) ≫
    colimit.desc (diagram I) (s.whisker
      (equivSmallModel (Neighbourhood.{u, u} I)).inverse)) b = _
  rw [colimit.ι_desc]
  exact ConcreteCategory.congr_hom (s.ι.naturality
    ((equivSmallModel (Neighbourhood.{u, u} I)).unitIso.hom.app B)) b

/-- Every element of the henselization algebra comes from an étale neighbourhood. -/
theorem exists_stage_eq (I : Ideal R) (x : algebra I) :
    ∃ (B : Neighbourhood.{u, u} I) (b : B.obj), stage I B b = x := by
  let E := equivSmallModel (Neighbourhood.{u, u} I)
  let _ : IsFiltered (SmallModel (Neighbourhood.{u, u} I)) :=
    IsFiltered.of_equivalence E
  let _ : PreservesColimit (diagram I) (forget (CommAlgCat R)) := by
    -- The concrete forgetful functor from `CommAlgCat` is definitionally this composite through
    -- the under category, where the preservation instances are available.
    change PreservesColimit (diagram I)
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R) ⋙
        forget CommRingCat.{u})
    exact Limits.comp_preservesColimit _ _
  obtain ⟨j, b, rfl⟩ := Concrete.colimit_exists_rep (diagram I) x
  refine ⟨E.inverse.obj j, b, ?_⟩
  -- Expose `stage` as the equivalence unit followed by the colimit inclusion, so the unit
  -- equation can rewrite the composite.
  change ((IsNeighbourhood I).ι.map (E.unitIso.hom.app (E.inverse.obj j)) ≫
    colimit.ι (diagram I) (E.functor.obj (E.inverse.obj j))) b = _
  rw [E.unit_app_inverse]
  -- After the unit rewrite, the goal is definitionally the elementwise colimit cocone equation.
  change (colimit.ι (diagram I) _)
      ((diagram I).map (E.counitIso.inv.app j) b) = _
  exact colimit.w_apply (diagram I) (E.counitIso.inv.app j) b

/-- Two maps from the henselization algebra are equal if they agree on every stage. -/
@[ext]
theorem hom_ext {I : Ideal R} {S : Type*} [Semiring S] [Algebra R S]
    {f g : algebra I →ₐ[R] S}
    (h : ∀ (B : Neighbourhood.{u, u} I), f.comp (stage I B) = g.comp (stage I B)) :
    f = g := by
  ext x
  obtain ⟨B, b, rfl⟩ := exists_stage_eq I x
  exact DFunLike.congr_fun (h B) b

/-- Extending the ideal from a neighbourhood to the henselization agrees with extending it
directly from the base ring. -/
@[simp]
theorem map_stage_map_algebraMap (I : Ideal R) (B : Neighbourhood.{u, u} I) :
    (I.map (algebraMap R B.obj)).map (↑(stage I B) : B.obj →+* algebra I) = extended I := by
  rw [Ideal.map_map]
  congr 1
  exact (stage I B).comp_algebraMap

/-- Every `R`-algebra map out of the henselization carries the extended ideal onto the ideal
generated by `I` in the target. -/
@[simp]
theorem map_extended (I : Ideal R) {S : Type*} [CommRing S] [Algebra R S]
    (f : algebra I →ₐ[R] S) : (extended I).map f = I.map (algebraMap R S) := by
  rw [extended, ← Ideal.map_coe, Ideal.map_map]
  exact congrArg (I.map ·) f.comp_algebraMap

end TauCeti.Henselization
