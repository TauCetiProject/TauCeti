/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Filtered
public import TauCeti.RingTheory.Henselization.SmallModel
public import TauCeti.Algebra.Category.CommAlgCat.SmallFilteredColimit

/-!
# The underlying algebra of a henselization

The henselization of a ring along an ideal is constructed as the filtered colimit of its
étale neighbourhoods. This file defines the resulting algebra and provides the canonical map
from every étale neighbourhood, together with the small-model diagram `diagram` and the
isomorphism `algebraIsoColimitDiagram` identifying the algebra with its colimit.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
-/

public section

open CategoryTheory Limits

universe u w

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

/-- The restriction of the étale neighbourhoods of `(R, I)` to a small model of the neighbourhood
category. Its colimit is identified with `algebra I` by `algebraIsoColimitDiagram`. -/
noncomputable abbrev diagram (I : Ideal R) :
    SmallModel (Neighbourhood.{u, u} I) ⥤ CommAlgCat.{u} R :=
  SmallFilteredAlgebraColimit.diagram (IsNeighbourhood I).ι

/-- The henselization algebra of `(R, I)`, constructed as the filtered colimit of its étale
neighbourhoods. -/
noncomputable def algebra (I : Ideal R) : CommAlgCat.{u} R :=
  SmallFilteredAlgebraColimit.algebra (IsNeighbourhood I).ι

/-- The ideal of the henselization algebra extended from `I`. -/
noncomputable abbrev extended (I : Ideal R) : Ideal (algebra I) :=
  I.map (algebraMap R (algebra I))

/-- The canonical map from an étale neighbourhood to the henselization algebra. -/
noncomputable def stage (I : Ideal R) (B : Neighbourhood.{u, u} I) :
    B.obj →ₐ[R] algebra I :=
  SmallFilteredAlgebraColimit.stage (IsNeighbourhood I).ι B

/-- `stage` unfolds to `SmallFilteredAlgebraColimit.stage` for the neighbourhood functor. -/
private theorem stage_def (I : Ideal R) (B : Neighbourhood.{u, u} I) :
    stage I B = SmallFilteredAlgebraColimit.stage (IsNeighbourhood I).ι B :=
  (rfl)

/-- The colimit over all étale neighbourhoods is the colimit over the small model. -/
noncomputable def algebraIsoColimitDiagram (I : Ideal R) : algebra I ≅ colimit (diagram I) :=
  SmallFilteredAlgebraColimit.algebraIsoColimitDiagram (IsNeighbourhood I).ι

/-- The comparison with the small-model colimit is compatible with the stage maps. -/
@[simp]
theorem algebraIsoColimitDiagram_inv_comp_ι (I : Ideal R)
    (smallObject : SmallModel (Neighbourhood.{u, u} I)) :
    (algebraIsoColimitDiagram I).inv.hom.comp (colimit.ι (diagram I) smallObject).hom =
      stage I ((equivSmallModel (Neighbourhood.{u, u} I)).inverse.obj smallObject) := by
  rw [stage_def]
  exact SmallFilteredAlgebraColimit.algebraIsoColimitDiagram_inv_comp_ι
    (IsNeighbourhood I).ι smallObject

/-- The stage maps form a cocone over the category of étale neighbourhoods. -/
@[simp]
theorem stage_naturality (I : Ideal R) {B C : Neighbourhood.{u, u} I} (f : B ⟶ C) :
    (stage I C).comp f.hom.hom = stage I B := by
  rw [stage_def, stage_def]
  exact SmallFilteredAlgebraColimit.stage_naturality (IsNeighbourhood I).ι f

/-- Naturality of the stage maps, evaluated at an element. -/
@[simp]
theorem stage_hom_apply (I : Ideal R) {B C : Neighbourhood.{u, u} I} (f : B ⟶ C)
    (b : B.obj) : stage I C (f.hom.hom b) = stage I B b :=
  SmallFilteredAlgebraColimit.stage_map_apply (IsNeighbourhood I).ι f b

/-- The map from the henselization algebra induced by a cocone on all étale neighbourhoods. -/
noncomputable def desc (I : Ideal R) (s : Cocone ((IsNeighbourhood I).ι)) :
    algebra I →ₐ[R] s.pt :=
  SmallFilteredAlgebraColimit.desc (IsNeighbourhood I).ι s

/-- `desc` unfolds to `SmallFilteredAlgebraColimit.desc`. -/
private theorem desc_def (I : Ideal R) (s : Cocone ((IsNeighbourhood I).ι)) :
    desc I s = SmallFilteredAlgebraColimit.desc (IsNeighbourhood I).ι s :=
  (rfl)

/-- The map induced by a cocone agrees with that cocone on every stage. -/
@[simp]
theorem desc_comp_stage (I : Ideal R) (s : Cocone ((IsNeighbourhood I).ι))
    (B : Neighbourhood.{u, u} I) :
    (desc I s).comp (stage I B) = (s.ι.app B).hom := by
  rw [desc_def, stage_def]
  exact SmallFilteredAlgebraColimit.desc_comp_stage (IsNeighbourhood I).ι s B

/-- The map induced by a cocone, evaluated at a stage element. -/
@[simp]
theorem desc_stage_apply (I : Ideal R) (s : Cocone ((IsNeighbourhood I).ι))
    (B : Neighbourhood.{u, u} I) (b : B.obj) :
    desc I s (stage I B b) = (s.ι.app B).hom b :=
  SmallFilteredAlgebraColimit.desc_stage_apply (IsNeighbourhood I).ι s B b

/-- A compatible family of `R`-algebra maps from the étale neighbourhoods of `(R, I)` to an
`R`-algebra `S` in any universe descends to the henselization algebra. -/
noncomputable def descOfCompatible (I : Ideal R) {S : Type*} [CommRing S] [Algebra R S]
    (stageMap : ∀ B : Neighbourhood.{u, u} I, B.obj →ₐ[R] S)
    (hcompat : ∀ {B C : Neighbourhood.{u, u} I} (f : B ⟶ C),
      (stageMap C).comp f.hom.hom = stageMap B) :
    algebra I →ₐ[R] S :=
  SmallFilteredAlgebraColimit.descOfCompatible (IsNeighbourhood I).ι stageMap hcompat

/-- `descOfCompatible` unfolds to `SmallFilteredAlgebraColimit.descOfCompatible` for the
neighbourhood functor. -/
private theorem descOfCompatible_def (I : Ideal R) {S : Type*} [CommRing S] [Algebra R S]
    (stageMap : ∀ B : Neighbourhood.{u, u} I, B.obj →ₐ[R] S)
    (hcompat : ∀ {B C : Neighbourhood.{u, u} I} (f : B ⟶ C),
      (stageMap C).comp f.hom.hom = stageMap B) :
    descOfCompatible I stageMap hcompat =
      SmallFilteredAlgebraColimit.descOfCompatible (IsNeighbourhood I).ι stageMap hcompat :=
  (rfl)

/-- The descent of a compatible family restricts to the family on every étale neighbourhood. -/
@[simp]
theorem descOfCompatible_comp_stage (I : Ideal R) {S : Type*} [CommRing S] [Algebra R S]
    (stageMap : ∀ B : Neighbourhood.{u, u} I, B.obj →ₐ[R] S)
    (hcompat : ∀ {B C : Neighbourhood.{u, u} I} (f : B ⟶ C),
      (stageMap C).comp f.hom.hom = stageMap B) (B : Neighbourhood.{u, u} I) :
    (descOfCompatible I stageMap hcompat).comp (stage I B) = stageMap B := by
  rw [descOfCompatible_def, stage_def]
  exact SmallFilteredAlgebraColimit.descOfCompatible_comp_stage (IsNeighbourhood I).ι stageMap
    hcompat B

/-- Elementwise form of `descOfCompatible_comp_stage`. -/
@[simp]
theorem descOfCompatible_stage_apply (I : Ideal R) {S : Type*} [CommRing S] [Algebra R S]
    (stageMap : ∀ B : Neighbourhood.{u, u} I, B.obj →ₐ[R] S)
    (hcompat : ∀ {B C : Neighbourhood.{u, u} I} (f : B ⟶ C),
      (stageMap C).comp f.hom.hom = stageMap B) (B : Neighbourhood.{u, u} I) (b : B.obj) :
    descOfCompatible I stageMap hcompat (stage I B b) = stageMap B b :=
  DFunLike.congr_fun (descOfCompatible_comp_stage I stageMap hcompat B) b

/-- Every element of the henselization algebra comes from an étale neighbourhood. -/
theorem exists_stage_eq (I : Ideal R) (x : algebra I) :
    ∃ (B : Neighbourhood.{u, u} I) (b : B.obj), stage I B b = x := by
  simp only [stage_def]
  exact SmallFilteredAlgebraColimit.exists_stage_eq (IsNeighbourhood I).ι x

/-- Two maps from the henselization algebra are equal if they agree on every stage. -/
@[ext]
theorem hom_ext {I : Ideal R} {S : Type w} [Semiring S] [Algebra R S]
    {f g : algebra I →ₐ[R] S}
    (h : ∀ (B : Neighbourhood.{u, u} I), f.comp (stage I B) = g.comp (stage I B)) :
    f = g :=
  SmallFilteredAlgebraColimit.hom_ext (IsNeighbourhood I).ι h

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
