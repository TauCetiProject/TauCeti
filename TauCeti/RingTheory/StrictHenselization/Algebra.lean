/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Filtered
public import TauCeti.RingTheory.StrictHenselization.SmallModel
public import TauCeti.Algebra.Category.CommAlgCat.SmallFilteredColimit

/-!
# The colimit algebra of pointed étale neighbourhoods

Pointed étale neighbourhoods form a filtered, essentially small category. Their algebra-valued
diagram has a colimit with canonical maps from each stage, identified by
`algebraIsoColimitDiagram` with the colimit of its small-model restriction `diagram`. The pointings
also induce a map from the colimit to the chosen target algebra.

## References

* Stacks Project, Tags 04GP, 04GQ, and 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`
  (Apache 2.0): `functor`, `colimitObj`, `toColimit`, `colimitPoint`, and
  `colimitPoint_comp_toColimit` in `StrictHenselizationConstruction.lean`; and
  `exists_stage_of_colimit_element` and `toColimit_naturality` in
  `StrictHenselizationStages.lean`.
-/

public section

open CategoryTheory Limits

universe u v w

namespace TauCeti.StrictHenselization

section Points

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- Forget the point but retain the étale algebra. -/
noncomputable abbrev algebraFunctor :
    Neighbourhood R Ω ⥤ CommAlgCat.{max u v} R :=
  (IsPointedNeighbourhood R Ω).ι ⋙ Over.forget _

/-- The cocone on pointed étale algebras with apex `ULift Ω` whose leg at each neighbourhood is
its point. -/
@[expose] noncomputable def pointCocone : Cocone (algebraFunctor R Ω) :=
  (Over.forgetCocone (CommAlgCat.of R (ULift.{u} Ω))).whisker (IsPointedNeighbourhood R Ω).ι

/-- The apex of `pointCocone` is `Ω` lifted to the universe of the base and target. -/
@[simp]
theorem pointCocone_pt : (pointCocone R Ω).pt = CommAlgCat.of R (ULift.{u} Ω) :=
  (rfl)

/-- The leg of `pointCocone` at a neighbourhood is its point. -/
@[simp]
theorem pointCocone_ι_app (B : Neighbourhood R Ω) : (pointCocone R Ω).ι.app B = B.obj.hom :=
  (rfl)

end Points

variable (R Ω : Type u) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- The restriction of the pointed étale algebras to a small model of the neighbourhood category.
Its colimit is identified with `algebra R Ω` by `algebraIsoColimitDiagram`. -/
noncomputable abbrev diagram :
    SmallModel (Neighbourhood R Ω) ⥤ CommAlgCat.{u} R :=
  SmallFilteredAlgebraColimit.diagram (algebraFunctor R Ω)

/-- The colimit of pointed étale algebras. For a local base ring and a separable closure of its
residue field as target, this is the strict henselization. -/
@[stacks 04GQ "strict henselization, colimit form"]
noncomputable def algebra : CommAlgCat.{u} R :=
  SmallFilteredAlgebraColimit.algebra (algebraFunctor R Ω)

/-- The canonical map from a pointed étale algebra to the colimit. -/
noncomputable def stage (B : Neighbourhood R Ω) : B.obj.left →ₐ[R] algebra R Ω :=
  SmallFilteredAlgebraColimit.stage (algebraFunctor R Ω) B

/-- `stage` unfolds to `SmallFilteredAlgebraColimit.stage` for the forgotten neighbourhood. -/
private theorem stage_def (B : Neighbourhood R Ω) :
    stage R Ω B = SmallFilteredAlgebraColimit.stage (algebraFunctor R Ω) B :=
  (rfl)

/-- The colimit over all pointed neighbourhoods is the colimit over the small model. -/
noncomputable def algebraIsoColimitDiagram : algebra R Ω ≅ colimit (diagram R Ω) :=
  SmallFilteredAlgebraColimit.algebraIsoColimitDiagram (algebraFunctor R Ω)

/-- The comparison with the small-model colimit is compatible with the stage maps. -/
@[simp]
theorem algebraIsoColimitDiagram_inv_comp_ι (smallObject : SmallModel (Neighbourhood R Ω)) :
    (algebraIsoColimitDiagram R Ω).inv.hom.comp (colimit.ι (diagram R Ω) smallObject).hom =
      stage R Ω ((equivSmallModel (Neighbourhood R Ω)).inverse.obj smallObject) := by
  rw [stage_def]
  exact SmallFilteredAlgebraColimit.algebraIsoColimitDiagram_inv_comp_ι
    (algebraFunctor R Ω) smallObject

/-- The stage maps commute with morphisms of pointed étale algebras. -/
@[simp]
theorem stage_naturality {B C : Neighbourhood R Ω} (f : B ⟶ C) :
    (stage R Ω C).comp f.hom.left.hom = stage R Ω B := by
  rw [stage_def, stage_def]
  exact SmallFilteredAlgebraColimit.stage_naturality (algebraFunctor R Ω) f

/-- Naturality of the stage maps on elements. -/
@[simp]
theorem stage_hom_apply {B C : Neighbourhood R Ω} (f : B ⟶ C) (b : B.obj.left) :
    stage R Ω C (f.hom.left.hom b) = stage R Ω B b :=
  SmallFilteredAlgebraColimit.stage_map_apply (algebraFunctor R Ω) f b

/-- A cocone on pointed étale algebras induces a map out of their colimit. -/
noncomputable def desc (s : Cocone (algebraFunctor R Ω)) :
    algebra R Ω →ₐ[R] s.pt :=
  SmallFilteredAlgebraColimit.desc (algebraFunctor R Ω) s

/-- `desc` unfolds to `SmallFilteredAlgebraColimit.desc`. -/
private theorem desc_def (s : Cocone (algebraFunctor R Ω)) :
    desc R Ω s = SmallFilteredAlgebraColimit.desc (algebraFunctor R Ω) s :=
  (rfl)

/-- The map induced by a cocone agrees with it at each stage. -/
@[simp]
theorem desc_comp_stage (s : Cocone (algebraFunctor R Ω)) (B : Neighbourhood R Ω) :
    (desc R Ω s).comp (stage R Ω B) = (s.ι.app B).hom := by
  rw [desc_def, stage_def]
  exact SmallFilteredAlgebraColimit.desc_comp_stage (algebraFunctor R Ω) s B

/-- The map induced by a cocone, evaluated at a stage element. -/
@[simp]
theorem desc_stage_apply (s : Cocone (algebraFunctor R Ω)) (B : Neighbourhood R Ω)
    (b : B.obj.left) : desc R Ω s (stage R Ω B b) = (s.ι.app B).hom b :=
  SmallFilteredAlgebraColimit.desc_stage_apply (algebraFunctor R Ω) s B b

/-- Every element of the colimit comes from a pointed étale neighbourhood. -/
theorem exists_stage_eq (x : algebra R Ω) :
    ∃ (B : Neighbourhood R Ω) (b : B.obj.left), stage R Ω B b = x := by
  simp only [stage_def]
  exact SmallFilteredAlgebraColimit.exists_stage_eq (algebraFunctor R Ω) x

/-- Finitely many elements of the colimit come from a common pointed étale neighbourhood. -/
theorem exists_stage_family {ι : Type*} [Finite ι] (x : ι → algebra R Ω) :
    ∃ (B : Neighbourhood R Ω) (b : ι → B.obj.left), ∀ i, stage R Ω B (b i) = x i :=
  SmallFilteredAlgebraColimit.exists_stage_family (algebraFunctor R Ω) x

/-- Algebra maps out of the colimit agree if they agree on every stage. -/
@[ext]
theorem hom_ext {S : Type w} [Semiring S] [Algebra R S]
    {f g : algebra R Ω →ₐ[R] S}
    (h : ∀ (B : Neighbourhood R Ω), f.comp (stage R Ω B) = g.comp (stage R Ω B)) :
    f = g :=
  SmallFilteredAlgebraColimit.hom_ext (algebraFunctor R Ω) h

/-- The pointings induce a map from the colimit to the chosen algebra. -/
noncomputable def toTarget : algebra R Ω →ₐ[R] Ω :=
  ULift.algEquiv.toAlgHom.comp (desc R Ω (pointCocone R Ω))

/-- `toTarget` is the descent of `pointCocone`, followed by the identification of `ULift Ω`
with `Ω`. -/
theorem toTarget_apply (x : algebra R Ω) :
    toTarget R Ω x = ULift.algEquiv (R := R) (A := Ω) (desc R Ω (pointCocone R Ω) x) :=
  (rfl)

/-- Composing a stage map with `toTarget` recovers the point `B.obj.hom` of that neighbourhood
(up to `ULift`). -/
@[simp]
theorem toTarget_comp_stage (B : Neighbourhood R Ω) :
    (toTarget R Ω).comp (stage R Ω B) =
      ULift.algEquiv.toAlgHom.comp B.obj.hom.hom := by
  ext element
  rw [AlgHom.comp_apply, toTarget_apply, desc_stage_apply, pointCocone_ι_app]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  -- The carrier of `CommAlgCat.of R (ULift Ω)` needs unification to see `ULift Ω`.
  exact ULift.algEquiv_apply _

/-- Elementwise form of `toTarget_comp_stage`. -/
@[simp]
theorem toTarget_stage_apply (B : Neighbourhood R Ω) (b : B.obj.left) :
    toTarget R Ω (stage R Ω B b) = (B.obj.hom.hom b).down := by
  rw [toTarget_apply, desc_stage_apply, pointCocone_ι_app]
  -- The carrier of `CommAlgCat.of R (ULift Ω)` needs unification to see `ULift Ω`.
  exact ULift.algEquiv_apply _

end TauCeti.StrictHenselization
