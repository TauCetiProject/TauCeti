/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.AllDegrees

/-!
# Continuous Shapiro on algebraic coinduction

For an open subgroup of a profinite group, algebraic coinduction of a smooth discrete
representation consists of locally constant equivariant functions. Equip it with its discrete
topology using `TauCeti.algebraicCoindAsSmooth`. Restriction followed by its algebraic evaluation
counit defines `TauCeti.ContinuousCohomology.algebraicShapiroMap` independently of the
topological coinduction comparison. It is an isomorphism in every degree, and
`TauCeti.topologicalCoindIsoAlgebraic_shapiro` proves that the comparison carries continuous
Shapiro to this map. These are continuous cohomology groups, with the original topology on the
group.

The evaluation counit agrees over commutative rings with Mathlib's `Rep.resCoindAdjunction`.
The construction uses Mathlib's compatible-pair functoriality of continuous cohomology and
Tau Ceti's canonical Shapiro isomorphism; no second cohomology or coinduction model is needed.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, second edition, Thm. 6.10.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (1.6.4), with the footnote on p. 61 that uses `Ind` for coinduction.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

section Comparison

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {R : Type v} [Ring R] [TopologicalSpace R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : OpenSubgroup G) (A : SmoothDiscreteTopRep.{v, u, u} R U.toSubgroup)

namespace ContinuousCohomology

/-- Restriction followed by evaluation at `1` on algebraically coinduced coefficients,
equipped with their smooth discrete topology. -/
noncomputable def algebraicShapiroMap (n : ℕ) :
    continuousCohomology n (algebraicCoindAsSmooth R G U A).obj ⟶
      continuousCohomology n A.obj :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
    (TopRep.ofHom (algebraicCoindCounit R G U A)) n

/-- The defining compatible pair of the algebraic Shapiro map is subgroup inclusion together
with the algebraic evaluation counit. -/
theorem algebraicShapiroMap_def (n : ℕ) :
    algebraicShapiroMap U A n =
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
        (TopRep.ofHom (algebraicCoindCounit R G U A)) n := (rfl)

/-- Coefficient transport from topological to algebraic coinduction intertwines the canonical
continuous Shapiro maps in every degree. -/
@[reassoc]
theorem coeffMap_topologicalCoindIsoAlgebraic_comp_algebraicShapiroMap (n : ℕ) :
    coeffMap (topologicalCoindIsoAlgebraic R G U A).hom.hom n ≫
        algebraicShapiroMap U A n = shapiroMapTopRep U.toSubgroup A n := by
  have h := map_comp_coeffMap (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
    (TopRep.ofHom (coindCounit R G U.toSubgroup A))
    (TopRep.ofHom (algebraicCoindCounit R G U A))
    (topologicalCoindIsoAlgebraic R G U A).hom.hom (𝟙 A.obj)
    ((topologicalCoindIsoAlgebraic_hom_comp_counit U A).trans (Category.comp_id _).symm) n
  simpa only [coeffMap_id, Category.comp_id, algebraicShapiroMap_def,
    shapiroMapTopRep_def] using h.symm

/-- The algebraic evaluation Shapiro map is an isomorphism for an open subgroup of a
profinite group. -/
theorem isIso_algebraicShapiroMap [TotallyDisconnectedSpace G] (n : ℕ) :
    IsIso (algebraicShapiroMap U A n) := by
  -- Coefficient transport is the map of an isomorphism under the inclusion and cohomology
  -- functors; their object fields are identified with the canonical cohomology carriers.
  let e := (smoothDiscreteι R G).mapIso (topologicalCoindIsoAlgebraic R G U A)
  let eH : continuousCohomology n (coindTopRep R G U.toSubgroup A).obj ≅
      continuousCohomology n (algebraicCoindAsSmooth R G U A).obj :=
    (continuousCohomologyFunctor (R := R) G n).mapIso e
  have : IsIso (coeffMap (topologicalCoindIsoAlgebraic R G U A).hom.hom n) :=
    inferInstanceAs (IsIso eH.hom)
  have : IsIso (coeffMap (topologicalCoindIsoAlgebraic R G U A).hom.hom n ≫
      algebraicShapiroMap U A n) :=
    (coeffMap_topologicalCoindIsoAlgebraic_comp_algebraicShapiroMap U A n).symm ▸
      isIso_shapiroMapTopRep U.toSubgroup U.isClosed A n
  exact IsIso.of_isIso_comp_left (coeffMap (topologicalCoindIsoAlgebraic R G U A).hom.hom n) _

/-- Continuous Shapiro's isomorphism on algebraic coinduction, with its smooth discrete
topology; its forward map is independently defined by restriction and algebraic evaluation. -/
noncomputable def algebraicShapiroIso [TotallyDisconnectedSpace G] (n : ℕ) :
    continuousCohomology n (algebraicCoindAsSmooth R G U A).obj ≅
      continuousCohomology n A.obj :=
  have := isIso_algebraicShapiroMap U A n
  asIso (algebraicShapiroMap U A n)

/-- The forward algebraic Shapiro isomorphism is the restriction/evaluation map. -/
@[simp]
theorem algebraicShapiroIso_hom [TotallyDisconnectedSpace G] (n : ℕ) :
    (algebraicShapiroIso U A n).hom = algebraicShapiroMap U A n := by
  rw [algebraicShapiroIso, asIso_hom]

end ContinuousCohomology

/-- The topological/algebraic coinduction comparison carries canonical continuous Shapiro's
isomorphism to the isomorphism defined by algebraic evaluation, in every degree. -/
@[reassoc]
theorem topologicalCoindIsoAlgebraic_shapiro [TotallyDisconnectedSpace G] (n : ℕ) :
    (ContinuousCohomology.continuousCohomologyFunctor (R := R) G n).map
        ((smoothDiscreteι R G).map (topologicalCoindIsoAlgebraic R G U A).hom) ≫
      (ContinuousCohomology.algebraicShapiroIso U A n).hom =
        (ContinuousCohomology.shapiroIsoTopRep U.toSubgroup U.isClosed A n).hom := by
  -- The inclusion forgets only the smoothness property, and the cohomology functor acts by
  -- `coeffMap`; expose those functor fields without unfolding either Shapiro construction.
  change ContinuousCohomology.coeffMap (topologicalCoindIsoAlgebraic R G U A).hom.hom n ≫
    (ContinuousCohomology.algebraicShapiroIso U A n).hom =
      (ContinuousCohomology.shapiroIsoTopRep U.toSubgroup U.isClosed A n).hom
  rw [ContinuousCohomology.algebraicShapiroIso_hom, ContinuousCohomology.shapiroIsoTopRep_hom]
  exact ContinuousCohomology.coeffMap_topologicalCoindIsoAlgebraic_comp_algebraicShapiroMap U A n

end Comparison

end TauCeti
