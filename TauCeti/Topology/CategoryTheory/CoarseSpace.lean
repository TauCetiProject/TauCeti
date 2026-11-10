/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ComposableArrows.Basic
public import TauCeti.Topology.CategoryTheory.Nerve

/-!
# The coarse projection of a topological groupoid's classifying space

For a native groupoid `C`, its coarse space is the quotient of its objects by isomorphism,
with the quotient topology. All vertices of a composable string have the same class. When
source is continuous on total arrows, these classes give a continuous augmentation of the
actual topological nerve and hence a map from its fat classifying space to the coarse space.
No arrows are removed, even when distinct isotropy arrows induce the same object map.

If units are also continuous, `TauCeti.fatClassifyingSpace.isQuotientMap_coarseMap` proves
that the coarse projection is a quotient map. In particular the coarse topology is detected
by this projection, not merely by the object quotient. Properness, étaleness and separation
are not needed for this construction. This does not assert that the projection is proper
or that its fibers are contractible.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2 and 4.
* G. Segal, *Classifying spaces and spectral sequences*, Section 2.

The carriers are Mathlib's `CategoryTheory.isIsomorphicSetoid` and the topological nerve
and fat realization constructed in `TauCeti.Topology.CategoryTheory.Nerve`.
-/

public noncomputable section

open CategoryTheory Opposite Topology

namespace TauCeti.fatClassifyingSpace

universe u

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The augmentation of the topological nerve by the isomorphism class of a vertex.
Its continuity uses only continuity of source on total arrows. -/
def coarseAugmentation :
    SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve C ⟶
      (Functor.const _).obj (TopCat.of (Quotient (isIsomorphicSetoid C))) where
  app _ := TopCat.ofHom ⟨fun F ↦ Quotient.mk _ (F.obj 0), by
    apply continuous_quot_mk.comp
    simpa only [Function.comp_def, ComposableArrows.totalArrow_left] using
      hs.comp (ComposableArrows.continuous_totalArrow 0 0 le_rfl)⟩
  naturality _ _ f := by
    ext F
    -- The nerve operator reindexes vertices; every vertex has the same isomorphism class.
    exact F.quotient_mk_obj
      ((SimplexCategory.toCat.map (SemiSimplexCategory.toSimplexCategory.map f.unop)).toFunctor.obj
        (0 : Fin (_ + 1)))

/-- The coarse augmentation reads the class of the first vertex. -/
@[simp↓]
theorem coarseAugmentation_app_apply (m : SemiSimplexCategoryᵒᵖ)
    (F : (SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve C).obj m) :
    (coarseAugmentation hs).app m F = Quotient.mk (isIsomorphicSetoid C) (F.obj 0) := (rfl)

/-- The coarse projection from the fat classifying space to the actual orbit quotient
of objects, with its quotient topology. -/
def coarseMap : fatClassifyingSpace C ⟶ TopCat.of (Quotient (isIsomorphicSetoid C)) :=
  fatRealization.augment (coarseAugmentation hs)

/-- The coarse projection is induced by the coarse augmentation of the topological nerve. -/
theorem coarseMap_eq_augment :
    coarseMap hs = fatRealization.augment (coarseAugmentation hs) := (rfl)

/-- A point of a simplex projects to the class of its first vertex. By
`ComposableArrows.quotient_mk_obj`, this is also the class of every other vertex. -/
-- Simplify before the functor-object types in the characteristic map are normalized.
@[simp↓]
theorem coarseMap_ι (m : SemiSimplexCategory)
    (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj m).len)
    (t : SemiSimplexCategory.toTop.obj m) :
    coarseMap hs (fatRealization.ι _ m (F, t)) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (fatRealization.augment_ι (coarseAugmentation hs) m F t).trans
    (coarseAugmentation_app_apply hs (op m) F)

/-- Every orbit occurs as the projection of a vertex in the fat classifying space. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap hs) := by
  refine Quotient.ind fun x ↦ ?_
  obtain ⟨t⟩ : Nonempty (SimplexCategory.toTop.{u}.obj
    (SemiSimplexCategory.toSimplexCategory.obj (SemiSimplexCategory.mk 0))) := inferInstance
  exact ⟨fatRealization.ι _ (SemiSimplexCategory.mk 0) (ComposableArrows.mk₀ x, t),
    coarseMap_ι hs _ _ _⟩

/-- With continuous units, the coarse projection is a quotient map: the topology on the
orbit space is also the final topology for the projection from the fat classifying space. -/
theorem isQuotientMap_coarseMap
    (hu : Continuous (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) :
    IsQuotientMap (coarseMap hs) := by
  have h₀ : Continuous (ComposableArrows.mk₀ : C → ComposableArrows C 0) := by
    apply ComposableArrows.continuous_iff.mpr
    intro i j hij
    -- A zero-string has only one vertex and one arrow, namely its unit.
    simpa [ComposableArrows.totalArrow_def, ComposableArrows.mk₀] using hu
  apply fatRealization.isQuotientMap_augment (coarseAugmentation hs) (SemiSimplexCategory.mk 0)
  have heq : ((coarseAugmentation hs).app (op (SemiSimplexCategory.mk 0))) ∘
      ComposableArrows.mk₀ = Quotient.mk (isIsomorphicSetoid C) :=
    funext fun x ↦ coarseAugmentation_app_apply hs _ _
  exact IsQuotientMap.of_comp h₀ ((coarseAugmentation hs).app _).hom.continuous
    (heq.symm ▸ isQuotientMap_quot_mk)

end TauCeti.fatClassifyingSpace
