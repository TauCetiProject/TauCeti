/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Pro.Basic

/-!
# Reindexing presented pro-objects

Let `F : I ⥤ C` be a small cofiltered diagram and `G : K ⥤ I` a functor from another small
cofiltered category. The stage projections `π F (G.obj k)` of `Pro.mk F` form a cone over
`G ⋙ F`, so they induce a comparison map `Pro.reindex G F : Pro.mk F ⟶ Pro.mk (G ⋙ F)`
whose `k`-th stage projection is `π F (G.obj k)`. It is natural in the diagram `F`, and
compatible with identities and composites of index functors.

When `G` is initial (the inverse-system form of cofinality), restricting the cone along `G`
does not change its limit property, so `Pro.reindex G F` is an isomorphism. In particular a
pro-object may be presented by any initial subdiagram of a presentation. Combined with
`TauCeti.IsCofiltered.exists_cofinite_directed`, every presented pro-object is isomorphic,
through `Pro.reindex`, to one indexed by the opposite of a cofinite directed partial order.
The inverse comparison is computed on stages by `Pro.inv_reindex_π` and
`Pro.inv_reindex_π_eq_π_comp_const_map`.

## Main declarations

* `TauCeti.Pro.reindex`: the comparison map along a functor of index categories.
* `TauCeti.Pro.reindex_π`: its stage projections.
* `TauCeti.Pro.reindexNatTrans`: the comparison as a natural transformation of functors on
  diagrams.
* `TauCeti.Pro.isIso_reindex`: the comparison along an initial functor is an isomorphism.
* `TauCeti.Pro.inv_reindex_π_eq_π_comp_const_map`: the stage projections of its inverse.

## References

* M. Artin and B. Mazur, *Étale homotopy*, Lecture Notes in Math. 100, Appendix, §§1–2.
* M. Kashiwara and P. Schapira, *Categories and Sheaves*, Proposition 6.1.8, by duality.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

namespace Pro

universe v u

variable {C : Type u} [Category.{v} C]
variable {I K L : Type v} [SmallCategory I] [IsCofiltered I] [SmallCategory K] [IsCofiltered K]
  [SmallCategory L] [IsCofiltered L]

/-- The comparison map from the pro-object presented by `F` to the one presented by its
restriction `G ⋙ F` along a functor of index categories. Its stage at `k` is the projection
of `Pro.mk F` to the stage `G.obj k`. -/
def reindex (G : K ⥤ I) (F : I ⥤ C) : mk F ⟶ mk (G ⋙ F) :=
  lift (F := G ⋙ F) ((mkCone F).whisker G)

/-- The stage projections of the reindexing comparison are the projections of the original
presentation. -/
@[reassoc (attr := simp)]
theorem reindex_π (G : K ⥤ I) (F : I ⥤ C) (k : K) :
    reindex G F ≫ π (G ⋙ F) k = π F (G.obj k) :=
  lift_π (F := G ⋙ F) _ k

/-- The universal map into `mk F`, followed by reindexing, is the universal map of the
whiskered cone. -/
@[reassoc (attr := simp)]
theorem lift_reindex (G : K ⥤ I) {F : I ⥤ C} (c : Cone (F ⋙ const)) :
    lift c ≫ reindex G F = lift (F := G ⋙ F) (c.whisker G) :=
  hom_ext fun k ↦ by simp

/-- Reindexing along the identity functor is the identity. -/
@[simp]
theorem reindex_id (F : I ⥤ C) : reindex (𝟭 I) F = 𝟙 (mk F) :=
  -- The diagrams `𝟭 I ⋙ F` and `F` are definitionally equal, as in `Functor.id_comp`.
  hom_ext fun i ↦ (reindex_π (𝟭 I) F i).trans (Category.id_comp _).symm

/-- Reindexing along a composite is the composite of the reindexings. -/
theorem reindex_comp (H : L ⥤ K) (G : K ⥤ I) (F : I ⥤ C) :
    reindex (H ⋙ G) F = reindex G F ≫ reindex H (G ⋙ F) :=
  hom_ext fun l ↦ by
    rw [reindex_π, Category.assoc]
    -- The diagrams `(H ⋙ G) ⋙ F` and `H ⋙ G ⋙ F` are definitionally equal, by
    -- `Functor.assoc`, so `exact` accepts the projection of either presentation.
    exact ((congrArg (reindex G F ≫ ·) (reindex_π H (G ⋙ F) l)).trans
      (reindex_π G F (H.obj l))).symm

/-- The reindexing comparison is natural in the diagram. -/
@[reassoc]
theorem lim_map_reindex (G : K ⥤ I) {F F' : I ⥤ C} (α : F ⟶ F') :
    lim.map α ≫ reindex G F' = reindex G F ≫ lim.map (Functor.whiskerLeft G α) :=
  hom_ext fun k ↦ by simp

/-- The reindexing comparisons along `G`, as a natural transformation from the presentation
functor to its precomposition with restriction along `G`. -/
def reindexNatTrans (G : K ⥤ I) :
    (lim : (I ⥤ C) ⥤ Pro C) ⟶ (Functor.whiskeringLeft K I C).obj G ⋙ lim where
  app F := reindex G F
  naturality _ _ α := lim_map_reindex G α

/-- The components of `reindexNatTrans G` are the reindexing comparisons. -/
@[simp]
theorem reindexNatTrans_app (G : K ⥤ I) (F : I ⥤ C) :
    (reindexNatTrans G).app F = reindex G F := (rfl)

/-- **Cofinal invariance of pro-objects.** Restricting a presentation along an initial functor
of index categories gives an isomorphic pro-object: the reindexing comparison is an
isomorphism. -/
instance isIso_reindex (G : K ⥤ I) [G.Initial] (F : I ⥤ C) : IsIso (reindex G F) := by
  -- `reindex G F` is the lift of the restricted presentation cone of `F`, which is a limit
  -- cone since `G` is initial, into the presentation cone of `G ⋙ F`.
  rw [(mkConeIsLimit (G ⋙ F)).uniq ((mkCone F).whisker G) _ (reindex_π G F)]
  exact (IsLimit.nonempty_isLimit_iff_isIso_lift _).mp
    ⟨(Functor.Initial.isLimitWhiskerEquiv G (mkCone F)).symm (mkConeIsLimit F)⟩

/-- Along an initial functor, the reindexing comparisons form a natural isomorphism. -/
instance isIso_reindexNatTrans (G : K ⥤ I) [G.Initial] :
    IsIso (reindexNatTrans (C := C) G) :=
  have (F : I ⥤ C) : IsIso ((reindexNatTrans G).app F) := isIso_reindex G F
  NatIso.isIso_of_isIso_app _

/-- The inverse of the reindexing comparison along an initial functor projects each stage
`G.obj k` to the stage `k` of the restricted presentation. -/
@[reassoc (attr := simp)]
theorem inv_reindex_π (G : K ⥤ I) [G.Initial] (F : I ⥤ C) (k : K) :
    inv (reindex G F) ≫ π F (G.obj k) = π (G ⋙ F) k := by
  rw [IsIso.inv_comp_eq, reindex_π]

/-- The inverse of the reindexing comparison along an initial functor projects an arbitrary
stage `i` through any stage `k` of the restricted presentation with a map `G.obj k ⟶ i`; since
`G` is initial, such a map exists for every `i`. -/
theorem inv_reindex_π_eq_π_comp_const_map (G : K ⥤ I) [G.Initial] (F : I ⥤ C) {i : I} {k : K}
    (f : G.obj k ⟶ i) :
    inv (reindex G F) ≫ π F i = π (G ⋙ F) k ≫ const.map (F.map f) := by
  rw [← π_naturality F f, inv_reindex_π_assoc]

end Pro

end TauCeti
