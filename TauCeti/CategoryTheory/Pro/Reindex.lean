/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Pro.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Reindexing presentations of pro-objects

A functor `G : J ⥤ I` of small cofiltered categories restricts a cofiltered diagram
`F : I ⥤ C` to `G ⋙ F`. Dually to `CategoryTheory.Limits.limit.pre`, it induces the
restriction morphism `Pro.pre F G : Pro.mk F ⟶ Pro.mk (G ⋙ F)`, whose projection to a
stage `j` is the projection of `Pro.mk F` to the stage `G.obj j`. Restriction is natural in
the diagram and compatible with composition of index functors.

When `G` is initial, the restriction morphism is an isomorphism, naturally in `F`
(`Pro.isIso_pre`, `Pro.isIso_preNatTrans`). So a pro-object does not change when its
presentation is replaced by a cofinal subdiagram, or more generally by its restriction along an
initial functor; the inverse is computed on stages by `Pro.inv_pre_π` and `Pro.inv_pre_π_eq`.
This lets a presentation be replaced by a cofinal one with more convenient indexing.

## References

* M. Kashiwara and P. Schapira, *Categories and Sheaves*, Proposition 2.5.2 and Chapter 6,
  by duality.
* M. Artin and B. Mazur, *Etale homotopy*, Lecture Notes in Mathematics 100, Appendix.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe v u

namespace Pro

variable {C : Type u} [Category.{v} C]
variable {I J K : Type v} [SmallCategory I] [IsCofiltered I] [SmallCategory J] [IsCofiltered J]
  [SmallCategory K] [IsCofiltered K]

/-- The restriction morphism from the pro-object presented by `F` to the one presented by its
restriction `G ⋙ F` along a functor of indices. -/
def pre (F : I ⥤ C) (G : J ⥤ I) : mk F ⟶ mk (G ⋙ F) :=
  lift (F := G ⋙ F) ((mkCone F).whisker G)

/-- The restriction morphism projects each stage `j` to the stage `G.obj j` of `F`. -/
@[reassoc (attr := simp)]
theorem pre_π (F : I ⥤ C) (G : J ⥤ I) (j : J) :
    pre F G ≫ π (G ⋙ F) j = π F (G.obj j) :=
  lift_π (F := G ⋙ F) _ j

/-- The universal map into `mk F`, followed by restriction, is the universal map of the
whiskered cone. -/
@[reassoc (attr := simp)]
theorem lift_pre {F : I ⥤ C} (G : J ⥤ I) (c : Cone (F ⋙ const)) :
    lift c ≫ pre F G = lift (F := G ⋙ F) (c.whisker G) := by
  ext j
  simp

/-- Restriction is natural in the diagram. -/
@[reassoc (attr := simp)]
theorem lim_map_pre {F F' : I ⥤ C} (α : F ⟶ F') (G : J ⥤ I) :
    lim.map α ≫ pre F' G = pre F G ≫ lim.map (Functor.whiskerLeft G α) := by
  ext j
  simp

/-- Restricting along a composite of index functors is restricting along each in turn. -/
@[reassoc]
theorem pre_pre (F : I ⥤ C) (G : J ⥤ I) (H : K ⥤ J) :
    pre F G ≫ pre (G ⋙ F) H = pre F (H ⋙ G) := by
  refine hom_ext fun k ↦ ?_
  -- The targets `mk (H ⋙ G ⋙ F)` and `mk ((H ⋙ G) ⋙ F)` agree definitionally, since
  -- composition of functors is definitionally associative; `pre_π` applies to both sides.
  rw [Category.assoc, pre_π, pre_π]
  exact (pre_π F (H ⋙ G) k).symm

/-- Restricting along the identity functor is the left unitor of the diagram. -/
theorem pre_id (F : I ⥤ C) : pre F (𝟭 I) = lim.map (Functor.leftUnitor F).inv := by
  ext i
  simp

/-- Restriction along `G`, as a natural transformation of functors from diagrams to
pro-objects. -/
def preNatTrans (G : J ⥤ I) :
    (lim : (I ⥤ C) ⥤ Pro C) ⟶ (Functor.whiskeringLeft J I C).obj G ⋙ lim where
  app F := pre F G
  naturality _ _ α := lim_map_pre α G

/-- The components of `preNatTrans G` are the restriction morphisms. -/
@[simp]
theorem preNatTrans_app (G : J ⥤ I) (F : I ⥤ C) : (preNatTrans G).app F = pre F G := (rfl)

/-- The cone over a restricted diagram obtained by whiskering a presentation cone along an
initial functor is a limit cone. -/
def isLimitMkConeWhisker (F : I ⥤ C) (G : J ⥤ I) [G.Initial] :
    IsLimit ((mkCone F).whisker G) :=
  (Functor.Initial.isLimitWhiskerEquiv G (mkCone F)).symm (mkConeIsLimit F)

/-- Restriction along an initial functor is an isomorphism of pro-objects. -/
instance isIso_pre (F : I ⥤ C) (G : J ⥤ I) [G.Initial] : IsIso (pre F G) := by
  -- `pre F G` underlies the comparison of the two limit cones over `G ⋙ F ⋙ const`.
  let e := IsLimit.uniqueUpToIso (isLimitMkConeWhisker F G) (mkConeIsLimit (G ⋙ F))
  have : pre F G = e.hom.hom := hom_ext fun j ↦ by
    rw [pre_π]
    exact (e.hom.w j).symm
  rw [this]
  exact (inferInstance : IsIso e.hom.hom)

/-- Restriction along an initial functor is a natural isomorphism. -/
instance isIso_preNatTrans (G : J ⥤ I) [G.Initial] : IsIso (preNatTrans (C := C) G) :=
  have (F : I ⥤ C) : IsIso ((preNatTrans G).app F) := by
    rw [preNatTrans_app]
    infer_instance
  NatIso.isIso_of_isIso_app _

/-- The inverse of restriction along an initial functor projects each stage `G.obj j` to the
stage `j` of the restricted diagram. -/
@[reassoc (attr := simp)]
theorem inv_pre_π (F : I ⥤ C) (G : J ⥤ I) [G.Initial] (j : J) :
    inv (pre F G) ≫ π F (G.obj j) = π (G ⋙ F) j := by
  rw [IsIso.inv_comp_eq, pre_π]

/-- The inverse of restriction along an initial functor projects an arbitrary stage `i` through
any stage `j` of the restricted diagram with a map `G.obj j ⟶ i`; since `G` is initial, such a
map exists for every `i`. -/
theorem inv_pre_π_eq (F : I ⥤ C) (G : J ⥤ I) [G.Initial] {i : I} {j : J} (f : G.obj j ⟶ i) :
    inv (pre F G) ≫ π F i = π (G ⋙ F) j ≫ const.map (F.map f) := by
  rw [← π_naturality F f, inv_pre_π_assoc]

end Pro
end TauCeti
