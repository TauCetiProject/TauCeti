/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Filtered
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Pro-objects and their cofiltered presentations

The category `TauCeti.Pro C` is the opposite of `Ind Cᵒᵖ`. The fully faithful
constant-object functor embeds `C` in it. A small cofiltered diagram `F` in `C`
determines a pro-object `Pro.mk F`, with canonical projections to its stages;
these projections exhibit it as the limit of the corresponding constant objects.

This construction uses Mathlib's `Ind.lim` and its filtered colimits, rather than
introducing a second category of formal diagrams. In particular, presentations
carry no extra choices of morphisms. The limit property permits maps into a
pro-object to be constructed, and compared, on all its stages.

## References

* M. Kashiwara and P. Schapira, *Categories and Sheaves*, Chapter 6, by duality.
* P. Scholze, *Étale cohomology of diamonds*, §7, Proposition 7.10.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace TauCeti

universe v u

/-- The pro-category of `C`, realized as the opposite of the ind-category of `Cᵒᵖ`. -/
abbrev Pro (C : Type u) [Category.{v} C] := (Ind Cᵒᵖ)ᵒᵖ

namespace Pro

variable {C : Type u} [Category.{v} C]

/-- The fully faithful embedding as constant pro-objects. -/
def const : C ⥤ Pro C := Ind.yoneda.rightOp

instance : const (C := C) |>.Full := inferInstanceAs Ind.yoneda.rightOp.Full
instance : const (C := C) |>.Faithful := inferInstanceAs Ind.yoneda.rightOp.Faithful

variable {I : Type v} [SmallCategory I] [IsCofiltered I]

attribute [local instance] IsCofiltered.isConnected

/-- The pro-object presented by a small cofiltered diagram. -/
def mk (F : I ⥤ C) : Pro C := op ((Ind.lim Iᵒᵖ).obj F.op)

/-- The canonical projection from a presented pro-object to one of its stages. -/
def π (F : I ⥤ C) (i : I) : mk F ⟶ const.obj (F.obj i) :=
  (colimit.ι (F.op ⋙ Ind.yoneda) (op i)).op

/-- Stage projections commute with transition maps. -/
@[reassoc (attr := simp)]
theorem π_naturality (F : I ⥤ C) {i j : I} (a : i ⟶ j) :
    π F i ≫ const.map (F.map a) = π F j :=
  congrArg Quiver.Hom.op (colimit.w (F.op ⋙ Ind.yoneda) a.op)

/-- The stage projections form a cone. Its vertex is exposed so that the cone's
legs and universal maps have source and target `mk F` without transports. -/
@[expose]
def mkCone (F : I ⥤ C) : Cone (F ⋙ const) where
  pt := mk F
  π :=
    { app := π F
      naturality := fun _ _ _ ↦ by simp }

/-- A cofiltered presentation realizes its pro-object as a limit of constant objects. -/
def mkConeIsLimit (F : I ⥤ C) : IsLimit (mkCone F) :=
  isLimitConeRightOpOfCocone (F.op ⋙ Ind.yoneda) (colimit.isColimit _)

/-- The vertex of the presentation cone is the presented pro-object. -/
@[simp]
theorem mkCone_pt (F : I ⥤ C) : (mkCone F).pt = mk F := (rfl)

/-- The legs of the presentation cone are the canonical stage projections. -/
@[simp]
theorem mkCone_π_app (F : I ⥤ C) (i : I) : (mkCone F).π.app i = π F i := (rfl)

/-- Morphisms into a presented pro-object are determined by their stage projections. -/
@[ext]
theorem hom_ext {F : I ⥤ C} {X : Pro C} {f g : X ⟶ mk F}
    (h : ∀ i, f ≫ π F i = g ≫ π F i) : f = g :=
  (mkConeIsLimit F).hom_ext h

/-- A natural transformation of cofiltered diagrams induces a morphism of pro-objects. -/
def mkMap {F G : I ⥤ C} (α : F ⟶ G) : mk F ⟶ mk G :=
  (mkConeIsLimit G).map (mkCone F) (Functor.whiskerRight α const)

/-- The induced pro-morphism has the specified map at each stage. -/
@[reassoc (attr := simp)]
theorem mkMap_π {F G : I ⥤ C} (α : F ⟶ G) (i : I) :
    mkMap α ≫ π G i = π F i ≫ const.map (α.app i) :=
  (mkConeIsLimit G).map_π (mkCone F) (Functor.whiskerRight α const) i

@[simp]
theorem mkMap_id (F : I ⥤ C) : mkMap (𝟙 F) = 𝟙 (mk F) := by
  apply hom_ext
  simp

@[simp]
theorem mkMap_comp {F G H : I ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
    mkMap (α ≫ β) = mkMap α ≫ mkMap β := by
  apply hom_ext
  simp

/-- A constant cofiltered presentation gives the corresponding constant pro-object. -/
def mkConstIso (X : C) : mk ((Functor.const I).obj X) ≅ const.obj X :=
  (mkConeIsLimit _).conePointUniqueUpToIso
    ((IsLimit.postcomposeInvEquiv (Functor.constComp I X const)
      (constCone I (const.obj X))).symm (isLimitConstCone I (const.obj X)))

/-- Every projection of a constant presentation is its comparison isomorphism. -/
@[simp]
theorem π_const (X : C) (i : I) :
    π ((Functor.const I).obj X) i = (mkConstIso (I := I) X).hom := by
  -- Reduce the dual-colimit vertex to compare the two presentation cones.
  simpa [mkConstIso, mk, mkCone, π, Ind.lim] using
    ((mkConeIsLimit ((Functor.const I).obj X)).conePointUniqueUpToIso_hom_comp
      ((IsLimit.postcomposeInvEquiv (Functor.constComp I X const)
        (constCone I (const.obj X))).symm (isLimitConstCone I (const.obj X))) i).symm

/-- The constant-presentation comparison is natural in the constant object. -/
@[reassoc (attr := simp)]
theorem mkMap_mkConstIso_hom {X Y : C} (f : X ⟶ Y) :
    mkMap ((Functor.const I).map f) ≫ (mkConstIso Y).hom =
      (mkConstIso X).hom ≫ const.map f := by
  let i : I := Classical.choice (IsCofiltered.nonempty (C := I))
  simpa only [π_const, Functor.const_map_app] using
    mkMap_π ((Functor.const I).map f) i

end Pro
end TauCeti
