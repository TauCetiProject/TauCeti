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
@[expose]
def const : C ⥤ Pro C := Ind.yoneda.rightOp

instance : const (C := C) |>.Full := inferInstanceAs Ind.yoneda.rightOp.Full
instance : const (C := C) |>.Faithful := inferInstanceAs Ind.yoneda.rightOp.Faithful

/-- The constant-object embedding is fully faithful. -/
protected def const.fullyFaithful : (const (C := C)).FullyFaithful :=
  Ind.yoneda.fullyFaithful.rightOp

/-- A constant pro-object is the opposite of the corresponding ind-representable. -/
theorem const_obj (X : C) : const.obj X = op (Ind.yoneda.obj (op X)) := (rfl)

/-- The constant-object embedding acts on maps by opposite Yoneda. -/
theorem const_map {X Y : C} (f : X ⟶ Y) :
    const.map f = (Ind.yoneda.map f.op).op := (rfl)

variable {I : Type v} [SmallCategory I] [IsCofiltered I]

attribute [local instance] IsCofiltered.isConnected

/-- The functor sending a cofiltered diagram in `C` to its pro-object, dual to `Ind.lim`. -/
@[expose]
def lim : (I ⥤ C) ⥤ Pro C := (Functor.opHom I C ⋙ Ind.lim Iᵒᵖ).rightOp

/-- The pro-object presented by a small cofiltered diagram. -/
abbrev mk (F : I ⥤ C) : Pro C := lim.obj F

/-- A presented pro-object is the opposite of the ind-limit of the opposite diagram. -/
theorem mk_def (F : I ⥤ C) : mk F = op ((Ind.lim Iᵒᵖ).obj F.op) := (rfl)

/-- The canonical projection from a presented pro-object to one of its stages. -/
def π (F : I ⥤ C) (i : I) : mk F ⟶ const.obj (F.obj i) :=
  (colimit.ι (F.op ⋙ Ind.yoneda) (op i)).op

/-- Stage projections are the opposites of the ind-presentation's colimit inclusions. -/
theorem π_def (F : I ⥤ C) (i : I) :
    π F i = (colimit.ι (F.op ⋙ Ind.yoneda) (op i)).op := (rfl)

/-- Stage projections commute with transition maps. -/
@[reassoc (attr := simp)]
theorem π_naturality (F : I ⥤ C) {i j : I} (a : i ⟶ j) :
    π F i ≫ const.map (F.map a) = π F j := by
  rw [const_map]
  -- By `π_def`, the legs are opposite colimit inclusions; taking opposites reverses
  -- composition as in `op_comp`, turning the colimit relation into this cone relation.
  exact congrArg Quiver.Hom.op (colimit.w (F.op ⋙ Ind.yoneda) a.op)

/-- The stage projections form a cone. The body is exposed so that the vertex in
`mkCone_π_app` is definitionally `mk F`, without equality transports. -/
@[expose]
def mkCone (F : I ⥤ C) : Cone (F ⋙ const) where
  pt := mk F
  π :=
    { app := π F
      naturality := fun _ _ _ ↦ by simp }

/-- A cofiltered presentation realizes its pro-object as a limit of constant objects. -/
def mkConeIsLimit (F : I ⥤ C) : IsLimit (mkCone F) :=
  -- `mkCone F` is definitionally `coneRightOpOfCocone (colimit.cocone (F.op ⋙ Ind.yoneda))`:
  -- `mk_def` identifies the vertex, and `π_def` identifies each leg with an opposite inclusion.
  isLimitConeRightOpOfCocone (F.op ⋙ Ind.yoneda) (colimit.isColimit _)

/-- The vertex of the presentation cone is the presented pro-object. -/
@[simp]
theorem mkCone_pt (F : I ⥤ C) : (mkCone F).pt = mk F := (rfl)

/-- The legs of the presentation cone are the canonical stage projections. -/
@[simp]
theorem mkCone_π_app (F : I ⥤ C) (i : I) : (mkCone F).π.app i = π F i := (rfl)

/-- The universal map from a cone to the pro-object presented by its diagram. -/
def lift {F : I ⥤ C} (c : Cone (F ⋙ const)) : c.pt ⟶ mk F :=
  (mkConeIsLimit F).lift c

/-- The universal map has the prescribed stage projections. -/
@[reassoc (attr := simp)]
theorem lift_π {F : I ⥤ C} (c : Cone (F ⋙ const)) (i : I) :
    lift c ≫ π F i = c.π.app i :=
  (mkConeIsLimit F).fac c i

/-- Morphisms into a presented pro-object are determined by their stage projections. -/
@[ext]
theorem hom_ext {F : I ⥤ C} {X : Pro C} {f g : X ⟶ mk F}
    (h : ∀ i, f ≫ π F i = g ≫ π F i) : f = g :=
  (mkConeIsLimit F).hom_ext h

/-- The induced pro-morphism has the specified map at each stage. -/
@[reassoc (attr := simp)]
theorem lim_map_π {F G : I ⥤ C} (α : F ⟶ G) (i : I) :
    lim.map α ≫ π G i = π F i ≫ const.map (α.app i) :=
  -- Unfolding `lim`, `rightOp`, `Functor.opHom` and `Ind.lim` (whiskering by Yoneda then
  -- `colim`) identifies `lim.map α` with `(colim.map (whiskerRight (NatTrans.op α)
  -- Ind.yoneda)).op`. Together with `π_def` and `const_map`, this is the opposite of `ι_map`.
  congrArg Quiver.Hom.op
    (colimit.ι_map (Functor.whiskerRight (NatTrans.op α) Ind.yoneda) (op i))

/-- A constant cofiltered presentation gives the corresponding constant pro-object. -/
def mkConstIso (X : C) : mk ((Functor.const I).obj X) ≅ const.obj X :=
  (mkConeIsLimit _).conePointUniqueUpToIso
    ((IsLimit.postcomposeInvEquiv (Functor.constComp I X const)
      (constCone I (const.obj X))).symm (isLimitConstCone I (const.obj X)))

/-- Every projection of a constant presentation is its comparison isomorphism. -/
@[simp]
theorem π_const (X : C) (i : I) :
    π ((Functor.const I).obj X) i = (mkConstIso (I := I) X).hom := by
  have h := (mkConeIsLimit ((Functor.const I).obj X)).conePointUniqueUpToIso_hom_comp
    ((IsLimit.postcomposeInvEquiv (Functor.constComp I X const)
      (constCone I (const.obj X))).symm (isLimitConstCone I (const.obj X))) i
  -- Unfold the cone to normalize the equality's ambient Hom type from `(mkCone _).pt` to `mk _`.
  simpa [mkConstIso, mkCone] using h.symm

/-- The constant-presentation comparison is natural in the constant object. -/
@[reassoc (attr := simp)]
theorem lim_map_mkConstIso_hom {X Y : C} (f : X ⟶ Y) :
    lim.map ((Functor.const I).map f) ≫ (mkConstIso Y).hom =
      (mkConstIso X).hom ≫ const.map f := by
  let i : I := Classical.choice (IsCofiltered.nonempty (C := I))
  simpa only [π_const, Functor.const_map_app] using
    lim_map_π ((Functor.const I).map f) i

end Pro
end TauCeti
