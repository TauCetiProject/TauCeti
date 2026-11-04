/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Marked.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Limits and colimits of marked simplicial sets

Limits and colimits of marked simplicial sets are computed on the underlying simplicial sets. In
a limit, an edge is marked when each of its projections is marked; in a colimit, the marked edges
are the images of the marked edges of the diagram. Thus the category `TauCeti.MarkedSSet` has
all small limits and colimits, and the forgetful functor to simplicial sets preserves them.

In particular the product `X ⊗ Y` of marked simplicial sets is the product of the underlying
simplicial sets, in which an edge is marked exactly when both of its components are, and the
terminal object is the point with its unique edge marked. We record this as the cartesian monoidal
structure on marked simplicial sets.

## Main definitions

* `TauCeti.MarkedSSet.limitCone`, `TauCeti.MarkedSSet.colimitCocone`: the limit and colimit
  markings on a limit cone and a colimit cocone of the underlying diagram of simplicial sets.
* `TauCeti.MarkedSSet.instCartesianMonoidalCategory`: the cartesian monoidal structure.

## Main results

* `TauCeti.MarkedSSet.mem_marked_iff_of_isLimit`: the edges of a limit which are marked are the
  ones all of whose projections are marked.
* `TauCeti.MarkedSSet.mem_marked_iff_of_isColimit`: the marked edges of a colimit are the images
  of marked edges.
* `TauCeti.MarkedSSet.mem_tensorObj_marked_iff`: an edge of `X ⊗ Y` is marked exactly when both
  of its components are.

## References

* J. Lurie, *Higher Topos Theory*, §3.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial

universe w w' u

namespace TauCeti

namespace MarkedSSet

variable {J : Type w} [Category.{w'} J] (F : J ⥤ MarkedSSet.{u})

section limits

/-- The cone over a diagram of marked simplicial sets given by a cone `c` over the underlying
diagram of simplicial sets, in which an edge of `c.pt` is marked when each of its projections is
marked. -/
@[expose, simps pt_toSSet]
def limitCone (c : Cone (F ⋙ forget)) : Cone F where
  pt :=
    { toSSet := c.pt
      marked := {e | ∀ j, (c.π.app j).app _ e ∈ (F.obj j).marked}
      σ_mem_marked x j := map_σ_mem_marked (c.π.app j) x }
  π :=
    { app j := ⟨c.π.app j, fun _ he ↦ he j⟩
      naturality _ _ f := hom_ext (c.π.naturality f) }

@[simp]
lemma limitCone_π_app_hom (c : Cone (F ⋙ forget)) (j : J) :
    ((limitCone F c).π.app j).hom = c.π.app j :=
  (rfl)

@[simp]
lemma mem_limitCone_marked_iff (c : Cone (F ⋙ forget)) (e : c.pt _⦋1⦌) :
    e ∈ (limitCone F c).pt.marked ↔ ∀ j, (c.π.app j).app _ e ∈ (F.obj j).marked :=
  Iff.rfl

variable {F} in
/-- The limit marking on a limit cone of the underlying simplicial sets is a limit cone. -/
def isLimitLimitCone {c : Cone (F ⋙ forget)} (hc : IsLimit c) : IsLimit (limitCone F c) where
  lift s := ⟨hc.lift (forget.mapCone s), fun e he j ↦ by
    have h : (c.π.app j).app _ ((hc.lift (forget.mapCone s)).app _ e) = (s.π.app j).hom.app _ e :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (hc.fac (forget.mapCone s) j) _) e
    exact h ▸ map_mem_marked (s.π.app j) he⟩
  fac s j := hom_ext (hc.fac (forget.mapCone s) j)
  uniq s m hm := hom_ext (hc.uniq (forget.mapCone s) m.hom fun j ↦ congrArg Hom.hom (hm j))

instance [HasLimit (F ⋙ forget)] : HasLimit F :=
  ⟨⟨⟨_, isLimitLimitCone (limit.isLimit _)⟩⟩⟩

instance [HasLimitsOfShape J SSet.{u}] : HasLimitsOfShape J MarkedSSet.{u} where

instance [HasLimitsOfSize.{w', w} SSet.{u}] : HasLimitsOfSize.{w', w} MarkedSSet.{u} where

instance : PreservesLimitsOfSize.{w', w} forget.{u} :=
  flatForgetAdj.rightAdjoint_preservesLimits

variable {F} in
/-- An edge of the apex of a limit cone of marked simplicial sets is marked exactly when each of
its projections is marked. -/
lemma mem_marked_iff_of_isLimit {c : Cone F} (hc : IsLimit c)
    (e : c.pt.toSSet _⦋1⦌) :
    e ∈ c.pt.marked ↔ ∀ j, (c.π.app j).hom.app _ e ∈ (F.obj j).marked := by
  refine ⟨fun he j ↦ map_mem_marked _ he, fun he ↦ ?_⟩
  have hc' := isLimitOfPreserves forget hc
  have hlift : (hc.lift (limitCone F (forget.mapCone c))).hom.app _ e = e :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (hc'.hom_ext (f' := 𝟙 _)
      fun j ↦ congrArg Hom.hom (hc.fac (limitCone F (forget.mapCone c)) j)) _) e
  exact hlift ▸ map_mem_marked (hc.lift (limitCone F (forget.mapCone c))) he

end limits

section colimits

/-- The cocone under a diagram of marked simplicial sets given by a cocone `c` under the
underlying diagram of simplicial sets, in which the marked edges of `c.pt` are the degenerate
edges and the images of the marked edges of the diagram. -/
@[expose, simps pt_toSSet]
def colimitCocone (c : Cocone (F ⋙ forget)) : Cocone F where
  pt :=
    { toSSet := c.pt
      marked := {e | e ∈ Set.range (c.pt.σ 0) ∨
        ∃ j, ∃ e' ∈ (F.obj j).marked, (c.ι.app j).app _ e' = e}
      σ_mem_marked x := .inl ⟨x, rfl⟩ }
  ι :=
    { app j := ⟨c.ι.app j, fun e he ↦ .inr ⟨j, e, he, rfl⟩⟩
      naturality _ _ f := hom_ext (c.ι.naturality f) }

@[simp]
lemma colimitCocone_ι_app_hom (c : Cocone (F ⋙ forget)) (j : J) :
    ((colimitCocone F c).ι.app j).hom = c.ι.app j :=
  (rfl)

@[simp]
lemma mem_colimitCocone_marked_iff (c : Cocone (F ⋙ forget)) (e : c.pt _⦋1⦌) :
    e ∈ (colimitCocone F c).pt.marked ↔
      e ∈ Set.range (c.pt.σ 0) ∨ ∃ j, ∃ e' ∈ (F.obj j).marked, (c.ι.app j).app _ e' = e :=
  Iff.rfl

variable {F} in
/-- The colimit marking on a colimit cocone of the underlying simplicial sets is a colimit
cocone. -/
def isColimitColimitCocone {c : Cocone (F ⋙ forget)} (hc : IsColimit c) :
    IsColimit (colimitCocone F c) where
  desc s := ⟨hc.desc (forget.mapCocone s), by
    rintro _ (⟨x, rfl⟩ | ⟨j, e, he, rfl⟩)
    · exact map_σ_mem_marked _ x
    have h : (hc.desc (forget.mapCocone s)).app _ ((c.ι.app j).app _ e) = (s.ι.app j).hom.app _ e :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (hc.fac (forget.mapCocone s) j) _) e
    exact h ▸ map_mem_marked (s.ι.app j) he⟩
  fac s j := hom_ext (hc.fac (forget.mapCocone s) j)
  uniq s m hm := hom_ext (hc.uniq (forget.mapCocone s) m.hom fun j ↦ congrArg Hom.hom (hm j))

instance [HasColimit (F ⋙ forget)] : HasColimit F :=
  ⟨⟨⟨_, isColimitColimitCocone (colimit.isColimit _)⟩⟩⟩

instance [HasColimitsOfShape J SSet.{u}] : HasColimitsOfShape J MarkedSSet.{u} where

instance [HasColimitsOfSize.{w', w} SSet.{u}] : HasColimitsOfSize.{w', w} MarkedSSet.{u} where

instance : PreservesColimitsOfSize.{w', w} forget.{u} :=
  forgetSharpAdj.leftAdjoint_preservesColimits

variable {F} in
/-- The marked edges of the apex of a colimit cocone of marked simplicial sets are the degenerate
edges and the images of the marked edges of the diagram. -/
lemma mem_marked_iff_of_isColimit {c : Cocone F} (hc : IsColimit c)
    (e : c.pt.toSSet _⦋1⦌) :
    e ∈ c.pt.marked ↔ e ∈ Set.range (c.pt.toSSet.σ 0) ∨
      ∃ j, ∃ e' ∈ (F.obj j).marked, (c.ι.app j).hom.app _ e' = e := by
  refine ⟨fun he ↦ ?_, ?_⟩
  · have hc' := isColimitOfPreserves forget hc
    have hdesc : (hc.desc (colimitCocone F (forget.mapCocone c))).hom.app _ e = e :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (hc'.hom_ext (f' := 𝟙 _)
        fun j ↦ congrArg Hom.hom (hc.fac (colimitCocone F (forget.mapCocone c)) j)) _) e
    exact hdesc ▸ map_mem_marked (hc.desc (colimitCocone F (forget.mapCocone c))) he
  · rintro (⟨x, rfl⟩ | ⟨j, e', he', rfl⟩)
    · exact c.pt.σ_mem_marked x
    · exact map_mem_marked _ he'

end colimits

section products

/-- The product of marked simplicial sets: the product of the underlying simplicial sets, in
which an edge is marked when both of its components are. -/
@[expose, simps toSSet]
def prod (X Y : MarkedSSet.{u}) : MarkedSSet.{u} where
  toSSet := X.toSSet ⊗ Y.toSSet
  marked := {e | (fst _ _ : X.toSSet ⊗ Y.toSSet ⟶ _).app _ e ∈ X.marked ∧
    (snd _ _ : X.toSSet ⊗ Y.toSSet ⟶ _).app _ e ∈ Y.marked}
  σ_mem_marked x := ⟨map_σ_mem_marked _ x, map_σ_mem_marked _ x⟩

/-- The product cone of two marked simplicial sets. -/
@[expose]
def prodFan (X Y : MarkedSSet.{u}) : BinaryFan X Y :=
  BinaryFan.mk (P := prod X Y) ⟨fst _ _, fun _ he ↦ he.1⟩ ⟨snd _ _, fun _ he ↦ he.2⟩

/-- The product cone of two marked simplicial sets is a limit cone. -/
@[expose]
def isLimitProdFan (X Y : MarkedSSet.{u}) : IsLimit (prodFan X Y) :=
  BinaryFan.IsLimit.mk _
    (fun f g ↦ ⟨lift f.hom g.hom, fun _ he ↦ ⟨f.map_mem_marked he, g.map_mem_marked he⟩⟩)
    (fun _ _ ↦ hom_ext (lift_fst _ _)) (fun _ _ ↦ hom_ext (lift_snd _ _))
    (fun _ _ _ h₁ h₂ ↦ hom_ext (CartesianMonoidalCategory.hom_ext _ _
      (congrArg Hom.hom h₁) (congrArg Hom.hom h₂)))

/-- If `T` is a terminal simplicial set, then `T♯` is a terminal marked simplicial set. -/
def isTerminalSharpObj {T : SSet.{u}} (hT : IsTerminal T) : IsTerminal (sharp.obj T) :=
  IsTerminal.ofUniqueHom (fun X ↦ toSharp (hT.from X.toSSet)) (fun _ _ ↦ hom_ext (hT.hom_ext _ _))

instance instCartesianMonoidalCategory : CartesianMonoidalCategory MarkedSSet.{u} :=
  .ofChosenFiniteProducts ⟨_, isTerminalSharpObj isTerminalTensorUnit⟩
    (fun X Y ↦ ⟨prodFan X Y, isLimitProdFan X Y⟩)

instance : BraidedCategory MarkedSSet.{u} :=
  .ofCartesianMonoidalCategory

variable {X Y X' Y' : MarkedSSet.{u}}

@[simp]
lemma tensorObj_toSSet (X Y : MarkedSSet.{u}) : (X ⊗ Y).toSSet = X.toSSet ⊗ Y.toSSet :=
  (rfl)

@[simp]
lemma tensorUnit_toSSet : (𝟙_ MarkedSSet.{u}).toSSet = 𝟙_ SSet.{u} :=
  (rfl)

/-- An edge of a product of marked simplicial sets is marked exactly when both of its components
are marked. -/
@[simp]
lemma mem_tensorObj_marked_iff (e : (X ⊗ Y).toSSet _⦋1⦌) :
    e ∈ (X ⊗ Y).marked ↔
      (fst _ _ : X.toSSet ⊗ Y.toSSet ⟶ _).app _ e ∈ X.marked ∧
        (snd _ _ : X.toSSet ⊗ Y.toSSet ⟶ _).app _ e ∈ Y.marked :=
  Iff.rfl

/-- Every edge of the terminal marked simplicial set is marked. -/
@[simp]
lemma mem_tensorUnit_marked (e : (𝟙_ MarkedSSet.{u}).toSSet _⦋1⦌) :
    e ∈ (𝟙_ MarkedSSet.{u}).marked :=
  Set.mem_univ e

@[simp]
lemma fst_hom (X Y : MarkedSSet.{u}) : (fst X Y).hom = fst X.toSSet Y.toSSet :=
  (rfl)

@[simp]
lemma snd_hom (X Y : MarkedSSet.{u}) : (snd X Y).hom = snd X.toSSet Y.toSSet :=
  (rfl)

@[simp]
lemma lift_hom {Z : MarkedSSet.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    (lift f g).hom = lift f.hom g.hom :=
  (rfl)

@[simp]
lemma toUnit_hom (X : MarkedSSet.{u}) : (toUnit X).hom = toUnit X.toSSet :=
  (rfl)

@[simp]
lemma tensorHom_hom (f : X ⟶ X') (g : Y ⟶ Y') : (f ⊗ₘ g).hom = f.hom ⊗ₘ g.hom :=
  (rfl)

@[simp]
lemma whiskerLeft_hom (X : MarkedSSet.{u}) (g : Y ⟶ Y') : (X ◁ g).hom = X.toSSet ◁ g.hom :=
  (rfl)

@[simp]
lemma whiskerRight_hom (f : X ⟶ X') (Y : MarkedSSet.{u}) : (f ▷ Y).hom = f.hom ▷ Y.toSSet :=
  (rfl)

end products

end MarkedSSet

end TauCeti
