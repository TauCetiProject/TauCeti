/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.Monoidal.Grp.Basic
import TauCeti.CategoryTheory.Comma.Over
import TauCeti.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Group objects over a base: monomorphisms and pullback functoriality

A morphism of group objects in a slice category is a monomorphism whenever its underlying
morphism in the original category is a monomorphism (`mono_of_mono_left`). This follows by
reflecting monomorphisms through the two faithful forgetful functors. In particular, closed
immersions of group schemes are monomorphisms without any affineness assumption.

In a category `C` with pullbacks, the slice categories `Over X` are cartesian monoidal via
`Over.cartesianMonoidalCategory`, and base change lifts to `(Over.pullback s).mapGrp`. This file
also records the canonical functoriality isomorphisms of base change on `Grp (Over X)` in
`_root_.CategoryTheory.Grp`:

* `CategoryTheory.Grp.pullbackIdIso`: `(Over.pullback (𝟙 X)).mapGrp.obj G ≅ G`.
* `CategoryTheory.Grp.pullbackCongrIso`:
  `(Over.pullback s₁).mapGrp.obj G ≅ (Over.pullback s₂).mapGrp.obj G` for `s₁ = s₂`.
* `CategoryTheory.Grp.pullbackOverlapIso`: the canonical overlap isomorphism on `Y ×_X Y` between
  the two pullbacks of `(Over.pullback p).mapGrp.obj G` along `pullback.fst p p` and
  `pullback.snd p p`, together with its first-projection formula `pullbackOverlapIso_hom_left_fst`.
-/

public section

universe v u

namespace CategoryTheory.Grp

/-- A morphism of group objects over a base is monic if its underlying morphism is monic. -/
instance (priority := 900) mono_of_mono_left {C : Type u} [Category.{v} C] {X : C}
    [CartesianMonoidalCategory (Over X)] {G H : Grp (Over X)} (f : G ⟶ H)
    [Mono f.hom.hom.left] : Mono f :=
  -- Forgetting inverses maps `f` to `f.hom` by definition.
  (Grp.forget₂Mon _).mono_of_mono_map (Mon.mono_of_mono_left f.hom)

section Pullback

open Limits

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C}

/-- The canonical isomorphism `(Over.pullback (𝟙 X)).mapGrp.obj G ≅ G` of group objects over `X`. -/
noncomputable def pullbackIdIso (G : Grp (Over X)) :
    (Over.pullback (𝟙 X)).mapGrp.obj G ≅ G :=
  (Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso).app G

/-- The underlying morphism in `Over X` of `(pullbackIdIso G).hom` is
`Over.pullbackId.hom.app G.X`. -/
@[simp]
theorem pullbackIdIso_hom_hom_hom (G : Grp (Over X)) :
    (pullbackIdIso G).hom.hom.hom = Over.pullbackId.hom.app G.X := by
  simp only [pullbackIdIso]
  exact Category.comp_id _

/-- The underlying morphism in `Over X` of `(pullbackIdIso G).inv` is
`Over.pullbackId.inv.app G.X`. -/
@[simp]
theorem pullbackIdIso_inv_hom_hom (G : Grp (Over X)) :
    (pullbackIdIso G).inv.hom.hom = Over.pullbackId.inv.app G.X := by
  simp only [pullbackIdIso]
  exact Category.id_comp _

/-- Naturality of `pullbackIdIso`. -/
@[reassoc]
theorem pullbackIdIso_hom_naturality {G H : Grp (Over X)} (f : G ⟶ H) :
    (Over.pullback (𝟙 X)).mapGrp.map f ≫ (pullbackIdIso H).hom = (pullbackIdIso G).hom ≫ f :=
  (Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso).hom.naturality f

/-- The canonical isomorphism between base changes of `G` along two equal morphisms `s₁ = s₂`. -/
noncomputable def pullbackCongrIso {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂) (G : Grp (Over X)) :
    (Over.pullback s₁).mapGrp.obj G ≅ (Over.pullback s₂).mapGrp.obj G :=
  eqToIso (by subst h; rfl)

/-- `pullbackCongrIso` along reflexivity is the identity isomorphism. -/
@[simp]
theorem pullbackCongrIso_rfl (s : Y ⟶ X) (G : Grp (Over X)) :
    pullbackCongrIso (rfl : s = s) G = Iso.refl _ :=
  (rfl)

/-- The underlying morphism in `Over Y` of `(pullbackCongrIso h G).hom` is `eqToHom`. -/
@[simp]
theorem pullbackCongrIso_hom_hom_hom {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂) (G : Grp (Over X)) :
    (pullbackCongrIso h G).hom.hom.hom =
      eqToHom (congrArg (fun f ↦ (Over.pullback f).obj G.X) h) := by
  subst h
  simp only [pullbackCongrIso, eqToIso.hom, eqToHom_refl, Grp.id', Mon.id_hom']
  -- Both sides are now `𝟙 _`, up to unfolding `((Over.pullback s₁).mapGrp.obj G).X` to
  -- `(Over.pullback s₁).obj G.X`.
  rfl

/-- The underlying morphism in `Over Y` of `(pullbackCongrIso h G).inv` is `eqToHom`. -/
@[simp]
theorem pullbackCongrIso_inv_hom_hom {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂) (G : Grp (Over X)) :
    (pullbackCongrIso h G).inv.hom.hom =
      eqToHom (congrArg (fun f ↦ (Over.pullback f).obj G.X) h.symm) := by
  subst h
  simp only [pullbackCongrIso, eqToIso.inv, eqToHom_refl, Grp.id', Mon.id_hom']
  -- Both sides are now `𝟙 _`, up to unfolding `((Over.pullback s₁).mapGrp.obj G).X` to
  -- `(Over.pullback s₁).obj G.X`.
  rfl

/-- Naturality of `pullbackCongrIso`. -/
@[reassoc]
theorem pullbackCongrIso_hom_naturality {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂)
    {G H : Grp (Over X)} (f : G ⟶ H) :
    (Over.pullback s₁).mapGrp.map f ≫ (pullbackCongrIso h H).hom =
      (pullbackCongrIso h G).hom ≫ (Over.pullback s₂).mapGrp.map f := by
  subst h
  simp

/-- The canonical overlap isomorphism on `Y ×_X Y` between the two pullbacks of the base-changed
group object `(Over.pullback p).mapGrp.obj G` along `pullback.fst p p` and `pullback.snd p p`. -/
noncomputable def pullbackOverlapIso (p : Y ⟶ X) (G : Grp (Over X)) :
    (Over.pullback (pullback.fst p p)).mapGrp.obj ((Over.pullback p).mapGrp.obj G) ≅
      (Over.pullback (pullback.snd p p)).mapGrp.obj ((Over.pullback p).mapGrp.obj G) :=
  (Over.mapGrpPullbackCompOfEq (pullback.fst p p) (pullback.condition (f := p) (g := p)) ≪≫
    Over.mapGrpPullbackComp (pullback.snd p p) p).app G

/-- Naturality of `pullbackOverlapIso`. -/
@[reassoc]
theorem pullbackOverlapIso_hom_naturality (p : Y ⟶ X) {G H : Grp (Over X)} (f : G ⟶ H) :
    (Over.pullback (pullback.fst p p)).mapGrp.map ((Over.pullback p).mapGrp.map f) ≫
        (pullbackOverlapIso p H).hom =
      (pullbackOverlapIso p G).hom ≫
        (Over.pullback (pullback.snd p p)).mapGrp.map ((Over.pullback p).mapGrp.map f) :=
  (Over.mapGrpPullbackCompOfEq (pullback.fst p p) (pullback.condition (f := p) (g := p)) ≪≫
    Over.mapGrpPullbackComp (pullback.snd p p) p).hom.naturality f

/-- On underlying objects, `pullbackOverlapIso p G` sends `((g, y₁), (y₁, y₂))` in
`(G ×_X Y) ×_Y (Y ×_X Y)` to `((g, y₂), (y₁, y₂))`: its first projection to `G ×_X Y` pairs the
`G`-coordinate `g` with the second `Y`-coordinate `y₂`. -/
@[reassoc]
theorem pullbackOverlapIso_hom_left_fst (p : Y ⟶ X) (G : Grp (Over X)) :
    (pullbackOverlapIso p G).hom.hom.hom.left ≫
        pullback.fst ((Over.pullback p).obj G.X).hom (pullback.snd p p) =
      pullback.lift
        (pullback.fst ((Over.pullback p).obj G.X).hom (pullback.fst p p) ≫
          pullback.fst G.X.hom p)
        (pullback.snd ((Over.pullback p).obj G.X).hom (pullback.fst p p) ≫
          pullback.snd p p)
        (by
          rw [Category.assoc, pullback.condition, ← Over.pullback_obj_hom p G.X,
            pullback.condition_assoc, pullback.condition, Category.assoc]) := by
  have hhom : (pullbackOverlapIso p G).hom.hom.hom =
      ((Over.pullbackComp (pullback.fst p p) p).inv.app G.X ≫
        eqToHom (congrArg (fun f ↦ (Over.pullback f).obj G.X)
          (pullback.condition (f := p) (g := p)))) ≫
        (Over.pullbackComp (pullback.snd p p) p).hom.app G.X := by
    simp only [pullbackOverlapIso, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
      Grp.comp', Mon.comp_hom', Over.mapGrpPullbackCompOfEq_hom_app_hom_hom,
      Over.mapGrpPullbackComp_hom_app_hom_hom]
    -- Unfold the intermediate object `((Over.pullback (pullback.snd p p ≫ p)).mapGrp.obj G).X`
    -- to `(Over.pullback (pullback.snd p p ≫ p)).obj G.X`.
    rfl
  have hleft : (pullbackOverlapIso p G).hom.hom.hom.left =
      ((Over.pullbackComp (pullback.fst p p) p).inv.app G.X).left ≫
        eqToHom (congrArg (fun f ↦ pullback G.X.hom f)
          (pullback.condition (f := p) (g := p))) ≫
        ((Over.pullbackComp (pullback.snd p p) p).hom.app G.X).left := by
    refine (congrArg Over.Hom.left hhom).trans ?_
    simp only [Over.comp_left, Over.eqToHom_left, Category.assoc]
    -- Unfold `((Over.pullback f).obj G.X).left` to `pullback G.X.hom f` in the `eqToHom`
    -- endpoints.
    rfl
  have hassoc :
      (((Over.pullbackComp (pullback.fst p p) p).inv.app G.X).left ≫
        eqToHom (congrArg (fun f ↦ pullback G.X.hom f)
          (pullback.condition (f := p) (g := p))) ≫
        ((Over.pullbackComp (pullback.snd p p) p).hom.app G.X).left) ≫
        pullback.fst ((Over.pullback p).obj G.X).hom (pullback.snd p p) =
      ((Over.pullbackComp (pullback.fst p p) p).inv.app G.X).left ≫
        eqToHom (congrArg (fun f ↦ pullback G.X.hom f)
          (pullback.condition (f := p) (g := p))) ≫
        ((Over.pullbackComp (pullback.snd p p) p).hom.app G.X).left ≫
        pullback.fst ((Over.pullback p).obj G.X).hom (pullback.snd p p) := by
    simp only [Category.assoc]
  exact ((congrArg (· ≫ _) hleft).trans hassoc).trans
    (Over.pullbackComp_inv_comp_eqToHom_comp_pullbackComp_hom_fst p G.X)

end Pullback

end CategoryTheory.Grp
