/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.Comma.Over.Pullback
public import TauCeti.CategoryTheory.Monoidal.Grp.Basic
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
  `pullback.snd p p`, lifting `Over.pullbackPullbackIsoOfComm` (`pullbackOverlapIso_hom_hom_hom`,
  `pullbackOverlapIso_inv_hom_hom`), together with its first-projection formula
  `pullbackOverlapIso_hom_left_fst`.
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

/-- The underlying morphism in `Over (Y ×_X Y)` of `(pullbackOverlapIso p G).hom` is
`Over.pullbackPullbackIsoOfComm` for `pullback.condition`. -/
@[simp]
theorem pullbackOverlapIso_hom_hom_hom (p : Y ⟶ X) (G : Grp (Over X)) :
    (pullbackOverlapIso p G).hom.hom.hom =
      (Over.pullbackPullbackIsoOfComm (pullback.condition (f := p) (g := p))).hom.app G.X := by
  simp only [pullbackOverlapIso, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    Grp.comp', Mon.comp_hom', Over.mapGrpPullbackCompOfEq_hom_app_hom_hom,
    Over.mapGrpPullbackComp_hom_app_hom_hom, Over.pullbackPullbackIsoOfComm_hom_app]
  exact Category.assoc _ _ _

/-- The underlying morphism in `Over (Y ×_X Y)` of `(pullbackOverlapIso p G).inv` is the inverse
of `Over.pullbackPullbackIsoOfComm` for `pullback.condition`. -/
@[simp]
theorem pullbackOverlapIso_inv_hom_hom (p : Y ⟶ X) (G : Grp (Over X)) :
    (pullbackOverlapIso p G).inv.hom.hom =
      (Over.pullbackPullbackIsoOfComm (pullback.condition (f := p) (g := p))).inv.app G.X := by
  have hIso : (Grp.forget (Over (pullback p p))).mapIso (pullbackOverlapIso p G) =
      (Over.pullbackPullbackIsoOfComm (pullback.condition (f := p) (g := p))).app G.X :=
    Iso.ext (pullbackOverlapIso_hom_hom_hom p G)
  exact congrArg Iso.inv hIso

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
  refine (congrArg
    (fun φ : (Over.pullback (pullback.fst p p)).obj ((Over.pullback p).obj G.X) ⟶
        (Over.pullback (pullback.snd p p)).obj ((Over.pullback p).obj G.X) ↦
      CommaMorphism.left φ ≫ pullback.fst ((Over.pullback p).obj G.X).hom (pullback.snd p p))
    (pullbackOverlapIso_hom_hom_hom p G)).trans (pullback.hom_ext ?_ ?_)
  · simp
  · simp [pullback.condition (f := pullback.snd G.X.hom p) (g := pullback.snd p p)]

end Pullback

end CategoryTheory.Grp
