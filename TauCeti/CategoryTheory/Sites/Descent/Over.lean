/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack
public import TauCeti.CategoryTheory.Sites.Over

/-!
# Restricting a pseudofunctor to a slice site

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `U : C`. Its restriction
`F.over U : LocallyDiscrete (Over U)ᵒᵖ ⥤ᵖ Cat` (`Pseudofunctor.over`, defined in
`TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete`) is `F` precomposed with
`(Over.forget U).op`: its fibre over `X : Over U` is the fibre of `F` over `X.left`, and its
pullback along a morphism `g` of `Over U` is the pullback of `F` along `g.left`. This is the
restriction of a stack on the site `(C, J)` to the slice site `(Over U, J.over U)`, the operation
along which local properties of stacks, such as being a gerbe or carrying a banding, are
restricted from `C` to `C/U`.

The main results are that the restriction of a prestack, respectively a stack, for `J` is a
prestack, respectively a stack, for `J.over U` (`Pseudofunctor.isPrestack_over`,
`Pseudofunctor.isStack_over`). Both are deduced from the comparison of descent data: for a family
`f i : X i ⟶ S` of morphisms of `Over U`, descent data for `F.over U` relative to `f` are
equivalent to descent data for `F` relative to the underlying family `(f i).left` of morphisms
of `C` (`Pseudofunctor.DescentData.overEquivalence`), compatibly with the functors from the fibre
over `S` (`Pseudofunctor.DescentData.toDescentDataCompOverFunctorIso`). The equivalence rests on
the fact that a compatibility morphism of a descent datum for `F.over U`, over `q : Y ⟶ S`, is
unchanged when `Y` is replaced by `Over.mk (q.left ≫ S.hom)` and the underlying morphisms of `C`
are kept fixed (`Pseudofunctor.DescentData.hom_eq_hom_homMk`).

Strong transformations and modifications restrict along the same functor, by the precomposition
pseudofunctor `Pseudofunctor.precomp Cat (Over.forget U).op.toPseudofunctor` of
`TauCeti.CategoryTheory.Bicategory.FunctorBicategory.Precomp`: the restriction of `η : F ⟶ G` is
the whiskering `(Over.forget U).op.toPseudofunctor.whiskerLeft η : F.over U ⟶ G.over U`, with the
same components, and a modification restricts to the modification with the same components.

The descent data, prestacks and stacks used here are Mathlib's `Pseudofunctor.DescentData`,
`Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`, by Joël Riou and Christian Merten.

## References

* [Jean Giraud, *Cohomologie non abélienne*][giraud1971], for prestacks and stacks.
-/

public section

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {U : C}

namespace DescentData

variable {ι : Type t} {S : Over U} {X : ι → Over U} (f : ∀ i, X i ⟶ S)

variable {F f} in
/-- A compatibility morphism of a descent datum for `F.over U`, over `q : Y ⟶ S`, is unchanged
when `Y` is replaced by the object `Over.mk (q.left ≫ S.hom)`, which has the same underlying
object, and the underlying morphisms `q.left`, `f₁.left` and `f₂.left` of `C` are kept fixed. -/
lemma hom_eq_hom_homMk (D : (F.over U).DescentData f) ⦃Y : Over U⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom (Y := Over.mk (q.left ≫ S.hom)) (Over.homMk q.left)
      (Over.homMk f₁.left (by simp [← hf₁])) (Over.homMk f₂.left (by simp [← hf₂]))
      (by ext; simp [← hf₁]) (by ext; simp [← hf₂]) := by
  have h := D.pullHom_hom (Y' := Over.mk (q.left ≫ S.hom)) (Over.homMk (𝟙 Y.left) (by simp)) q
    (Over.homMk q.left) (by ext; simp) f₁ f₂ hf₁ hf₂ (Over.homMk f₁.left (by simp [← hf₁]))
    (Over.homMk f₂.left (by simp [← hf₂])) (by ext; simp) (by ext; simp)
  rw [← h, pullHom_toPseudofunctor_comp (F := F)]
  -- The underlying morphism of `Over.homMk (𝟙 Y.left)` is `𝟙 Y.left` by definition, so this is
  -- the pullback along an identity.
  exact (pullHom_id (F := F) _).symm

/-- The functor from descent data for `F.over U` relative to `f` to descent data for `F`
relative to the underlying family `(f i).left`. It keeps the objects; over `q : Y ⟶ S.left`, the
morphisms of the image are those of the given descent datum over the object
`Over.mk (q ≫ S.hom)` of `Over U`. -/
@[expose, simps]
def overFunctor : (F.over U).DescentData f ⥤ F.DescentData (fun i ↦ (f i).left) where
  obj D :=
    { obj := D.obj
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        D.hom (Y := Over.mk (q ≫ S.hom)) (Over.homMk q) (Over.homMk f₁ (by simp [← hf₁]))
          (Over.homMk f₂ (by simp [← hf₂])) (by ext; exact hf₁) (by ext; exact hf₂)
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        have := D.pullHom_hom
          (Over.homMk g (by simp [← hq]) : Over.mk (q' ≫ S.hom) ⟶ Over.mk (q ≫ S.hom))
          (Over.homMk q) (Over.homMk q') (by ext; exact hq) (Over.homMk f₁ (by simp [← hf₁]))
          (Over.homMk f₂ (by simp [← hf₂])) (by ext; exact hf₁) (by ext; exact hf₂)
          (Over.homMk gf₁ (by simp [← hgf₁, ← hf₁, ← hq]))
          (Over.homMk gf₂ (by simp [← hgf₂, ← hf₂, ← hq]))
          (by ext; exact hgf₁) (by ext; exact hgf₂)
        rwa [pullHom_toPseudofunctor_comp] at this
      hom_self Y q i g hg := D.hom_self _ _ (by ext; exact hg)
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := D.hom_comp _ _ _ _ _ _ _ }
  map φ :=
    { hom := φ.hom
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := φ.comm (Y := Over.mk (q ≫ S.hom)) (Over.homMk q)
        (Over.homMk f₁ (by simp [← hf₁])) (Over.homMk f₂ (by simp [← hf₂])) (by ext; exact hf₁)
        (by ext; exact hf₂) }

/-- The functor from descent data for `F` relative to the underlying family `(f i).left` to
descent data for `F.over U` relative to `f`. It keeps the objects; over `q : Y ⟶ S` in `Over U`,
the morphisms of the image are those of the given descent datum over `q.left`. -/
@[expose, simps]
def overInverse : F.DescentData (fun i ↦ (f i).left) ⥤ (F.over U).DescentData f where
  obj D :=
    { obj := D.obj
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        D.hom q.left f₁.left f₂.left (by rw [← hf₁, Over.comp_left])
          (by rw [← hf₂, Over.comp_left])
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
        -- The morphisms `(Over.forget U).map _` produced by `pullHom_toPseudofunctor_comp` are
        -- the underlying morphisms `_.left` by definition.
        (pullHom_toPseudofunctor_comp (F := F) _ _ _ _ _ _ _).trans (D.pullHom_hom _ _ _
          (by rw [← hq]; rfl) _ _ (by rw [← hf₁]; rfl) (by rw [← hf₂]; rfl) _ _
          (by rw [← hgf₁]; rfl) (by rw [← hgf₂]; rfl))
      hom_self Y q i g hg := D.hom_self _ _ (by rw [← hg, Over.comp_left])
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := D.hom_comp _ _ _ _
        (by rw [← hf₁, Over.comp_left]) (by rw [← hf₂, Over.comp_left])
        (by rw [← hf₃, Over.comp_left]) }
  map φ :=
    { hom := φ.hom
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := φ.comm q.left f₁.left f₂.left
        (by rw [← hf₁, Over.comp_left]) (by rw [← hf₂, Over.comp_left]) }

/-- Descent data for `F.over U` relative to a family `f` of morphisms of `Over U` are
equivalent to descent data for `F` relative to the underlying family `(f i).left` of morphisms of
`C`. Both functors keep the objects and the morphisms of descent data, and the unit and counit
have identity components. -/
@[expose, simps! functor inverse counitIso_hom_app_hom counitIso_inv_app_hom]
def overEquivalence : (F.over U).DescentData f ≌ F.DescentData (fun i ↦ (f i).left) where
  functor := overFunctor F f
  inverse := overInverse F f
  -- In the compatibility condition below, the objects of `D` and of its image under
  -- `overFunctor F f ⋙ overInverse F f` agree only after unfolding these functors, so the goal is
  -- not type-correct at reducible transparency and `simp` and `rw` cannot see the identities
  -- `F.map (𝟙 _)`; `erw` matches them up to this unfolding.
  unitIso := NatIso.ofComponents (fun D ↦ isoMk (fun _ ↦ Iso.refl _)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ by
      erw [Iso.refl_hom, Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id]
      exact (hom_eq_hom_homMk D q f₁ f₂ hf₁ hf₂).symm)) (fun _ ↦ by
        ext
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
  -- The composite `overInverse F f ⋙ overFunctor F f` is the identity functor by definition: it
  -- keeps the objects and, since `(Over.homMk g).left` is `g`, the compatibility morphisms.
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by
    ext
    exact Category.id_comp _

/-- The unit of `overEquivalence` has identity components. -/
@[simp]
lemma overEquivalence_unitIso_hom_app_hom (D : (F.over U).DescentData f) (i : ι) :
    ((overEquivalence F f).unitIso.hom.app D).hom i = 𝟙 (D.obj i) :=
  rfl

/-- The inverse of the unit of `overEquivalence` has identity components. -/
@[simp]
lemma overEquivalence_unitIso_inv_app_hom (D : (F.over U).DescentData f) (i : ι) :
    ((overEquivalence F f).unitIso.inv.app D).hom i = 𝟙 (D.obj i) :=
  rfl

/-- Pulling back an object of `F` over `S.left` along the family `f`, then passing to descent
data for `F`, is pulling it back along the underlying family of `f`. The isomorphism has identity
components. -/
@[expose]
def toDescentDataCompOverFunctorIso :
    (F.over U).toDescentData f ⋙ overFunctor F f ≅ F.toDescentData (fun i ↦ (f i).left) :=
  NatIso.ofComponents (fun M ↦ isoMk (fun _ ↦ Iso.refl _) (fun _ q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
      -- As for the unit of `overEquivalence`, the goal is type-correct only up to unfolding
      -- `overFunctor F f` and `Pseudofunctor.comp`, so `erw` is needed to see the identities
      -- `F.map (𝟙 _)`.
      erw [Iso.refl_hom, Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id]
      -- Both sides are the composites of the comparisons of `F.over U`, respectively `F`, which
      -- agree by `comp_mapComp'_eq_mapComp'`.
      have e₁ : Over.homMk (U := Over.mk (q ≫ S.hom)) f₁ (by simp [← hf₁]) ≫ f i₁ =
          Over.homMk q := by ext; exact hf₁
      have h₁ := comp_mapComp'_eq_mapComp' (Over.forget U).op.toPseudofunctor F (f i₁).op.toLoc
        (Over.homMk (U := Over.mk (q ≫ S.hom)) f₁ (by simp [← hf₁])).op.toLoc
        (Over.homMk q).op.toLoc (by rw [← e₁]; rfl)
      have e₂ : Over.homMk (U := Over.mk (q ≫ S.hom)) f₂ (by simp [← hf₂]) ≫ f i₂ =
          Over.homMk q := by ext; exact hf₂
      have h₂ := comp_mapComp'_eq_mapComp' (Over.forget U).op.toPseudofunctor F (f i₂).op.toLoc
        (Over.homMk (U := Over.mk (q ≫ S.hom)) f₂ (by simp [← hf₂])).op.toLoc
        (Over.homMk q).op.toLoc (by rw [← e₂]; rfl)
      exact congr($(h₁).inv.toNatTrans.app M ≫ $(h₂).hom.toNatTrans.app M).symm))
    (fun _ ↦ by
      ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The isomorphism `toDescentDataCompOverFunctorIso` has identity components. -/
@[simp]
lemma toDescentDataCompOverFunctorIso_hom_app_hom (M : (F.over U).obj (.mk (op S))) (i : ι) :
    ((toDescentDataCompOverFunctorIso F f).hom.app M).hom i =
      𝟙 (((F.over U).map (f i).op.toLoc).toFunctor.obj M) :=
  rfl

/-- The inverse of the isomorphism `toDescentDataCompOverFunctorIso` has identity components. -/
@[simp]
lemma toDescentDataCompOverFunctorIso_inv_app_hom (M : (F.over U).obj (.mk (op S))) (i : ι) :
    ((toDescentDataCompOverFunctorIso F f).inv.app M).hom i =
      𝟙 (((F.over U).map (f i).op.toLoc).toFunctor.obj M) :=
  rfl

end DescentData

variable (U) (J : GrothendieckTopology C)

/-- The restriction to `Over U` of a prestack for `J` is a prestack for `J.over U`. -/
instance isPrestack_over [F.IsPrestack J] : (F.over U).IsPrestack (J.over U) :=
  .of_isPrestackFor fun _ R hR ↦ by
    rw [isPrestackFor_iff]
    have hR' := (J.ofArrows_mem_over_iff _ _).1 (by rwa [Sieve.ofArrows_category])
    let e := DescentData.overEquivalence F (fun g : R.arrows.category ↦ g.obj.hom)
    exact ⟨((F.fullyFaithfulToDescentData _ hR').comp e.fullyFaithfulInverse).ofIso
      (DescentData.toDescentDataCompOverFunctorIso F _).symm.compInverseIso⟩

/-- The restriction to `Over U` of a stack for `J` is a stack for `J.over U`. -/
instance isStack_over [F.IsStack J] : (F.over U).IsStack (J.over U) where
  essSurj_of_sieve R hR := by
    have hR' := (J.ofArrows_mem_over_iff _ _).1 (by rwa [Sieve.ofArrows_category])
    let e := DescentData.overEquivalence F (fun g : R.arrows.category ↦ g.obj.hom)
    have : ((F.over U).toDescentData _ ⋙ e.functor).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso (DescentData.toDescentDataCompOverFunctorIso F _)).2
        (F.isEquivalence_toDescentData _ hR')
    have := Functor.isEquivalence_of_comp_right ((F.over U).toDescentData _) e.functor
    infer_instance

end CategoryTheory.Pseudofunctor
