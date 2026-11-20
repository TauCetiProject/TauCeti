/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Sites.Over

/-!
# Restricting a pseudofunctor to a slice site

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `U : C`. Its restriction
`F.over U : LocallyDiscrete (Over U)ᵒᵖ ⥤ᵖ Cat` is `F` precomposed with `(Over.forget U).op`: its
fibre over `X : Over U` is the fibre of `F` over `X.left`, and its pullback along a morphism `g`
of `Over U` is the pullback of `F` along `g.left`. This is the restriction of a stack on the site
`(C, J)` to the slice site `(Over U, J.over U)`, the operation along which local properties of
stacks, such as being a gerbe or carrying a banding, are restricted from `C` to `C/U`.

The main results are that the restriction of a prestack, respectively a stack, for `J` is a
prestack, respectively a stack, for `J.over U` (`Pseudofunctor.isPrestack_over`,
`Pseudofunctor.isStack_over`). Both are deduced from the comparison of descent data: for a family
`f i : X i ⟶ S` of morphisms of `Over U`, descent data for `F.over U` relative to `f` are
equivalent to descent data for `F` relative to the underlying family `(f i).left` of morphisms
of `C` (`Pseudofunctor.DescentData.overEquivalence`), compatibly with the functors from the fibre
over `S` (`Pseudofunctor.DescentData.toDescentDataCompOverFunctorIso`). The equivalence rests on
the fact that the value of a descent datum for `F.over U` over an object `Y` of `Over U` depends
only on `Y.left` (`Pseudofunctor.DescentData.hom_eq_hom_homMk`).

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

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (U : C)

/-- The restriction of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` to the slice `Over U`,
that is `F` precomposed with `(Over.forget U).op`. Its fibre over `X : Over U` is the fibre of
`F` over `X.left`, and its pullback along `g : X ⟶ Y` is the pullback of `F` along `g.left`. -/
abbrev over : LocallyDiscrete (Over U)ᵒᵖ ⥤ᵖ Cat.{v', u'} :=
  (Over.forget U).op.toPseudofunctor.comp F

variable {F U}

/-- The unit comparison of `F.over U` at a morphism `f` of `Over U` equal to an identity is that
of `F` at `f.left`. -/
lemma over_mapId' {X : Over U} (f : X ⟶ X) (hf : f = 𝟙 X) :
    (F.over U).mapId' f.op.toLoc (by rw [hf]; rfl) = F.mapId' f.left.op.toLoc (by rw [hf]; rfl) :=
  comp_mapId'_eq_mapId' _ _ _ _

/-- The composition comparison of `F.over U` along `f ≫ g = fg` in `Over U` is that of `F` along
`f.left ≫ g.left = fg.left`. -/
lemma over_mapComp' {X Y Z : Over U} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) :
    (F.over U).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl) =
      F.mapComp' g.left.op.toLoc f.left.op.toLoc fg.left.op.toLoc (by rw [← h]; rfl) :=
  comp_mapComp'_eq_mapComp' _ _ _ _ _ _

/-- Pulling back a morphism between pullbacks along a morphism `g` of `Over U`, for `F.over U`, is
pulling it back along `g.left` for `F`. -/
lemma LocallyDiscreteOpToCat.pullHom_over ⦃X₁ X₂ : Over U⦄ ⦃M₁ : (F.over U).obj (.mk (op X₁))⦄
    ⦃M₂ : (F.over U).obj (.mk (op X₂))⦄ ⦃Y : Over U⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((F.over U).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((F.over U).map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : Over U⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom (F := F) (X₁ := X₁.left) (X₂ := X₂.left) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁.left)
        (f₂ := f₂.left) φ g.left gf₁.left
        gf₂.left (by rw [← hgf₁, Over.comp_left]) (by rw [← hgf₂, Over.comp_left]) := by
  unfold pullHom
  rw [over_mapComp' g f₁ gf₁ hgf₁, over_mapComp' g f₂ gf₂ hgf₂]
  -- Both sides now use the comparisons of `F`; the pullback functors `(F.over U).map g.op.toLoc`
  -- and `F.map g.left.op.toLoc` agree by unfolding `Pseudofunctor.comp`.
  rfl

namespace DescentData

variable (F) {ι : Type t} {S : Over U} {X : ι → Over U} (f : ∀ i, X i ⟶ S)

/-- A descent datum for `F.over U` relative to `f` gives one for `F` relative to the underlying
family `(f i).left`, with the same objects: over `q : Y ⟶ S.left`, its morphisms are those of the
given descent datum over the object `Over.mk (q ≫ S.hom)` of `Over U`. -/
@[expose, simps]
def overFunctorObj (D : (F.over U).DescentData f) : F.DescentData (fun i ↦ (f i).left) where
  obj := D.obj
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
    rwa [pullHom_over] at this
  hom_self Y q i g hg := D.hom_self _ _ (by ext; exact hg)
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := D.hom_comp _ _ _ _ _ _ _

/-- A descent datum for `F` relative to the underlying family `(f i).left` gives one for
`F.over U` relative to `f`, with the same objects: over `q : Y ⟶ S` in `Over U`, its morphisms
are those of the given descent datum over `q.left`. -/
@[expose, simps]
def overInverseObj (D : F.DescentData (fun i ↦ (f i).left)) : (F.over U).DescentData f where
  obj := D.obj
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    D.hom q.left f₁.left f₂.left (by rw [← hf₁, Over.comp_left]) (by rw [← hf₂, Over.comp_left])
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    exact (pullHom_over (F := F) _ _ _ _ _ _).trans (D.pullHom_hom _ _ _
      (by rw [← hq, Over.comp_left]) _ _ (by rw [← hf₁, Over.comp_left])
      (by rw [← hf₂, Over.comp_left]) _ _ (by rw [← hgf₁, Over.comp_left])
      (by rw [← hgf₂, Over.comp_left]))
  hom_self Y q i g hg := D.hom_self _ _ (by rw [← hg, Over.comp_left])
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := D.hom_comp _ _ _ _ (by rw [← hf₁, Over.comp_left])
    (by rw [← hf₂, Over.comp_left]) (by rw [← hf₃, Over.comp_left])

variable {F f} in
/-- The morphisms of a descent datum for `F.over U` over an object `Y` of `Over U` depend only on
`Y.left`: they agree with those over the object `Over.mk (q.left ≫ S.hom)`, which has the same
underlying object as `Y`. -/
lemma hom_eq_hom_homMk (D : (F.over U).DescentData f) ⦃Y : Over U⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom (Y := Over.mk (q.left ≫ S.hom)) (Over.homMk q.left)
      (Over.homMk f₁.left (by simp [← hf₁])) (Over.homMk f₂.left (by simp [← hf₂]))
      (by ext; simp [← hf₁]) (by ext; simp [← hf₂]) := by
  have h := D.pullHom_hom (Y' := Over.mk (q.left ≫ S.hom)) (Over.homMk (𝟙 Y.left) (by simp)) q
    (Over.homMk q.left) (by ext; simp) f₁ f₂ hf₁ hf₂ (Over.homMk f₁.left (by simp [← hf₁]))
    (Over.homMk f₂.left (by simp [← hf₂])) (by ext; simp) (by ext; simp)
  rw [← h, pullHom_over (F := F)]
  -- The underlying morphism of `Over.homMk (𝟙 Y.left)` is `𝟙 Y.left` by definition, so this is
  -- the pullback along an identity.
  exact (pullHom_id (F := F) _).symm

/-- The functor from descent data for `F.over U` relative to `f` to descent data for `F`
relative to the underlying family of `f`. -/
@[expose, simps]
def overFunctor : (F.over U).DescentData f ⥤ F.DescentData (fun i ↦ (f i).left) where
  obj := overFunctorObj F f
  map φ :=
    { hom := φ.hom
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := φ.comm (Y := Over.mk (q ≫ S.hom)) (Over.homMk q)
        (Over.homMk f₁ (by simp [← hf₁])) (Over.homMk f₂ (by simp [← hf₂])) (by ext; exact hf₁)
        (by ext; exact hf₂) }

/-- The functor from descent data for `F` relative to the underlying family of `f` to descent
data for `F.over U` relative to `f`. -/
@[expose, simps]
def overInverse : F.DescentData (fun i ↦ (f i).left) ⥤ (F.over U).DescentData f where
  obj := overInverseObj F f
  map φ :=
    { hom := φ.hom
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := φ.comm q.left f₁.left f₂.left
        (by rw [← hf₁, Over.comp_left]) (by rw [← hf₂, Over.comp_left]) }

/-- Descent data for `F.over U` relative to a family `f` of morphisms of `Over U` are
equivalent to descent data for `F` relative to the underlying family `(f i).left` of morphisms of
`C`. Both functors keep the objects and the morphisms of descent data. -/
@[expose, simps! functor inverse]
def overEquivalence : (F.over U).DescentData f ≌ F.DescentData (fun i ↦ (f i).left) where
  functor := overFunctor F f
  inverse := overInverse F f
  -- In the compatibility conditions below, the fibres of `F.over U` and of `F` agree only after
  -- unfolding `Pseudofunctor.comp` and `Functor.toPseudofunctor`, so `simp` and `rw` cannot see
  -- the identities `F.map (𝟙 _)`; `erw` matches them up to this unfolding.
  unitIso := NatIso.ofComponents (fun D ↦ isoMk (fun _ ↦ Iso.refl _)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ by
      erw [Iso.refl_hom, Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id]
      exact (hom_eq_hom_homMk D q f₁ f₂ hf₁ hf₂).symm)) (fun _ ↦ by
        ext
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun D ↦ isoMk (fun _ ↦ Iso.refl _)
    (fun _ _ _ _ _ _ _ _ ↦ by
      erw [Iso.refl_hom, Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id]
      rfl)) (fun _ ↦ by
        ext
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp _ := by
    ext
    exact Category.id_comp _

/-- Pulling back an object of `F` over `S.left` along the family `f`, then passing to descent
data for `F`, is pulling it back along the underlying family of `f`. -/
def toDescentDataCompOverFunctorIso :
    (F.over U).toDescentData f ⋙ overFunctor F f ≅ F.toDescentData (fun i ↦ (f i).left) :=
  NatIso.ofComponents (fun M ↦ isoMk (fun _ ↦ Iso.refl _) (fun _ q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
      -- As in `overEquivalence`, `erw` sees the identities through the fibres of `F.over U`.
      erw [Iso.refl_hom, Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id]
      -- Both sides are the composites of the comparisons of `F.over U`, respectively `F`, which
      -- agree by `over_mapComp'`.
      have h₁ := over_mapComp' (F := F) (Over.homMk (U := Over.mk (q ≫ S.hom)) f₁
        (by simp [← hf₁])) (f i₁) (Over.homMk q) (by ext; exact hf₁)
      have h₂ := over_mapComp' (F := F) (Over.homMk (U := Over.mk (q ≫ S.hom)) f₂
        (by simp [← hf₂])) (f i₂) (Over.homMk q) (by ext; exact hf₂)
      exact congr($(h₁).inv.toNatTrans.app M ≫ $(h₂).hom.toNatTrans.app M).symm))
    (fun _ ↦ by
      ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end DescentData

variable (F U) (J : GrothendieckTopology C)

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
