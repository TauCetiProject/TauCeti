/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Bicategory.Functor.Pi
public import TauCeti.CategoryTheory.Pi.Basic

/-!
# Products of stacks

Let `F i`, for `i : I`, be a family of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` and
`TauCeti.Stack.pi F` their product. Descent data for the product along a family of morphisms
`f j : X j ⟶ S` are families of descent data for the `F i` (`pi.descentDataEquiv`), compatibly
with the descent functors (`pi.toDescentDataCompDescentDataEquivIso`). Hence, for a Grothendieck
topology `J` on `C`, the product of prestacks is a prestack (`pi.isPrestack`) and the product of
stacks is a stack (`pi.isStack`); in particular the terminal pseudofunctor is a stack
(`terminal.isStack`). With the 2-fiber products of stacks
(`TauCeti.Stack.twoFiberProduct.isStack`), stacks are closed under products, 2-fiber products
and the terminal object. These three constructions do not generate all finite weighted 2-limits
(inserters, for instance, are not among them), so closure under general finite 2-limits is not
claimed here.

## Main declarations

* `TauCeti.Stack.pi.descentDataEquiv`: the equivalence between descent data for the product and
  families of descent data for the factors.
* `TauCeti.Stack.pi.isPrestack`, `TauCeti.Stack.pi.isStack`: the product of prestacks
  (respectively stacks) is a prestack (respectively stack).
* `TauCeti.Stack.terminal.isStack`: the terminal pseudofunctor is a stack.
-/

open CategoryTheory Bicategory Opposite

universe t w u' v' v u

@[expose] public section

namespace TauCeti.Stack.pi

open Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {I : Type w}
  {F : I → Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}

@[simp]
lemma pullHom_apply ⦃X₁ X₂ : C⦄ ⦃M₁ : (pi F).obj (.mk (op X₁))⦄ ⦃M₂ : (pi F).obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((pi F).map f₁.op.toLoc).toFunctor.obj M₁ ⟶ ((pi F).map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) (i : I) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ i = pullHom (F := F i) (φ i) g gf₁ gf₂ hgf₁ hgf₂ := by
  simp only [pullHom, comp_apply', map_map_apply, mapComp'_hom_app_apply,
    mapComp'_inv_app_apply]
  -- The two sides differ only in the implicit objects of the compositions.
  rfl

/-- An identity component on either side of a morphism between images of two functors can be
dropped. This discharges the compatibility conditions of `DescentData.isoMk` for identity
components: there the identities live in the fibers of `pi F`, which are product categories only
definitionally, so `Functor.map_id` does not rewrite them directly. -/
private lemma map_id_comp_eq_comp_map_id {D₁ D₂ E : Type*} [Category D₁] [Category D₂]
    [Category E] (G : D₁ ⥤ E) (G' : D₂ ⥤ E) {x : D₁} {y : D₂} {φ ψ : G.obj x ⟶ G'.obj y}
    (h : φ = ψ) : G.map (𝟙 x) ≫ φ = ψ ≫ G'.map (𝟙 y) := by
  simp [h]

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ j, X j ⟶ S)

/-- The `i`-th projection of descent data for the product. -/
@[simps]
def descentDataπ (i : I) : (pi F).DescentData f ⥤ (F i).DescentData f where
  obj D :=
    { obj j := D.obj j i
      hom _ q _ _ f₁ f₂ hf₁ hf₂ := D.hom q f₁ f₂ hf₁ hf₂ i
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← pullHom_apply, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self _ q _ g hg := congrFun (D.hom_self q g hg) i
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := congrFun (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) i }
  map φ :=
    { hom j := φ.hom j i
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := congrFun (φ.comm q f₁ f₂ hf₁ hf₂) i }

/-- The functor sending a family of descent data for the factors to the descent datum for the
product with those components. -/
@[simps!]
def descentDataMk : (∀ i, (F i).DescentData f) ⥤ (pi F).DescentData f where
  obj D :=
    { obj j := (fun i ↦ (D i).obj j : (pi F).obj (.mk (op (X j))))
      hom _ q _ _ f₁ f₂ hf₁ hf₂ i := (D i).hom q f₁ f₂ hf₁ hf₂
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := funext fun i ↦
        (pullHom_apply _ g _ _ hgf₁ hgf₂ i).trans
          ((D i).pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
      hom_self _ q _ g hg := funext fun i ↦ (D i).hom_self q g hg
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        funext fun i ↦ (D i).hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃ }
  map φ :=
    { hom j i := (φ i).hom j
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := funext fun i ↦ (φ i).comm q f₁ f₂ hf₁ hf₂ }

/-- Descent data for the product of a family of pseudofunctors are families of descent data for
the factors. -/
@[simps! functor_obj inverse_obj]
def descentDataEquiv : (pi F).DescentData f ≌ ∀ i, (F i).DescentData f where
  functor := Functor.pi' (descentDataπ f)
  inverse := descentDataMk f
  -- Both composites are the identity up to eta-expansion of families and of structures.
  unitIso := NatIso.ofComponents
    (fun D ↦ DescentData.isoMk (fun j ↦ Iso.refl (D.obj j)) (fun _ _ _ _ _ _ _ _ ↦ by
      dsimp only [Iso.refl_hom]
      exact map_id_comp_eq_comp_map_id _ _ rfl))
    (fun _ ↦ by
      ext j
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents
    (fun D ↦ Pi.isoMk fun i ↦ DescentData.isoMk (fun j ↦ Iso.refl ((D i).obj j))
      (fun _ _ _ _ _ _ _ _ ↦ by
        dsimp only [Iso.refl_hom]
        exact map_id_comp_eq_comp_map_id _ _ rfl))
    (fun _ ↦ by
      funext i
      ext j
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp _ := by
    funext i
    ext j
    exact Category.comp_id _

@[simp]
lemma toDescentData_obj_hom_apply (M : (pi F).obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S) ⦃j₁ j₂ : ι⦄
    (f₁ : Y ⟶ X j₁) (f₂ : Y ⟶ X j₂) (hf₁ : f₁ ≫ f j₁ = q) (hf₂ : f₂ ≫ f j₂ = q) (i : I) :
    (((pi F).toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ i =
      (((F i).toDescentData f).obj (M i)).hom q f₁ f₂ hf₁ hf₂ := by
  -- Unfold `toDescentData` on the product, whose comparisons are only definitionally those of
  -- `Pseudofunctor.DescentData.ofObj`.
  change (((pi F).mapComp' (f j₁).op.toLoc f₁.op.toLoc q.op.toLoc _).inv.toNatTrans.app M ≫
    ((pi F).mapComp' (f j₂).op.toLoc f₂.op.toLoc q.op.toLoc _).hom.toNatTrans.app M) i = _
  rw [comp_apply', mapComp'_inv_app_apply, mapComp'_hom_app_apply]
  rfl

/-- Under `descentDataEquiv`, the descent functor of the product is the product of the descent
functors of the factors. -/
@[simps!]
def toDescentDataCompDescentDataEquivIso :
    (pi F).toDescentData f ⋙ (descentDataEquiv f).functor ≅
      Functor.pi fun i ↦ (F i).toDescentData f :=
  NatIso.ofComponents (fun M ↦ Pi.isoMk fun i ↦ DescentData.isoMk
    (fun j ↦ Iso.refl (((F i).map (f j).op.toLoc).toFunctor.obj (M i)))
    (fun Y q j₁ j₂ f₁ f₂ hf₁ hf₂ ↦ by
      dsimp only [Iso.refl_hom]
      exact map_id_comp_eq_comp_map_id _ _
        (toDescentData_obj_hom_apply f M q f₁ f₂ hf₁ hf₂ i).symm))
    (fun _ ↦ by
      funext i
      ext j
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable {f}

/-- If the descent functors of all the `F i` along a family of morphisms are fully faithful, so
is the descent functor of the product. -/
noncomputable def fullyFaithfulToDescentData (hF : ∀ i, ((F i).toDescentData f).FullyFaithful) :
    ((pi F).toDescentData f).FullyFaithful :=
  ((Functor.FullyFaithful.pi hF).comp (descentDataEquiv f).fullyFaithfulInverse).ofIso
    (Iso.isoCompInverse (toDescentDataCompDescentDataEquivIso f)).symm

/-- If the descent functors of all the `F i` along a family of morphisms are essentially
surjective, so is the descent functor of the product. -/
lemma essSurj_toDescentData [∀ i, ((F i).toDescentData f).EssSurj] :
    ((pi F).toDescentData f).EssSurj :=
  -- The source of `Functor.pi` is the product category, only definitionally the fiber of `pi F`,
  -- so the instances are passed explicitly.
  @Functor.essSurj_of_iso _ _ _ _ _ _
    (@Functor.essSurj_comp _ _ _ _ _ _ _ _
      (Functor.essSurj_pi fun i ↦ (F i).toDescentData f) inferInstance)
    (Iso.isoCompInverse (toDescentDataCompDescentDataEquivIso f)).symm

variable {J : GrothendieckTopology C}

/-- The product of prestacks is a prestack. -/
instance isPrestack [∀ i, (F i).IsPrestack J] : (pi F).IsPrestack J :=
  IsPrestack.of_isPrestackFor fun _ R hR ↦
    ⟨⟨fullyFaithfulToDescentData fun i ↦ ((F i).isPrestackFor' R hR).fullyFaithful⟩⟩

/-- The product of stacks is a stack. -/
instance isStack [∀ i, (F i).IsStack J] : (pi F).IsStack J where
  essSurj_of_sieve R hR :=
    have := fun i ↦ IsStack.essSurj_of_sieve (F i) R hR
    essSurj_toDescentData

end TauCeti.Stack.pi

namespace TauCeti.Stack.terminal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The terminal pseudofunctor is a stack. -/
instance isStack : (terminal.{u', v'} (C := C)).IsStack J :=
  have (i : PEmpty.{1}) :
      (i.elim : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}).IsStack J := i.elim
  pi.isStack

end TauCeti.Stack.terminal

end
