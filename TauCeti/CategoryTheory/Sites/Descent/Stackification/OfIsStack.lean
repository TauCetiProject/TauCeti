/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.Unit

/-!
# The stackification of a stack

Let `F` be a prestack for a Grothendieck topology `J` on a category `C` with pullbacks, and `M` an
object of `F` over `U`. For any two `w`-small covering families `f` and `g` of `U`, the descent
data of `M` along `f` and along `g` are isomorphic objects of the fibre `Obj J F U` of the
stackification (`Obj.ofObjIso`): both are pullbacks along the identity of `U` of the image of
`M` under `Obj.toObjFunctor` (`Obj.PullbackData.ofObj`), so `Obj.PullbackData.isoOfData`
identifies them. In particular the descent datum of `M` along any covering family is isomorphic
to the image of `M` under `Obj.toObjFunctor` (`Obj.ofObjIsoToObjFunctor`).

When `F` is a stack, every descent datum along a covering family is effective, so every object of
`Obj J F U` is in the essential image of `Obj.toObjFunctor`. As this functor is fully faithful
(`Obj.fullyFaithfulToObjFunctor`), it is an equivalence `F.obj U ≌ Obj J F U`
(`Obj.toObjEquivalence`): stackification fixes a stack, fibre by fibre (part of Stacks,
Lemma 02ZN).

## Main declarations

* `TauCeti.Stack.Stackification.Obj.ofObjIso`: the descent data of an object along two covering
  families are isomorphic.
* `TauCeti.Stack.Stackification.Obj.essSurj_toObjFunctor`: for a stack, `toObjFunctor` is
  essentially surjective.
* `TauCeti.Stack.Stackification.Obj.toObjEquivalence`: for a stack, `toObjFunctor` is an
  equivalence.

## References

* [Stacks Project, Lemma 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

public section

noncomputable section

universe w v' u' v u

open CategoryTheory Limits Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat

namespace TauCeti.Stack.Stackification.Obj

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [HasPullbacks C] {U : C}
  {ι κ : Type w} {X : ι → C} {Y : κ → C} (f : ∀ i, X i ⟶ U) (g : ∀ j, Y j ⟶ U)

section

variable (M : F.obj (.mk (op U))) (hf : Sieve.ofArrows X f ∈ J U)
  (hg : Sieve.ofArrows Y g ∈ J U) [F.IsPrestack J]

/-- The descent datum of `M` along a covering family `f` is the pullback along the identity of `U`
of the image of `M` under `toObjFunctor`, through the comparison isomorphisms
`b^* (f i)^* M ≅ c^* M ≅ c^* (𝟙 U)^* M` for `b ≫ f i = c`. -/
def PullbackData.ofObj :
    PullbackData (𝟙 U) ((toObjFunctor.{w} J F U).obj M)
      (ofDescentData f hf ((F.toDescentData f).obj M)) where
  α _ := ⟨⟩
  β i := f i
  w _ := rfl
  iso T i b c h :=
    { hom := (F.mapComp' (f i).op.toLoc b.op.toLoc c.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← h])).inv.toNatTrans.app M ≫
        (F.mapComp' (𝟙 U).op.toLoc c.op.toLoc c.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Category.comp_id])).hom.toNatTrans.app M
      inv := (F.mapComp' (𝟙 U).op.toLoc c.op.toLoc c.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Category.comp_id])).inv.toNatTrans.app M ≫
        (F.mapComp' (f i).op.toLoc b.op.toLoc c.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← h])).hom.toNatTrans.app M
      hom_inv_id := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (Cat.Hom.hom_inv_id_toNatTrans_app_assoc _ _ _)).trans
          (Cat.Hom.inv_hom_id_toNatTrans_app _ _))
      inv_hom_id := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (Cat.Hom.hom_inv_id_toNatTrans_app_assoc _ _ _)).trans
          (Cat.Hom.inv_hom_id_toNatTrans_app _ _)) }
  pullHom_iso T i b c h T' g gb gc hgb hgc :=
    (pullHom_comp _ _ g gb gc gc hgb hgc hgc).trans (congrArg₂ (· ≫ ·)
      (pullHom_mapComp'_inv _ _ _ _ h _ _ _ hgb hgc)
      (pullHom_mapComp'_hom _ _ _ _ (Category.comp_id c) _ _ _ hgc hgc))
  hom_eq T i i' q' b b' hb hb' c c' h h' := by
    obtain rfl : c = q' := h.symm.trans hb
    obtain rfl : c' = c := h'.symm.trans hb'
    -- The objects of the fibre and the sources of the comparison isomorphisms agree only up to
    -- unfolding, so the cancellation is stated in the fibre and applied with `exact`.
    have key {A B D E : F.obj (.mk (op T))} (x : A ⟶ B) (e : B ≅ D) (y : D ⟶ D) (hy : y = 𝟙 D)
        (z : B ⟶ E) : x ≫ z = (x ≫ e.hom) ≫ y ≫ e.inv ≫ z := by
      simp [hy]
    exact key _ ((Cat.Hom.toNatIso (F.mapComp' _ _ _
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Category.comp_id]))).app M) _
      (DescentData.hom_self _ _ _ rfl) _

/-- **Descent data of an object along two covering families are isomorphic.** For a prestack `F`,
an object `M` of `F` over `U` and two `w`-small covering families `f` and `g` of `U`, the descent
data of `M` along `f` and along `g` are isomorphic in `Obj J F U`, as pullbacks of the image of
`M` under `toObjFunctor` along the identity of `U`. -/
abbrev ofObjIso :
    ofDescentData f hf ((F.toDescentData f).obj M) ≅
      ofDescentData g hg ((F.toDescentData g).obj M) :=
  PullbackData.isoOfData (PullbackData.ofObj f M hf) (PullbackData.ofObj g M hg)

/-- The descent datum of `M` along a covering family `f` is isomorphic to the image of `M` under
`toObjFunctor`, its descent datum along the identity of `U`. -/
abbrev ofObjIsoToObjFunctor :
    ofDescentData f hf ((F.toDescentData f).obj M) ≅ (toObjFunctor.{w} J F U).obj M :=
  PullbackData.isoOfData (PullbackData.ofObj f M hf) (PullbackData.refl _)

end

section IsStack

variable (J F) [F.IsStack J]

/-- **Stackification fixes a stack, essential surjectivity.** For a stack `F`, every descent
datum along a covering family is isomorphic to the image under `toObjFunctor` of an object of
`F`. -/
instance essSurj_toObjFunctor (U : C) : (toObjFunctor.{w} J F U).EssSurj where
  mem_essImage A := by
    obtain ⟨ι, X, f, hf, D⟩ := A
    have := F.isEquivalence_toDescentData f hf
    exact ⟨(F.toDescentData f).objPreimage D, ⟨(ofObjIsoToObjFunctor f _ hf).symm ≪≫
      (ofDescentDataFunctor f hf).mapIso ((F.toDescentData f).objObjPreimageIso D)⟩⟩

/-- For a stack `F`, `toObjFunctor` is an equivalence. -/
instance isEquivalence_toObjFunctor (U : C) : (toObjFunctor.{w} J F U).IsEquivalence :=
  have := (fullyFaithfulToObjFunctor.{w} J F U).full
  have := (fullyFaithfulToObjFunctor.{w} J F U).faithful
  { }

/-- **Stackification fixes a stack**, fibre by fibre: for a stack `F`, the fibre `F.obj U` is
equivalent to the fibre `Obj J F U` of descent data along `w`-small covering families, through
`toObjFunctor` (part of Stacks, Lemma 02ZN). -/
abbrev toObjEquivalence (U : C) : F.obj (.mk (op U)) ≌ Obj.{w} J F U :=
  (toObjFunctor.{w} J F U).asEquivalence

end IsStack

end TauCeti.Stack.Stackification.Obj
