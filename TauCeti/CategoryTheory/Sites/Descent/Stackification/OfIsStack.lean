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
stackification (`Obj.ofObjIso`): the local evaluations of the isomorphism are the descent
isomorphisms of `M` along the family formed by the members of `f` and of `g` together. Taking
for `g` the identity of `U`, the descent datum of `M` along any covering family is isomorphic to
the image of `M` under `Obj.toObjFunctor` (`Obj.ofObjIsoToObjFunctor`).

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

/-- The family over `ι ⊕ κ` formed by the members of `f` and of `g`. -/
abbrev sumFamily : ∀ s : ι ⊕ κ, Sum.elim X Y s ⟶ U
  | .inl i => f i
  | .inr j => g j

section

variable (M : F.obj (.mk (op U))) (hf : Sieve.ofArrows X f ∈ J U)
  (hg : Sieve.ofArrows Y g ∈ J U) [F.IsPrestack J]

/-- The morphism from the descent datum of `M` along `f` to its descent datum along `g`, whose
local evaluations are the descent isomorphisms of `M` along `sumFamily f g`. -/
def ofObjHom :
    ofDescentData f hf ((F.toDescentData f).obj M) ⟶
      ofDescentData g hg ((F.toDescentData g).obj M) :=
  Hom.ofApp
    (fun _ i j a b w ↦ ((F.toDescentData (sumFamily f g)).obj M).hom (a ≫ f i)
      (i₁ := .inl i) (i₂ := .inr j) a b rfl w.symm)
    (fun _ i j a b w _ h ha hb hha hhb ↦
      ((F.toDescentData (sumFamily f g)).obj M).pullHom_hom (i₁ := .inl i) (i₂ := .inr j) h
        (a ≫ f i) (ha ≫ f i) (by rw [← hha, Category.assoc]) a b rfl w.symm ha hb hha hhb)
    (fun _ i i' j j' a a' b b' w w' ha ↦ by
      change ((F.toDescentData (sumFamily f g)).obj M).hom (a ≫ f i) (i₁ := .inl i)
          (i₂ := .inl i') a a' rfl ha.symm ≫ _ = _ ≫
        ((F.toDescentData (sumFamily f g)).obj M).hom (a ≫ f i) (i₁ := .inr j) (i₂ := .inr j') b b'
          w.symm (w'.symm.trans ha.symm)
      exact (DescentData.hom_comp_hom ((F.toDescentData (sumFamily f g)).obj M)
        (i₁ := Sum.inl i) (i₂ := Sum.inl i') (i₃ := Sum.inr j') _ _ a a' b'
        rfl ha.symm rfl w'.symm).trans
        (DescentData.hom_comp_hom ((F.toDescentData (sumFamily f g)).obj M)
          (i₁ := Sum.inl i) (i₂ := Sum.inr j) (i₃ := Sum.inr j') _ _ a b b'
          rfl w.symm w.symm (w'.symm.trans ha.symm)).symm)

/-- The local evaluations of `ofObjHom` are the descent isomorphisms of `M` along
`sumFamily f g`. -/
lemma app_ofObjHom ⦃T : C⦄ ⦃i : ι⦄ ⦃j : κ⦄ (a : T ⟶ X i) (b : T ⟶ Y j)
    (w : a ≫ f i = b ≫ g j) :
    Hom.app (ofObjHom f g M hf hg) (i := i) (j := j) a b w =
      ((F.toDescentData (sumFamily f g)).obj M).hom (a ≫ f i) (i₁ := Sum.inl i)
        (i₂ := Sum.inr j) a b rfl w.symm :=
  Hom.app_ofApp _ _ _ _ _ _

omit [HasPullbacks C] [F.IsPrestack J] in
/-- The descent isomorphisms of `M` along `sumFamily g f` are those along `sumFamily f g`, with
the two summands exchanged. -/
lemma toDescentData_sumFamily_hom_swap ⦃T : C⦄ (q : T ⟶ U) ⦃i : ι⦄ ⦃j : κ⦄ (b : T ⟶ Y j)
    (a : T ⟶ X i) (hb : b ≫ g j = q) (ha : a ≫ f i = q) :
    ((F.toDescentData (sumFamily g f)).obj M).hom q (i₁ := Sum.inl j) (i₂ := Sum.inr i) b a hb ha =
      ((F.toDescentData (sumFamily f g)).obj M).hom q (i₁ := Sum.inr j) (i₂ := Sum.inl i) b a hb
        ha :=
  rfl

/-- `ofObjHom g f` is a left inverse of `ofObjHom f g`. -/
lemma ofObjHom_comp_ofObjHom :
    ofObjHom f g M hf hg ≫ ofObjHom g f M hg hf = 𝟙 _ := by
  refine Hom.ext_of_sieve _ hg fun T i i' a a' w hR ↦ ?_
  obtain ⟨j, b, hb⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hR
  rw [comp_app _ _ a b a' w hb (hb.symm.trans w), app_ofObjHom, app_ofObjHom, id_app]
  exact (congrArg (_ ≫ ·) (toDescentData_sumFamily_hom_swap f g M (b ≫ g j) b a' rfl
    (hb.symm.trans w).symm)).trans
    (DescentData.hom_comp_hom ((F.toDescentData (sumFamily f g)).obj M)
      (i₁ := Sum.inl i) (i₂ := Sum.inr j) (i₃ := Sum.inl i') _ _ a b a'
      rfl hb.symm rfl (hb.symm.trans w).symm)

/-- **Descent data of an object along two covering families are isomorphic.** For a prestack `F`,
an object `M` of `F` over `U` and two `w`-small covering families `f` and `g` of `U`, the descent
data of `M` along `f` and along `g` are isomorphic in `Obj J F U`. -/
@[expose, simps]
def ofObjIso :
    ofDescentData f hf ((F.toDescentData f).obj M) ≅
      ofDescentData g hg ((F.toDescentData g).obj M) where
  hom := ofObjHom f g M hf hg
  inv := ofObjHom g f M hg hf
  hom_inv_id := ofObjHom_comp_ofObjHom f g M hf hg
  inv_hom_id := ofObjHom_comp_ofObjHom g f M hg hf

/-- The descent datum of `M` along a covering family `f` is isomorphic to the image of `M` under
`toObjFunctor`, its descent datum along the identity of `U`. -/
abbrev ofObjIsoToObjFunctor :
    ofDescentData f hf ((F.toDescentData f).obj M) ≅ (toObjFunctor.{w} J F U).obj M :=
  ofObjIso f (fun _ : PUnit.{w + 1} ↦ 𝟙 U) M hf (ofArrows_id_mem U)

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
