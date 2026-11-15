/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Closed.Functor

/-!
# Internal Hom under a monoidal equivalence

An equivalence preserves a chosen internal Hom as soon as its tensor comparison with the
source object is invertible. The internal-Hom structures on the two categories may be chosen
independently. The result identifies the canonical comparison, characterized by evaluation,
as an isomorphism; it does not replace either chosen closed structure by a transported one.

The proof uses the hom-set equivalence of a fully faithful functor and the two tensor--Hom
adjunctions. Essential surjectivity then lets Yoneda detect the comparison's invertibility.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

universe u₁ u₂ v₁ v₂

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- An equivalence commutes with internal Hom from `A` when its tensor comparison with `A`
is invertible. Only the tensor comparisons with this left factor are needed; there is no
hypothesis on the unit comparison. -/
theorem CategoryTheory.Functor.ihomComparison_isIso_of_equivalence
    (F : C ⥤ D) [F.LaxMonoidal] [F.IsEquivalence]
    (A : C) [Closed A] [Closed (F.obj A)]
    [∀ P, IsIso (Functor.LaxMonoidal.μ F A P)] : IsIso (F.ihomComparison A) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro B
  let FF := Functor.FullyFaithful.ofFullyFaithful F
  apply isIso_of_yoneda_map_bijective
  intro T
  let P := F.objPreimage T
  let e : F.obj P ≅ T := F.objObjPreimageIso T
  let E : (T ⟶ F.obj ((ihom A).obj B)) ≃
      (T ⟶ (ihom (F.obj A)).obj (F.obj B)) :=
    (Iso.homCongr e.symm (Iso.refl _)).trans <|
      FF.homEquiv.symm.trans <|
        ((ihom.adjunction A).homEquiv P B).symm.trans <|
          FF.homEquiv.trans <|
            (Iso.homCongr (asIso (Functor.LaxMonoidal.μ F A P)).symm (Iso.refl _)).trans <|
              ((ihom.adjunction (F.obj A)).homEquiv (F.obj P) (F.obj B)).trans
                (Iso.homCongr e (Iso.refl _))
  have hE (x : T ⟶ F.obj ((ihom A).obj B)) : E x = x ≫ (F.ihomComparison A).app B := by
    dsimp only [E, Equiv.trans_apply, Iso.homCongr, Functor.FullyFaithful.homEquiv]
    simp only [Equiv.coe_fn_mk, Equiv.symm_mk, Iso.refl_hom, Iso.symm_inv,
      asIso_hom, Category.comp_id]
    -- The hom-set equivalence is currying after the tensorator, up to the object isomorphism.
    change e.inv ≫ curry (Functor.LaxMonoidal.μ F A P ≫
      F.map (uncurry (FF.preimage (e.hom ≫ x)))) = _
    apply (cancel_epi e.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    apply uncurry_injective
    have hn := Functor.LaxMonoidal.μ_natural_right F A (FF.preimage (e.hom ≫ x))
    rw [FF.map_preimage] at hn
    rw [uncurry_curry, ← Category.assoc, uncurry_natural_left, Functor.uncurry_ihomComparison,
      ← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ← uncurry_eq]
  exact (funext hE) ▸ E.bijective

end
