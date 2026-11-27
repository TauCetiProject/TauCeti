/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.AuslanderReitenDuality

/-!
# Comparison of Auslander–Reiten translates

In an exact category with finite-length groups of Yoneda extensions, two Auslander–Reiten
dualities with the same dualizing module have canonically isomorphic translate functors.
The comparison identifies their Ext pairings. This applies when comparing a translate from
almost-split conflations with one defined using a transpose and a dual.

The component at `Z` is the comparison of two representations of `D Ext¹(Z, -)` on the
injectively stable category. Naturality uses compatibility of both pairings with pullback
of extensions, as in the determination of the translate on morphisms in Iyama, Nakaoka and Palu,
*Auslander–Reiten theory in extriangulated categories*, arXiv:1805.03776 (v3), Lemma 3.10.
-/

public section

namespace TauCeti.ExactStructure.AuslanderReitenDuality

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C} {R : Type*} [CommRing R] [Linear R C] {Q : Type w}
  [AddCommGroup Q] [Module R Q] [Module.Injective R Q] [Small.{w} R]
  (A B : E.AuslanderReitenDuality R Q)
  (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)
  (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X))

private noncomputable def translateIsoApp (Z : C) :
    A.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) ≅
      B.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) :=
  costableIsoOfBijective
    (fun X ↦ A.bijective_costablePairing_form hQ (hfin Z X))
    (fun X ↦ B.bijective_costablePairing_form hQ (hfin Z X))

/-- The canonical natural isomorphism between the translates of two Auslander–Reiten dualities
with the same dualizing module. Its components identify the two pairings with extensions. -/
noncomputable def translateIso : A.functor ≅ B.functor :=
  NatIso.ofComponents (fun Z ↦ translateIsoApp A B hQ hfin Z.as) (by
    rintro ⟨Z⟩ ⟨Z'⟩ f
    obtain ⟨u, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective
      (X := Z) (Y := Z') f
    -- Express the components on the chosen representatives so the pairing lemmas match.
    change A.functor.map (E.projectivelyTrivialIdeal.quotientFunctor.map u) ≫
        (translateIsoApp A B hQ hfin Z').hom =
      (translateIsoApp A B hQ hfin Z).hom ≫
        B.functor.map (E.projectivelyTrivialIdeal.quotientFunctor.map u)
    have hForm (W : C) :
        costablePairing (B.form W) (A.translateObj W) (translateIsoApp A B hQ hfin W).hom =
          A.form W :=
      costablePairing_costableIsoOfBijective_hom
        (fun X ↦ A.bijective_costablePairing_form hQ (hfin W X))
        (fun X ↦ B.bijective_costablePairing_form hQ (hfin W X))
    apply (B.bijective_costablePairing_form hQ (hfin Z' (A.translateObj Z))).injective
    rw [costablePairing_comp, hForm Z']
    ext ξ
    calc
      _ = A.form Z (ξ.pullback u) := by
        rw [A.costablePairing_form, ← A.stablePairing_form, stablePairing_map]
      _ = _ := by
        rw [B.costablePairing_form, ← B.linearEquiv_pullback, ← B.costablePairing_form, hForm Z])

/-- The comparison component at `Z` pairs with the second duality's universal element to give
the first duality's universal element. -/
@[simp]
theorem costablePairing_translateIso_hom (Z : C) :
    costablePairing (B.form Z) (A.translateObj Z)
      ((A.translateIso B hQ hfin).hom.app (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) =
      A.form Z :=
  costablePairing_costableIsoOfBijective_hom
    (fun X ↦ A.bijective_costablePairing_form hQ (hfin Z X))
    (fun X ↦ B.bijective_costablePairing_form hQ (hfin Z X))

/-- Postcomposition with the translate comparison identifies the two Ext pairings. -/
@[simp]
theorem linearEquiv_comp_translateIso_hom (Z X : C) (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      A.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) :
    B.linearEquiv Z X ξ
      (a ≫ (A.translateIso B hQ hfin).hom.app (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) =
      A.linearEquiv Z X ξ a := by
  rw [← B.costablePairing_form, costablePairing_comp, A.costablePairing_translateIso_hom,
    A.costablePairing_form]

/-- The translate comparison is the unique natural transformation whose components identify
the universal elements of the two dualities. -/
theorem translateIso_hom_unique (α : A.functor ⟶ B.functor)
    (hα : ∀ Z : C, costablePairing (B.form Z) (A.translateObj Z)
      (α.app (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) = A.form Z) :
    α = (A.translateIso B hQ hfin).hom := by
  ext ⟨Z⟩
  exact (B.bijective_costablePairing_form hQ (hfin Z (A.translateObj Z))).injective
    ((hα Z).trans (A.costablePairing_translateIso_hom B hQ hfin Z).symm)

/-- Postcomposition with the inverse translate comparison identifies the Ext pairings in the
reverse direction. -/
@[simp]
theorem linearEquiv_comp_translateIso_inv (Z X : C) (ξ : E.Ext1 Z X)
    (b : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      B.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) :
    A.linearEquiv Z X ξ
      (b ≫ (A.translateIso B hQ hfin).inv.app (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) =
      B.linearEquiv Z X ξ b := by
  rw [← A.linearEquiv_comp_translateIso_hom B hQ hfin, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

/-- Reversing the two dualities inverts the canonical comparison. -/
@[simp]
theorem translateIso_symm : (A.translateIso B hQ hfin).symm = B.translateIso A hQ hfin := by
  apply Iso.ext
  apply B.translateIso_hom_unique A hQ hfin
  intro Z
  exact costablePairing_costableIsoOfBijective_inv
    (fun X ↦ A.bijective_costablePairing_form hQ (hfin Z X))
    (fun X ↦ B.bijective_costablePairing_form hQ (hfin Z X))

/-- Comparing an Auslander–Reiten duality with itself gives the identity isomorphism. -/
@[simp]
theorem translateIso_refl : A.translateIso A hQ hfin = Iso.refl A.functor := by
  symm
  apply Iso.ext
  apply A.translateIso_hom_unique A hQ hfin
  intro Z
  exact costablePairing_id (A.form Z)

/-- The canonical comparisons compose across three models of Auslander–Reiten duality. -/
theorem translateIso_trans (D : E.AuslanderReitenDuality R Q) :
    A.translateIso B hQ hfin ≪≫ B.translateIso D hQ hfin = A.translateIso D hQ hfin := by
  apply Iso.ext
  apply A.translateIso_hom_unique D hQ hfin
  intro Z
  rw [Iso.trans_hom, NatTrans.comp_app, costablePairing_comp,
    B.costablePairing_translateIso_hom, A.costablePairing_translateIso_hom]

end TauCeti.ExactStructure.AuslanderReitenDuality
