/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Formula
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.StableEquivalence
public import TauCeti.Algebra.Category.ModuleCat.Ext.FiniteLength
import TauCeti.CategoryTheory.Linear.FullyFaithful
import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# Naturality of the Auslander–Reiten formula in the presented module

For a finitely presented module `X`, the Auslander–Reiten formula identifies the dual of
`Ext¹(X, N)` with morphisms `N ⟶ D Tr X` modulo maps factoring through injectives. For a map
`t : X ⟶ X'` lifted to finite projective presentations, the dual of pullback along `t`
corresponds to postcomposition with the class of `D Tr(t)`.

The proof uses the identification of the pairing with the defect formula evaluated on an
injective copresentation of `N`. The naturality of the contravariant defect in `X` comes from
functoriality of base change, and the naturality of the covariant defect comes from
postcomposition on Hom. Using the stable translate makes this naturality independent of a choice
of lifts. Over an Artin algebra, Matlis biduality turns the pairing into the first
Auslander–Reiten formula for finitely generated modules.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365**
  (2003), 267–270, second Corollary, p. 269.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti TauCeti.ExactStructure LinearMap
open scoped ModuleCat.Algebra

universe u v w

variable (R : Type u) {A : Type v} (E : Type w) [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup E] [Module R E] [Module.Injective R E] [Small.{w} R]
  {X X' : ModuleCat.{max u v w} A} (P : FiniteProjectivePresentation X)
  (P' : FiniteProjectivePresentation X') {t : X ⟶ X'}
  {t₀ : P.P₀ →ₗ[A] P'.P₀} {t₁ : P.P₁ →ₗ[A] P'.P₁}

/-- For a morphism lifted to finite projective presentations, the dual of pullback on
`Ext¹(-, N)` corresponds to postcomposition with the class of `D Tr(t)`. -/
theorem dualExt1EquivCostableHom_comap {N N' : ModuleCat.{max u v w} A}
    (e : (ExactStructure.abelian _).Extension N' N)
    (he : (ExactStructure.abelian _).isInjective e.obj)
    (ht₀ : P'.π ∘ₗ t₀ = t.hom ∘ₗ P.π) (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁)
    (χ : (ExactStructure.abelian _).Ext1 X N →ₗ[R] E) :
    dualExt1EquivCostableHom R E P' e he (χ ∘ₗ Ext1.pullbackLinearMap R t) =
      dualExt1EquivCostableHom R E P e he χ ≫
        (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map
          (matlisDualTransposeMap R E P P' ht₁) := by
  have hχ : (χ ∘ₗ Ext1.pullbackLinearMap R t) ∘ₗ
      (contravariantDefectEquivExt1 R e he X').toLinearMap =
        (χ ∘ₗ (contravariantDefectEquivExt1 R e he X).toLinearMap) ∘ₗ
          contravariantDefectComap R e.g.hom t.hom := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, contravariantDefectComap_mk,
      contravariantDefectEquivExt1_mk, Ext1.pullbackLinearMap_apply, Ext1.pullback_pullback,
      ofHom_comp, ofHom_hom]
  simp only [dualExt1EquivCostableHom_apply, hχ,
    Function.Exact.dualContravariantDefectEquivCovariantDefect_comap P.exact P.surjective
      P'.exact P'.surjective e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
      e.function_exact ht₀ ht₁]
  generalize Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
    e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g e.function_exact
    (χ ∘ₗ (contravariantDefectEquivExt1 R e he X).toLinearMap) = y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [homCokernelMap_mk, covariantDefectEquivCostableHom_mk,
    covariantDefectEquivCostableHom_mk, ← Functor.map_comp, matlisDualTransposeMap_eq]
  simp only [← ofHom_comp, LinearMap.comp_assoc, LinearEquiv.symm_comp_assoc]

/-- Pullback on `Ext¹(-, N)` along a morphism lifted to finite projective presentations is
adjoint under the Auslander–Reiten pairing to postcomposition with the class of `D Tr(t)`. -/
theorem auslanderReitenFormula_comap (N : ModuleCat.{max u v w} A)
    (ht₀ : P'.π ∘ₗ t₀ = t.hom ∘ₗ P.π) (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁)
    (a : (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj N ⟶
      (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj
        (matlisDualTranspose R E P)) :
    auslanderReitenFormula R E P' N
        (a ≫ (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map
          (matlisDualTransposeMap R E P P' ht₁)) =
      auslanderReitenFormula R E P N a ∘ₗ Ext1.pullbackLinearMap R t := by
  obtain ⟨χ, rfl⟩ := (auslanderReitenFormula R E P N).symm.surjective a
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply,
    auslanderReitenFormula_symm_eq_dualExt1EquivCostableHom R E P
      (InjectivePresentation.abelian N).extension
      (InjectivePresentation.abelian N).isInjective_extension_obj,
    auslanderReitenFormula_symm_eq_dualExt1EquivCostableHom R E P'
      (InjectivePresentation.abelian N).extension
      (InjectivePresentation.abelian N).isInjective_extension_obj,
    dualExt1EquivCostableHom_comap R E P P' _ _ ht₀ ht₁]

end ModuleCat

namespace TauCeti

open CategoryTheory ExactStructure

universe u v w

variable {R : Type v} [CommRing R] {A : Type u} [Ring A] [Algebra R A] {E : Type v}
  [AddCommGroup E] [Module R E] [Module.Injective R E]

open scoped ModuleCat.Algebra

local notation "S" => ExactStructure.abelian (ModuleCat A)

/-- Compare the two costable quotients via the identity on module maps. -/
private noncomputable abbrev costableComparison :
    (ExactStructure.abelian (ModuleCat.{w} A)).InjectiveStableCategory ⥤
      (ExactStructure.abelian (ModuleCat.{w} A)).injectivelyTrivialIdeal.Quotient :=
  (S).injectiveStableIdeal.lift (S).injectivelyTrivialIdeal.quotientFunctor (by
    rw [MorphismIdeal.kerIdeal_quotientFunctor]
    exact injectiveStableIdeal_le_injectivelyTrivialIdeal)

private instance faithful_costableComparison [Small.{w} A] :
    (costableComparison.{u, w} (A := A)).Faithful := by
  apply (MorphismIdeal.faithful_lift_iff _ _ _).mpr
  rw [MorphismIdeal.kerIdeal_quotientFunctor]
  exact abelian_enoughInjectives.injectivelyTrivialIdeal_eq.le

private theorem costableComparison_map {N N' : ModuleCat.{max u v} A} (f : N ⟶ N') :
    (costableComparison (A := A)).map ((S).injectiveStableFunctor.map f) =
      (S).injectivelyTrivialIdeal.quotientFunctor.map f :=
  Quotient.lift_map_functor_map _ _ _ _

private noncomputable def costableTranslateIso (X : FinitelyPresentedStableModule.{u, max u v} A) :
    (costableComparison (A := A)).obj ((stableTranslate R A E).obj X) ≅
      (S).injectivelyTrivialIdeal.quotientFunctor.obj
        (ModuleCat.matlisDualTranspose R E X.presentation) :=
  (costableComparison (A := A)).mapIso
    (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := E) X)

private noncomputable def stableAuslanderReitenFormula
    (X : FinitelyPresentedStableModule.{u, max u v} A) (N : ModuleCat.{max u v} A) :
    ((S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) ≃ₗ[R]
      ((S).Ext1 X.obj.as N →ₗ[R] E) :=
  (costableComparison (A := A)).homLinearEquiv R _ _ ≪≫ₗ
    Linear.homCongr R (Iso.refl _) (costableTranslateIso (R := R) (E := E) X) ≪≫ₗ
    ModuleCat.auslanderReitenFormula R E (FinitelyPresentedStableModule.presentation X) N

private theorem stableAuslanderReitenFormula_apply
    (X : FinitelyPresentedStableModule.{u, max u v} A) (N : ModuleCat.{max u v} A)
    (a : (S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) :
    stableAuslanderReitenFormula (R := R) (E := E) X N a =
      ModuleCat.auslanderReitenFormula R E (FinitelyPresentedStableModule.presentation X) N
        ((costableComparison (A := A)).map a ≫
          (costableTranslateIso (R := R) (E := E) X).hom) := by
  simp only [stableAuslanderReitenFormula, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Functor.homLinearEquiv_apply, Iso.refl_inv, Category.id_comp]

variable [IsArtinianRing R] [Module.Finite R A]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

/-- **The first Auslander–Reiten formula.** Over an Artin algebra, for finitely generated modules
`X` and `N`, `Ext¹(X, N)` is the Matlis dual of maps from `N` to `τX` modulo injectives.
Here `τ` is the stable translate `D Tr`, and the dual is taken with respect to an injective
`R`-module `E` whose socle contains one copy of each simple `R`-module. Yoneda extensions are
computed in `ModuleCat A`. -/
noncomputable def ext1EquivDualCostableHom
    (X : FinitelyPresentedStableModule.{u, max u v} A) (N : ModuleCat.{max u v} A)
    [Module.Finite A N] :
    (S).Ext1 X.obj.as N ≃ₗ[R]
      (((S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) →ₗ[R] E) :=
  have : Module.FinitePresentation A X.obj.as := X.property
  (LinearEquiv.ofBijective LinearMap.applyₗ
    (bijective_applyₗ_of_forall_isMaximal hE (ModuleCat.isFiniteLength_ext1 R X.obj.as N))) ≪≫ₗ
    ((stableAuslanderReitenFormula (R := R) (E := E) X N).arrowCongr
      (LinearEquiv.refl R E)).symm

private theorem ext1EquivDualCostableHom_apply_eq_pairing
    (X : FinitelyPresentedStableModule.{u, max u v} A) {N : ModuleCat.{max u v} A}
    [Module.Finite A N] (ξ : (S).Ext1 X.obj.as N)
    (a : (S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) :
    ext1EquivDualCostableHom hE X N ξ a =
      stableAuslanderReitenFormula (R := R) (E := E) X N a ξ :=
  rfl

/-- On the stable class of a map to the dual transpose of the chosen presentation,
the first Auslander–Reiten formula evaluates the Auslander–Reiten form on the pushout. -/
@[simp]
theorem ext1EquivDualCostableHom_apply
    (X : FinitelyPresentedStableModule.{u, max u v} A) {N : ModuleCat.{max u v} A}
    [Module.Finite A N] (ξ : (S).Ext1 X.obj.as N)
    (a : N ⟶ ModuleCat.matlisDualTranspose R E X.presentation) :
    ext1EquivDualCostableHom hE X N ξ
      ((S).injectiveStableFunctor.map a ≫
        (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := E) X).inv) =
      ModuleCat.auslanderReitenForm R E X.presentation (ξ.pushout a) := by
  have hinv : (costableComparison (A := A)).map
      (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := E) X).inv =
        (costableTranslateIso (R := R) (E := E) X).inv := rfl
  rw [ext1EquivDualCostableHom_apply_eq_pairing, stableAuslanderReitenFormula_apply,
    Functor.map_comp (costableComparison (A := A)), hinv, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, costableComparison_map a, ModuleCat.auslanderReitenFormula_map_apply]

/-- Pullback along a representative `t` of a stable morphism `g` corresponds to the dual
of postcomposition with `τg`. -/
theorem ext1EquivDualCostableHom_pullback
    {X X' : FinitelyPresentedStableModule.{u, max u v} A} (g : X ⟶ X')
    (t : X.obj.as ⟶ X'.obj.as) (ht : (S).projectiveStableFunctor.map t = g.hom)
    {N : ModuleCat.{max u v} A} [Module.Finite A N] (ξ : (S).Ext1 X'.obj.as N)
    (a : (S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) :
    ext1EquivDualCostableHom hE X N (ξ.pullback t) a =
      ext1EquivDualCostableHom hE X' N ξ (a ≫ (stableTranslate R A E).map g) := by
  obtain ⟨t₀, t₁, ht₀, ht₁⟩ := exists_lift_projective_presentation
    X.presentation.exact.linearMap_comp_eq_zero X'.presentation.exact X'.presentation.surjective
    t.hom
  have hg : (ObjectProperty.homMk ((S).projectiveStableFunctor.map t) : X ⟶ X') = g :=
    ObjectProperty.hom_ext _ ht
  -- Compare the chosen translate with the lift on presentations in the costable quotient.
  have hτ := stableTranslateObjIsoMatlisDualTranspose_naturality (R := R) (E := E) t ht₀ ht₁
  rw [hg] at hτ
  have h : (costableComparison (A := A)).map ((stableTranslate R A E).map g) ≫
      (costableTranslateIso (R := R) (E := E) X').hom =
    (costableTranslateIso (R := R) (E := E) X).hom ≫
      (S).injectivelyTrivialIdeal.quotientFunctor.map
        (ModuleCat.matlisDualTransposeMap R E X.presentation X'.presentation ht₁) := by
    have hm := congrArg (costableComparison (A := A)).map hτ
    simp only [Functor.map_comp (costableComparison (A := A))] at hm
    exact hm.trans (congrArg (_ ≫ ·) (costableComparison_map _))
  rw [ext1EquivDualCostableHom_apply_eq_pairing, ext1EquivDualCostableHom_apply_eq_pairing,
    stableAuslanderReitenFormula_apply, stableAuslanderReitenFormula_apply,
    Functor.map_comp (costableComparison (A := A)), Category.assoc, h, ← Category.assoc,
    ModuleCat.auslanderReitenFormula_comap R E _ _ _ ht₀ ht₁, LinearMap.comp_apply,
    Ext1.pullbackLinearMap_apply]

/-- Pushout in the coefficient module corresponds to the dual of precomposition with its
costable class. -/
theorem ext1EquivDualCostableHom_pushout
    (X : FinitelyPresentedStableModule.{u, max u v} A) {N N' : ModuleCat.{max u v} A}
    [Module.Finite A N] [Module.Finite A N'] (f : N ⟶ N') (ξ : (S).Ext1 X.obj.as N)
    (a : (S).injectiveStableFunctor.obj N' ⟶ (stableTranslate R A E).obj X) :
    ext1EquivDualCostableHom hE X N' (ξ.pushout f) a =
      ext1EquivDualCostableHom hE X N ξ ((S).injectiveStableFunctor.map f ≫ a) := by
  rw [ext1EquivDualCostableHom_apply_eq_pairing, ext1EquivDualCostableHom_apply_eq_pairing,
    stableAuslanderReitenFormula_apply, stableAuslanderReitenFormula_apply,
    Functor.map_comp (costableComparison (A := A)), Category.assoc, costableComparison_map f,
    ModuleCat.auslanderReitenFormula_naturality R E _ f, LinearMap.comp_apply,
    Ext1.pushoutLinearMap_apply]

end TauCeti
