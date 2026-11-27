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

/-!
# Naturality of the Auslander–Reiten formula in the presented module

For a finitely presented module `X`, the Auslander–Reiten formula identifies the dual of
`Ext¹(X, N)` with morphisms `N ⟶ D Tr X` modulo maps factoring through injectives. For a map
`t : X ⟶ X'` lifted to finite projective presentations, the dual of pullback along `t`
corresponds to postcomposition with the class of `D Tr(t)`.

The stable translate makes the presentation-level formula independent of a choice of lifts.
The resulting pairing is natural in both variables. Over an Artin algebra, Matlis biduality
turns the pairing into the first Auslander–Reiten formula for finitely generated modules.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365**
  (2003), 267–270, second Corollary, p. 269.
-/

public section

namespace TauCeti

open CategoryTheory ExactStructure

universe u v w

variable {R : Type v} [CommRing R] {A : Type u} [Ring A] [Algebra R A] {E : Type v}
  [AddCommGroup E] [Module R E] [Module.Injective R E]

open scoped ModuleCat.Algebra

local notation "S" => ExactStructure.abelian (ModuleCat A)

/-- The Auslander–Reiten pairing for the stable translate `τ`. Maps from `N` to `τX`
modulo injectives identify with the dual of `Ext¹(X, N)`. -/
noncomputable def stableAuslanderReitenFormula
    (X : FinitelyPresentedStableModule.{u, max u v} A) (N : ModuleCat.{max u v} A) :
    ((S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) ≃ₗ[R]
      ((S).Ext1 X.obj.as N →ₗ[R] E) :=
  letI := EnoughInjectives.injectiveStableToTrivialFunctor_isEquivalence
    (abelian_enoughInjectives (A := ModuleCat.{max u v} A))
  Linear.homCongr R (Iso.refl _) (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := E) X) ≪≫ₗ
    (S).injectiveStableToTrivialFunctor.homLinearEquiv R _ _ ≪≫ₗ
    ModuleCat.auslanderReitenFormula R E X.presentation N

/-- Evaluate the stable pairing by transporting the morphism to the dual transpose of the
chosen presentation. -/
theorem stableAuslanderReitenFormula_apply
    (X : FinitelyPresentedStableModule.{u, max u v} A) (N : ModuleCat.{max u v} A)
    (a : (S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) :
    stableAuslanderReitenFormula (R := R) (E := E) X N a =
      ModuleCat.auslanderReitenFormula R E X.presentation N
        ((S).injectiveStableToTrivialFunctor.map
          (X := (S).injectiveStableFunctor.obj N)
          (Y := (S).injectiveStableFunctor.obj (ModuleCat.matlisDualTranspose R E X.presentation))
          (a ≫ (stableTranslateObjIsoMatlisDualTranspose (R := R) (E := E) X).hom)) := by
  simp only [stableAuslanderReitenFormula, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Functor.homLinearEquiv_apply, Iso.refl_inv, Category.id_comp]

/-- In the stable pairing, pullback along a representative `t` of a stable morphism `g`
corresponds to postcomposition with `τg`. -/
theorem stableAuslanderReitenFormula_pullback
    {X X' : FinitelyPresentedStableModule.{u, max u v} A} (g : X ⟶ X')
    (t : X.obj.as ⟶ X'.obj.as) (ht : (S).projectiveStableFunctor.map t = g.hom)
    {N : ModuleCat.{max u v} A} (ξ : (S).Ext1 X'.obj.as N)
    (a : (S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) :
    stableAuslanderReitenFormula (R := R) (E := E) X N a (ξ.pullback t) =
      stableAuslanderReitenFormula (R := R) (E := E) X' N
        (a ≫ (stableTranslate R A E).map g) ξ := by
  obtain ⟨t₀, t₁, ht₀, ht₁⟩ := exists_lift_projective_presentation
    X.presentation.exact.linearMap_comp_eq_zero X'.presentation.exact X'.presentation.surjective
    t.hom
  have hg : (ObjectProperty.homMk ((S).projectiveStableFunctor.map t) : X ⟶ X') = g :=
    ObjectProperty.hom_ext _ ht
  have hτ := stableTranslateObjIsoMatlisDualTranspose_naturality (R := R) (E := E) t ht₀ ht₁
  rw [hg] at hτ
  rw [stableAuslanderReitenFormula_apply, stableAuslanderReitenFormula_apply, Category.assoc, hτ,
    ← Category.assoc a, Functor.map_comp _ (a ≫ (stableTranslateObjIsoMatlisDualTranspose X).hom),
    injectiveStableToTrivialFunctor_map,
    ModuleCat.auslanderReitenFormula_comap R E _ _ _ ht₀ ht₁, LinearMap.comp_apply,
    Ext1.pullbackLinearMap_apply]

/-- In the stable pairing, pushout along a map of coefficient modules corresponds to
precomposition with its costable class. -/
theorem stableAuslanderReitenFormula_pushout
    (X : FinitelyPresentedStableModule.{u, max u v} A) {N N' : ModuleCat.{max u v} A}
    (f : N ⟶ N') (ξ : (S).Ext1 X.obj.as N)
    (a : (S).injectiveStableFunctor.obj N' ⟶ (stableTranslate R A E).obj X) :
    stableAuslanderReitenFormula (R := R) (E := E) X N' a (ξ.pushout f) =
      stableAuslanderReitenFormula (R := R) (E := E) X N
        ((S).injectiveStableFunctor.map f ≫ a) ξ := by
  rw [stableAuslanderReitenFormula_apply, stableAuslanderReitenFormula_apply, Category.assoc,
    Functor.map_comp _ ((S).injectiveStableFunctor.map f), injectiveStableToTrivialFunctor_map,
    ModuleCat.auslanderReitenFormula_naturality,
    LinearMap.comp_apply, Ext1.pushoutLinearMap_apply]

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
  rw [ext1EquivDualCostableHom_apply_eq_pairing, stableAuslanderReitenFormula_apply,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, injectiveStableToTrivialFunctor_map,
    ModuleCat.auslanderReitenFormula_map_apply]

/-- Pullback along a representative `t` of a stable morphism `g` corresponds to the dual
of postcomposition with `τg`. -/
theorem ext1EquivDualCostableHom_pullback
    {X X' : FinitelyPresentedStableModule.{u, max u v} A} (g : X ⟶ X')
    (t : X.obj.as ⟶ X'.obj.as) (ht : (S).projectiveStableFunctor.map t = g.hom)
    {N : ModuleCat.{max u v} A} [Module.Finite A N] (ξ : (S).Ext1 X'.obj.as N)
    (a : (S).injectiveStableFunctor.obj N ⟶ (stableTranslate R A E).obj X) :
    ext1EquivDualCostableHom hE X N (ξ.pullback t) a =
      ext1EquivDualCostableHom hE X' N ξ (a ≫ (stableTranslate R A E).map g) := by
  simpa only [ext1EquivDualCostableHom_apply_eq_pairing] using
    stableAuslanderReitenFormula_pullback (R := R) (E := E) g t ht ξ a

/-- Pushout in the coefficient module corresponds to the dual of precomposition with its
costable class. -/
theorem ext1EquivDualCostableHom_pushout
    (X : FinitelyPresentedStableModule.{u, max u v} A) {N N' : ModuleCat.{max u v} A}
    [Module.Finite A N] [Module.Finite A N'] (f : N ⟶ N') (ξ : (S).Ext1 X.obj.as N)
    (a : (S).injectiveStableFunctor.obj N' ⟶ (stableTranslate R A E).obj X) :
    ext1EquivDualCostableHom hE X N' (ξ.pushout f) a =
      ext1EquivDualCostableHom hE X N ξ ((S).injectiveStableFunctor.map f ≫ a) := by
  simpa only [ext1EquivDualCostableHom_apply_eq_pairing] using
    stableAuslanderReitenFormula_pushout (R := R) (E := E) X f ξ a

end TauCeti
