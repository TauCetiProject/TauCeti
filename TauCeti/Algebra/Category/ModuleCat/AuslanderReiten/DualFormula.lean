/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Defect
public import TauCeti.Algebra.Module.AuslanderReiten.Defect.Formula
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.StableEquivalence

/-!
# The second Auslander–Reiten formula

Let `R` be a commutative ring, `A` an `R`-algebra, `E` an injective `R`-module and
`D = Hom_R(-, E)`. For a module `X` with a presentation `P₁ → P₀ → X → 0` by finitely generated
projectives, write `τX = D Tr X`. Then for every module `M`

`Ext¹_A(M, τX) ≅ D (Hom_A(X, M) modulo the maps factoring through projectives)`.

This is Auslander's defect formula `D δ^*(X) ≅ δ_*(τX)` for a short exact sequence `K ⟶ Q ⟶ M` with
`Q` projective: its contravariant defect at `X` is the stable `Hom` from `X` to `M`, and its
covariant defect at `τX` is `Ext¹(M, τX)`
(`TauCeti/Algebra/Category/ModuleCat/AuslanderReiten/Defect.lean`). Here `Mod A / 𝒫` is the
category of all modules modulo the maps through projectives.

Over an Artin algebra, with `hE : Hom_R(R ⧸ 𝔪, E)` of length one for every maximal ideal `𝔪` of
`R`, the translate is an equivalence `τ : (mod A) / 𝒫 ≌ (mod A) / ℐ`
(`TauCeti.stableTranslateEquivalence`), with a chosen quasi-inverse `τ⁻`. Applying the formula to
`X = τ⁻ N` and transporting `Ext¹(M, -)` along `τ τ⁻ N ≅ N` modulo injectives
(`TauCeti.matlisDualTransposeInverseIso`) gives the **second Auslander–Reiten formula**

`Ext¹_A(M, N) ≅ D ((Mod A / 𝒫)(τ⁻ N, M))`

for every module `M` and every finitely generated module `N`, dual to
`ModuleCat.auslanderReitenFormula`.

## Main definitions

* `ModuleCat.ext1TranslateEquivDualStableHom`: `Ext¹(M, τX) ≅ D (Mod A / 𝒫)(X, M)`.
* `TauCeti.ext1EquivDualStableHom`: **the second Auslander–Reiten formula**
  `Ext¹(M, N) ≅ D (Mod A / 𝒫)(τ⁻ N, M)` over an Artin algebra.

## Main results

* `ModuleCat.ext1TranslateEquivDualStableHom_naturality` and
  `TauCeti.ext1EquivDualStableHom_naturality`: naturality in `M`.
* `ModuleCat.ext1TranslateEquivDualStableHom_comap` and
  `TauCeti.ext1EquivDualStableHom_naturality_right`: naturality in `X`, and in `N`, from the
  naturality of `τ τ⁻ N ≅ N` (`TauCeti.matlisDualTransposeInverseIso_naturality`) and
  `TauCeti.ExactStructure.Ext1.pushoutLinearEquivOfIso_symm_pushout`.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270, Corollary.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.4, Propositions IV.4.5–IV.4.6.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Theorem IV.2.13.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti TauCeti.ExactStructure LinearMap
open scoped ModuleCat.Algebra

universe u v w

variable (R : Type u) {A : Type v} (E : Type w) [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup E] [Module R E] {X M K : ModuleCat.{max u v w} A}
  (P : FiniteProjectivePresentation X) (e : (ExactStructure.abelian _).Extension M K)
  (he : (ExactStructure.abelian _).isProjective e.obj)

variable [Module.Injective R E] [Small.{w} R]

/-- **The Auslander–Reiten formula `Ext¹(M, τX) ≅ D (Mod A / 𝒫)(X, M)`.** Let `A` be an algebra over
a commutative ring `R`, `E` an injective `R`-module and `D = Hom_R(-, E)`. For a module `X` with a
presentation `P` by finitely generated projectives, `τX = D Tr X`, and a short exact sequence
`K ⟶ Q ⟶ M` with `Q` projective, `Ext¹(M, τX)` is the dual of `Hom(X, M)` modulo the maps
factoring through projectives. It is Auslander's defect formula for `K ⟶ Q ⟶ M`. -/
noncomputable def ext1TranslateEquivDualStableHom :
    (ExactStructure.abelian _).Ext1 M (matlisDualTranspose R E P) ≃ₗ[R]
      (((ExactStructure.abelian _).projectiveStableFunctor.obj X ⟶
        (ExactStructure.abelian _).projectiveStableFunctor.obj M) →ₗ[R] E) :=
  (((contravariantDefectEquivStableHom R e he X).arrowCongr (LinearEquiv.refl R E)).symm ≪≫ₗ
    Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
      e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
      e.function_exact ≪≫ₗ
    covariantDefectEquivExt1 R (matlisDualTransposeEquiv R E P) e he).symm

/-- The inverse of `Ext¹(M, τX) ≅ D (Mod A / 𝒫)(X, M)` is the defect formula applied to
`χ ∘ (δ^*(X) ≅ (Mod A / 𝒫)(X, M))`, read in `Ext¹(M, τX)`. -/
theorem ext1TranslateEquivDualStableHom_symm_apply
    (χ : ((ExactStructure.abelian _).projectiveStableFunctor.obj X ⟶
      (ExactStructure.abelian _).projectiveStableFunctor.obj M) →ₗ[R] E) :
    (ext1TranslateEquivDualStableHom R E P e he).symm χ =
      covariantDefectEquivExt1 R (matlisDualTransposeEquiv R E P) e he
        (Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
          e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
          e.function_exact
          (χ ∘ₗ (contravariantDefectEquivStableHom R e he X).toLinearMap)) := by
  simp only [ext1TranslateEquivDualStableHom, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  congr 2

variable {M' K' : ModuleCat.{max u v w} A} (e' : (ExactStructure.abelian _).Extension M' K')
  (he' : (ExactStructure.abelian _).isProjective e'.obj)

/-- Naturality in `M`, for a given morphism `(a₁, a₂, f)` of the two sequences. -/
private theorem ext1TranslateEquivDualStableHom_naturality_aux {a₁ : K ⟶ K'}
    {a₂ : e.obj ⟶ e'.obj} {f : M ⟶ M'} (h₁ : e.f ≫ a₂ = a₁ ≫ e'.f) (h₂ : e.g ≫ f = a₂ ≫ e'.g)
    (ξ : (ExactStructure.abelian _).Ext1 M' (matlisDualTranspose R E P)) :
    ext1TranslateEquivDualStableHom R E P e he (ξ.pullback f) =
      ext1TranslateEquivDualStableHom R E P e' he' ξ ∘ₗ
        Linear.rightComp R _ ((ExactStructure.abelian _).projectiveStableFunctor.map f) := by
  have k₁ : a₂.hom ∘ₗ e.f.hom = e'.f.hom ∘ₗ a₁.hom := congrArg Hom.hom h₁
  have k₂ : f.hom ∘ₗ e.g.hom = e'.g.hom ∘ₗ a₂.hom := congrArg Hom.hom h₂
  obtain ⟨χ, rfl⟩ := (ext1TranslateEquivDualStableHom R E P e' he').symm.surjective ξ
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply,
    ext1TranslateEquivDualStableHom_symm_apply, ext1TranslateEquivDualStableHom_symm_apply]
  -- Postcomposition with `f` is the map of contravariant defects.
  have hχ : (χ ∘ₗ Linear.rightComp R _ ((ExactStructure.abelian _).projectiveStableFunctor.map f))
      ∘ₗ (contravariantDefectEquivStableHom R e he X).toLinearMap =
        (χ ∘ₗ (contravariantDefectEquivStableHom R e' he' X).toLinearMap) ∘ₗ
          contravariantDefectMap R k₂ X := LinearMap.ext fun x ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Linear.rightComp_apply]
    rw [contravariantDefectEquivStableHom_map R e he e' he' k₂]
  rw [hχ, Function.Exact.dualContravariantDefectEquivCovariantDefect_naturality _ _ _ _ _
    e'.shortExact.moduleCat_injective_f e'.shortExact.moduleCat_surjective_g
    e'.function_exact k₁ k₂,
    covariantDefectEquivExt1_map R (matlisDualTransposeEquiv R E P) e he e' he' h₁ h₂]

/-- **Naturality of `Ext¹(M, τX) ≅ D (Mod A / 𝒫)(X, M)` in `M`.** For short exact sequences
`K ⟶ Q ⟶ M` and `K' ⟶ Q' ⟶ M'` with projective middle terms and a map `f : M ⟶ M'`, base change
along `f` corresponds to the dual of postcomposition with the stable class of `f`. -/
theorem ext1TranslateEquivDualStableHom_naturality (f : M ⟶ M')
    (ξ : (ExactStructure.abelian _).Ext1 M' (matlisDualTranspose R E P)) :
    ext1TranslateEquivDualStableHom R E P e he (ξ.pullback f) =
      ext1TranslateEquivDualStableHom R E P e' he' ξ ∘ₗ
        Linear.rightComp R _ ((ExactStructure.abelian _).projectiveStableFunctor.map f) := by
  -- Lift `f` to a morphism of the sequences through the projective middle term of `e`.
  let a₂ : e.obj ⟶ e'.obj :=
    he.factorThru ((ExactStructure.abelian _).isDeflation_g e'.conflation) (e.g ≫ f)
  have h₂ : e.g ≫ f = a₂ ≫ e'.g := (isProjective.factorThru_comp _ _ _).symm
  have hk : (e.f ≫ a₂) ≫ e'.g = 0 := by
    rw [Category.assoc, ← h₂, ← Category.assoc, e.zero, Limits.zero_comp]
  exact ext1TranslateEquivDualStableHom_naturality_aux R E P e he e' he'
    (e'.isKernelCokernelPair.lift_f _ hk).symm h₂ ξ

variable {X' : ModuleCat.{max u v w} A} (P' : FiniteProjectivePresentation X') {t : X ⟶ X'}
  {t₀ : P.P₀ →ₗ[A] P'.P₀} {t₁ : P.P₁ →ₗ[A] P'.P₁}

/-- **Naturality of `Ext¹(M, τX) ≅ D (Mod A / 𝒫)(X, M)` in `X`.** For a map `t : X → X'` lifted by
`(t₀, t₁)` to the presentations, cobase change along `D Tr(t) : τX → τX'` corresponds to the dual of
precomposition with the stable class of `t`. -/
theorem ext1TranslateEquivDualStableHom_comap (ht₀ : P'.π ∘ₗ t₀ = t.hom ∘ₗ P.π)
    (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁)
    (ξ : (ExactStructure.abelian _).Ext1 M (matlisDualTranspose R E P)) :
    ext1TranslateEquivDualStableHom R E P' e he (ξ.pushout (matlisDualTransposeMap R E P P' ht₁)) =
      ext1TranslateEquivDualStableHom R E P e he ξ ∘ₗ
        Linear.leftComp R _ ((ExactStructure.abelian _).projectiveStableFunctor.map t) := by
  obtain ⟨χ, rfl⟩ := (ext1TranslateEquivDualStableHom R E P e he).symm.surjective ξ
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply,
    ext1TranslateEquivDualStableHom_symm_apply, ext1TranslateEquivDualStableHom_symm_apply]
  -- Precomposition with `t` is the map of contravariant defects.
  have hχ : (χ ∘ₗ Linear.leftComp R _ ((ExactStructure.abelian _).projectiveStableFunctor.map t))
      ∘ₗ (contravariantDefectEquivStableHom R e he X').toLinearMap =
        (χ ∘ₗ (contravariantDefectEquivStableHom R e he X).toLinearMap) ∘ₗ
          contravariantDefectComap R e.g.hom t.hom := LinearMap.ext fun x ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Linear.leftComp_apply]
    rw [contravariantDefectEquivStableHom_comap]
  rw [hχ, Function.Exact.dualContravariantDefectEquivCovariantDefect_comap P.exact P.surjective
    P'.exact P'.surjective e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
    e.function_exact ht₀ ht₁,
    covariantDefectEquivExt1_homCokernelMap, matlisDualTransposeMap_eq]

end ModuleCat

namespace TauCeti

open CategoryTheory ExactStructure
open scoped ModuleCat.Algebra

universe u v

variable {R : Type v} [CommRing R] {A : Type u} [Ring A] [Algebra R A] {E : Type v}
  [AddCommGroup E] [Module R E] [Module.Injective R E]
  [IsArtinianRing R] [Module.Finite R A]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

include hE in
/-- **The second Auslander–Reiten formula.** Let `A` be an Artin algebra over a commutative Artinian
ring `R`, and `E` an injective `R`-module with `Hom_R(R ⧸ 𝔪, E)` of length one for every maximal
ideal `𝔪` of `R`, and `D = Hom_R(-, E)`. For a module `M` and a finitely generated module `N`,
`Ext¹_A(M, N) ≅ D ((Mod A / 𝒫)(τ⁻ N, M))`, where `τ⁻` is the chosen quasi-inverse of the stable
equivalence `τ : (mod A) / 𝒫 ≌ (mod A) / ℐ`. -/
noncomputable def ext1EquivDualStableHom (M : ModuleCat.{max u v} A)
    (N : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (ExactStructure.abelian _).Ext1 M N.obj.as ≃ₗ[R]
      ((((stableTranslateEquivalence R A E hE).inverse.obj N).obj ⟶
        (ExactStructure.abelian _).projectiveStableFunctor.obj M) →ₗ[R] E) :=
  (Ext1.pushoutLinearEquivOfIso injectiveStableIdeal_le_injectivelyTrivialIdeal R
      (matlisDualTransposeInverseIso hE N)).symm ≪≫ₗ
    ModuleCat.ext1TranslateEquivDualStableHom R E
      (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N))
      (ProjectivePresentation.abelian M).extension
      (ProjectivePresentation.abelian M).isProjective_extension_obj

include hE in
/-- **Naturality of the second Auslander–Reiten formula in `M`.** For a map `f : M ⟶ M'`, base
change along `f` corresponds to the dual of postcomposition with the stable class of `f`. -/
theorem ext1EquivDualStableHom_naturality {M M' : ModuleCat.{max u v} A}
    (N : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) (f : M ⟶ M')
    (ξ : (ExactStructure.abelian _).Ext1 M' N.obj.as) :
    ext1EquivDualStableHom hE M N (ξ.pullback f) =
      ext1EquivDualStableHom hE M' N ξ ∘ₗ
        Linear.rightComp R _ ((ExactStructure.abelian _).projectiveStableFunctor.map f) := by
  simp only [ext1EquivDualStableHom, LinearEquiv.trans_apply,
    Ext1.pushoutLinearEquivOfIso_symm_pullback]
  exact ModuleCat.ext1TranslateEquivDualStableHom_naturality R E _ _ _ _ _ f _

include hE in
/-- **Naturality of the second Auslander–Reiten formula in `N`.** For a map `g : N ⟶ N'` of
finitely generated modules modulo injectives, represented by `g₀`, cobase change along `g₀`
corresponds to the dual of precomposition with `τ⁻ g`. -/
theorem ext1EquivDualStableHom_naturality_right (M : ModuleCat.{max u v} A)
    {N N' : FinitelyGeneratedInjectiveStableModule.{u, max u v} A} (g : N ⟶ N')
    (g₀ : N.obj.as ⟶ N'.obj.as)
    (hg : (ExactStructure.abelian _).injectiveStableFunctor.map g₀ = g.hom)
    (ξ : (ExactStructure.abelian _).Ext1 M N.obj.as) :
    ext1EquivDualStableHom hE M N' (ξ.pushout g₀) =
      ext1EquivDualStableHom hE M N ξ ∘ₗ
        Linear.leftComp R _ ((stableTranslateEquivalence R A E hE).inverse.map g).hom := by
  obtain ⟨t, ht⟩ := Functor.map_surjective (ExactStructure.abelian _).projectiveStableFunctor
    ((stableTranslateEquivalence R A E hE).inverse.map g).hom
  obtain ⟨t₀, t₁, ht₀, ht₁⟩ := exists_lift_projective_presentation
    (FinitelyPresentedStableModule.presentation _).exact.linearMap_comp_eq_zero
    (FinitelyPresentedStableModule.presentation _).exact
    (FinitelyPresentedStableModule.presentation _).surjective t.hom
  -- `D Tr(t)` and `g₀` are compatible with `τ τ⁻ N ≅ N` modulo injectives.
  have hn := (matlisDualTransposeInverseIso_naturality hE g t ht ht₀ ht₁).trans
    (congrArg (_ ≫ ·) hg.symm)
  simp only [ext1EquivDualStableHom, LinearEquiv.trans_apply]
  rw [Ext1.pushoutLinearEquivOfIso_symm_pushout _ R _ _ hn, ← ht]
  exact ModuleCat.ext1TranslateEquivDualStableHom_comap R E _ _ _ _ ht₀ ht₁ _

end TauCeti
