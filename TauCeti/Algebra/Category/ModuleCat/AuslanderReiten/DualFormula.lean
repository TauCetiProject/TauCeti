/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Formula
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.StableEquivalence
public import TauCeti.CategoryTheory.Exact.YonedaExt.Projective
import TauCeti.RingTheory.MatlisDuality.Semilocal

/-!
# The second Auslander–Reiten formula

Let `R` be a commutative ring, `A` an `R`-algebra, `E` an injective `R`-module and
`D = Hom_R(-, E)`. For a module `X` with a presentation `P₁ → P₀ → X → 0` by finitely generated
projectives, write `τX = D Tr X`. Then for every module `M`

`Ext¹_A(M, τX) ≅ D (Hom_A(X, M) modulo the maps factoring through projectives)`.

This is Auslander's defect formula `D δ^*(X) ≅ δ_*(τX)` for a short exact sequence `K ⟶ P ⟶ M` with
`P` projective: its contravariant defect at `X` is the stable `Hom` from `X` to `M`, and its
covariant defect at `τX` is `Ext¹(M, τX)`
(`TauCeti/CategoryTheory/Exact/YonedaExt/Projective.lean`).

Over an Artin algebra, with `hE : Hom_R(R ⧸ 𝔪, E)` of length one for every maximal ideal `𝔪`, the
translate is an equivalence `τ : (mod A) / 𝒫 ≌ (mod A) / ℐ`
(`TauCeti.stableTranslateEquivalence`). Applying the formula to `X = τ⁻ N` and transporting
`Ext¹(M, -)` along `τ τ⁻ N ≅ N` modulo injectives gives the **second Auslander–Reiten formula**

`Ext¹_A(M, N) ≅ D ((mod A / 𝒫)(τ⁻ N, M))`

for finitely generated `M` and `N`, dual to `ModuleCat.auslanderReitenFormula`.

## Main definitions

* `ModuleCat.contravariantDefectEquivStableHom`: the contravariant defect of `K ⟶ P ⟶ M` at `Y` is
  the stable `Hom` from `Y` to `M`.
* `ModuleCat.covariantDefectEquivExt1`: the covariant defect of `K ⟶ P ⟶ M` at `τX` is
  `Ext¹(M, τX)`.
* `ModuleCat.ext1TranslateEquivDualStableHom`: `Ext¹(M, τX) ≅ D (mod A / 𝒫)(X, M)`.
* `TauCeti.stableTranslateObjIsoMatlisDualTranspose` and `TauCeti.matlisDualTransposeInverseIso`:
  the translate is the class of `D Tr X`, and `τ τ⁻ N ≅ N` modulo injectives.
* `TauCeti.ext1EquivDualStableHom`: **the second Auslander–Reiten formula**
  `Ext¹(M, N) ≅ D (mod A / 𝒫)(τ⁻ N, M)` over an Artin algebra.

## Main results

* `ModuleCat.ext1TranslateEquivDualStableHom_naturality` and
  `TauCeti.ext1EquivDualStableHom_naturality`: naturality in `M`.
* `ModuleCat.ext1TranslateEquivDualStableHom_comap` and
  `TauCeti.ext1EquivDualStableHom_naturality_right`: naturality in `X`, and in `N`, from the
  naturality of `τ τ⁻ N ≅ N` (`TauCeti.matlisDualTransposeInverseIso_naturality`).

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270, Corollary.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Theorem IV.2.13.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti TauCeti.ExactStructure LinearMap
open scoped ModuleCat.Algebra

universe u v w

section Defect

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  {M K : ModuleCat.{w} A} (e : (ExactStructure.abelian _).Extension M K)
  (he : (ExactStructure.abelian _).isProjective e.obj)

/-- **The contravariant defect is stable `Hom`.** For a short exact sequence `K ⟶ P ⟶ M` of
`A`-modules with `P` projective, the cokernel of `Hom_A(Y, P) → Hom_A(Y, M)` is the `Hom` space
from `Y` to `M` modulo the maps factoring through projectives. -/
noncomputable def contravariantDefectEquivStableHom (Y : ModuleCat.{w} A) :
    contravariantDefect R e.g.hom Y ≃ₗ[R]
      ((ExactStructure.abelian _).projectiveStableFunctor.obj Y ⟶
        (ExactStructure.abelian _).projectiveStableFunctor.obj M) :=
  (Submodule.Quotient.equiv _ _ (homLinearEquiv (S := R)) (by
      ext g
      simp only [Submodule.mem_map, LinearMap.mem_range]
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨s.hom, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨_, ⟨ofHom s, rfl⟩, rfl⟩)).symm ≪≫ₗ
    e.homQuotientEquivStableHom he R Y

/-- The class of `g : Y → M` in the contravariant defect is its stable class. -/
@[simp]
theorem contravariantDefectEquivStableHom_mk {Y : ModuleCat.{w} A} (g : Y →ₗ[A] M) :
    contravariantDefectEquivStableHom R e he Y (Submodule.Quotient.mk g) =
      (ExactStructure.abelian _).projectiveStableFunctor.map (ofHom g) := by
  simp only [contravariantDefectEquivStableHom, LinearEquiv.trans_apply,
    Submodule.Quotient.equiv_symm, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    Extension.homQuotientEquivStableHom_mk]
  rfl

end Defect

variable (R : Type u) {A : Type v} (E : Type w) [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup E] [Module R E] {X M K : ModuleCat.{max u v w} A}
  (P : FiniteProjectivePresentation X) (e : (ExactStructure.abelian _).Extension M K)
  (he : (ExactStructure.abelian _).isProjective e.obj)

/-- **The covariant defect at `τX` is `Ext¹`.** For a short exact sequence `K ⟶ P ⟶ M` with `P`
projective, the cokernel of `Hom_A(P, τX) → Hom_A(K, τX)` is `Ext¹(M, τX)`, where `τX = D Tr X`.
-/
noncomputable def covariantDefectEquivExt1 :
    covariantDefect R e.f.hom (MatlisDual R E (AuslanderReitenTranspose P.p)) ≃ₗ[R]
      (ExactStructure.abelian _).Ext1 M (matlisDualTranspose R E P) :=
  Submodule.Quotient.equiv _ _ (matlisDualTransposeHomEquiv R E P K).symm (by
      ext g
      simp only [Submodule.mem_map, LinearMap.mem_range]
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨ofHom s, by ext; simp [LinearMap.lcomp_apply']; rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨_, ⟨s.hom, rfl⟩, by ext; simp; rfl⟩) ≪≫ₗ
    e.homQuotientEquivExt1OfIsProjective he R _

/-- The class of `v : K → τX` in the covariant defect is the cobase change `v_* [K ⟶ P ⟶ M]`. -/
@[simp]
theorem covariantDefectEquivExt1_mk (v : K →ₗ[A] MatlisDual R E (AuslanderReitenTranspose P.p)) :
    covariantDefectEquivExt1 R E P e he (Submodule.Quotient.mk v) =
      (ExactStructure.Ext1.mk e).pushout ((matlisDualTransposeHomEquiv R E P K).symm v) := by
  simp [covariantDefectEquivExt1]

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra in
/-- The dual of a bundled right module `N`, on which `R` acts through `Aᵐᵒᵖ`, is the Matlis dual of
any right module `N'` linearly equivalent to it, for any action of `R` on `N'` compatible with
`Aᵐᵒᵖ`. -/
noncomputable def matlisDualOpObjEquivOfLinearEquiv {N' : Type*} [AddCommGroup N']
    [Module Aᵐᵒᵖ N'] [Module R N'] [IsScalarTower R Aᵐᵒᵖ N'] (N : ModuleCat.{max u v w} Aᵐᵒᵖ)
    (e : N' ≃ₗ[Aᵐᵒᵖ] N) : (matlisDualOp R E).obj (Opposite.op N) ≃ₗ[A] MatlisDual R E N' :=
  (matlisDualOpObjEquiv R E N).trans (MatlisDual.congrOp e)

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra in
@[simp]
theorem matlisDualOpObjEquivOfLinearEquiv_apply {N' : Type*} [AddCommGroup N']
    [Module Aᵐᵒᵖ N'] [Module R N'] [IsScalarTower R Aᵐᵒᵖ N'] (N : ModuleCat.{max u v w} Aᵐᵒᵖ)
    (e : N' ≃ₗ[Aᵐᵒᵖ] N) (φ : (matlisDualOp R E).obj (Opposite.op N)) (x : N') :
    MatlisDual.equivLinearMap R E N' (matlisDualOpObjEquivOfLinearEquiv R E N e φ) x =
      MatlisDual.equivLinearMap R E N (matlisDualOpObjEquiv R E N φ) (e x) :=
  MatlisDual.congrOp_apply e _ x

variable [Module.Injective R E] [Small.{w} R]

/-- **The Auslander–Reiten formula `Ext¹(M, τX) ≅ D (mod A / 𝒫)(X, M)`.** Let `A` be an algebra over
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
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e.shortExact.exact) ≪≫ₗ
    covariantDefectEquivExt1 R E P e he).symm

/-- The inverse of `Ext¹(M, τX) ≅ D (mod A / 𝒫)(X, M)` is the defect formula applied to
`χ ∘ (δ^*(X) ≅ (mod A / 𝒫)(X, M))`, read in `Ext¹(M, τX)`. -/
theorem ext1TranslateEquivDualStableHom_symm_apply
    (χ : ((ExactStructure.abelian _).projectiveStableFunctor.obj X ⟶
      (ExactStructure.abelian _).projectiveStableFunctor.obj M) →ₗ[R] E) :
    (ext1TranslateEquivDualStableHom R E P e he).symm χ =
      covariantDefectEquivExt1 R E P e he
        (Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
          e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
          ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e.shortExact.exact)
          (χ ∘ₗ (contravariantDefectEquivStableHom R e he X).toLinearMap)) := by
  simp [ext1TranslateEquivDualStableHom]
  rfl

variable {M' K' : ModuleCat.{max u v w} A} (e' : (ExactStructure.abelian _).Extension M' K')
  (he' : (ExactStructure.abelian _).isProjective e'.obj) {a₁ : K ⟶ K'} {a₂ : e.obj ⟶ e'.obj}
  {f : M ⟶ M'}

/-- **Naturality of `Ext¹(M, τX) ≅ D (mod A / 𝒫)(X, M)` in `M`.** For a morphism `(a₁, a₂, f)`
from `K ⟶ P ⟶ M` to `K' ⟶ P' ⟶ M'`, both with projective middle terms, base change along `f`
corresponds to the dual of postcomposition with the stable class of `f`. -/
theorem ext1TranslateEquivDualStableHom_naturality (h₁ : e.f ≫ a₂ = a₁ ≫ e'.f)
    (h₂ : e.g ≫ f = a₂ ≫ e'.g)
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
          contravariantDefectMap R k₂ X := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, contravariantDefectEquivStableHom_mk,
      contravariantDefectMap_mk, Linear.rightComp_apply, ← Functor.map_comp]
    rfl
  rw [hχ, Function.Exact.dualContravariantDefectEquivCovariantDefect_naturality _ _ _ _ _
    e'.shortExact.moduleCat_injective_f e'.shortExact.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e'.shortExact.exact) k₁ k₂]
  generalize Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
    e'.shortExact.moduleCat_injective_f e'.shortExact.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e'.shortExact.exact)
    (χ ∘ₗ (contravariantDefectEquivStableHom R e' he' X).toLinearMap) = y
  induction y using Submodule.Quotient.induction_on with
  | _ v =>
    rw [covariantDefectMap_mk, covariantDefectEquivExt1_mk, covariantDefectEquivExt1_mk,
      ExactStructure.Ext1.pushout_pullback,
      ← ExactStructure.Ext1.pushout_mk_eq_pullback_mk a₂ h₁ h₂.symm,
      ExactStructure.Ext1.pushout_pushout]
    congr 1
    ext
    simp
    rfl

variable {X' : ModuleCat.{max u v w} A} (P' : FiniteProjectivePresentation X') {t : X ⟶ X'}
  {t₀ : P.P₀ →ₗ[A] P'.P₀} {t₁ : P.P₁ →ₗ[A] P'.P₁}

omit [Module.Injective R E] [Small.{w} R] in
/-- The map `D Tr X → D Tr X'` dual to the map of transposes induced by a lift `(t₀, t₁)` of a map
`X → X'` to the presentations. -/
noncomputable def matlisDualTransposeMap (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁) :
    matlisDualTranspose R E P ⟶ matlisDualTranspose R E P' :=
  ofHom (MatlisDual.mapOp (AuslanderReitenTranspose.map t₀ t₁ ht₁))

omit [Module.Injective R E] [Small.{w} R] in
/-- The bundled dual of `Tr X`, with the action of `R` through `Aᵐᵒᵖ`, is `τX = D Tr X`. -/
noncomputable def matlisDualOpTransposeIso :
    (matlisDualOp R E).obj (Opposite.op (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))) ≅
      matlisDualTranspose R E P where
  hom := ofHom (matlisDualOpObjEquivOfLinearEquiv R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
    (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P.p))).toLinearMap
  inv := ofHom (matlisDualOpObjEquivOfLinearEquiv R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
    (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P.p))).symm.toLinearMap
  hom_inv_id := by
    ext x
    exact (matlisDualOpObjEquivOfLinearEquiv R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
      (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P.p))).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact (matlisDualOpObjEquivOfLinearEquiv R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
      (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P.p))).apply_symm_apply x

omit [Module.Injective R E] [Small.{w} R] in
/-- The dual of the map of transposes is `D Tr(t)`, through `ModuleCat.matlisDualOpTransposeIso`. -/
theorem matlisDualOp_map_comp_matlisDualOpTransposeIso_hom (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁) :
    (matlisDualOp R E).map (ofHom (AuslanderReitenTranspose.map t₀ t₁ ht₁)).op ≫
        (matlisDualOpTransposeIso R E P').hom =
      (matlisDualOpTransposeIso R E P).hom ≫ matlisDualTransposeMap R E P P' ht₁ := by
  ext φ : 2
  refine (MatlisDual.equivLinearMap R E _).injective (LinearMap.ext fun τ ↦ ?_)
  have h₁ := matlisDualOpObjEquivOfLinearEquiv_apply R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P'.p))
    (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P'.p))
    (matlisDualOpMap R E (ofHom (AuslanderReitenTranspose.map t₀ t₁ ht₁)) φ) τ
  have h₂ := matlisDualOpObjEquiv_map_apply R E (ofHom (AuslanderReitenTranspose.map t₀ t₁ ht₁)) φ τ
  have h₃ := matlisDualOpObjEquivOfLinearEquiv_apply R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
    (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P.p)) φ
    (AuslanderReitenTranspose.map t₀ t₁ ht₁ τ)
  exact h₁.trans (h₂.trans (h₃.symm.trans (MatlisDual.mapOp_apply _ _ τ).symm))

/-- **Naturality of `Ext¹(M, τX) ≅ D (mod A / 𝒫)(X, M)` in `X`.** For a map `t : X → X'` lifted by
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
          contravariantDefectComap R e.g.hom t.hom := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, contravariantDefectEquivStableHom_mk,
      contravariantDefectComap_mk, Linear.leftComp_apply, ← Functor.map_comp]
    rfl
  rw [hχ, Function.Exact.dualContravariantDefectEquivCovariantDefect_comap P.exact P.surjective
    P'.exact P'.surjective e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e.shortExact.exact) ht₀ ht₁]
  generalize Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
    e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e.shortExact.exact)
    (χ ∘ₗ (contravariantDefectEquivStableHom R e he X).toLinearMap) = y
  induction y using Submodule.Quotient.induction_on with
  | _ v =>
    rw [covariantDefectMapRight_mk, covariantDefectEquivExt1_mk, covariantDefectEquivExt1_mk,
      ExactStructure.Ext1.pushout_pushout]
    congr 1
    ext x
    simp only [LinearMap.comp_apply, matlisDualTransposeHomEquiv_symm_apply, matlisDualTransposeMap]
    exact congrArg (MatlisDual.mapOp (AuslanderReitenTranspose.map t₀ t₁ ht₁))
      (matlisDualTransposeHomEquiv_symm_apply R E P v x)

end ModuleCat

namespace TauCeti

open CategoryTheory ExactStructure
open scoped ModuleCat.Algebra

universe u v

variable {R : Type v} [CommRing R] {A : Type u} [Ring A] [Algebra R A] {E : Type v}
  [AddCommGroup E] [Module R E] [Module.Injective R E]
  [IsArtinianRing R] [Module.Finite R A]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

/-- The finite projective presentation of a finitely presented module chosen by
`TauCeti.stableTranspose`. -/
noncomputable abbrev FinitelyPresentedStableModule.presentation
    (X : FinitelyPresentedStableModule.{u, max u v} A) : FiniteProjectivePresentation X.obj.as :=
  letI := X.property
  FiniteProjectivePresentation.ofFinitePresentation

omit [IsArtinianRing R] [Module.Finite R A] in
/-- The translate of a finitely presented module, as the class of `D Tr X` for the presentation
chosen by `TauCeti.stableTranspose`. -/
noncomputable def stableTranslateObjIsoMatlisDualTranspose
    (X : FinitelyPresentedStableModule.{u, max u v} A) :
    (stableTranslate R A E).obj X ≅
      (ExactStructure.abelian _).injectiveStableFunctor.obj
        (ModuleCat.matlisDualTranspose R E
          (FinitelyPresentedStableModule.presentation X)) :=
  let P := FinitelyPresentedStableModule.presentation X
  eqToIso (by rw [stableTranslate_def]) ≪≫
    stableTranslateFunctorObjIso R E FinitelyPresentedStableModule.presentation X ≪≫
    (ExactStructure.abelian _).injectiveStableFunctor.mapIso
      (ModuleCat.matlisDualOpTransposeIso R E P)

omit [IsArtinianRing R] [Module.Finite R A] in
/-- **Naturality of `τX ≅ D Tr X` modulo injectives.** For a map `t : X → X'` lifted by
`(t₀, t₁)` to the presentations chosen by `TauCeti.stableTranspose`, the translate of the stable
class of `t` is the class of `D Tr(t)`. -/
theorem stableTranslateObjIsoMatlisDualTranspose_naturality
    {X X' : FinitelyPresentedStableModule.{u, max u v} A} (t : X.obj.as ⟶ X'.obj.as)
    {t₀ : (FinitelyPresentedStableModule.presentation X).P₀ →ₗ[A]
      (FinitelyPresentedStableModule.presentation X').P₀}
    {t₁ : (FinitelyPresentedStableModule.presentation X).P₁ →ₗ[A]
      (FinitelyPresentedStableModule.presentation X').P₁}
    (ht₀ : (FinitelyPresentedStableModule.presentation X').π ∘ₗ t₀ =
      t.hom ∘ₗ (FinitelyPresentedStableModule.presentation X).π)
    (ht₁ : t₀ ∘ₗ (FinitelyPresentedStableModule.presentation X).p =
      (FinitelyPresentedStableModule.presentation X').p ∘ₗ t₁) :
    (stableTranslate R A E).map
        (ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map t)) ≫
      (stableTranslateObjIsoMatlisDualTranspose X').hom =
    (stableTranslateObjIsoMatlisDualTranspose X).hom ≫
      (ExactStructure.abelian _).injectiveStableFunctor.map
        (ModuleCat.matlisDualTransposeMap R E _ _ ht₁) := by
  have hT := (AuslanderReitenTranspose.stableMap_quotient_map
    (FinitelyPresentedStableModule.presentation X).exact.linearMap_comp_eq_zero
    (FinitelyPresentedStableModule.presentation X').exact
    (FinitelyPresentedStableModule.presentation X').surjective t.hom t₀ t₁ ht₀ ht₁).symm
  simp only [stableTranslateObjIsoMatlisDualTranspose, Iso.trans_hom, eqToIso.hom,
    Category.assoc]
  rw [Functor.congr_hom (stableTranslate_def (R := R) (A := A) (E := E)),
    stableTranslateFunctor_map _
      (ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map t)) _ hT]
  have key := ModuleCat.matlisDualOp_map_comp_matlisDualOpTransposeIso_hom R E _ _ ht₁
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.inv_hom_id_assoc]
  congr 2
  exact ((ExactStructure.abelian _).injectiveStableFunctor.map_comp _ _).symm.trans
    ((congrArg (ExactStructure.abelian _).injectiveStableFunctor.map key).trans
      ((ExactStructure.abelian _).injectiveStableFunctor.map_comp _ _))

include hE in
/-- **`τ τ⁻ N ≅ N`** modulo injectives, with `τ` computed as `D Tr` of the presentation chosen by
`TauCeti.stableTranspose`. -/
noncomputable def matlisDualTransposeInverseIso
    (N : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (ExactStructure.abelian _).injectiveStableFunctor.obj
        (ModuleCat.matlisDualTranspose R E (FinitelyPresentedStableModule.presentation
          ((stableTranslateEquivalence R A E hE).inverse.obj N))) ≅
      (ExactStructure.abelian _).injectiveStableFunctor.obj N.obj.as :=
  haveI := finite_of_forall_isMaximal hE
  (stableTranslateObjIsoMatlisDualTranspose _).symm ≪≫
    ((finiteStableTranslateCompιIso R A E).app _).symm ≪≫
    (ObjectProperty.ι _).mapIso
      (eqToIso (by rw [Functor.comp_obj, stableTranslateEquivalence_functor]) ≪≫
        (stableTranslateEquivalence R A E hE).counitIso.app N)

include hE in
/-- **Naturality of `τ τ⁻ N ≅ N` modulo injectives.** For a map `g : N ⟶ N'` and a lift
`(t₀, t₁)` of a representative `t` of `τ⁻ g` to the chosen presentations, `D Tr(t)` corresponds to
`g`. -/
theorem matlisDualTransposeInverseIso_naturality
    {N N' : FinitelyGeneratedInjectiveStableModule.{u, max u v} A} (g : N ⟶ N')
    (t : ((stableTranslateEquivalence R A E hE).inverse.obj N).obj.as ⟶
      ((stableTranslateEquivalence R A E hE).inverse.obj N').obj.as)
    (ht : (ExactStructure.abelian _).projectiveStableFunctor.map t =
      ((stableTranslateEquivalence R A E hE).inverse.map g).hom)
    {t₀ : (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N)).P₀ →ₗ[A]
      (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N')).P₀}
    {t₁ : (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N)).P₁ →ₗ[A]
      (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N')).P₁}
    (ht₀ : (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N')).π ∘ₗ t₀ =
      t.hom ∘ₗ (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N)).π)
    (ht₁ : t₀ ∘ₗ (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N)).p =
      (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N')).p ∘ₗ t₁) :
    (ExactStructure.abelian _).injectiveStableFunctor.map
        (ModuleCat.matlisDualTransposeMap R E _ _ ht₁) ≫
      (matlisDualTransposeInverseIso hE N').hom =
    (matlisDualTransposeInverseIso hE N).hom ≫ g.hom := by
  have := finite_of_forall_isMaximal hE
  have hs : ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map t) =
      (stableTranslateEquivalence R A E hE).inverse.map g :=
    ObjectProperty.hom_ext _ ht
  have h₁ := stableTranslateObjIsoMatlisDualTranspose_naturality (R := R) (E := E) t ht₀ ht₁
  rw [hs, ← Iso.inv_comp_eq] at h₁
  -- The counit of `τ` is natural, with `τ = finiteStableTranslate` up to `eqToHom`.
  have hc := (stableTranslateEquivalence R A E hE).counitIso.hom.naturality g
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hc
  rw [Functor.congr_hom (stableTranslateEquivalence_functor A hE)] at hc
  simp only [matlisDualTransposeInverseIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_inv, eqToIso.hom, ← h₁, Category.assoc, Iso.hom_inv_id_assoc]
  rw [(finiteStableTranslateCompιIso R A E).inv.naturality_assoc]
  congr 2
  have hg : g.hom = (ObjectProperty.ι _).map g := rfl
  rw [hg, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Iso.app_hom, Iso.app_hom, Category.assoc, ← hc]
  simp

include hE in
/-- **The second Auslander–Reiten formula.** Let `A` be an Artin algebra over a commutative Artinian
ring `R`, and `E` an injective `R`-module with `Hom_R(R ⧸ 𝔪, E)` of length one for every maximal
ideal `𝔪`, and `D = Hom_R(-, E)`. For a finitely presented module `M` and a finitely generated
module `N`, `Ext¹_A(M, N) ≅ D ((mod A / 𝒫)(τ⁻ N, M))`, where `τ⁻` is the inverse of the stable
equivalence `τ : (mod A) / 𝒫 ≌ (mod A) / ℐ`. -/
noncomputable def ext1EquivDualStableHom (M : FinitelyPresentedStableModule.{u, max u v} A)
    (N : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (ExactStructure.abelian _).Ext1 M.obj.as N.obj.as ≃ₗ[R]
      ((((stableTranslateEquivalence R A E hE).inverse.obj N).obj ⟶ M.obj) →ₗ[R] E) :=
  (Ext1.pushoutLinearEquivOfIso R (matlisDualTransposeInverseIso hE N)).symm ≪≫ₗ
    ModuleCat.ext1TranslateEquivDualStableHom R E
      (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N))
      (ProjectivePresentation.abelian M.obj.as).extension
      (ProjectivePresentation.abelian M.obj.as).isProjective_extension_obj

include hE in
/-- **Naturality of the second Auslander–Reiten formula in `M`.** For a map `f : M ⟶ M'` of
finitely presented modules, base change along `f` corresponds to the dual of postcomposition with
the stable class of `f`. -/
theorem ext1EquivDualStableHom_naturality {M M' : FinitelyPresentedStableModule.{u, max u v} A}
    (N : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) (f : M.obj.as ⟶ M'.obj.as)
    (ξ : (ExactStructure.abelian _).Ext1 M'.obj.as N.obj.as) :
    ext1EquivDualStableHom hE M N (ξ.pullback f) =
      ext1EquivDualStableHom hE M' N ξ ∘ₗ
        Linear.rightComp R _ ((ExactStructure.abelian _).projectiveStableFunctor.map f) := by
  let Q := (ProjectivePresentation.abelian M.obj.as).extension
  let Q' := (ProjectivePresentation.abelian M'.obj.as).extension
  -- Lift `f` to a morphism of the chosen projective presentations.
  let a₂ : Q.obj ⟶ Q'.obj := (ProjectivePresentation.abelian M.obj.as).isProjective_extension_obj
    |>.factorThru ((ExactStructure.abelian _).isDeflation_g Q'.conflation) (Q.g ≫ f)
  have h₂ : Q.g ≫ f = a₂ ≫ Q'.g := (isProjective.factorThru_comp _ _ _).symm
  have hk : (Q.f ≫ a₂) ≫ Q'.g = 0 := by
    rw [Category.assoc, ← h₂, ← Category.assoc, Q.zero, Limits.zero_comp]
  have h₁ : Q.f ≫ a₂ = Q'.isKernelCokernelPair.lift (Q.f ≫ a₂) hk ≫ Q'.f :=
    (Q'.isKernelCokernelPair.lift_f _ hk).symm
  simp only [ext1EquivDualStableHom, LinearEquiv.trans_apply,
    Ext1.pushoutLinearEquivOfIso_symm_pullback]
  exact ModuleCat.ext1TranslateEquivDualStableHom_naturality R E _ _ _ _ _ h₁ h₂ _

include hE in
/-- **Naturality of the second Auslander–Reiten formula in `N`.** For a map `g : N ⟶ N'` of
finitely generated modules modulo injectives, represented by `g₀`, cobase change along `g₀`
corresponds to the dual of precomposition with `τ⁻ g`. -/
theorem ext1EquivDualStableHom_naturality_right (M : FinitelyPresentedStableModule.{u, max u v} A)
    {N N' : FinitelyGeneratedInjectiveStableModule.{u, max u v} A} (g : N ⟶ N')
    (g₀ : N.obj.as ⟶ N'.obj.as)
    (hg : (ExactStructure.abelian _).injectiveStableFunctor.map g₀ = g.hom)
    (ξ : (ExactStructure.abelian _).Ext1 M.obj.as N.obj.as) :
    ext1EquivDualStableHom hE M N' (ξ.pushout g₀) =
      ext1EquivDualStableHom hE M N ξ ∘ₗ
        Linear.leftComp R _ ((stableTranslateEquivalence R A E hE).inverse.map g).hom := by
  obtain ⟨t, ht⟩ := Functor.map_surjective (ExactStructure.abelian _).projectiveStableFunctor
    ((stableTranslateEquivalence R A E hE).inverse.map g).hom
  obtain ⟨t₀, t₁, ht₀, ht₁⟩ := exists_lift_projective_presentation
    (FinitelyPresentedStableModule.presentation _).exact.linearMap_comp_eq_zero
    (FinitelyPresentedStableModule.presentation _).exact
    (FinitelyPresentedStableModule.presentation _).surjective t.hom
  have hn := matlisDualTransposeInverseIso_naturality hE g t ht ht₀ ht₁
  simp only [ext1EquivDualStableHom, LinearEquiv.trans_apply]
  rw [← ht]
  refine Eq.trans ?_ (ModuleCat.ext1TranslateEquivDualStableHom_comap R E _ _ _ _ ht₀ ht₁ _)
  congr 1
  -- Both sides are cobase changes along representatives of the same stable map.
  obtain ⟨b, hb⟩ := Functor.map_surjective (ExactStructure.abelian _).injectiveStableFunctor
    (matlisDualTransposeInverseIso hE N).inv
  obtain ⟨b', hb'⟩ := Functor.map_surjective (ExactStructure.abelian _).injectiveStableFunctor
    (matlisDualTransposeInverseIso hE N').inv
  rw [Ext1.pushoutLinearEquivOfIso_symm_apply R _ b' hb',
    Ext1.pushoutLinearEquivOfIso_symm_apply R _ b hb, Ext1.pushout_pushout, Ext1.pushout_pushout]
  refine Ext1.pushout_eq_of_injectiveStableFunctor_map_eq ξ ?_
  rw [Functor.map_comp, Functor.map_comp, hg, hb, hb', Iso.eq_inv_comp, ← Category.assoc,
    Iso.comp_inv_eq, hn]

end TauCeti
