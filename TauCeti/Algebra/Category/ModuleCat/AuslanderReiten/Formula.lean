/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Module.AuslanderReiten.DefectFormula
public import TauCeti.Algebra.Module.Projective.FinitePresentation
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.YonedaExt.Injective
public import TauCeti.CategoryTheory.Exact.YonedaExt.LocalDuality

/-!
# The Auslander–Reiten formula

Let `R` be a commutative ring, `A` an `R`-algebra, `E` an injective `R`-module and
`D = Hom_R(-, E)`. For an `A`-module `X` with a presentation `P₁ → P₀ → X → 0` by finitely
generated projectives, write `τX = D Tr X` for the dual of its transpose. The
**Auslander–Reiten formula** says that for every `A`-module `N`,

`D Ext¹_A(X, N) ≅ Hom_A(N, τX)` modulo the maps factoring through injectives,

naturally in `N`. The right side is the `Hom` space of the quotient of `ModuleCat A` by the ideal
`ℐ` of injectively trivial maps, those that extend across every monomorphism.

We follow Krause's derivation from Auslander's defect formula. Take a short exact sequence
`N ⟶ I ⟶ N'` with `I` injective. Its contravariant defect at `X`, the cokernel of
`Hom(X, I) → Hom(X, N')`, is `Ext¹(X, N)`, and its covariant defect at `τX`, the cokernel of
`Hom(I, τX) → Hom(N, τX)`, is `Hom(N, τX)` modulo `ℐ`
(`TauCeti/CategoryTheory/Exact/YonedaExt/Injective.lean`). So the defect formula
`D δ^*(X) ≅ δ_*(τX)` gives `D Ext¹(X, N) ≅ (A/ℐ)(N, τX)`, natural in the sequence.

The isomorphism is then made canonical. The **Auslander–Reiten form**
`Ext¹(X, τX) → E` is the image of the identity of `τX` for one chosen sequence, and its pairing
`(a, ξ) ↦ φ(a_* ξ)` (`TauCeti.ExactStructure.costablePairing`) is perfect for every `N`, by
naturality applied to a morphism of sequences extending `a : N ⟶ τX`. Thus `τX` represents
`D Ext¹(X, -)` on the injectively stable category.

No finiteness of `R` or `A` and no minimality of the presentation is needed.

## Implementation notes

An object of `ModuleCat A` remembers only its `A`-action. Its `R`-action, and the `R`-linear
structure of `ModuleCat A`, come from the scoped instances of `ModuleCat.Algebra`. On the carrier
`Hom_R(Tr X, E)` of `τX` this action agrees with the native `R`-action only propositionally. The
bundled translate `ModuleCat.matlisDualTranspose` is therefore a plain definition, so that
instance search sees only the categorical action on it, and `ModuleCat.matlisDualTransposeHomEquiv`
compares the two actions on morphisms into it.

## Main definitions

* `ModuleCat.matlisDualTranspose R E P`: the module `τX = D Tr X`.
* `ModuleCat.contravariantDefectEquivExt1`: the contravariant defect of `N ⟶ I ⟶ N'` at `Y` is
  `Ext¹(Y, N)`.
* `ModuleCat.dualExt1EquivCostableHom`: `D Ext¹(X, N) ≅ (A/ℐ)(N, τX)` from the defect formula of
  `N ⟶ I ⟶ N'`.
* `ModuleCat.auslanderReitenForm R E P`: the Auslander–Reiten form `Ext¹(X, τX) → E`.
* `ModuleCat.auslanderReitenFormula R E P N`: **the Auslander–Reiten formula**
  `(A/ℐ)(N, τX) ≅ D Ext¹(X, N)`.

## Main results

* `ModuleCat.dualExt1EquivCostableHom_naturality`: naturality in the sequence.
* `ModuleCat.auslanderReitenFormula_naturality`: naturality of the formula in `N`.
* `ModuleCat.bijective_costablePairing_auslanderReitenForm`: the pairing of the Auslander–Reiten
  form is perfect.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270, Corollary.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.2, for Artin algebras.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti TauCeti.ExactStructure LinearMap
open scoped ModuleCat.Algebra

universe u v w t

/-! ### The contravariant defect is `Ext¹` -/

section Defect

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  {N N' : ModuleCat.{t} A}

variable (R) in
/-- **The contravariant defect is `Ext¹`.** For a short exact sequence `N ⟶ I ⟶ N'` of
`A`-modules with `I` injective, the cokernel of `Hom_A(Y, I) → Hom_A(Y, N')` is `Ext¹(Y, N)`,
through `u ↦ u^* [N ⟶ I ⟶ N']`. -/
noncomputable def contravariantDefectEquivExt1
    (e : (ExactStructure.abelian _).Extension N' N)
    (he : (ExactStructure.abelian _).isInjective e.obj) (Y : ModuleCat.{t} A) :
    contravariantDefect R e.g.hom Y ≃ₗ[R] (ExactStructure.abelian _).Ext1 Y N :=
  (Submodule.Quotient.equiv _ _ (homLinearEquiv (S := R)) (by
      ext g
      simp only [Submodule.mem_map, LinearMap.mem_range]
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨s.hom, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨_, ⟨ofHom s, rfl⟩, rfl⟩)).symm ≪≫ₗ
    e.homQuotientEquivExt1 he R Y

/-- The class of `g : Y → N'` in the contravariant defect is the base change `g^* [N ⟶ I ⟶ N']`.
-/
@[simp]
theorem contravariantDefectEquivExt1_mk
    (e : (ExactStructure.abelian _).Extension N' N)
    (he : (ExactStructure.abelian _).isInjective e.obj) {Y : ModuleCat.{t} A}
    (g : Y →ₗ[A] N') :
    contravariantDefectEquivExt1 R e he Y (Submodule.Quotient.mk g) =
      (Ext1.mk e).pullback (ofHom g) := by
  simp only [contravariantDefectEquivExt1, LinearEquiv.trans_apply, Submodule.Quotient.equiv_symm,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, Extension.homQuotientEquivExt1_mk]
  rfl

end Defect

/-! ### The translate `D Tr X` -/

variable (R : Type u) {A : Type v} (E : Type w) [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup E] [Module R E] {X : ModuleCat.{max u v w} A}
  (P : FiniteProjectivePresentation X)

/-- The **Auslander–Reiten translate** `τX = D Tr X = Hom_R(Tr X, E)` of a module `X` with a
presentation `P` by finitely generated projectives, as an object of `ModuleCat A`. -/
@[expose] def matlisDualTranspose : ModuleCat.{max u v w} A :=
  ModuleCat.of A (MatlisDual R E (AuslanderReitenTranspose P.p))

/-- Morphisms into `D Tr X` are the `A`-linear maps into `Hom_R(Tr X, E)`. On the left, `R` acts
through the `R`-linear structure of `ModuleCat A`, and on the right through its action on `E`. -/
noncomputable def matlisDualTransposeHomEquiv (M : ModuleCat.{max u v w} A) :
    (M ⟶ matlisDualTranspose R E P) ≃ₗ[R]
      (M →ₗ[A] MatlisDual R E (AuslanderReitenTranspose P.p)) where
  toFun f := f.hom
  invFun g := ofHom g
  map_add' _ _ := rfl
  -- Both actions of `c` are the action of `algebraMap R A c`.
  map_smul' c f := LinearMap.ext fun x ↦ (IsScalarTower.algebraMap_smul A c (f.hom x)).symm.trans
    (IsScalarTower.algebraMap_smul (M := MatlisDual R E (AuslanderReitenTranspose P.p)) A c
      (f.hom x))
  left_inv _ := rfl
  right_inv _ := rfl

/-- `ModuleCat.matlisDualTransposeHomEquiv` keeps the underlying function. -/
@[simp]
theorem matlisDualTransposeHomEquiv_apply {M : ModuleCat.{max u v w} A}
    (f : M ⟶ matlisDualTranspose R E P) (x : M) :
    matlisDualTransposeHomEquiv R E P M f x = f x :=
  (rfl)

/-- The inverse of `ModuleCat.matlisDualTransposeHomEquiv` keeps the underlying function. -/
@[simp]
theorem matlisDualTransposeHomEquiv_symm_apply {M : ModuleCat.{max u v w} A}
    (g : M →ₗ[A] MatlisDual R E (AuslanderReitenTranspose P.p)) (x : M) :
    (matlisDualTransposeHomEquiv R E P M).symm g x = g x :=
  (rfl)

/-! ### The defect formula as `D Ext¹(X, N) ≅ (A/ℐ)(N, τX)` -/

variable {N N' : ModuleCat.{max u v w} A} (e : (ExactStructure.abelian _).Extension N' N)
  (he : (ExactStructure.abelian _).isInjective e.obj)

/-- **The covariant defect at `τX` is costable `Hom`.** For a short exact sequence `N ⟶ I ⟶ N'`
with `I` injective, the cokernel of `Hom_A(I, τX) → Hom_A(N, τX)` is `(A/ℐ)(N, τX)`. -/
noncomputable def covariantDefectEquivCostableHom :
    covariantDefect R e.f.hom (MatlisDual R E (AuslanderReitenTranspose P.p)) ≃ₗ[R]
      ((ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj N ⟶
        (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj
          (matlisDualTranspose R E P)) :=
  Submodule.Quotient.equiv _ _ (matlisDualTransposeHomEquiv R E P N).symm (by
      ext g
      simp only [Submodule.mem_map, LinearMap.mem_range]
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨ofHom s, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨_, ⟨s.hom, rfl⟩, rfl⟩) ≪≫ₗ
    e.homQuotientEquivCostableHom he R _

/-- The class of `u : N → D Tr X` in the covariant defect is the class of `u` modulo `ℐ`. -/
@[simp]
theorem covariantDefectEquivCostableHom_mk
    (u : N →ₗ[A] MatlisDual R E (AuslanderReitenTranspose P.p)) :
    covariantDefectEquivCostableHom R E P e he (Submodule.Quotient.mk u) =
      (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map
        ((matlisDualTransposeHomEquiv R E P N).symm u) := by
  simp [covariantDefectEquivCostableHom]

variable [Module.Injective R E] [Small.{w} R]

/-- **Auslander's defect formula as the Auslander–Reiten formula.** For a short exact sequence
`N ⟶ I ⟶ N'` with `I` injective, `D Ext¹(X, N) ≅ (A/ℐ)(N, τX)`, where `τX = D Tr X`. -/
noncomputable def dualExt1EquivCostableHom :
    ((ExactStructure.abelian _).Ext1 X N →ₗ[R] E) ≃ₗ[R]
      ((ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj N ⟶
        (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj
          (matlisDualTranspose R E P)) :=
  (contravariantDefectEquivExt1 R e he X).symm.arrowCongr (LinearEquiv.refl R E) ≪≫ₗ
    Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
      e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e.shortExact.exact) ≪≫ₗ
    covariantDefectEquivCostableHom R E P e he

/-- The defect formula applied to `χ ∘ (δ^*(X) ≅ Ext¹(X, N))`, read in `(A/ℐ)(N, τX)`. -/
theorem dualExt1EquivCostableHom_apply
    (χ : (ExactStructure.abelian _).Ext1 X N →ₗ[R] E) :
    dualExt1EquivCostableHom R E P e he χ =
      covariantDefectEquivCostableHom R E P e he
        (Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
          e.shortExact.moduleCat_injective_f e.shortExact.moduleCat_surjective_g
          ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e.shortExact.exact)
          (χ ∘ₗ (contravariantDefectEquivExt1 R e he X).toLinearMap)) :=
  (rfl)

variable {N'' N''' : ModuleCat.{max u v w} A}
  (e' : (ExactStructure.abelian _).Extension N''' N'')
  (he' : (ExactStructure.abelian _).isInjective e'.obj)
  {a : N ⟶ N''} {a₂ : e.obj ⟶ e'.obj} {a₃ : N' ⟶ N'''}

/-- **Naturality of `D Ext¹(X, N) ≅ (A/ℐ)(N, τX)`** in the short exact sequence. For a morphism
`(a, a₂, a₃)` from `N ⟶ I ⟶ N'` to `N'' ⟶ I' ⟶ N'''`, both with injective middle terms, the dual of
cobase change along `a` corresponds to precomposition with `a`. -/
theorem dualExt1EquivCostableHom_naturality (h₁ : e.f ≫ a₂ = a ≫ e'.f)
    (h₂ : e.g ≫ a₃ = a₂ ≫ e'.g) (χ : (ExactStructure.abelian _).Ext1 X N'' →ₗ[R] E) :
    dualExt1EquivCostableHom R E P e he (χ ∘ₗ Ext1.pushoutLinearMap R a) =
      (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map a ≫
        dualExt1EquivCostableHom R E P e' he' χ := by
  have k₁ : a₂.hom ∘ₗ e.f.hom = e'.f.hom ∘ₗ a.hom := congrArg Hom.hom h₁
  have k₂ : a₃.hom ∘ₗ e.g.hom = e'.g.hom ∘ₗ a₂.hom := congrArg Hom.hom h₂
  have hχ : (χ ∘ₗ Ext1.pushoutLinearMap R a) ∘ₗ
      (contravariantDefectEquivExt1 R e he X).toLinearMap =
        (χ ∘ₗ (contravariantDefectEquivExt1 R e' he' X).toLinearMap) ∘ₗ
          contravariantDefectMap R k₂ X := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, contravariantDefectEquivExt1_mk,
      Ext1.pushoutLinearMap_apply, contravariantDefectMap_mk]
    rw [← Ext1.pushout_pullback, Ext1.pushout_mk_eq_pullback_mk a₂ h₁ h₂.symm,
      Ext1.pullback_pullback]
    rfl
  rw [dualExt1EquivCostableHom_apply, hχ,
    Function.Exact.dualContravariantDefectEquivCovariantDefect_naturality _ _ _ _ _
      e'.shortExact.moduleCat_injective_f e'.shortExact.moduleCat_surjective_g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e'.shortExact.exact) k₁ k₂,
    dualExt1EquivCostableHom_apply]
  generalize Function.Exact.dualContravariantDefectEquivCovariantDefect P.exact P.surjective
    e'.shortExact.moduleCat_injective_f e'.shortExact.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e'.shortExact.exact)
    (χ ∘ₗ (contravariantDefectEquivExt1 R e' he' X).toLinearMap) = y
  induction y using Submodule.Quotient.induction_on with
  | _ u =>
    rw [covariantDefectMap_mk, covariantDefectEquivCostableHom_mk,
      covariantDefectEquivCostableHom_mk, ← Functor.map_comp]
    rfl

/-! ### The Auslander–Reiten formula -/

/-- The **Auslander–Reiten form** `Ext¹(X, τX) → E`, where `τX = D Tr X`: the linear form
corresponding to the identity of `τX` under `D Ext¹(X, τX) ≅ (A/ℐ)(τX, τX)`, for a chosen
embedding of `τX` into an injective module. -/
noncomputable def auslanderReitenForm :
    (ExactStructure.abelian _).Ext1 X (matlisDualTranspose R E P) →ₗ[R] E :=
  (dualExt1EquivCostableHom R E P (InjectivePresentation.abelian _).extension
    (InjectivePresentation.abelian _).isInjective_extension_obj).symm (𝟙 _)

/-- **The Auslander–Reiten formula, as a perfect pairing.** The pairing
`(A/ℐ)(N, τX) → D Ext¹(X, N)`, `a ↦ (ξ ↦ φ(a_* ξ))`, of the Auslander–Reiten form `φ` is
bijective for every module `N`. -/
theorem bijective_costablePairing_auslanderReitenForm (N : ModuleCat.{max u v w} A) :
    Function.Bijective (costablePairing (auslanderReitenForm R E P) N) := by
  let Q := (InjectivePresentation.abelian N).extension
  let T := (InjectivePresentation.abelian (matlisDualTranspose R E P)).extension
  have hT : (ExactStructure.abelian _).isInjective T.obj :=
    (InjectivePresentation.abelian _).isInjective_extension_obj
  suffices h : costablePairing (auslanderReitenForm R E P) N =
      (dualExt1EquivCostableHom R E P Q
        (InjectivePresentation.abelian N).isInjective_extension_obj).symm.toLinearMap by
    rw [h]
    exact LinearEquiv.bijective _
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ :=
    (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map_surjective x
  rw [LinearEquiv.coe_coe, LinearEquiv.eq_symm_apply]
  -- Extend `a` to a morphism from `N ⟶ I ⟶ N'` to the chosen sequence of `τX`.
  let a₂ := hT.factorThru ((ExactStructure.abelian _).isInflation_f Q.conflation) (a ≫ T.f)
  have h₁ : Q.f ≫ a₂ = a ≫ T.f := isInjective.comp_factorThru _ _ _
  have hk : Q.f ≫ a₂ ≫ T.g = 0 := by rw [reassoc_of% h₁, T.zero, Limits.comp_zero]
  have h₂ := Q.isKernelCokernelPair.g_desc (a₂ ≫ T.g) hk
  have hφ : costablePairing (auslanderReitenForm R E P) N
      ((ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map a) =
        auslanderReitenForm R E P ∘ₗ Ext1.pushoutLinearMap R a :=
    LinearMap.ext fun ξ ↦ by simp
  rw [hφ, dualExt1EquivCostableHom_naturality R E P Q _ T hT h₁ h₂, auslanderReitenForm,
    LinearEquiv.apply_symm_apply, Category.comp_id]

/-- **The Auslander–Reiten formula.** Let `A` be an algebra over a commutative ring `R`, `E` an
injective `R`-module and `D = Hom_R(-, E)`. For a module `X` with a presentation `P` by finitely
generated projectives and `τX = D Tr X`, for every module `N`
`D Ext¹_A(X, N) ≅ Hom_A(N, τX)` modulo the maps factoring through injectives, naturally in `N`:
a morphism `a : N ⟶ τX` corresponds to `ξ ↦ φ(a_* ξ)`, for the Auslander–Reiten form `φ`. -/
noncomputable def auslanderReitenFormula (N : ModuleCat.{max u v w} A) :
    ((ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj N ⟶
        (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj
          (matlisDualTranspose R E P)) ≃ₗ[R]
      ((ExactStructure.abelian _).Ext1 X N →ₗ[R] E) :=
  LinearEquiv.ofBijective _ (bijective_costablePairing_auslanderReitenForm R E P N)

/-- The Auslander–Reiten formula is the pairing of the Auslander–Reiten form. -/
@[simp]
theorem auslanderReitenFormula_apply (N : ModuleCat.{max u v w} A)
    (x : (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj N ⟶
      (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj
        (matlisDualTranspose R E P)) :
    auslanderReitenFormula R E P N x = costablePairing (auslanderReitenForm R E P) N x :=
  (rfl)

/-- The Auslander–Reiten formula on the class of `a : N ⟶ τX` evaluates the Auslander–Reiten form
on cobase changes along `a`. -/
theorem auslanderReitenFormula_map_apply {N : ModuleCat.{max u v w} A}
    (a : N ⟶ matlisDualTranspose R E P) (ξ : (ExactStructure.abelian _).Ext1 X N) :
    auslanderReitenFormula R E P N
        ((ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map a) ξ =
      auslanderReitenForm R E P (ξ.pushout a) := by
  simp

/-- **Naturality of the Auslander–Reiten formula in `N`.** Precomposition with `b : N ⟶ N''`
corresponds to the dual of cobase change along `b`. -/
theorem auslanderReitenFormula_naturality {N N'' : ModuleCat.{max u v w} A} (b : N ⟶ N'')
    (x : (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj N'' ⟶
      (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj
        (matlisDualTranspose R E P)) :
    auslanderReitenFormula R E P N
        ((ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map b ≫ x) =
      auslanderReitenFormula R E P N'' x ∘ₗ Ext1.pushoutLinearMap R b := by
  obtain ⟨a, rfl⟩ :=
    (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map_surjective x
  ext ξ
  rw [← Functor.map_comp, auslanderReitenFormula_map_apply, LinearMap.comp_apply,
    Ext1.pushoutLinearMap_apply, auslanderReitenFormula_map_apply, Ext1.pushout_pushout]

end ModuleCat
