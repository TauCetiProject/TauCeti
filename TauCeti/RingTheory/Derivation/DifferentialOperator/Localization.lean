/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Module
public import TauCeti.RingTheory.Derivation.DifferentialOperator.PrincipalParts
public import TauCeti.RingTheory.Derivation.Localization

/-!
# Localization of differential operators and modules of principal parts

Let `A` be a commutative `R`-algebra, `S` a multiplicative submonoid of `A`, `B` a localization of
`A` at `S`, and `fM : M →ₗ[A] M_S` a localization of an `A`-module `M` at `S`. For any `B`-module
`N` and any `m : ℕ`, every differential operator `D : M →ₗ[R] N` of order at most `m` over `A`
extends uniquely along `fM` to a differential operator `M_S →ₗ[R] N` of order at most `m` over `B`.
Consequently, modules of principal parts commute with localization: the natural map
`PrincipalParts R A M m →ₗ[A] PrincipalParts R B M_S m` exhibits `PrincipalParts R B M_S m` as the
localization of `PrincipalParts R A M m` at `S`, and induces a `B`-linear isomorphism
`B ⊗[A] PrincipalParts R A M m ≃ₗ[B] PrincipalParts R B M_S m`.

## Main definitions

* `TauCeti.differentialOperators.extendOfIsLocalization`: the unique extension of
  `D : differentialOperators R A M N m` to `differentialOperators R B M_S N m` when `N` is a
  `B`-module.
* `TauCeti.differentialOperators.extendOfIsLocalizationEquiv`: the `R`-linear equivalence
  `differentialOperators R A M N m ≃ₗ[R] differentialOperators R B M_S N m`.
* `TauCeti.PrincipalParts.tensorLocalizationEquiv`: the `B`-linear isomorphism
  `B ⊗[A] PrincipalParts R A M m ≃ₗ[B] PrincipalParts R B M_S m`.

## Main results

* `IsLocalizedModule.eq_of_mem_differentialOperators` and
  `IsLocalizedModule.eq_zero_of_mem_differentialOperators`: differential operators of finite order
  out of `M_S` into a `B`-module are uniquely determined by their values on the image of `M`.
* `TauCeti.differentialOperators.coe_extendOfIsLocalization_derivation`: compatibility of
  `differentialOperators.extendOfIsLocalization` at order `1` with
  `Derivation.extendOfIsLocalization`.
* `TauCeti.PrincipalParts.isBaseChange_mapAlgebra` and
  `TauCeti.PrincipalParts.isLocalizedModule_mapAlgebra`: `PrincipalParts R B M_S m` is the base
  change along `A → B` (and localization at `S`) of `PrincipalParts R A M m`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §§16.7–16.8,
  especially Propositions (16.7.6) and (16.8.6).
-/

public section

noncomputable section

open scoped TensorProduct

/-! ### Uniqueness on localized modules -/

section Uniqueness

variable {R A B M M_S N : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra A B] [Algebra R B]
  [AddCommMonoid M] [Module A M]
  [AddCommMonoid M_S] [Module R M_S] [Module A M_S] [Module B M_S]
  [IsScalarTower A B M_S] [IsScalarTower R B M_S]
  [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

/-- Two differential operators of finite order from a localized module `M_S` into a `B`-module `N`
are equal once they agree on the image of `M`. -/
theorem IsLocalizedModule.eq_of_mem_differentialOperators (S : Submonoid A) [IsLocalization S B]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {m : ℕ} {E₁ E₂ : M_S →ₗ[R] N}
    (hE₁ : E₁ ∈ TauCeti.differentialOperators R B M_S N m)
    (hE₂ : E₂ ∈ TauCeti.differentialOperators R B M_S N m)
    (hf : ∀ x : M, E₁ (fM x) = E₂ (fM x)) : E₁ = E₂ := by
  induction m generalizing E₁ E₂ with
  | zero =>
    ext y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S fM y
    dsimp only at hs
    apply (IsLocalization.map_units B s).smul_left_cancel.mp
    rw [← TauCeti.mem_differentialOperators_zero_iff.1 hE₁,
      ← TauCeti.mem_differentialOperators_zero_iff.1 hE₂, algebraMap_smul, ← Submonoid.smul_def,
      hs, hf]
  | succ m ih =>
    ext y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S fM y
    dsimp only at hs
    have hC_eq :
        TauCeti.smulCommutator R (algebraMap A B s) E₁ =
          TauCeti.smulCommutator R (algebraMap A B s) E₂ := by
      refine ih ((TauCeti.mem_differentialOperators_succ_iff.1 hE₁) _)
        ((TauCeti.mem_differentialOperators_succ_iff.1 hE₂) _) fun x' ↦ ?_
      rw [TauCeti.smulCommutator_apply_apply, TauCeti.smulCommutator_apply_apply, algebraMap_smul,
        ← map_smul, hf, hf]
    have hy := congr($hC_eq y)
    rw [TauCeti.smulCommutator_apply_apply, TauCeti.smulCommutator_apply_apply, algebraMap_smul,
      ← Submonoid.smul_def, hs, hf, sub_right_inj] at hy
    exact (IsLocalization.map_units B s).smul_left_cancel.mp hy

/-- A differential operator of finite order from a localized module `M_S` into a `B`-module `N` that
vanishes on the image of `M` is identically zero. -/
theorem IsLocalizedModule.eq_zero_of_mem_differentialOperators (S : Submonoid A)
    [IsLocalization S B] (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {m : ℕ} {E : M_S →ₗ[R] N}
    (hE : E ∈ TauCeti.differentialOperators R B M_S N m) (hf : ∀ x : M, E (fM x) = 0) :
    E = 0 :=
  IsLocalizedModule.eq_of_mem_differentialOperators S fM hE (zero_mem _) fun x ↦
    (hf x).trans (LinearMap.zero_apply _).symm

end Uniqueness

namespace TauCeti

/-! ### Extension of differential operators to localizations -/

namespace differentialOperators

section Extend

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M M_S N : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup M_S] [Module R M_S] [Module A M_S]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- Cocycle rule for the localized commutators `C a`: `[D, a₁ * a₂]` acts on `y : M_S` as
`a₁ • C a₂ y + C a₁ (a₂ • y)`. -/
private theorem commutator_mul_eq (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} {D : M →ₗ[R] N} {C : A → M_S →ₗ[R] N}
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x)
    (a₁ a₂ : A) (y : M_S) :
    C (a₁ * a₂) y = algebraMap A B a₁ • C a₂ y + C a₁ (algebraMap A B a₂ • y) := by
  let R_op : M_S →ₗ[R] N :=
    algebraMap A B a₁ • C a₂ +
      C a₁ ∘ₗ (LinearMap.lsmul B M_S (algebraMap A B a₂)).restrictScalars R
  have hR_mem : R_op ∈ differentialOperators R B M_S N m :=
    add_mem (smul_mem_differentialOperators _ (hC_mem a₂))
      (comp_restrictScalars_mem_differentialOperators (hC_mem a₁) _)
  have heq : C (a₁ * a₂) = R_op := by
    refine IsLocalizedModule.eq_of_mem_differentialOperators S fM (hC_mem _) hR_mem fun x ↦ ?_
    simp only [R_op, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.coe_restrictScalars, LinearMap.lsmul_apply, algebraMap_smul, ← map_smul, hC_f,
      smulCommutator_apply_apply, smul_sub, smul_smul]
    abel
  exact congr($heq y)

/-- Scaling `(x, s)` by any `a : A` multiplies `D x - C s y` by `algebraMap A B a`. -/
private theorem scale_sub_commutator (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} {D : M →ₗ[R] N} {C : A → M_S →ₗ[R] N}
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x)
    {y : M_S} {x : M} {s : A} (hs : s • y = fM x) (a : A) :
    algebraMap A B a • (D x - C s y) = D (a • x) - C (a * s) y := by
  have h1 : D (a • x) = algebraMap A B a • D x + C a (algebraMap A B s • y) := by
    rw [algebraMap_smul B s y, hs, hC_f, smulCommutator_apply_apply, algebraMap_smul B a (D x)]
    abel
  rw [h1, commutator_mul_eq S B fM hC_mem hC_f a s y, smul_sub]
  abel

/-- Independence of `(IsLocalization.map_units B s).unit⁻¹ • (D x - C s y)` from the choice of
presentation `s • y = fM x`. -/
private theorem extendSuccFun_wellDefined (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} {D : M →ₗ[R] N} {C : A → M_S →ₗ[R] N}
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x)
    {y : M_S} {x₁ x₂ : M} {s₁ s₂ : S} (hs₁ : s₁ • y = fM x₁) (hs₂ : s₂ • y = fM x₂) :
    ((IsLocalization.map_units B s₁).unit⁻¹ : Bˣ) • (D x₁ - C s₁ y) =
      ((IsLocalization.map_units B s₂).unit⁻¹ : Bˣ) • (D x₂ - C s₂ y) := by
  have hs₁' : (s₁ : A) • y = fM x₁ := by simpa [Submonoid.smul_def] using hs₁
  have hs₂' : (s₂ : A) • y = fM x₂ := by simpa [Submonoid.smul_def] using hs₂
  have hfeq : fM ((s₂ : A) • x₁) = fM ((s₁ : A) • x₂) := by
    rw [map_smul, map_smul, ← hs₁', ← hs₂', smul_comm]
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) hfeq
  have hcross :
      algebraMap A B s₂ • (D x₁ - C s₁ y) = algebraMap A B s₁ • (D x₂ - C s₂ y) := by
    apply (IsLocalization.map_units B t).smul_left_cancel.mp
    have hs₁₂ : ((s₂ : A) * s₁) • y = fM ((s₂ : A) • x₁) := by
      rw [mul_smul, hs₁', map_smul]
    have hs₂₁ : ((s₁ : A) * s₂) • y = fM ((s₁ : A) • x₂) := by
      rw [mul_smul, hs₂', map_smul]
    rw [scale_sub_commutator S B fM hC_mem hC_f hs₁' s₂,
      scale_sub_commutator S B fM hC_mem hC_f hs₂' s₁,
      scale_sub_commutator S B fM hC_mem hC_f hs₁₂ t,
      scale_sub_commutator S B fM hC_mem hC_f hs₂₁ t]
    rw [Submonoid.smul_def, Submonoid.smul_def] at ht
    rw [ht, mul_comm (s₂ : A) s₁]
  apply (IsLocalization.map_units B s₁).smul_left_cancel.mp
  apply (IsLocalization.map_units B s₂).smul_left_cancel.mp
  have h₁ (z : N) :
      algebraMap A B s₁ • (((IsLocalization.map_units B s₁).unit⁻¹ : Bˣ) • z) = z := by
    simpa [Units.smul_def] using smul_inv_smul (IsLocalization.map_units B s₁).unit z
  have h₂ (z : N) :
      algebraMap A B s₂ • (((IsLocalization.map_units B s₂).unit⁻¹ : Bˣ) • z) = z := by
    simpa [Units.smul_def] using smul_inv_smul (IsLocalization.map_units B s₂).unit z
  rw [h₁, smul_comm (algebraMap A B s₂) (algebraMap A B s₁), h₂]
  exact hcross

private def extendSuccFun (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [IsLocalization S B] [Module B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    (D : M →ₗ[R] N) (C : A → M_S →ₗ[R] N) (y : M_S) : N :=
  let p := (IsLocalizedModule.surj S fM y).choose
  ((IsLocalization.map_units B p.2).unit⁻¹ : Bˣ) • (D p.1 - C p.2 y)

private theorem smul_extendSuccFun (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} {D : M →ₗ[R] N} {C : A → M_S →ₗ[R] N}
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x)
    {y : M_S} {x : M} {s : S} (hs : s • y = fM x) :
    algebraMap A B s • extendSuccFun S B fM D C y = D x - C s y := by
  dsimp only [extendSuccFun]
  rw [extendSuccFun_wellDefined S B fM hC_mem hC_f (IsLocalizedModule.surj S fM y).choose_spec hs]
  simpa [Units.smul_def] using smul_inv_smul (IsLocalization.map_units B s).unit (D x - C s y)

private def extendSuccLinearMap (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} (D : M →ₗ[R] N) (C : A → M_S →ₗ[R] N)
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x) : M_S →ₗ[R] N where
  toFun := extendSuccFun S B fM D C
  map_add' y₁ y₂ := by
    obtain ⟨⟨x₁, s₁⟩, hs₁⟩ := IsLocalizedModule.surj S fM y₁
    obtain ⟨⟨x₂, s₂⟩, hs₂⟩ := IsLocalizedModule.surj S fM y₂
    dsimp only at hs₁ hs₂
    have h₁ : (s₁ * s₂) • y₁ = fM ((s₂ : A) • x₁) := by
      rw [mul_comm, mul_smul, hs₁, Submonoid.smul_def, map_smul]
    have h₂ : (s₁ * s₂) • y₂ = fM ((s₁ : A) • x₂) := by
      rw [mul_smul, hs₂, Submonoid.smul_def, map_smul]
    have h₁₂ : (s₁ * s₂) • (y₁ + y₂) = fM ((s₂ : A) • x₁ + (s₁ : A) • x₂) := by
      rw [smul_add, h₁, h₂, map_add]
    apply (IsLocalization.map_units B (s₁ * s₂)).smul_left_cancel.mp
    rw [smul_add, smul_extendSuccFun S B fM hC_mem hC_f h₁₂,
      smul_extendSuccFun S B fM hC_mem hC_f h₁, smul_extendSuccFun S B fM hC_mem hC_f h₂,
      map_add, map_add]
    abel
  map_smul' r y := by
    have := IsScalarTower.to₁₂₄ R A B M_S
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S fM y
    dsimp only at hs
    have hs' : (s : A) • y = fM x := by simpa [Submonoid.smul_def] using hs
    have hrs : s • (r • y) = fM (r • x) := by
      simp [Submonoid.smul_def, fM.map_smul_of_tower, ← hs', smul_comm (s : A) r y]
    apply (IsLocalization.map_units B s).smul_left_cancel.mp
    rw [RingHom.id_apply, smul_extendSuccFun S B fM hC_mem hC_f hrs, smul_comm _ r,
      smul_extendSuccFun S B fM hC_mem hC_f hs, map_smul, map_smul, smul_sub]

@[simp]
private theorem extendSuccLinearMap_apply (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} (D : M →ₗ[R] N) (C : A → M_S →ₗ[R] N)
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x) (y : M_S) :
    extendSuccLinearMap S B fM D C hC_mem hC_f y = extendSuccFun S B fM D C y :=
  rfl

private theorem extendSuccLinearMap_apply_f (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} {D : M →ₗ[R] N} {C : A → M_S →ₗ[R] N}
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x) (x : M) :
    extendSuccLinearMap S B fM D C hC_mem hC_f (fM x) = D x := by
  have h1 := smul_extendSuccFun S B fM hC_mem hC_f (s := 1) (one_smul S (fM x))
  have hC1 : C 1 (fM x) = 0 := by simp [hC_f]
  simpa [hC1] using h1

private theorem smulCommutator_algebraMap_extendSuccLinearMap (S : Submonoid A) (B : Type*)
    [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} {D : M →ₗ[R] N} {C : A → M_S →ₗ[R] N}
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x) (a : A) :
    smulCommutator R (algebraMap A B a) (extendSuccLinearMap S B fM D C hC_mem hC_f) =
      C a := by
  ext y
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S fM y
  dsimp only at hs
  have hs' : (s : A) • y = fM x := by simpa [Submonoid.smul_def] using hs
  have hay : s • (algebraMap A B a • y) = fM (a • x) := by
    simp [Submonoid.smul_def, algebraMap_smul, smul_comm (s : A) a y, hs']
  apply (IsLocalization.map_units B s).smul_left_cancel.mp
  rw [smulCommutator_apply_apply, smul_sub, extendSuccLinearMap_apply, extendSuccLinearMap_apply,
    smul_extendSuccFun S B fM hC_mem hC_f hay, smul_comm (algebraMap A B s) (algebraMap A B a),
    smul_extendSuccFun S B fM hC_mem hC_f hs,
    scale_sub_commutator S B fM hC_mem hC_f hs' a,
    mul_comm a (s : A), commutator_mul_eq S B fM hC_mem hC_f s a y]
  abel

private theorem extendSuccLinearMap_mem_differentialOperators (S : Submonoid A) (B : Type*)
    [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]
    {m : ℕ} {D : M →ₗ[R] N} {C : A → M_S →ₗ[R] N}
    (hC_mem : ∀ a : A, C a ∈ differentialOperators R B M_S N m)
    (hC_f : ∀ (a : A) (x : M), C a (fM x) = smulCommutator R a D x) :
    extendSuccLinearMap S B fM D C hC_mem hC_f ∈
      differentialOperators R B M_S N (m + 1) := by
  let E := extendSuccLinearMap S B fM D C hC_mem hC_f
  rw [mem_differentialOperators_succ_iff]
  intro b
  obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.surj S b
  dsimp only at ht
  have hmul :
      C a = algebraMap A B t • smulCommutator R b E + b • C t + smulCommutator R b (C t) := by
    rw [← smulCommutator_algebraMap_extendSuccLinearMap S B fM hC_mem hC_f a, ← ht, mul_comm b,
      smulCommutator_mul, smulCommutator_algebraMap_extendSuccLinearMap S B fM hC_mem hC_f t]
  have hsub : algebraMap A B t • smulCommutator R b E ∈ differentialOperators R B M_S N m := by
    have h1 : b • C t ∈ differentialOperators R B M_S N m :=
      smul_mem_differentialOperators b (hC_mem t)
    have h2 : smulCommutator R b (C t) ∈ differentialOperators R B M_S N m :=
      (mem_differentialOperators_succ_iff.1 (differentialOperators_le_succ m (hC_mem t))) b
    have heq :
        algebraMap A B t • smulCommutator R b E = C a - (b • C t + smulCommutator R b (C t)) := by
      rw [hmul]; abel
    rw [heq]
    exact sub_mem (hC_mem a) (add_mem h1 h2)
  have hinv :
      (((IsLocalization.map_units B t).unit⁻¹ : Bˣ) : B) •
        (algebraMap A B t • smulCommutator R b E) ∈ differentialOperators R B M_S N m :=
    smul_mem_differentialOperators _ hsub
  have hcancel :
      (((IsLocalization.map_units B t).unit⁻¹ : Bˣ) : B) •
        (algebraMap A B t • smulCommutator R b E) = smulCommutator R b E := by
    simpa [Units.smul_def] using
      inv_smul_smul (IsLocalization.map_units B t).unit (smulCommutator R b E)
  rwa [hcancel] at hinv

private def extendAux (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] :
    ∀ {m : ℕ} (D : differentialOperators R A M N m),
      { E : differentialOperators R B M_S N m //
        ∀ x : M, (E : M_S →ₗ[R] N) (fM x) = (D : M →ₗ[R] N) x }
  | 0, D =>
    letI := isLocalizedModule_id S N B
    let g := IsLocalizedModule.lift S fM (differentialOperatorsZeroEquiv R A M N D)
      (IsLocalizedModule.map_units (LinearMap.id : N →ₗ[A] N))
    ⟨(differentialOperatorsZeroEquiv R B M_S N).symm (g.extendScalarsOfIsLocalization S B),
      fun x ↦ by simp [g]⟩
  | m + 1, D =>
    let c := fun a : A ↦
      extendAux S B fM
        ⟨smulCommutator R a D.val, (mem_differentialOperators_succ_iff.1 D.property) a⟩
    ⟨⟨extendSuccLinearMap S B fM D.val (fun a ↦ (c a).val.val) (fun a ↦ (c a).val.property)
        (fun a ↦ (c a).property),
      extendSuccLinearMap_mem_differentialOperators S B fM
        (fun a ↦ (c a).val.property) (fun a ↦ (c a).property)⟩,
      extendSuccLinearMap_apply_f S B fM (fun a ↦ (c a).val.property) (fun a ↦ (c a).property)⟩

/-- Every differential operator `D : differentialOperators R A M N m` into a `B`-module `N` extends
uniquely along a module localization `fM : M →ₗ[A] M_S` to `differentialOperators R B M_S N m`. -/
def extendOfIsLocalization (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {m : ℕ}
    (D : differentialOperators R A M N m) :
    differentialOperators R B M_S N m :=
  (extendAux S B fM D).val

@[simp]
theorem extendOfIsLocalization_apply (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {m : ℕ}
    (D : differentialOperators R A M N m) (x : M) :
    (extendOfIsLocalization S B fM D : M_S →ₗ[R] N) (fM x) = (D : M →ₗ[R] N) x :=
  (extendAux S B fM D).property x

/-- Uniqueness characterization of `extendOfIsLocalization`. -/
theorem eq_extendOfIsLocalization (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {m : ℕ}
    {D : differentialOperators R A M N m} {E : differentialOperators R B M_S N m}
    (hE : ∀ x : M, (E : M_S →ₗ[R] N) (fM x) = (D : M →ₗ[R] N) x) :
    E = extendOfIsLocalization S B fM D :=
  Subtype.ext <| IsLocalizedModule.eq_of_mem_differentialOperators S fM E.property
    (extendOfIsLocalization S B fM D).property fun x ↦
      (hE x).trans (extendOfIsLocalization_apply S B fM D x).symm

@[simp]
theorem extendOfIsLocalization_smul (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {m : ℕ}
    (a : A) (D : differentialOperators R A M N m) :
    extendOfIsLocalization S B fM (a • D) =
      algebraMap A B a • extendOfIsLocalization S B fM D :=
  (eq_extendOfIsLocalization S B fM fun x ↦ by simp [algebraMap_smul]).symm

/-- Extending differential operators along a localization `fM : M →ₗ[A] M_S` is an `R`-linear
equivalence `differentialOperators R A M N m ≃ₗ[R] differentialOperators R B M_S N m` when `N` is a
`B`-module. -/
def extendOfIsLocalizationEquiv (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] (m : ℕ) :
    differentialOperators R A M N m ≃ₗ[R] differentialOperators R B M_S N m :=
  LinearEquiv.ofLinearMap
    { toFun := extendOfIsLocalization S B fM
      map_add' := fun _ _ ↦ (eq_extendOfIsLocalization S B fM fun x ↦ by simp).symm
      map_smul' := fun _ _ ↦ (eq_extendOfIsLocalization S B fM fun x ↦ by simp).symm }
    (restrictOfAlgebra B fM m)
    (LinearMap.ext fun _ ↦ (eq_extendOfIsLocalization S B fM fun _ ↦ by simp).symm)
    (LinearMap.ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp)

@[simp]
theorem extendOfIsLocalizationEquiv_apply (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {m : ℕ}
    (D : differentialOperators R A M N m) :
    extendOfIsLocalizationEquiv S B fM m D = extendOfIsLocalization S B fM D := by
  rfl

@[simp]
theorem extendOfIsLocalizationEquiv_symm_apply (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {m : ℕ}
    (E : differentialOperators R B M_S N m) :
    (extendOfIsLocalizationEquiv S B fM m).symm E = restrictOfAlgebra B fM m E := by
  rfl

/-- Compatibility of `extendOfIsLocalization` with order monotonicity `n ≤ m`. -/
theorem inclusion_extendOfIsLocalization (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B M_S] [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] {n m : ℕ} (h : n ≤ m)
    (D : differentialOperators R A M N n) :
    Submodule.inclusion (differentialOperators_mono h) (extendOfIsLocalization S B fM D) =
      extendOfIsLocalization S B fM (Submodule.inclusion (differentialOperators_mono h) D) :=
  eq_extendOfIsLocalization S B fM fun x ↦ extendOfIsLocalization_apply S B fM D x

/-- Compatibility of `extendOfIsLocalization` at order `1` with `Derivation.extendOfIsLocalization`:
extending an `R`-derivation `A → N` as a derivation agrees with extending it as a first-order
differential operator. -/
theorem coe_extendOfIsLocalization_derivation (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization S B]
    [Module B N] [IsScalarTower A B N] [IsScalarTower R B N]
    (D : Derivation R A N) :
    (D.extendOfIsLocalization S (T := B)).toLinearMap =
      (extendOfIsLocalization S B (Algebra.linearMap A B)
        ⟨D.toLinearMap, D.mem_differentialOperators_one⟩ : B →ₗ[R] N) := by
  refine IsLocalizedModule.eq_of_mem_differentialOperators S (Algebra.linearMap A B)
    (D.extendOfIsLocalization S (T := B)).mem_differentialOperators_one
    (extendOfIsLocalization S B (Algebra.linearMap A B)
      ⟨D.toLinearMap, D.mem_differentialOperators_one⟩).property fun a ↦ ?_
  rw [extendOfIsLocalization_apply]
  simp

end Extend

end differentialOperators

/-! ### Base change and localization of `PrincipalParts` -/

namespace PrincipalParts

section Localization

private def jetIntoTensor (R B : Type*) {A M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (m : ℕ) :
    differentialOperators R A M (B ⊗[A] PrincipalParts R A M m) m :=
  ⟨(TensorProduct.AlgebraTensorModule.mk A B B (PrincipalParts R A M m) 1).restrictScalars R ∘ₗ
      jet R A M m,
    LinearMap.restrictScalars_comp_mem_differentialOperators
      (TensorProduct.mk A B (PrincipalParts R A M m) 1) (jet_mem_differentialOperators m)⟩

/-- Modules of principal parts commute with localization: for a localization `B` of `A` at `S` and
`fM : M →ₗ[A] M_S` a localization of `M` at `S`, `B ⊗[A] PrincipalParts R A M m` is canonically
`B`-linearly isomorphic to `PrincipalParts R B M_S m`. -/
def tensorLocalizationEquiv (R : Type*) {A M M_S : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsLocalization S B]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup M_S] [Module R M_S] [Module A M_S] [Module B M_S]
    [IsScalarTower A B M_S] [IsScalarTower R B M_S]
    (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM] (m : ℕ) :
    B ⊗[A] PrincipalParts R A M m ≃ₗ[B] PrincipalParts R B M_S m :=
  LinearEquiv.ofLinearMap
    ((mapAlgebra R B fM m).liftBaseChange B)
    (lift (differentialOperators.extendOfIsLocalization S B fM (jetIntoTensor R B m)))
    (hom_ext fun y ↦ by
      let lhs : M_S →ₗ[R] PrincipalParts R B M_S m :=
        (((mapAlgebra R B fM m).liftBaseChange B).restrictScalars R) ∘ₗ
          ((lift (differentialOperators.extendOfIsLocalization S B fM
            (jetIntoTensor R B m))).restrictScalars R) ∘ₗ jet R B M_S m
      have hlhs : lhs ∈ differentialOperators R B M_S (PrincipalParts R B M_S m) m :=
        LinearMap.restrictScalars_comp_mem_differentialOperators _
          (LinearMap.restrictScalars_comp_mem_differentialOperators _
            (jet_mem_differentialOperators m))
      have heq : lhs = jet R B M_S m := by
        refine IsLocalizedModule.eq_of_mem_differentialOperators S fM hlhs
          (jet_mem_differentialOperators m) fun x ↦ ?_
        simp [lhs, jetIntoTensor]
      exact congr($heq y))
    (TensorProduct.AlgebraTensorModule.ext fun b z ↦ by
      have hb : b ⊗ₜ[A] z = b • ((1 : B) ⊗ₜ[A] z) := by simp [TensorProduct.smul_tmul']
      rw [hb, map_smul, map_smul]
      congr 1
      let inv := lift (differentialOperators.extendOfIsLocalization S B fM (jetIntoTensor R B m))
      let lhs : PrincipalParts R A M m →ₗ[A] B ⊗[A] PrincipalParts R A M m :=
        inv.restrictScalars A ∘ₗ mapAlgebra R B fM m
      have heq : lhs = TensorProduct.mk A B (PrincipalParts R A M m) 1 :=
        hom_ext fun x ↦ by simp [lhs, inv, jetIntoTensor]
      simpa [lhs, inv] using congr($heq z))

section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [IsLocalization S B]
  {M M_S : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup M_S] [Module R M_S] [Module A M_S] [Module B M_S]
  [IsScalarTower A B M_S] [IsScalarTower R B M_S]
  (fM : M →ₗ[A] M_S) [IsLocalizedModule S fM]

@[simp]
theorem tensorLocalizationEquiv_tmul (m : ℕ) (b : B) (z : PrincipalParts R A M m) :
    tensorLocalizationEquiv R S B fM m (b ⊗ₜ[A] z) = b • mapAlgebra R B fM m z := by
  rfl

theorem tensorLocalizationEquiv_tmul_jet (m : ℕ) (b : B) (x : M) :
    tensorLocalizationEquiv R S B fM m (b ⊗ₜ[A] jet R A M m x) =
      b • jet R B M_S m (fM x) := by
  simp

@[simp]
theorem tensorLocalizationEquiv_symm_jet (m : ℕ) (x : M) :
    (tensorLocalizationEquiv R S B fM m).symm (jet R B M_S m (fM x)) =
      (1 : B) ⊗ₜ[A] jet R A M m x := by
  apply (tensorLocalizationEquiv R S B fM m).injective
  simp

include S in
variable (R) in
/-- `PrincipalParts R B M_S m` is the base change of `PrincipalParts R A M m` along a localization
`A → B`. -/
theorem isBaseChange_mapAlgebra (m : ℕ) :
    IsBaseChange B (mapAlgebra R B fM m) :=
  IsBaseChange.of_equiv (tensorLocalizationEquiv R S B fM m) fun z ↦ by simp

variable (R) in
/-- `PrincipalParts R B M_S m` is the localization of `PrincipalParts R A M m` at `S`. -/
theorem isLocalizedModule_mapAlgebra (m : ℕ) :
    IsLocalizedModule S (mapAlgebra R B fM m) :=
  (isLocalizedModule_iff_isBaseChange S B _).2 (isBaseChange_mapAlgebra R S B fM m)

end

end Localization

end PrincipalParts

end TauCeti
