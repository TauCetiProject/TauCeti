/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.GroupWithZero.Action.Regular
import TauCeti.Algebra.TensorProduct.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor kernels after localization

Localization makes a tensor map injective exactly when every element of the original tensor
kernel is killed by an element of the localization submonoid.
-/

public section

open TensorProduct LinearMap

namespace IsLocalizedModule

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- A tensor map is injective after localization exactly when its original kernel is torsion
with respect to the localization submonoid. -/
theorem lTensor_injective_iff (T : Submonoid S)
    {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
    (l : M →ₗ[S] Mp) [IsLocalizedModule T l]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') :
    Function.Injective (f.lTensor Mp) ↔
      ∀ t : M ⊗[R] N, f.lTensor M t = 0 → ∃ s ∈ T, s • t = 0 := by
  let g := AlgebraTensorModule.rTensor R N l
  let h := AlgebraTensorModule.rTensor R N' l
  have : IsLocalizedModule T g := IsLocalizedModule.rTensor (A := S) T l
  have : IsLocalizedModule T h := IsLocalizedModule.rTensor (A := S) T l
  have square (t : M ⊗[R] N) : f.lTensor Mp (g t) = h (f.lTensor M t) := by
    simp only [g, h, AlgebraTensorModule.coe_rTensor]
    exact LinearMap.lTensor_rTensor_comm (l.restrictScalars R) f t
  constructor
  · intro hf t ht
    have hg : g t = 0 := hf (by rw [square, ht, map_zero, map_zero])
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff T (f := g)).mp hg
    exact ⟨s, s.property, hs⟩
  · intro hf
    refine IsLocalizedModule.injective_of_map_zero T g (g :=
      AlgebraTensorModule.lTensor S Mp f) fun t ht ↦ ?_
    have hh : h (f.lTensor M t) = 0 := (square t).symm.trans ht
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff T (f := h)).mp hh
    obtain ⟨u, hu, hut⟩ := hf (s.val • t) (by
      rw [← AlgebraTensorModule.coe_lTensor (A := S), map_smul]
      exact hs)
    apply IsLocalizedModule.smul_injective g (⟨u, hu⟩ * s)
    simp only [Submonoid.smul_def, Submonoid.coe_mul]
    rw [← map_smul, mul_smul, hut, map_zero, smul_zero]

end IsLocalizedModule

namespace Module

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R₀ R₁ S₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀]

/-- Injectivity at the prime of the original algebra persists at a prime after base change. -/
theorem lTensor_injective_localization_tensor (q₁ : Ideal (R₁ ⊗[R₀] S₀)) [q₁.IsPrime]
    {M N' : Type*} [AddCommGroup M] [Module R₀ M]
        [Module R₁ M] [IsScalarTower R₀ R₁ M]
    [AddCommGroup N'] [Module R₀ N'] [Module R₁ N'] [IsScalarTower R₀ R₁ N'] (f : N' →ₗ[R₁]
        M)
    (h : Function.Injective ((f.restrictScalars R₀).lTensor
      (Localization.AtPrime (q₁.comap Algebra.TensorProduct.includeRight.toRingHom)))) :
    Function.Injective (f.lTensor (Localization.AtPrime q₁)) := by
  set q₀ := q₁.comap (Algebra.TensorProduct.includeRight.toRingHom : S₀ →+* R₁ ⊗[R₀] S₀)
  rw [IsLocalizedModule.lTensor_injective_iff q₀.primeCompl
    (Algebra.linearMap S₀ (Localization.AtPrime q₀))] at h
  rw [IsLocalizedModule.lTensor_injective_iff q₁.primeCompl
    (Algebra.linearMap _ (Localization.AtPrime q₁))]
  intro y hy
  obtain ⟨t, ht, hty⟩ := h
      (Algebra.IsPushout.cancelBaseChange R₀ S₀ R₁ (R₁ ⊗[R₀] S₀) N' y)
      (by
    rw [← Algebra.TensorProduct.cancelBaseChange_lTensor, hy, map_zero])
  refine ⟨1 ⊗ₜ t, ht, ?_⟩
  apply (Algebra.IsPushout.cancelBaseChange R₀ S₀ R₁ (R₁ ⊗[R₀] S₀) N').injective
  rw [← Algebra.TensorProduct.right_algebraMap_apply, algebraMap_smul,
    map_smul, hty, map_zero]

end Module


namespace Algebra

/-- A denominator annihilating the tensor kernel gives regularity after localization. -/
lemma isSMulRegular_localized_tensor_of_kernel
    {R B N : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] (q : Ideal B) [q.IsPrime]
    (b t : B) (ht : t ∉ q)
    (hker : ∀ x : B ⊗[R] N, b • x = 0 → t • x = 0) :
    IsSMulRegular (Localization.AtPrime q ⊗[R] N)
      (algebraMap B (Localization.AtPrime q) b) := by
  refine IsSMulRegular.of_right_eq_zero_of_smul (R := Localization.AtPrime q)
    (M := Localization.AtPrime q ⊗[R] N) fun z hz ↦ ?_
  let ℓ := AlgebraTensorModule.rTensor R N (Algebra.linearMap B (Localization.AtPrime q))
  have : IsLocalizedModule q.primeCompl ℓ := IsLocalizedModule.rTensor (A := B) _ _
  obtain ⟨⟨z', s⟩, hu⟩ := IsLocalizedModule.surj q.primeCompl ℓ z
  simp only [Submonoid.smul_def] at hu
  have h1 : ℓ (b • z') = 0 := by
    rw [map_smul, ← hu, smul_comm, ← algebraMap_smul (Localization.AtPrime q) b z,
      hz, smul_zero]
  obtain ⟨u', hu'⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl (f := ℓ)).mp h1
  rw [Submonoid.smul_def] at hu'
  have h2 : t • ((u' : B) • z') = 0 := hker _ (by rw [smul_comm,
    hu'])
  have h3 : (t * u' * s : B) • z = 0 := by
    rw [mul_smul (t * u'), hu, ← map_smul, mul_smul, h2, LinearMap.map_zero]
  refine (Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units ℓ (⟨t, ht⟩ * u' * s)) |>.1 ?_
  rw [LinearMap.map_zero, Module.algebraMap_end_apply]
  exact h3

end Algebra

namespace Module

universe u

variable {R₀ R₁ S₀ : Type u} [CommRing R₀] [CommRing R₁] [CommRing S₀]
  [Algebra R₀ R₁] [Algebra R₀ S₀]

/-- A tensor map that kills the multiplication kernel continues to kill that kernel
after localizing the algebra at a prime. -/
theorem lTensor_eq_zero_of_localization
    (q : Ideal S₀) [q.IsPrime] (I : Ideal R₀) {N : Type*} [AddCommGroup N] [Module R₀ N]
    (σ : I →ₗ[R₀] N)
    (h : ∀ ξ : S₀ ⊗[R₀] I,
      TensorProduct.rid R₀ S₀ (I.subtype.lTensor S₀ ξ) = 0 → σ.lTensor S₀ ξ = 0)
    (ξ : Localization.AtPrime q ⊗[R₀] I)
    (hk : TensorProduct.rid R₀ (Localization.AtPrime q)
      (I.subtype.lTensor (Localization.AtPrime q) ξ) = 0) :
    σ.lTensor (Localization.AtPrime q) ξ = 0 := by
  let M := Localization.AtPrime q
  let ℓ : S₀ →ₗ[S₀] M := Algebra.linearMap S₀ M
  let g' : S₀ ⊗[R₀] I →ₗ[S₀] M ⊗[R₀] I := AlgebraTensorModule.rTensor R₀ I ℓ
  let gL : S₀ ⊗[R₀] N →ₗ[S₀] M ⊗[R₀] N := AlgebraTensorModule.rTensor R₀ N ℓ
  have : IsLocalizedModule q.primeCompl g' := IsLocalizedModule.rTensor (A := S₀) _ ℓ
  have : IsLocalizedModule q.primeCompl gL := IsLocalizedModule.rTensor (A := S₀) _ ℓ
  let μ : M ⊗[R₀] I →ₗ[S₀] M := (AlgebraTensorModule.rid R₀ S₀ M).toLinearMap ∘ₗ
    AlgebraTensorModule.lTensor S₀ M I.subtype
  let μ' : S₀ ⊗[R₀] I →ₗ[S₀] S₀ := (AlgebraTensorModule.rid R₀ S₀ S₀).toLinearMap ∘ₗ
    AlgebraTensorModule.lTensor S₀ S₀ I.subtype
  have hnat1 (x : S₀ ⊗[R₀] I) : μ (g' x) = ℓ (μ' x) := by
    induction x with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul s a =>
      simp [μ, μ', g', ℓ, Algebra.smul_def, IsScalarTower.algebraMap_apply R₀ S₀ M]
  have hnat2 (x : S₀ ⊗[R₀] I) : AlgebraTensorModule.lTensor S₀ M σ (g' x) =
      gL (AlgebraTensorModule.lTensor S₀ S₀ σ x) := by
    induction x with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul s a => rfl
  obtain ⟨⟨k', s⟩, hs⟩ := IsLocalizedModule.surj q.primeCompl g' ξ
  simp only [Submonoid.smul_def] at hs
  have h1 : ℓ (μ' k') = 0 := by
    rw [← hnat1, ← hs, map_smul]
    -- The localized algebra-linear tensor map restricts to the original base-linear map.
    change (s : S₀) • (TensorProduct.rid R₀ M (I.subtype.lTensor M ξ)) = 0
    rw [hk, smul_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl (f := ℓ)).mp h1
  rw [Submonoid.smul_def, ← map_smul] at ht
  have hμ' (x) : μ' x = TensorProduct.rid R₀ S₀ (I.subtype.lTensor S₀ x) :=
    -- The algebra-linear multiplication map restricts to this base-linear map.
    (rfl)
  rw [hμ'] at ht
  have hker : TensorProduct.rid R₀ S₀ (I.subtype.lTensor S₀ ((t : S₀) • k')) = 0 := ht
  have h3 : AlgebraTensorModule.lTensor S₀ S₀ σ ((t : S₀) • k') = 0 := h _ hker
  have h4 : ((t : S₀) * s) • AlgebraTensorModule.lTensor S₀ M σ ξ = 0 := by
    rw [mul_smul, ← map_smul, hs, ← map_smul, ← map_smul g', hnat2, h3, map_zero]
  have hu := IsLocalizedModule.map_units gL
    ⟨t * s, mul_mem t.property s.property⟩
  refine (Module.End.isUnit_iff _).mp hu |>.1 ?_
  rw [map_zero, Module.algebraMap_end_apply]
  exact h4

/-- Contracting a prime of a tensor product to the base and extending it to the
localized tensor product gives an ideal in the Jacobson radical. -/
theorem mapIdeal_le_jacobson_localization_tensor
    (q : Ideal (R₁ ⊗[R₀] S₀)) [q.IsPrime] :
    (((q.comap Algebra.TensorProduct.includeRight.toRingHom).comap (algebraMap R₀ S₀)).map
      (algebraMap R₀ R₁)).map (algebraMap R₁ (Localization.AtPrime q)) ≤ Ideal.jacobson ⊥ := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap,
    Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, Ideal.mem_comap,
    IsScalarTower.algebraMap_apply R₁ (R₁ ⊗[R₀] S₀) (Localization.AtPrime q),
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q,
    ← IsScalarTower.algebraMap_apply R₀ R₁ (R₁ ⊗[R₀] S₀),
    ← (Algebra.TensorProduct.includeRight : S₀ →ₐ[R₀] R₁ ⊗[R₀] S₀).commutes r]
  exact hr

end Module
