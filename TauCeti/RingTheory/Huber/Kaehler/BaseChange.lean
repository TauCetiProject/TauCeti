/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Map
public import TauCeti.RingTheory.Huber.Kaehler.UniversalProperty
public import TauCeti.RingTheory.Huber.NoetherianType.Basic

import TauCeti.RingTheory.Huber.TensorProduct.Derivation

/-!
# Completed base change for continuous differentials

This file establishes Huber (1996), §1.6, Proposition 1.6.3(iii): for `A → B` topologically of
finite type into a complete Hausdorff Huber ring `B` of noetherian type and `A → A'` adic into a
Huber ring `A'` of noetherian type (no completeness on `A'`), there is a `B'`-linear isomorphism
`Ωᶜ[B'⁄A'] ≃ₗ[B'] B' ⊗[B] Ωᶜ[B⁄A]` for `B' = B ⊗̂_A A'` (`baseChangeEquiv`), generalizing Mathlib's
`KaehlerDifferential.tensorKaehlerEquiv` (`Mathlib.RingTheory.Kaehler.TensorProduct`), with
`CompletedTensor.leftAlgebra`, `CompletedTensor.rightAlgebra`, and `isAdicHom_rightAlgebra`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Proposition 1.6.3(iii).
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

section BaseChange

variable {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
  [Algebra A B] [Algebra A A']
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B]
  [TopologicalSpace A'] [IsTopologicalRing A'] [IsHuberRing A'] [IsNoetherianType A']
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A A')]

attribute [local instance] leftAlgebra rightAlgebra isAdicHom_rightAlgebra

omit [IsUniformAddGroup B] [IsHuberRing B] [CompleteSpace B] [T0Space B] [IsNoetherianType B]
  [IsNoetherianType A'] in
private theorem baseChange_isTopologicallyFiniteType
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    IsTopologicallyFiniteType (algebraMap A' (CompletedTensor A B A')) := by
  rw [algebraMap_rightAlgebra]; exact isTopologicallyFiniteType_inr hAB

/-- Equip `(B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]` with its natural `(B ⊗̂_A A')`-module topology and construct
the universal continuous `A'`-derivation `B ⊗̂_A A' → (B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]`. -/
private noncomputable def baseChangeDerivation
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    let B' := CompletedTensor A B A'
    let M := B' ⊗[B] ContinuousKaehlerDifferential A B
    letI : TopologicalSpace M := moduleTopology B' M
    {δ : Derivation A' B' M // Continuous δ ∧ ∀ b : B, δ (inl A B A' b) = 1 ⊗ₜ[B] D A B b} := by
  let B' := CompletedTensor A B A'
  let M := B' ⊗[B] ContinuousKaehlerDifferential A B
  have : IsNoetherianType B' :=
    .of_isTopologicallyFiniteType (baseChange_isTopologicallyFiniteType hAB)
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  letI : TopologicalSpace M := moduleTopology B' M
  have : IsModuleTopology B' M := ⟨rfl⟩
  letI : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup B' M
  letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  obtain ⟨_, _, _, _⟩ :=
    IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology (A := B') (M := M)
  haveI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a ↦ by simp [B']
  have : ContinuousSMul B B' := continuousSMul_of_algebraMap B B'
    (by rw [algebraMap_leftAlgebra]; exact continuous_inl A B A')
  have : ContinuousSMul B M := IsScalarTower.continuousSMul B'
  let dB : Derivation A B M :=
    (TensorProduct.mk B B' (ContinuousKaehlerDifferential A B) 1).compDer (D A B)
  have hdB : Continuous dB := (IsModuleTopology.continuous_of_linearMap
    (TensorProduct.mk B B' (ContinuousKaehlerDifferential A B) 1)).comp (continuous_D hAB)
  have hinl : (algebraMap B' B').comp (inl A B A') = algebraMap B B' := by simp [B']
  have hinr : (algebraMap B' B').comp (inr A B A') = algebraMap A' B' := by simp [B']
  let dA : Derivation A B' M := CompletedTensor.liftDerivation (R := B')
    dB (0 : Derivation A A' M) hdB continuous_const continuous_id hinl hinr
  have hdA_inr (a' : A') : dA (inr A B A' a') = 0 :=
    (liftDerivation_inr (R := B') dB 0 hdB continuous_const continuous_id hinl hinr a').trans rfl
  let δ : Derivation A' B' M := Derivation.mk'
    { toFun := dA, map_add' := dA.map_add, map_smul' a' z := by
        rw [RingHom.id_apply, Algebra.smul_def, dA.leibniz, algebraMap_smul,
          algebraMap_rightAlgebra, hdA_inr, smul_zero, add_zero] } dA.leibniz
  exact ⟨δ, continuous_liftDerivation (R := B') dB 0 hdB continuous_const continuous_id hinl hinr,
    fun b ↦ liftDerivation_inl (R := B') dB 0 hdB continuous_const continuous_id hinl hinr b⟩

/-- Scalar-extended comparison map `(B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A] →ₗ[B ⊗̂_A A'] Ωᶜ[(B ⊗̂_A A')⁄A']`. -/
private noncomputable def baseChangeFromTensor :
    CompletedTensor A B A' ⊗[B] ContinuousKaehlerDifferential A B →ₗ[CompletedTensor A B A']
      ContinuousKaehlerDifferential A' (CompletedTensor A B A') :=
  map (algebraMap A A') (by ext a; simp)
    (by rw [algebraMap_leftAlgebra]; exact continuous_inl A B A')

/-- Bundled universal-property map `Ωᶜ[(B ⊗̂_A A')⁄A'] →ₗ[B ⊗̂_A A'] (B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]`
and its value on `d (inl b)`. -/
private noncomputable def baseChangeToTensorAux
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    {l : ContinuousKaehlerDifferential A' (CompletedTensor A B A') →ₗ[CompletedTensor A B A']
      CompletedTensor A B A' ⊗[B] ContinuousKaehlerDifferential A B //
      ∀ b : B, l (D A' (CompletedTensor A B A') (inl A B A' b)) =
        (1 : CompletedTensor A B A') ⊗ₜ[B] D A B b} := by
  let B' := CompletedTensor A B A'; let M := B' ⊗[B] ContinuousKaehlerDifferential A B
  have : IsNoetherianType B' :=
    .of_isTopologicallyFiniteType (baseChange_isTopologicallyFiniteType hAB)
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  letI : TopologicalSpace M := moduleTopology B' M; have : IsModuleTopology B' M := ⟨rfl⟩
  let δ := baseChangeDerivation (A' := A') hAB
  exact ⟨liftOfFinite δ.val δ.property.1,
    fun b ↦ (liftOfFinite_D δ.val δ.property.1 (inl A B A' b)).trans (δ.property.2 b)⟩

private theorem baseChangeToTensor_comp_fromTensor
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    (baseChangeToTensorAux (A' := A') hAB).val.comp baseChangeFromTensor = LinearMap.id :=
  linearMap_tensor_ext hAB fun b ↦ by
    simp only [LinearMap.comp_apply, LinearMap.id_apply, baseChangeFromTensor, map_tmul,
      mapSemilinear_D, one_smul, algebraMap_leftAlgebra]
    exact (baseChangeToTensorAux (A' := A') hAB).property b

private theorem baseChangeFromTensor_comp_toTensor
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    baseChangeFromTensor.comp (baseChangeToTensorAux (A' := A') hAB).val = LinearMap.id := by
  have hA'B' := baseChange_isTopologicallyFiniteType (A' := A') hAB
  have : IsNoetherianType (CompletedTensor A B A') := .of_isTopologicallyFiniteType hA'B'
  refine linearMap_ext_of_dense_adjoin hA'B' (CompletedTensor.dense_adjoin_range_inl A B A') ?_
  rintro _ ⟨b, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    (baseChangeToTensorAux (A' := A') hAB).property, baseChangeFromTensor, map_tmul,
    mapSemilinear_D, one_smul, algebraMap_leftAlgebra]

/-- **Huber Proposition 1.6.3(iii) (Base change of continuous differentials)**: for `A → B`
topologically of finite type into a complete Hausdorff Huber ring `B` of noetherian type and
`A → A'` adic into a Huber ring `A'` of noetherian type, completed base change induces
`Ωᶜ[(B ⊗̂_A A')⁄A'] ≃ₗ[B ⊗̂_A A'] (B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]` (using `CompletedTensor.leftAlgebra`,
`CompletedTensor.rightAlgebra`, and `CompletedTensor.isAdicHom_rightAlgebra`). -/
noncomputable def baseChangeEquiv (A' : Type*) [CommRing A'] [Algebra A A']
    [TopologicalSpace A'] [IsTopologicalRing A'] [IsHuberRing A'] [IsNoetherianType A']
    [IsAdicHom (algebraMap A A')]
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    ContinuousKaehlerDifferential A' (CompletedTensor A B A') ≃ₗ[CompletedTensor A B A']
      CompletedTensor A B A' ⊗[B] ContinuousKaehlerDifferential A B :=
  LinearEquiv.ofLinearMap (baseChangeToTensorAux (A' := A') hAB).val baseChangeFromTensor
    (baseChangeToTensor_comp_fromTensor (A' := A') hAB)
    (baseChangeFromTensor_comp_toTensor (A' := A') hAB)

/-- The inverse of `baseChangeEquiv` evaluates on a pure tensor `b' ⊗ₜ ω` via the semilinear
change-of-rings map along `A → A'` and `inl : B → B ⊗̂_A A'`. -/
@[simp]
theorem baseChangeEquiv_symm_tmul (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (b' : CompletedTensor A B A') (ω : ContinuousKaehlerDifferential A B) :
    (baseChangeEquiv A' hAB).symm (b' ⊗ₜ[B] ω) =
      b' • mapSemilinear (algebraMap A A') (algebraMap B (CompletedTensor A B A'))
        (by ext a; simp)
        (by rw [algebraMap_leftAlgebra]; exact continuous_inl A B A') ω :=
  map_tmul _ _ _ b' ω

/-- The inverse of `baseChangeEquiv` sends `b' ⊗ₜ d b` to `b' • d (inl b)`. -/
theorem baseChangeEquiv_symm_tmul_D (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (b' : CompletedTensor A B A') (b : B) :
    (baseChangeEquiv A' hAB).symm (b' ⊗ₜ[B] D A B b) =
      b' • D A' (CompletedTensor A B A') (inl A B A' b) := by
  rw [baseChangeEquiv_symm_tmul, mapSemilinear_D, algebraMap_leftAlgebra]

/-- `baseChangeEquiv` sends `d (inl b)` to `1 ⊗ₜ d b`. -/
@[simp]
theorem baseChangeEquiv_D_inl (A' : Type*) [CommRing A'] [Algebra A A']
    [TopologicalSpace A'] [IsTopologicalRing A'] [IsHuberRing A'] [IsNoetherianType A']
    [IsAdicHom (algebraMap A A')]
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) (b : B) :
    baseChangeEquiv A' hAB (D A' (CompletedTensor A B A') (inl A B A' b)) =
      (1 : CompletedTensor A B A') ⊗ₜ[B] D A B b :=
  (baseChangeToTensorAux (A' := A') hAB).property b

/-- `baseChangeEquiv` annihilates `d (inr a')`. -/
@[simp]
theorem baseChangeEquiv_D_inr (hAB : IsTopologicallyFiniteType (algebraMap A B)) (a' : A') :
    baseChangeEquiv A' hAB (D A' (CompletedTensor A B A') (inr A B A' a')) = 0 := by
  rw [← algebraMap_rightAlgebra, Derivation.map_algebraMap, map_zero]

/-- `baseChangeEquiv` sends `d (toCompletion (b ⊗ₜ a'))` to `inr a' ⊗ₜ d b`. -/
theorem baseChangeEquiv_D_toCompletion_tmul (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (b : B) (a' : A') :
    baseChangeEquiv A' hAB (D A' (CompletedTensor A B A') (toCompletion A B A' (b ⊗ₜ[A] a'))) =
      inr A B A' a' ⊗ₜ[B] D A B b := by
  rw [CompletedTensor.toCompletion_tmul, Derivation.leibniz, map_add, map_smul, map_smul,
    baseChangeEquiv_D_inr, smul_zero, zero_add, baseChangeEquiv_D_inl, smul_tmul', smul_eq_mul,
    mul_one]

end BaseChange

end TauCeti.Huber.ContinuousKaehlerDifferential
