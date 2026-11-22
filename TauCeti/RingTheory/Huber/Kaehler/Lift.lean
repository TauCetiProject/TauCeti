/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Basic
public import TauCeti.RingTheory.Huber.NoetherianType.Basic
import TauCeti.RingTheory.Huber.NoetherianType.ModuleTopology
import TauCeti.RingTheory.Huber.TensorProduct.Derivation

/-!
# Universal lift for continuous differentials

Let `A → B` be an adic homomorphism into a complete Hausdorff nonarchimedean ring `B`. Every
continuous `A`-derivation `δ : B → M` into a complete Hausdorff nonarchimedean `B`-module lifts
to a continuous `B`-linear map `Ωᶜ[B⁄A] →L[B] M`
(`TauCeti.Huber.ContinuousKaehlerDifferential.lift`), without any noetherian or finite-type
hypotheses; when `B` is of noetherian type, any continuous `A`-derivation into a finite `B`-module
with its natural topology lifts to `Ωᶜ[B⁄A] →ₗ[B] N` (`liftOfFinite`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2)(ii).
-/

public section

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

section Lift

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]

/-- Descend `CompletedTensor.liftDerivation 0 δ` from `I` modulo `I²` to `Ωᶜ[B⁄A] →ₗ[B] M`. -/
private noncomputable def liftLinearMap
    {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
    [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
    [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]
    (δ : Derivation A B M) (hδ : Continuous δ) :
    {l : ContinuousKaehlerDifferential A B →ₗ[B] M // ∀ b, l (D A B b) = δ b} := by
  letI : Algebra (CompletedTensor A B B) B := (mulRingHom A B).toAlgebra
  letI : Module (CompletedTensor A B B) M := Module.compHom M (mulRingHom A B)
  haveI : IsScalarTower (CompletedTensor A B B) B M :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hsmul (r : CompletedTensor A B B) (m : M) : r • m = mulRingHom A B r • m := rfl
  let d : Derivation A (CompletedTensor A B B) M :=
    CompletedTensor.liftDerivation (R := B) (0 : Derivation A B M) δ continuous_const hδ
      (continuous_mulRingHom A B) (RingHom.ext (mulRingHom_inl A B))
      (RingHom.ext (mulRingHom_inr A B))
  let g : ideal A B →ₗ[CompletedTensor A B B] M :=
    { toFun x := d x.val, map_add' x y := map_add d x.val y.val
      map_smul' r x := by
        rw [RingHom.id_apply, SetLike.val_smul, smul_eq_mul, d.leibniz, hsmul x.val,
          mem_ideal_iff.mp x.property, zero_smul, add_zero] }
  have hg (x y : ideal A B) : g (x * y) = 0 := by
    simp only [g, LinearMap.coe_mk, AddHom.coe_mk, MulMemClass.coe_mul, d.leibniz, hsmul,
      mem_ideal_iff.mp x.property, mem_ideal_iff.mp y.property, zero_smul, add_zero]
  let q : ContinuousKaehlerDifferential A B →ₗ[CompletedTensor A B B] M :=
    (Ideal.Cotangent.lift g hg).comp (cotangentEquiv A B).toLinearMap
  refine ⟨{ toFun := q, map_add' := q.map_add, map_smul' b ω := by
    { rw [RingHom.id_apply, ← inl_smul, q.map_smul, hsmul, mulRingHom_inl] } }, fun b ↦ ?_⟩
  have hd_inr : d (inr A B B b) = δ b := liftDerivation_inr ..
  have hd_inl : d (inl A B B b) = 0 := liftDerivation_inl ..
  simp [D_apply, q, g, hd_inr, hd_inl]

/-- **Universal lift for continuous differentials** (Huber 1996, §1.6, Definition 1.6.1 and
(1.6.2)(ii), existence): any continuous `A`-derivation `δ : B → M` factors through a continuous
`B`-linear map `Ωᶜ[B⁄A] →L[B] M`. Neither `A` nor `B` needs any noetherian or finite-type
hypothesis for existence. -/
noncomputable def lift {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
    [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
    [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]
    (δ : Derivation A B M) (hδ : Continuous δ) : ContinuousKaehlerDifferential A B →L[B] M :=
  { (liftLinearMap δ hδ).val with
    cont := IsModuleTopology.continuous_of_linearMap (liftLinearMap δ hδ).val }

/-- Evaluating the universal lift on `d b` recovers `δ b`. -/
@[simp] theorem lift_D {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
    [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
    [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]
    (δ : Derivation A B M) (hδ : Continuous δ) (b : B) : lift δ hδ (D A B b) = δ b :=
  (liftLinearMap δ hδ).property b

/-- Precomposing the universal lift with `D A B` recovers `δ`. -/
@[simp] theorem compDer_lift_D {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
    [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
    [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]
    (δ : Derivation A B M) (hδ : Continuous δ) : (lift δ hδ).toLinearMap.compDer (D A B) = δ := by
  ext b; exact lift_D δ hδ b

section FiniteTarget

variable [IsHuberRing B] [IsNoetherianType B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [Module.Finite B N] [TopologicalSpace N] [IsModuleTopology B N]

private noncomputable def liftOfFiniteAux (δ : Derivation A B N) (hδ : Continuous δ) :
    {l : ContinuousKaehlerDifferential A B →ₗ[B] N // ∀ b, l (D A B b) = δ b} := by
  letI := IsModuleTopology.isTopologicalAddGroup B N
  letI := IsTopologicalAddGroup.rightUniformSpace N
  obtain ⟨_, _, _, _⟩ :=
    IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology (A := B) (M := N)
  exact ⟨(lift δ hδ).toLinearMap, lift_D δ hδ⟩

/-- **Universal lift into a finite `B`-module with its natural topology** (Huber 1996, §1.6,
Definition 1.6.1 and (1.6.2)(ii)): any continuous `A`-derivation `δ : B → N` lifts to
`Ωᶜ[B⁄A] →ₗ[B] N`. -/
noncomputable def liftOfFinite (δ : Derivation A B N) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential A B →ₗ[B] N := (liftOfFiniteAux δ hδ).val

/-- Evaluating `liftOfFinite δ hδ` on `d b` recovers `δ b`. -/
@[simp] theorem liftOfFinite_D (δ : Derivation A B N) (hδ : Continuous δ) (b : B) :
    liftOfFinite δ hδ (D A B b) = δ b := (liftOfFiniteAux δ hδ).property b

/-- Precomposing `liftOfFinite δ hδ` with `D A B` recovers `δ`. -/
@[simp] theorem compDer_liftOfFinite_D (δ : Derivation A B N) (hδ : Continuous δ) :
    (liftOfFinite δ hδ).compDer (D A B) = δ := by ext b; exact liftOfFinite_D δ hδ b

end FiniteTarget

end Lift

end TauCeti.Huber.ContinuousKaehlerDifferential
