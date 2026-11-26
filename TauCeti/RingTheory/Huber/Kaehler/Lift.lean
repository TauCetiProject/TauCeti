/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Basic
import TauCeti.RingTheory.Huber.TensorProduct.Derivation

/-!
# Universal lift for continuous differentials

Let `A → B` be an adic homomorphism into a complete Hausdorff nonarchimedean ring `B`. Every
continuous `A`-derivation `δ : B → M` into a complete Hausdorff nonarchimedean `B`-module lifts
to a continuous `B`-linear map `Ωᶜ[B⁄A] →L[B] M`
(`Derivation.liftContinuousKaehlerDifferential`), without any noetherian or finite-type hypotheses.

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

/-- Descend `CompletedTensor.liftDerivationOfAlgebraMap 0 δ` from `I` modulo `I²` to
`Ωᶜ[B⁄A] →ₗ[B] M`. -/
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
    CompletedTensor.liftDerivationOfAlgebraMap (R := B) (0 : Derivation A B M) δ
      continuous_const hδ (continuous_mulRingHom A B) (RingHom.ext (mulRingHom_inl A B))
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
  have hd_inr : d (inr A B B b) = δ b := liftDerivationOfAlgebraMap_inr ..
  have hd_inl : d (inl A B B b) = 0 := liftDerivationOfAlgebraMap_inl ..
  simp [D_apply, q, g, hd_inr, hd_inl]

end Lift

end TauCeti.Huber.ContinuousKaehlerDifferential

namespace Derivation

open TauCeti.Huber ContinuousKaehlerDifferential

section Lift

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]

/-- **Universal lift for continuous differentials** (Huber 1996, §1.6, Definition 1.6.1 and
(1.6.2)(ii), existence): any continuous `A`-derivation `δ : B → M` factors through a continuous
`B`-linear map `Ωᶜ[B⁄A] →L[B] M`. Neither `A` nor `B` needs any noetherian or finite-type
hypothesis for existence. -/
noncomputable def liftContinuousKaehlerDifferential (δ : Derivation A B M) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential A B →L[B] M :=
  { (liftLinearMap δ hδ).val with
    cont := IsModuleTopology.continuous_of_linearMap (liftLinearMap δ hδ).val }

/-- Evaluating the universal lift on `d b` recovers `δ b`. -/
@[simp] theorem liftContinuousKaehlerDifferential_comp_D (δ : Derivation A B M)
    (hδ : Continuous δ) (b : B) :
    δ.liftContinuousKaehlerDifferential hδ (D A B b) = δ b :=
  (liftLinearMap δ hδ).property b

/-- Precomposing the universal lift with `D A B` recovers `δ`. -/
@[simp] theorem liftContinuousKaehlerDifferential_comp (δ : Derivation A B M)
    (hδ : Continuous δ) :
    (δ.liftContinuousKaehlerDifferential hδ).toLinearMap.compDer (D A B) = δ := by
  ext b; exact δ.liftContinuousKaehlerDifferential_comp_D hδ b

end Lift

end Derivation
