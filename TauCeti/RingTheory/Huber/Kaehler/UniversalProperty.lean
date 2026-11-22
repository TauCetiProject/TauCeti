/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.FiniteType
public import TauCeti.RingTheory.Huber.Kaehler.Lift

/-!
# Universal property of continuous differentials

For `A → B` topologically of finite type into complete Hausdorff Huber `B` of noetherian type, this
file combines `ContinuousKaehlerDifferential.lift` and `liftOfFinite` with `continuous_D` and
`linearMap_ext` to give uniqueness (`hom_ext`, `existsUnique_lift`),
`continuousLinearMapEquivDerivation`, and uniqueness for `liftOfFinite`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2)(ii).
-/

public section

namespace TauCeti.Huber.ContinuousKaehlerDifferential

section FiniteType

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]

/-- **Uniqueness for continuous linear maps out of `Ωᶜ[B⁄A]`** (Huber 1996, §1.6, Definition 1.6.1
and (1.6.2)(ii)): two continuous `B`-linear maps out of `Ωᶜ[B⁄A]` agreeing on `D A B` are equal. -/
theorem hom_ext (h : IsTopologicallyFiniteType (algebraMap A B))
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [Module B M]
    {f₁ f₂ : ContinuousKaehlerDifferential A B →L[B] M}
    (heq : ∀ b, f₁ (D A B b) = f₂ (D A B b)) : f₁ = f₂ :=
  ContinuousLinearMap.ext fun ω ↦ DFunLike.congr_fun (linearMap_ext h heq) ω

section UniversalEquiv

variable {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]

/-- **Universal property of `Ωᶜ[B⁄A]`** (Huber 1996, §1.6, Definition 1.6.1 and (1.6.2)(ii)):
every continuous `A`-derivation `δ : B → M` factors through a unique `Ωᶜ[B⁄A] →L[B] M`. -/
theorem existsUnique_lift (h : IsTopologicallyFiniteType (algebraMap A B))
    (δ : Derivation A B M) (hδ : Continuous δ) :
    ∃! f : ContinuousKaehlerDifferential A B →L[B] M, ∀ b, f (D A B b) = δ b :=
  ⟨lift δ hδ, lift_D δ hδ, fun _ hf ↦ hom_ext h fun b ↦ (hf b).trans (lift_D δ hδ b).symm⟩

/-- **Equivalence between continuous `B`-linear maps `Ωᶜ[B⁄A] →L[B] M` and continuous
`A`-derivations `B → M`** (Huber 1996, §1.6, Definition 1.6.1 and (1.6.2)(ii)). -/
noncomputable def continuousLinearMapEquivDerivation
    (h : IsTopologicallyFiniteType (algebraMap A B)) :
    (ContinuousKaehlerDifferential A B →L[B] M) ≃ {δ : Derivation A B M // Continuous δ} where
  toFun f := ⟨f.toLinearMap.compDer (D A B), f.continuous.comp (continuous_D h)⟩
  invFun δ := lift δ.val δ.property
  left_inv _ := hom_ext h fun b ↦ lift_D _ _ b
  right_inv δ := Subtype.ext (compDer_lift_D δ.val δ.property)

/-- The underlying derivation of `continuousLinearMapEquivDerivation h f` is `f ∘ d`. -/
@[simp] theorem continuousLinearMapEquivDerivation_apply_coe
    (h : IsTopologicallyFiniteType (algebraMap A B))
    (f : ContinuousKaehlerDifferential A B →L[B] M) :
    ((continuousLinearMapEquivDerivation h f : {δ : Derivation A B M // Continuous δ}) :
      Derivation A B M) = f.toLinearMap.compDer (D A B) := (rfl)

/-- The inverse of `continuousLinearMapEquivDerivation` is `lift`. -/
@[simp] theorem continuousLinearMapEquivDerivation_symm_apply
    (h : IsTopologicallyFiniteType (algebraMap A B))
    (δ : {δ : Derivation A B M // Continuous δ}) :
    (continuousLinearMapEquivDerivation h).symm δ = lift δ.val δ.property := (rfl)

/-- `continuousLinearMapEquivDerivation` sends `lift δ hδ` back to `⟨δ, hδ⟩`. -/
@[simp] theorem continuousLinearMapEquivDerivation_lift
    (h : IsTopologicallyFiniteType (algebraMap A B)) (δ : Derivation A B M) (hδ : Continuous δ) :
    continuousLinearMapEquivDerivation h (lift δ hδ) = ⟨δ, hδ⟩ :=
  Subtype.ext (compDer_lift_D δ hδ)

/-- Lifting the derivation `f ∘ d` recovers the continuous `B`-linear map `f`. -/
@[simp] theorem lift_compDer_D (h : IsTopologicallyFiniteType (algebraMap A B))
    (f : ContinuousKaehlerDifferential A B →L[B] M)
    (hf : Continuous (f.toLinearMap.compDer (D A B))) :
    lift (f.toLinearMap.compDer (D A B)) hf = f := hom_ext h fun b ↦ lift_D _ _ b

end UniversalEquiv

/-- Lifting `f ∘ d` into a finite `B`-module carrying its natural topology recovers `f`, when
`A` is a Huber ring and `A → B` is topologically of finite type. -/
@[simp] theorem liftOfFinite_compDer_D (h : IsTopologicallyFiniteType (algebraMap A B))
    {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.Finite B N] [TopologicalSpace N] [IsModuleTopology B N]
    (f : ContinuousKaehlerDifferential A B →ₗ[B] N) (hf : Continuous (f.compDer (D A B))) :
    liftOfFinite (f.compDer (D A B)) hf = f := linearMap_ext h fun b ↦ liftOfFinite_D _ _ b

end FiniteType

end TauCeti.Huber.ContinuousKaehlerDifferential
