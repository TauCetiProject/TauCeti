/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.FiniteType
import Mathlib.LinearAlgebra.TensorProduct.Lift
import TauCeti.RingTheory.Huber.TensorProduct.Derivation

/-!
# Continuity and universal property of continuous differentials

Let `A → B` be an adic homomorphism into a complete Hausdorff ring `B`. This file establishes
the universal property of `(Ωᶜ[B⁄A], d)` for continuous `A`-derivations into complete Hausdorff
nonarchimedean `B`-modules (Huber 1996, §1.6, Definition 1.6.1 and (1.6.2)(ii)), extending
Mathlib's `Derivation.liftKaehlerDifferential` and `KaehlerDifferential.linearMapEquivDerivation`
(`Mathlib.RingTheory.Kaehler.Basic`):

* `lift` descends `CompletedTensor.liftDerivation 0 δ` via `Ideal.Cotangent.lift` without any
  finiteness or noetherian hypotheses.
* When `A` is Huber, `B` is complete Hausdorff Huber of noetherian type, and `A → B` is
  topologically of finite type, `Submodule.isModuleTopology_of_isNoetherianType` gives continuity
  of `fromIdeal` and `D` (`continuous_fromIdeal`, `continuous_D`), while `span_range_derivation`
  gives uniqueness (`hom_ext`, `continuousLinearMapEquivDerivation`) and finite-target lifts
  (`liftOfFinite`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2)(ii).
-/

public section

open TensorProduct UniformSpace Topology
open scoped Uniformity

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

section Lift

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]

/-- Descend the derivation `CompletedTensor.liftDerivation 0 δ` from `I` modulo `I²` to
`Ωᶜ[B⁄A] →ₗ[B] M`. -/
private noncomputable def liftLinearMap (δ : Derivation A B M) (hδ : Continuous δ) :
    {l : ContinuousKaehlerDifferential A B →ₗ[B] M // ∀ b, l (D A B b) = δ b} := by
  letI : Algebra (CompletedTensor A B B) B := (mulRingHom A B).toAlgebra
  letI : Module (CompletedTensor A B B) M := Module.compHom M (mulRingHom A B)
  haveI : IsScalarTower (CompletedTensor A B B) B M :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hsmul (r : CompletedTensor A B B) (m : M) : r • m = mulRingHom A B r • m := rfl
  have h0 : Continuous (0 : Derivation A B M) := continuous_const
  let d : Derivation A (CompletedTensor A B B) M :=
    CompletedTensor.liftDerivation (R := B) (0 : Derivation A B M) δ h0 hδ
      (continuous_mulRingHom A B) (RingHom.ext (mulRingHom_inl A B))
      (RingHom.ext (mulRingHom_inr A B))
  let g : ideal A B →ₗ[CompletedTensor A B B] M :=
    { toFun x := d x.1
      map_add' x y := map_add d x.1 y.1
      map_smul' r x := by
        rw [RingHom.id_apply, SetLike.val_smul, smul_eq_mul, d.leibniz, hsmul x.1,
          mem_ideal_iff.mp x.2, zero_smul, add_zero] }
  have hg (x y : ideal A B) : g (x * y) = 0 := by
    simp only [g, LinearMap.coe_mk, AddHom.coe_mk, MulMemClass.coe_mul, d.leibniz, hsmul,
      mem_ideal_iff.mp x.2, mem_ideal_iff.mp y.2, zero_smul, add_zero]
  let q : ContinuousKaehlerDifferential A B →ₗ[CompletedTensor A B B] M :=
    (Ideal.Cotangent.lift g hg).comp (cotangentEquiv A B).toLinearMap
  refine ⟨{ toFun := q
            map_add' := q.map_add
            map_smul' b ω := by
              rw [RingHom.id_apply, ← inl_smul, q.map_smul, hsmul, mulRingHom_inl] }, fun b ↦ ?_⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk, D_apply, q, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, cotangentEquiv_fromIdeal, Ideal.Cotangent.lift_toCotangent,
    g, map_sub, d]
  rw [liftDerivation_inr, liftDerivation_inl, zero_apply, sub_zero]

/-- **Universal lift for continuous differentials** (Huber 1996, §1.6, Definition 1.6.1 and
(1.6.2)(ii), existence): any continuous `A`-derivation `δ : B → M` into a complete Hausdorff
nonarchimedean `B`-module factors through a continuous `B`-linear map `Ωᶜ[B⁄A] →L[B] M`. Neither
`A` nor `B` needs any noetherian or finite-type hypothesis for existence. -/
noncomputable def lift (δ : Derivation A B M) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential A B →L[B] M :=
  { (liftLinearMap δ hδ).1 with
    cont := IsModuleTopology.continuous_of_linearMap (liftLinearMap δ hδ).1 }

/-- Evaluating the universal lift on `d b` recovers `δ b`. -/
@[simp]
theorem lift_D (δ : Derivation A B M) (hδ : Continuous δ) (b : B) :
    lift δ hδ (D A B b) = δ b :=
  (liftLinearMap δ hδ).2 b

/-- Precomposing the universal lift with `D A B` recovers `δ`. -/
@[simp]
theorem compDer_lift_D (δ : Derivation A B M) (hδ : Continuous δ) :
    (lift δ hδ).toLinearMap.compDer (D A B) = δ := by
  ext b; exact lift_D δ hδ b

end Lift

section FiniteType

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]

/-- **Continuity of the quotient presentation `I → Ωᶜ[B⁄A]`**: when `A, B` are Huber with `B`
complete Hausdorff of noetherian type and `A → B` topologically of finite type, `fromIdeal A B` is
continuous for the subspace topology on `ideal A B` and the `B`-module topology on `Ωᶜ[B⁄A]`. -/
theorem continuous_fromIdeal (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Continuous (fromIdeal A B) := by
  have : IsNoetherianType (CompletedTensor A B B) :=
    .of_isTopologicallyFiniteType (isTopologicallyFiniteType_inl h)
  have : Module.Finite (CompletedTensor A B B) (ideal A B) := Module.Finite.iff_fg.mpr (ideal_fg h)
  have : IsModuleTopology (CompletedTensor A B B) (ideal A B) :=
    (ideal A B).isModuleTopology_of_isNoetherianType
  exact IsModuleTopology.continuous_of_linearMap (fromIdeal A B)

/-- **Continuity of the universal derivation** (Huber 1996, §1.6, Definition 1.6.1 and
(1.6.2)(ii)): when `A, B` are Huber with `B` complete Hausdorff of noetherian type and `A → B` is
topologically of finite type, `d : B → Ωᶜ[B⁄A]` is continuous. -/
theorem continuous_D (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Continuous (D A B) := by
  have hsub : Continuous fun b : B ↦
      (⟨inr A B B b - inl A B B b, inr_sub_inl_mem_ideal A B b⟩ : ideal A B) :=
    Continuous.subtype_mk ((continuous_inr A B B).sub (continuous_inl A B B)) _
  exact ((continuous_fromIdeal h).comp hsub).congr fun b ↦ (D_apply A B b).symm

/-- Two `B`-linear maps out of `Ωᶜ[B⁄A]` that agree on `d '' S` (for `A[S]` dense in `B`) are
equal when `A → B` is topologically of finite type into complete Hausdorff Huber `B` of noetherian
type. -/
theorem linearMap_ext_of_dense_adjoin (h : IsTopologicallyFiniteType (algebraMap A B))
    {S : Set B} (hS : Dense (Algebra.adjoin A S : Set B))
    {M : Type*} [AddCommGroup M] [Module B M]
    {f₁ f₂ : ContinuousKaehlerDifferential A B →ₗ[B] M}
    (heq : ∀ s ∈ S, f₁ (D A B s) = f₂ (D A B s)) : f₁ = f₂ :=
  LinearMap.ext_on (span_D_eq_top h hS) fun _ ⟨s, hs, hds⟩ ↦ hds ▸ heq s hs

/-- **Uniqueness for linear maps out of `Ωᶜ[B⁄A]`** (Huber 1996, §1.6, (1.6.2)(ii)): two `B`-linear
maps out of `Ωᶜ[B⁄A]` agreeing on `D A B` are equal. -/
theorem linearMap_ext (h : IsTopologicallyFiniteType (algebraMap A B))
    {M : Type*} [AddCommGroup M] [Module B M]
    {f₁ f₂ : ContinuousKaehlerDifferential A B →ₗ[B] M}
    (heq : ∀ b, f₁ (D A B b) = f₂ (D A B b)) : f₁ = f₂ :=
  linearMap_ext_of_dense_adjoin h (S := Set.univ) (by simp [Algebra.adjoin_univ])
    fun b _ ↦ heq b

/-- **Uniqueness for `R`-linear maps out of `R ⊗[B] Ωᶜ[B⁄A]`**: two `R`-linear maps agreeing on
`1 ⊗ₜ d b` for all `b : B` are equal. -/
theorem linearMap_tensor_ext (h : IsTopologicallyFiniteType (algebraMap A B))
    {R : Type*} [CommRing R] [Algebra B R]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    {f g : R ⊗[B] ContinuousKaehlerDifferential A B →ₗ[R] Q}
    (heq : ∀ b : B, f (1 ⊗ₜ[B] D A B b) = g (1 ⊗ₜ[B] D A B b)) : f = g := by
  let : Module B Q := Module.compHom Q (algebraMap B R)
  have : IsScalarTower B R Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact (LinearMap.liftBaseChangeEquiv R).symm.injective (linearMap_ext h heq)

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
  invFun δ := lift δ.1 δ.2
  left_inv _ := hom_ext h fun b ↦ lift_D _ _ b
  right_inv δ := Subtype.ext (compDer_lift_D δ.1 δ.2)

/-- The underlying derivation of `continuousLinearMapEquivDerivation h f` is `f ∘ d`. -/
@[simp]
theorem continuousLinearMapEquivDerivation_apply_coe
    (h : IsTopologicallyFiniteType (algebraMap A B))
    (f : ContinuousKaehlerDifferential A B →L[B] M) :
    ((continuousLinearMapEquivDerivation h f : {δ : Derivation A B M // Continuous δ}) :
      Derivation A B M) = f.toLinearMap.compDer (D A B) := (rfl)

/-- The inverse of `continuousLinearMapEquivDerivation` is `lift`. -/
@[simp]
theorem continuousLinearMapEquivDerivation_symm_apply
    (h : IsTopologicallyFiniteType (algebraMap A B))
    (δ : {δ : Derivation A B M // Continuous δ}) :
    (continuousLinearMapEquivDerivation h).symm δ = lift δ.1 δ.2 := (rfl)

/-- `continuousLinearMapEquivDerivation` sends `lift δ hδ` back to `⟨δ, hδ⟩`. -/
@[simp]
theorem continuousLinearMapEquivDerivation_lift
    (h : IsTopologicallyFiniteType (algebraMap A B))
    (δ : Derivation A B M) (hδ : Continuous δ) :
    continuousLinearMapEquivDerivation h (lift δ hδ) = ⟨δ, hδ⟩ :=
  Subtype.ext (compDer_lift_D δ hδ)

/-- Lifting the derivation `f ∘ d` recovers the continuous `B`-linear map `f`. -/
@[simp]
theorem lift_compDer_D (h : IsTopologicallyFiniteType (algebraMap A B))
    (f : ContinuousKaehlerDifferential A B →L[B] M)
    (hf : Continuous (f.toLinearMap.compDer (D A B))) :
    lift (f.toLinearMap.compDer (D A B)) hf = f :=
  hom_ext h fun b ↦ lift_D _ _ b

end UniversalEquiv

end FiniteType

section FiniteTarget

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [Module.Finite B N] [TopologicalSpace N] [IsModuleTopology B N]

/-- Internal bundled lift into a finite `B`-module with its natural topology, sharing the
uniform-group setup across `liftOfFinite` and `liftOfFinite_D`. -/
private noncomputable def liftOfFiniteAux (δ : Derivation A B N) (hδ : Continuous δ) :
    {l : ContinuousKaehlerDifferential A B →ₗ[B] N // ∀ b, l (D A B b) = δ b} := by
  letI : IsTopologicalAddGroup N := IsModuleTopology.isTopologicalAddGroup B N
  letI : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  obtain ⟨_, _, _, _⟩ :=
    IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology (A := B) (M := N)
  exact ⟨(lift δ hδ).toLinearMap, lift_D δ hδ⟩

/-- **Universal lift into a finite `B`-module with its natural topology** (Huber 1996, §1.6,
Definition 1.6.1 and (1.6.2)(ii)): any continuous `A`-derivation `δ : B → N` lifts to
`Ωᶜ[B⁄A] →ₗ[B] N`. -/
noncomputable def liftOfFinite (δ : Derivation A B N) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential A B →ₗ[B] N :=
  (liftOfFiniteAux δ hδ).1

/-- Evaluating `liftOfFinite δ hδ` on `d b` recovers `δ b`. -/
@[simp]
theorem liftOfFinite_D (δ : Derivation A B N) (hδ : Continuous δ) (b : B) :
    liftOfFinite δ hδ (D A B b) = δ b :=
  (liftOfFiniteAux δ hδ).2 b

/-- Precomposing `liftOfFinite δ hδ` with `D A B` recovers `δ`. -/
@[simp]
theorem compDer_liftOfFinite_D (δ : Derivation A B N) (hδ : Continuous δ) :
    (liftOfFinite δ hδ).compDer (D A B) = δ := by
  ext b; exact liftOfFinite_D δ hδ b

/-- Lifting `f ∘ d` into a finite `B`-module carrying its natural topology recovers `f`, when
`A` is a Huber ring and `A → B` is topologically of finite type. -/
@[simp]
theorem liftOfFinite_compDer_D [IsHuberRing A] (h : IsTopologicallyFiniteType (algebraMap A B))
    (f : ContinuousKaehlerDifferential A B →ₗ[B] N)
    (hf : Continuous (f.compDer (D A B))) :
    liftOfFinite (f.compDer (D A B)) hf = f :=
  linearMap_ext h fun b ↦ liftOfFinite_D _ _ b

end FiniteTarget

end TauCeti.Huber.ContinuousKaehlerDifferential
