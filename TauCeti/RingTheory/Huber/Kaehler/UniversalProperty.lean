/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.TrivSqZeroExt
public import TauCeti.RingTheory.Huber.Kaehler.FiniteType
public import Mathlib.Topology.Instances.TrivSqZeroExt

/-!
# Continuity and universal property of continuous differentials

Let `A → B` be an adic homomorphism into a complete Hausdorff ring `B`. This file establishes
the universal property of `(Ωᶜ[B⁄A], d)` for continuous `A`-derivations into complete Hausdorff
nonarchimedean topological `B`-modules (Huber 1996, §1.6, (1.6.2)(b)):

* **Existence (`lift`) — without finiteness or noetherian hypotheses**: for any complete Hausdorff
  nonarchimedean `B`-module `M` and any continuous `A`-derivation `δ : B → M`, the corresponding
  point `b ↦ (b, δ b)` of the trivial square-zero extension `TrivSqZeroExt B M`
  (`TauCeti.derivationToTrivSqZeroExtEquivLift`) combines with `inl : B → TrivSqZeroExt B M` via
  `CompletedTensor.lift` into a continuous ring homomorphism `Φ : B ⊗̂_A B →+* TrivSqZeroExt B M`
  over `mulRingHom A B`. Its second component vanishes on `I²` and is `B ⊗̂_A B`-linear on
  `I = ker (mulRingHom A B)`, hence descends to a continuous `B`-linear map
  `lift δ hδ : Ωᶜ[B⁄A] →L[B] M` satisfying `lift δ hδ (d b) = δ b`.
* **Continuity of `d` and uniqueness (`hom_ext`)**: when `A` is a Huber ring, `B` is of noetherian
  type, and `A → B` is topologically of finite type, the finitely generated ideal `I ⊆ B ⊗̂_A B`
  carries the `B ⊗̂_A B`-module topology (`IsNoetherianType.isModuleTopology_submodule`), making
  `fromIdeal : I → Ωᶜ[B⁄A]` and `D : B → Ωᶜ[B⁄A]` continuous (`continuous_fromIdeal`,
  `continuous_D`), while `span_range_derivation` gives uniqueness of maps out of `Ωᶜ[B⁄A]`
  (`linearMap_ext`, `hom_ext`) and the equivalence `(Ωᶜ[B⁄A] →L[B] M) ≃ {δ // Continuous δ}`
  (`continuousLinearMapEquiv`).
* **Finite target modules (`liftOfFinite`)**: when `N` is a finitely generated `B`-module with its
  natural `B`-module topology and `B` is of noetherian type, `N` is automatically complete,
  Hausdorff, and nonarchimedean, so any continuous `A`-derivation `B → N` lifts directly to a
  `B`-linear map `Ωᶜ[B⁄A] →ₗ[B] N`.

## Main definitions and results

* `TauCeti.Huber.ContinuousKaehlerDifferential.lift`: universal lift `Ωᶜ[B⁄A] →L[B] M` of a
  continuous derivation `δ : Derivation A B M`.
* `TauCeti.Huber.ContinuousKaehlerDifferential.continuous_fromIdeal`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.continuous_D`: continuity of `I → Ωᶜ[B⁄A]` and
  `d : B → Ωᶜ[B⁄A]`.
* `TauCeti.Huber.ContinuousKaehlerDifferential.linearMap_ext`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.hom_ext`: uniqueness of linear and continuous linear
  maps out of `Ωᶜ[B⁄A]`.
* `TauCeti.Huber.ContinuousKaehlerDifferential.continuousLinearMapEquiv`: equivalence between
  `Ωᶜ[B⁄A] →L[B] M` and continuous `A`-derivations `B → M`.
* `TauCeti.Huber.ContinuousKaehlerDifferential.liftOfFinite`: specialisation of `lift` to finite
  `B`-modules carrying `moduleTopology B N`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, (1.6.2)(b).
-/

public section

open UniformSpace Topology
open scoped Uniformity

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

section Lift

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]

/-- Scalar multiplication of `B ⊗̂_A B` on `Ωᶜ[B⁄A]` factors through the continuous multiplication
map `B ⊗̂_A B → B` (`smul_eq_mulRingHom_smul`), hence is continuous for the `B`-module topology. -/
instance : ContinuousSMul (CompletedTensor A B B) (ContinuousKaehlerDifferential A B) where
  continuous_smul := by
    have h : (fun p : CompletedTensor A B B × ContinuousKaehlerDifferential A B ↦ p.1 • p.2) =
        fun p ↦ mulRingHom A B p.1 • p.2 := by
      ext ⟨r, ω⟩
      exact smul_eq_mulRingHom_smul r ω
    rw [h]
    exact ((continuous_mulRingHom A B).comp continuous_fst).smul continuous_snd

section TargetModule

variable {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]

/-- Lift a continuous `A`-derivation `δ : B → M` to a `mulRingHom A B`-derivation
`B ⊗̂_A B →+ M` via the completed tensor product universal property into `TrivSqZeroExt B M`. -/
private noncomputable def liftCompletedDerivation (δ : Derivation A B M) (hδ : Continuous δ) :
    {f : CompletedTensor A B B →+ M //
      (∀ x y, f (x * y) = mulRingHom A B x • f y + mulRingHom A B y • f x) ∧
        ∀ b : B, f (inr A B B b - inl A B B b) = δ b} := by
  letI : Module Bᵐᵒᵖ M := Module.compHom M ((RingHom.id B).fromOpposite mul_comm)
  letI : IsCentralScalar B M := ⟨fun _ _ ↦ rfl⟩
  letI : IsScalarTower A Bᵐᵒᵖ M := ⟨fun a b m ↦ smul_assoc a b.unop m⟩
  letI : ContinuousSMul Bᵐᵒᵖ M :=
    ⟨(MulOpposite.continuous_unop.comp continuous_fst).smul continuous_snd⟩
  letI : NonarchimedeanRing (TrivSqZeroExt B M) :=
    { is_nonarchimedean := (inferInstance : NonarchimedeanAddGroup (B × M)).is_nonarchimedean }
  let ψ : B →ₐ[A] TrivSqZeroExt B M := (TauCeti.derivationToTrivSqZeroExtEquivLift A B B δ).1
  have hψ_cont : Continuous ψ :=
    (TrivSqZeroExt.continuous_inl.add (TrivSqZeroExt.continuous_inr.comp hδ)).congr
      fun b ↦ by ext <;> simp [ψ]
  have hcomm : (TrivSqZeroExt.inlHom B M).comp (algebraMap A B) =
      (ψ : B →+* TrivSqZeroExt B M).comp (algebraMap A B) :=
    RingHom.ext fun a ↦ (ψ.commutes a).symm
  let Φ : CompletedTensor A B B →+* TrivSqZeroExt B M :=
    CompletedTensor.lift (TrivSqZeroExt.inlHom B M) (ψ : B →+* TrivSqZeroExt B M)
      hcomm TrivSqZeroExt.continuous_inl hψ_cont
  have Φ_inl (b : B) : Φ (inl A B B b) = TrivSqZeroExt.inl b := lift_inl _ _ hcomm _ _ b
  have Φ_inr (b : B) : Φ (inr A B B b) = ψ b := lift_inr _ _ hcomm _ _ b
  let fstRingHom : TrivSqZeroExt B M →+* B := (TrivSqZeroExt.fstHom B B M).toRingHom
  have hfst : fstRingHom.comp Φ = mulRingHom A B :=
    CompletedTensor.hom_ext (TrivSqZeroExt.continuous_fst.comp (continuous_lift ..))
      (continuous_mulRingHom A B)
      (RingHom.ext fun b ↦ by simp [fstRingHom, Φ_inl])
      (RingHom.ext fun b ↦ by simp [fstRingHom, Φ_inr, ψ])
  have hfst_apply (z : CompletedTensor A B B) : (Φ z).fst = mulRingHom A B z :=
    RingHom.congr_fun hfst z
  refine ⟨AddMonoidHom.mk' (fun z ↦ (Φ z).snd) (fun x y ↦ by simp [map_add]),
    fun x y ↦ ?_, fun b ↦ ?_⟩
  · change (Φ (x * y)).snd = mulRingHom A B x • (Φ y).snd + mulRingHom A B y • (Φ x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst_apply, hfst_apply]
    rfl
  · change (Φ (inr A B B b - inl A B B b)).snd = δ b
    rw [map_sub, Φ_inr, Φ_inl]
    simp [ψ]

/-- Descend `liftCompletedDerivation δ hδ` from `I` modulo `I²` to `Ωᶜ[B⁄A] →ₗ[B] M`. -/
private noncomputable def liftLinearMap (δ : Derivation A B M) (hδ : Continuous δ) :
    {l : ContinuousKaehlerDifferential A B →ₗ[B] M // ∀ b, l (D A B b) = δ b} := by
  letI : Module (CompletedTensor A B B) M := Module.compHom M (mulRingHom A B)
  let d := liftCompletedDerivation δ hδ
  let g : ideal A B →ₗ[CompletedTensor A B B] M :=
    { toFun x := d.1 x.1
      map_add' x y := map_add d.1 x.1 y.1
      map_smul' r x := by
        change d.1 (r * x.1) = mulRingHom A B r • d.1 x.1
        rw [d.2.1, mem_ideal_iff.mp x.2, zero_smul, add_zero] }
  have hker : ideal A B • (⊤ : Submodule (CompletedTensor A B B) (ideal A B)) ≤ LinearMap.ker g :=
    fun _ hz ↦ Submodule.smul_induction_on hz
      (fun r hr x _ ↦ by
        change g (r • x) = 0
        rw [map_smul]
        change mulRingHom A B r • g x = 0
        rw [mem_ideal_iff.mp hr, zero_smul])
      (fun u v hu hv ↦ by rw [LinearMap.mem_ker, map_add, hu, hv, add_zero])
  let q := (Submodule.liftQ _ g hker).comp (cotangentEquiv A B).toLinearMap
  refine ⟨{ toFun := q
            map_add' := q.map_add
            map_smul' b ω := by
              change q (inl A B B b • ω) = b • q ω
              rw [q.map_smul]
              change mulRingHom A B (inl A B B b) • q ω = b • q ω
              rw [mulRingHom_inl] }, fun b ↦ ?_⟩
  rw [D_apply]
  change Submodule.liftQ _ g hker (cotangentEquiv A B (fromIdeal A B
    ⟨inr A B B b - inl A B B b, inr_sub_inl_mem_ideal A B b⟩)) = δ b
  rw [cotangentEquiv_fromIdeal]
  exact d.2.2 b

/-- **Universal lift for continuous differentials** (Huber 1996, (1.6.2)(b), existence): any
continuous `A`-derivation `δ : B → M` into a complete Hausdorff nonarchimedean `B`-module factors
through a continuous `B`-linear map `Ωᶜ[B⁄A] →L[B] M`. Neither `A` nor `B` needs any noetherian or
finite-type hypothesis for existence. -/
noncomputable def lift (δ : Derivation A B M) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential A B →L[B] M :=
  { (liftLinearMap δ hδ).1 with
    cont := IsModuleTopology.continuous_of_linearMap (liftLinearMap δ hδ).1 }

@[simp]
theorem lift_D (δ : Derivation A B M) (hδ : Continuous δ) (b : B) :
    lift δ hδ (D A B b) = δ b :=
  (liftLinearMap δ hδ).2 b

@[simp]
theorem lift_comp_D (δ : Derivation A B M) (hδ : Continuous δ) :
    (lift δ hδ).toLinearMap.compDer (D A B) = δ := by
  ext b
  exact lift_D δ hδ b

end TargetModule

end Lift

section FiniteType

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]

/-- **Continuity of the quotient presentation `I → Ωᶜ[B⁄A]`**: when `A → B` is topologically of
finite type and `B` is of noetherian type, the completed diagonal ideal `I` is finitely generated
over `B ⊗̂_A B`, hence carries the `B ⊗̂_A B`-module topology as its subspace topology, so
`fromIdeal A B` is continuous. -/
theorem continuous_fromIdeal (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Continuous (fromIdeal A B) := by
  have : IsNoetherianType (CompletedTensor A B B) :=
    .of_isTopologicallyFiniteType (isTopologicallyFiniteType_inl h)
  have : Module.Finite (CompletedTensor A B B) (ideal A B) :=
    Module.Finite.iff_fg.mpr (ideal_fg h)
  have : IsModuleTopology (CompletedTensor A B B) (ideal A B) :=
    IsNoetherianType.isModuleTopology_submodule (A := CompletedTensor A B B) (ideal A B)
  exact IsModuleTopology.continuous_of_linearMap (fromIdeal A B)

/-- **Huber (1.6.2)(b), continuity of the universal derivation**: when `A → B` is topologically of
finite type and `B` is of noetherian type, `d : B → Ωᶜ[B⁄A]` is continuous for the natural
`B`-module topology on `Ωᶜ[B⁄A]`. -/
theorem continuous_D (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Continuous (D A B) := by
  have hsub : Continuous fun b : B ↦
      (⟨inr A B B b - inl A B B b, inr_sub_inl_mem_ideal A B b⟩ : ideal A B) :=
    Continuous.subtype_mk ((continuous_inr A B B).sub (continuous_inl A B B)) _
  exact ((continuous_fromIdeal h).comp hsub).congr fun b ↦ (D_apply A B b).symm

/-- Two `B`-linear maps out of `Ωᶜ[B⁄A]` that agree on `d '' S`, for `S ⊆ B` generating a dense
`A`-subalgebra, are equal. -/
theorem linearMap_ext_of_dense_adjoin (h : IsTopologicallyFiniteType (algebraMap A B))
    {S : Set B} (hS : Dense (Algebra.adjoin A S : Set B))
    {M : Type*} [AddCommGroup M] [Module B M]
    {f₁ f₂ : ContinuousKaehlerDifferential A B →ₗ[B] M}
    (heq : ∀ s ∈ S, f₁ (D A B s) = f₂ (D A B s)) : f₁ = f₂ := by
  refine LinearMap.ext fun ω ↦ ?_
  have hmem : ω ∈ Submodule.span B (D A B '' S) := by
    rw [span_D_eq_top h hS]
    trivial
  refine Submodule.span_induction (fun x hx ↦ ?_) (by simp)
    (fun x y _ _ hx hy ↦ by simp [hx, hy]) (fun b x _ hx ↦ by simp [hx]) hmem
  obtain ⟨s, hs, rfl⟩ := hx
  exact heq s hs

/-- **Uniqueness for linear maps out of `Ωᶜ[B⁄A]`**: under the hypotheses of Huber (1.6.2)(a), two
`B`-linear maps out of `Ωᶜ[B⁄A]` agreeing on `D A B` are equal. -/
theorem linearMap_ext (h : IsTopologicallyFiniteType (algebraMap A B))
    {M : Type*} [AddCommGroup M] [Module B M]
    {f₁ f₂ : ContinuousKaehlerDifferential A B →ₗ[B] M}
    (heq : ∀ b, f₁ (D A B b) = f₂ (D A B b)) : f₁ = f₂ :=
  linearMap_ext_of_dense_adjoin h (S := Set.univ) (by simp [Algebra.adjoin_univ])
    fun b _ ↦ heq b

/-- **Uniqueness for continuous linear maps out of `Ωᶜ[B⁄A]`** (Huber 1996, (1.6.2)(b)). -/
theorem hom_ext (h : IsTopologicallyFiniteType (algebraMap A B))
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [Module B M]
    {f₁ f₂ : ContinuousKaehlerDifferential A B →L[B] M}
    (heq : ∀ b, f₁ (D A B b) = f₂ (D A B b)) : f₁ = f₂ :=
  ContinuousLinearMap.ext fun ω ↦ DFunLike.congr_fun (linearMap_ext h heq) ω

section UniversalEquiv

variable {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]

/-- **Universal property of `Ωᶜ[B⁄A]`** (Huber 1996, (1.6.2)(b)): every continuous `A`-derivation
`δ : B → M` into a complete Hausdorff nonarchimedean `B`-module factors through a unique continuous
`B`-linear map `Ωᶜ[B⁄A] →L[B] M`. -/
theorem existsUnique_lift (h : IsTopologicallyFiniteType (algebraMap A B))
    (δ : Derivation A B M) (hδ : Continuous δ) :
    ∃! f : ContinuousKaehlerDifferential A B →L[B] M, ∀ b, f (D A B b) = δ b :=
  ⟨lift δ hδ, lift_D δ hδ, fun _ hf ↦ hom_ext h fun b ↦ (hf b).trans (lift_D δ hδ b).symm⟩

/-- **Equivalence between continuous `B`-linear maps `Ωᶜ[B⁄A] →L[B] M` and continuous
`A`-derivations `B → M`** (Huber 1996, (1.6.2)(b)). -/
noncomputable def continuousLinearMapEquiv (h : IsTopologicallyFiniteType (algebraMap A B)) :
    (ContinuousKaehlerDifferential A B →L[B] M) ≃ {δ : Derivation A B M // Continuous δ} where
  toFun f := ⟨f.toLinearMap.compDer (D A B), f.continuous.comp (continuous_D h)⟩
  invFun δ := lift δ.1 δ.2
  left_inv _ := hom_ext h fun b ↦ lift_D _ _ b
  right_inv δ := Subtype.ext (lift_comp_D δ.1 δ.2)

@[simp]
theorem continuousLinearMapEquiv_apply_coe (h : IsTopologicallyFiniteType (algebraMap A B))
    (f : ContinuousKaehlerDifferential A B →L[B] M) :
    ((continuousLinearMapEquiv h f : {δ : Derivation A B M // Continuous δ}) :
      Derivation A B M) = f.toLinearMap.compDer (D A B) := (rfl)

@[simp]
theorem continuousLinearMapEquiv_symm_apply (h : IsTopologicallyFiniteType (algebraMap A B))
    (δ : {δ : Derivation A B M // Continuous δ}) :
    (continuousLinearMapEquiv h).symm δ = lift δ.1 δ.2 := (rfl)

end UniversalEquiv

end FiniteType

section FiniteTarget

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [Module.Finite B N] [TopologicalSpace N] [IsModuleTopology B N]

/-- **Universal lift into a finite `B`-module with its natural topology** (Huber 1996, (1.6.2)(b)):
when `B` is a complete Hausdorff Huber ring of noetherian type, any finite `B`-module `N` carrying
`moduleTopology B N` is automatically complete, Hausdorff, and nonarchimedean, so any continuous
`A`-derivation `δ : B → N` lifts to a `B`-linear map `Ωᶜ[B⁄A] →ₗ[B] N` (which is itself continuous
by `IsModuleTopology.continuous_of_linearMap`). -/
noncomputable def liftOfFinite (δ : Derivation A B N) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential A B →ₗ[B] N := by
  let _ : IsTopologicalAddGroup N := IsModuleTopology.isTopologicalAddGroup B N
  let _ : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  have : IsUniformAddGroup N := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp
    (IsNoetherianType.isNaturallyComplete (A := B) (M := N))
  have : NonarchimedeanAddGroup N := by
    rw [eq_moduleTopology B N]
    exact TauCeti.nonarchimedeanAddGroup_moduleTopology (A := B)
  exact (lift δ hδ).toLinearMap

@[simp]
theorem liftOfFinite_D (δ : Derivation A B N) (hδ : Continuous δ) (b : B) :
    liftOfFinite δ hδ (D A B b) = δ b := by
  let _ : IsTopologicalAddGroup N := IsModuleTopology.isTopologicalAddGroup B N
  let _ : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  have : IsUniformAddGroup N := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp
    (IsNoetherianType.isNaturallyComplete (A := B) (M := N))
  have : NonarchimedeanAddGroup N := by
    rw [eq_moduleTopology B N]
    exact TauCeti.nonarchimedeanAddGroup_moduleTopology (A := B)
  exact lift_D δ hδ b

@[simp]
theorem liftOfFinite_comp_D (δ : Derivation A B N) (hδ : Continuous δ) :
    (liftOfFinite δ hδ).compDer (D A B) = δ := by
  ext b
  exact liftOfFinite_D δ hδ b

end FiniteTarget

end TauCeti.Huber.ContinuousKaehlerDifferential
