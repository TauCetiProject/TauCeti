/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Topology.Algebra.Module.PontryaginDual.Duality

/-!
# Contragredient group actions on coefficient-linear Pontryagin duals

Given a continuous representation `ρ : ContRepresentation R G M`, this file defines the
contragredient representation `contragredient E ρ` on `ModulePontryaginDual R E M` via
`(g · φ)(x) = φ(ρ g⁻¹ x)` and functoriality on continuous intertwining maps (`mapIntertwining`),
together with joint continuity on both sides, central-character inversion, and `G`-equivariant
biduality and full faithfulness.

## References

* V. Paškūnas, *The image of Colmez's Montreal functor*, Publ. Math. IHÉS 118 (2013), §2.
-/

public section

universe u v w w'

open scoped ContRepresentation

namespace TauCeti.ModulePontryaginDual

section Basic

variable {R : Type u} (E : Type v) {G : Type*} {M : Type w} {N : Type w'}
  [CommRing R] [Group G]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul R E]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]

/-- The contragredient continuous representation of `G` on `ModulePontryaginDual R E M`, given by
`(g · φ)(x) = φ(ρ g⁻¹ x)`. -/
def contragredient (ρ : ContRepresentation R G M) :
    ContRepresentation R G (ModulePontryaginDual R E M) where
  toMonoidHom :=
    { toFun := fun g ↦ map (E := E) (ρ g⁻¹)
      map_one' := by ext φ x; simp [map_apply]
      map_mul' := fun g h ↦ by ext φ x; simp [map_apply, mul_inv_rev, map_mul] }
@[simp] theorem contragredient_apply (ρ : ContRepresentation R G M) (g : G)
    (φ : ModulePontryaginDual R E M) (x : M) :
    contragredient E ρ g φ x = φ (ρ g⁻¹ x) := map_apply (ρ g⁻¹) φ x

/-- A continuous intertwining map dualizes to one between the contragredient representations. -/
def mapIntertwining {ρ₁ : ContRepresentation R G M} {ρ₂ : ContRepresentation R G N}
    (f : ρ₁ →ⁱL ρ₂) : contragredient E ρ₂ →ⁱL contragredient E ρ₁ where
  toContinuousLinearMap := map (E := E) f.toContinuousLinearMap
  isIntertwining' g := by
    ext ψ x
    simp only [ContinuousLinearMap.comp_apply, map_apply, contragredient_apply,
      ContIntertwiningMap.toContinuousLinearMap_apply]
    rw [f.isIntertwining g⁻¹ x]
@[simp] theorem mapIntertwining_apply {ρ₁ : ContRepresentation R G M}
    {ρ₂ : ContRepresentation R G N} (f : ρ₁ →ⁱL ρ₂) (ψ : ModulePontryaginDual R E N) (x : M) :
    mapIntertwining E f ψ x = ψ (f x) := map_apply f.toContinuousLinearMap ψ x

/-- Scalar action by a unit `u : Rˣ` on `M` dualizes to scalar action by `u⁻¹` on `M^∨`. -/
theorem contragredient_eq_inv_smul (ρ : ContRepresentation R G M) {g : G} {u : Rˣ}
    (hg : ∀ x : M, ρ g x = (u : R) • x) (φ : ModulePontryaginDual R E M) :
    contragredient E ρ g φ = ((u⁻¹ : Rˣ) : R) • φ := by
  ext x
  have hmul : (u : R) • ρ g⁻¹ x = x := by
    rw [← hg, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  rw [contragredient_apply, show ρ g⁻¹ x = ((u⁻¹ : Rˣ) : R) • x by
    rw [← one_smul R (ρ g⁻¹ x), ← Units.inv_mul u, mul_smul, hmul], map_smul, smul_apply]

/-- Evaluation into the double dual intertwines `ρ` with its double contragredient. -/
theorem eval_contragredient (ρ : ContRepresentation R G M) (g : G) (x : M) :
    contragredient E (contragredient E ρ) g (eval R E M x) = eval R E M (ρ g x) :=
  ext fun _ ↦ by simp [eval_apply, contragredient_apply]

section JointContinuity

variable [TopologicalSpace G] [ContinuousInv G]

/-- If `M` is discrete and `G` acts jointly continuously on `M`, then the contragredient action
of `G` on `ModulePontryaginDual R E M` is jointly continuous. -/
theorem continuous_contragredient_of_discrete [DiscreteTopology M]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2)) :
    Continuous (fun p : G × ModulePontryaginDual R E M ↦ contragredient E ρ p.1 p.2) := by
  refine continuous_of_continuous_eval fun m ↦ continuous_iff_continuousAt.mpr fun ⟨g₀, φ₀⟩ ↦ ?_
  have hU : IsOpen ((fun g : G ↦ ρ g⁻¹ m) ⁻¹' {ρ g₀⁻¹ m}) :=
    (isOpen_discrete _).preimage (hρ.comp (continuous_inv.prodMk continuous_const))
  refine (((continuous_eval_const (ρ g₀⁻¹ m)).comp continuous_snd).continuousAt).congr
    (Filter.eventually_of_mem ((hU.prod isOpen_univ).mem_nhds ⟨rfl, trivial⟩) ?_)
  rintro ⟨g, φ⟩ ⟨hg, -⟩
  simp only [Function.comp_apply, contragredient_apply]
  rw [Set.mem_preimage.mp hg]

/-- For a compact continuous `G`-module `M` and discrete `E`, every level set
`{g : G | contragredient E ρ g φ = ψ}` is open in `G`. -/
theorem isOpen_setOf_contragredient_eq_of_compact [CompactSpace M] [DiscreteTopology E]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2))
    (φ ψ : ModulePontryaginDual R E M) : IsOpen {g : G | contragredient E ρ g φ = ψ} := by
  rw [isOpen_iff_forall_mem_open]; intro g₀ hg₀
  let F : G × M → E := fun p ↦ φ (ρ p.1⁻¹ p.2) - ψ p.2
  have hn : IsOpen (F ⁻¹' {0}) := (isOpen_discrete {0}).preimage <|
    ((map_continuous φ).comp (hρ.comp (continuous_fst.inv.prodMk continuous_snd))).sub
      ((map_continuous ψ).comp continuous_snd)
  have hsub : ({g₀} : Set G) ×ˢ (Set.univ : Set M) ⊆ F ⁻¹' {0} := by
    rintro ⟨g, m⟩ ⟨rfl, -⟩; simp [F, show φ (ρ g⁻¹ m) = ψ m by simpa using DFunLike.congr_fun hg₀ m]
  obtain ⟨u, _, huo, -, hsu, htv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hn hsub
  exact ⟨u, fun g hg ↦ ext fun m ↦ by
    rw [contragredient_apply]; exact sub_eq_zero.mp (huv (Set.mk_mem_prod hg (htv trivial))),
    huo, hsu rfl⟩

/-- If `M` is compact, `E` is discrete, and `G` acts jointly continuously on `M`, then every
element of `ModulePontryaginDual R E M` has an open stabilizer in `G`. -/
theorem isOpen_stabilizer_contragredient_of_compact [CompactSpace M] [DiscreteTopology E]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2))
    (φ : ModulePontryaginDual R E M) : IsOpen {g : G | contragredient E ρ g φ = φ} :=
  isOpen_setOf_contragredient_eq_of_compact E ρ hρ φ φ

/-- If `M` is compact, `E` is discrete, and `G` acts jointly continuously on `M`, then the
contragredient action of `G` on `ModulePontryaginDual R E M` is jointly continuous. -/
theorem continuous_contragredient_of_compact [CompactSpace M] [DiscreteTopology E]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2)) :
    Continuous (fun p : G × ModulePontryaginDual R E M ↦ contragredient E ρ p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr fun ⟨g₀, φ₀⟩ ↦ ?_
  have hS := isOpen_setOf_contragredient_eq_of_compact E ρ hρ φ₀ (contragredient E ρ g₀ φ₀)
  refine (continuousAt_const (y := contragredient E ρ g₀ φ₀)).congr
    (Filter.eventually_of_mem ((hS.prod (isOpen_discrete {φ₀})).mem_nhds ⟨rfl, rfl⟩) ?_)
  rintro ⟨g, φ⟩ ⟨hg, hφ⟩; obtain rfl : φ = φ₀ := hφ; exact hg.symm

end JointContinuity

/-- Full faithfulness of `mapIntertwining` follows from `G`-equivariant biduality equivalences. -/
private theorem bijective_mapIntertwining_of_equiv
    {ρ₁ : ContRepresentation R G M} {ρ₂ : ContRepresentation R G N}
    (e₁ : ρ₁.Equiv (contragredient E (contragredient E ρ₁)))
    (e₂ : ρ₂.Equiv (contragredient E (contragredient E ρ₂)))
    (he₁ : ∀ x φ, e₁ x φ = φ x) (he₂ : ∀ x φ, e₂ x φ = φ x) :
    Function.Bijective (mapIntertwining E (ρ₁ := ρ₁) (ρ₂ := ρ₂)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun g ↦
    e₂.symm.toContIntertwiningMap.comp ((mapIntertwining E g).comp e₁.toContIntertwiningMap),
    fun f ↦ by
      ext x
      have h1 : (e₂.symm.toContIntertwiningMap.comp
          ((mapIntertwining E (mapIntertwining E f)).comp e₁.toContIntertwiningMap)) x =
          e₂.symm (mapIntertwining E (mapIntertwining E f) (e₁ x)) := rfl
      have h2 : mapIntertwining E (mapIntertwining E f) (e₁ x) = e₂ (f x) :=
        ext fun φ ↦ by simp [he₁, he₂, mapIntertwining_apply]
      simp only [ContIntertwiningMap.toContinuousLinearMap_apply]
      rw [h1, h2, e₂.symm_apply_apply],
    fun g ↦ by
      ext φ x
      have h1 : (e₂.symm.toContIntertwiningMap.comp
          ((mapIntertwining E g).comp e₁.toContIntertwiningMap)) x =
          e₂.symm (mapIntertwining E g (e₁ x)) := rfl
      simp only [ContIntertwiningMap.toContinuousLinearMap_apply, mapIntertwining_apply]
      rw [h1, ← he₂ _ φ, e₂.apply_symm_apply]; simp [he₁, mapIntertwining_apply]⟩

end Basic

section CompactBiduality

variable {R : Type u} (E : Type v) {G : Type*}
  [CommRing R] [TopologicalSpace R] [CompactSpace R] [Group G]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul R E] [Module.Injective R E] [Small.{v} R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- `G`-equivariant biduality for a compact continuous representation. -/
noncomputable def evalEquivOfCompactRep
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    (hN : IsCompactModule R N) (ρ : ContRepresentation R G N) :
    ρ.Equiv (contragredient E (contragredient E ρ)) :=
  ContRepresentation.Equiv.mk (evalEquivOfCompact (E := E) hE hN) fun g ↦ by
    ext x φ; simp [evalEquivOfCompact_apply, contragredient_apply]
@[simp] theorem evalEquivOfCompactRep_apply
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    (hN : IsCompactModule R N) (ρ : ContRepresentation R G N) (x : N)
    (φ : ModulePontryaginDual R E N) :
    evalEquivOfCompactRep E hE hN ρ x φ = φ x := evalEquivOfCompact_apply hE hN x φ

/-- Full faithfulness of `mapIntertwining` on compact continuous `G`-representations. -/
theorem bijective_mapIntertwining_of_compact {N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module R N₁] [TopologicalSpace N₁] [IsTopologicalAddGroup N₁]
    [AddCommGroup N₂] [Module R N₂] [TopologicalSpace N₂] [IsTopologicalAddGroup N₂]
    (hN₁ : IsCompactModule R N₁) (hN₂ : IsCompactModule R N₂)
    (ρ₁ : ContRepresentation R G N₁) (ρ₂ : ContRepresentation R G N₂) :
    Function.Bijective (mapIntertwining E (ρ₁ := ρ₁) (ρ₂ := ρ₂)) :=
  bijective_mapIntertwining_of_equiv E
    (evalEquivOfCompactRep E hE hN₁ ρ₁) (evalEquivOfCompactRep E hE hN₂ ρ₂)
    (evalEquivOfCompactRep_apply E hE hN₁ ρ₁) (evalEquivOfCompactRep_apply E hE hN₂ ρ₂)

end CompactBiduality

section DiscreteBiduality

variable {R : Type u} (E : Type v) {G : Type*}
  [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [TotallyDisconnectedSpace R] [Group G]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [ContinuousSMul R E] [Module.Injective R E] [Small.{v} R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- `G`-equivariant biduality for a discrete continuous representation with continuous
`R`-action. -/
noncomputable def evalEquivOfDiscreteRep
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul R M] (ρ : ContRepresentation R G M) :
    ρ.Equiv (contragredient E (contragredient E ρ)) :=
  ContRepresentation.Equiv.mk (evalEquivOfDiscrete (E := E) hE) fun g ↦ by
    ext x φ; simp [evalEquivOfDiscrete_apply, contragredient_apply]
@[simp] theorem evalEquivOfDiscreteRep_apply
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul R M] (ρ : ContRepresentation R G M) (x : M) (φ : ModulePontryaginDual R E M) :
    evalEquivOfDiscreteRep E hE ρ x φ = φ x := evalEquivOfDiscrete_apply hE x φ

/-- Full faithfulness of `mapIntertwining` on discrete continuous `G`-representations with
continuous `R`-action. -/
theorem bijective_mapIntertwining_of_discrete {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
    [ContinuousSMul R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
    [ContinuousSMul R M₂]
    (ρ₁ : ContRepresentation R G M₁) (ρ₂ : ContRepresentation R G M₂) :
    Function.Bijective (mapIntertwining E (ρ₁ := ρ₁) (ρ₂ := ρ₂)) :=
  bijective_mapIntertwining_of_equiv E
    (evalEquivOfDiscreteRep E hE ρ₁) (evalEquivOfDiscreteRep E hE ρ₂)
    (evalEquivOfDiscreteRep_apply E hE ρ₁) (evalEquivOfDiscreteRep_apply E hE ρ₂)

end DiscreteBiduality

end TauCeti.ModulePontryaginDual
