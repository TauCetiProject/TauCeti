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

Given a continuous representation `ρ : ContRepresentation R G M` of a group `G` on a topological
`R`-module `M`, this file defines the contragredient continuous representation on the
coefficient-linear Pontryagin dual `ModulePontryaginDual R E M`, given by
`(g · φ)(x) = φ(ρ g⁻¹ x)`.

## Main definitions and results

* `TauCeti.ModulePontryaginDual.contragredient`: the contragredient continuous representation on
  `ModulePontryaginDual R E M`.
* `TauCeti.ModulePontryaginDual.mapIntertwining`: functoriality of `ModulePontryaginDual` on
  continuous intertwining maps (`ContIntertwiningMap`).
* `TauCeti.ModulePontryaginDual.continuous_contragredient_of_discrete`: if `M` is discrete and
  the `G`-action on `M` is jointly continuous, then the contragredient action on `M^∨` is jointly
  continuous.
* `TauCeti.ModulePontryaginDual.isOpen_stabilizer_contragredient_of_compact`: if `M` is compact,
  `E` is discrete, and the `G`-action on `M` is jointly continuous, then every element of `M^∨`
  has an open stabilizer in `G`.
* `TauCeti.ModulePontryaginDual.continuous_contragredient_of_compact`: joint continuity of the
  contragredient action on the dual of a compact continuous `G`-module.
* `TauCeti.ModulePontryaginDual.contragredient_eq_inv_smul`: scalar action by a unit `u : Rˣ`
  dualizes to scalar action by `u⁻¹` (central character inversion `ζ ↦ ζ⁻¹`).
* `TauCeti.ModulePontryaginDual.evalEquivOfCompactRep` and
  `TauCeti.ModulePontryaginDual.evalEquivOfDiscreteRep`: `G`-equivariant biduality equivalences
  `ρ.Equiv (contragredient E (contragredient E ρ))`.
* `TauCeti.ModulePontryaginDual.bijective_mapIntertwining_of_compact` and
  `TauCeti.ModulePontryaginDual.bijective_mapIntertwining_of_discrete`: full faithfulness on
  continuous intertwining maps.

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
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul R E]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]

/-- The contragredient continuous representation of `G` on `ModulePontryaginDual R E M`, given by
`(g · φ)(x) = φ(ρ g⁻¹ x)`. -/
def contragredient (ρ : ContRepresentation R G M) :
    ContRepresentation R G (ModulePontryaginDual R E M) where
  toMonoidHom := {
    toFun := fun g ↦ map (E := E) (ρ g⁻¹)
    map_one' := by
      ext φ x
      simp [map_apply]
    map_mul' := fun g h ↦ by
      ext φ x
      simp [map_apply, mul_inv_rev, map_mul] }

@[simp]
theorem contragredient_apply (ρ : ContRepresentation R G M) (g : G)
    (φ : ModulePontryaginDual R E M) (x : M) :
    contragredient E ρ g φ x = φ (ρ g⁻¹ x) := by
  change map (E := E) (ρ g⁻¹) φ x = φ (ρ g⁻¹ x)
  exact map_apply (ρ g⁻¹) φ x

/-- A continuous intertwining map `f : ρ₁ →ⁱL ρ₂` dualizes to a continuous intertwining map between
the contragredient representations in the opposite direction. -/
def mapIntertwining {ρ₁ : ContRepresentation R G M} {ρ₂ : ContRepresentation R G N}
    (f : ρ₁ →ⁱL ρ₂) :
    contragredient E ρ₂ →ⁱL contragredient E ρ₁ where
  toContinuousLinearMap := map (E := E) f.toContinuousLinearMap
  isIntertwining' g := by
    ext ψ x
    simp only [ContinuousLinearMap.comp_apply, map_apply, contragredient_apply,
      ContIntertwiningMap.toContinuousLinearMap_apply]
    rw [f.isIntertwining g⁻¹ x]

@[simp]
theorem mapIntertwining_apply {ρ₁ : ContRepresentation R G M} {ρ₂ : ContRepresentation R G N}
    (f : ρ₁ →ⁱL ρ₂) (ψ : ModulePontryaginDual R E N) (x : M) :
    mapIntertwining E f ψ x = ψ (f x) := by
  change map (E := E) f.toContinuousLinearMap ψ x = ψ (f x)
  exact map_apply f.toContinuousLinearMap ψ x

/-- Scalar action by a unit `u : Rˣ` on `M` dualizes to scalar action by `u⁻¹` on `M^∨`. -/
theorem contragredient_eq_inv_smul (ρ : ContRepresentation R G M) {g : G} {u : Rˣ}
    (hg : ∀ x : M, ρ g x = (u : R) • x) (φ : ModulePontryaginDual R E M) :
    contragredient E ρ g φ = ((u⁻¹ : Rˣ) : R) • φ := by
  ext x
  have hinv : ρ g⁻¹ x = ((u⁻¹ : Rˣ) : R) • x := by
    have hmul : (u : R) • ρ g⁻¹ x = x := by
      calc
        (u : R) • ρ g⁻¹ x = ρ g (ρ g⁻¹ x) := (hg (ρ g⁻¹ x)).symm
        _ = (ρ g * ρ g⁻¹) x := rfl
        _ = ρ (g * g⁻¹) x := by rw [← map_mul]
        _ = x := by simp
    calc
      ρ g⁻¹ x = ((u⁻¹ : Rˣ) : R) • ((u : R) • ρ g⁻¹ x) := by
        rw [smul_smul, Units.inv_mul, one_smul]
      _ = ((u⁻¹ : Rˣ) : R) • x := by rw [hmul]
  rw [contragredient_apply, hinv, map_smul, smul_apply]

/-- Evaluation into the double dual intertwines `ρ` with its double contragredient. -/
theorem eval_contragredient (ρ : ContRepresentation R G M) (g : G) (x : M) :
    contragredient E (contragredient E ρ) g (eval R E M x) = eval R E M (ρ g x) := by
  ext φ
  simp [eval_apply, contragredient_apply]

/-- If `M` is discrete and `G` acts jointly continuously on `M`, then the contragredient action
of `G` on `ModulePontryaginDual R E M` is jointly continuous. -/
theorem continuous_contragredient_of_discrete [DiscreteTopology M]
    [TopologicalSpace G] [ContinuousInv G]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2)) :
    Continuous (fun p : G × ModulePontryaginDual R E M ↦ contragredient E ρ p.1 p.2) := by
  refine continuous_of_continuous_eval fun m ↦ ?_
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, φ₀⟩
  let m₀ : M := ρ g₀⁻¹ m
  let U : Set G := (fun g : G ↦ ρ g⁻¹ m) ⁻¹' {m₀}
  have hcont_g : Continuous (fun g : G ↦ ρ g⁻¹ m) :=
    hρ.comp (continuous_inv.prodMk continuous_const)
  have hUopen : IsOpen U := (isOpen_discrete {m₀}).preimage hcont_g
  have hnhds : U ×ˢ Set.univ ∈ nhds (g₀, φ₀) :=
    (hUopen.prod isOpen_univ).mem_nhds ⟨rfl, trivial⟩
  have hconst : ContinuousAt (fun p : G × ModulePontryaginDual R E M ↦ p.2 m₀) (g₀, φ₀) :=
    ((continuous_eval_const m₀).comp continuous_snd).continuousAt
  refine hconst.congr (Filter.eventually_of_mem hnhds ?_)
  rintro ⟨g, φ⟩ ⟨hg, -⟩
  have hgm : ρ g⁻¹ m = m₀ := hg
  change φ m₀ = contragredient E ρ g φ m
  rw [contragredient_apply, hgm]

/-- For a compact continuous `G`-module `M` and discrete `E`, every level set
`{g : G | contragredient E ρ g φ = ψ}` is open in `G`. -/
theorem isOpen_setOf_contragredient_eq_of_compact [CompactSpace M] [DiscreteTopology E]
    [TopologicalSpace G] [ContinuousInv G]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2))
    (φ ψ : ModulePontryaginDual R E M) :
    IsOpen {g : G | contragredient E ρ g φ = ψ} := by
  rw [isOpen_iff_forall_mem_open]
  intro g₀ hg₀
  let F : G × M → E := fun p ↦ φ (ρ p.1⁻¹ p.2) - ψ p.2
  have hFcont : Continuous F :=
    ((map_continuous φ).comp (hρ.comp (continuous_fst.inv.prodMk continuous_snd))).sub
      ((map_continuous ψ).comp continuous_snd)
  have hn : IsOpen (F ⁻¹' {0}) := (isOpen_discrete {0}).preimage hFcont
  have hsub : ({g₀} : Set G) ×ˢ (Set.univ : Set M) ⊆ F ⁻¹' {0} := by
    rintro ⟨g, m⟩ ⟨hg, -⟩
    have hg' : g = g₀ := Set.mem_singleton_iff.mp hg
    have hgm : φ (ρ g⁻¹ m) = ψ m := by
      rw [hg']
      simpa only [contragredient_apply] using DFunLike.congr_fun hg₀ m
    simp [F, hgm]
  obtain ⟨u, v, huo, -, hsu, htv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hn hsub
  refine ⟨u, fun g hg ↦ ?_, huo, hsu rfl⟩
  ext m
  have hmem : F (g, m) ∈ ({0} : Set E) := huv ⟨hg, htv trivial⟩
  rw [contragredient_apply]
  exact sub_eq_zero.mp hmem

/-- If `M` is compact, `E` is discrete, and `G` acts jointly continuously on `M`, then every
element of `ModulePontryaginDual R E M` has an open stabilizer in `G`. -/
theorem isOpen_stabilizer_contragredient_of_compact [CompactSpace M] [DiscreteTopology E]
    [TopologicalSpace G] [ContinuousInv G]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2))
    (φ : ModulePontryaginDual R E M) :
    IsOpen {g : G | contragredient E ρ g φ = φ} :=
  isOpen_setOf_contragredient_eq_of_compact E ρ hρ φ φ

/-- If `M` is compact, `E` is discrete, and `G` acts jointly continuously on `M`, then the
contragredient action of `G` on the discrete module `ModulePontryaginDual R E M` is jointly
continuous. -/
theorem continuous_contragredient_of_compact [CompactSpace M] [DiscreteTopology E]
    [TopologicalSpace G] [ContinuousInv G]
    (ρ : ContRepresentation R G M) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2)) :
    Continuous (fun p : G × ModulePontryaginDual R E M ↦ contragredient E ρ p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, φ₀⟩
  let S : Set G := {g : G | contragredient E ρ g φ₀ = contragredient E ρ g₀ φ₀}
  have hSopen : IsOpen S :=
    isOpen_setOf_contragredient_eq_of_compact E ρ hρ φ₀ (contragredient E ρ g₀ φ₀)
  have hnhds : S ×ˢ {φ₀} ∈ nhds (g₀, φ₀) :=
    (hSopen.prod (isOpen_discrete {φ₀})).mem_nhds ⟨rfl, rfl⟩
  refine (continuousAt_const (y := contragredient E ρ g₀ φ₀)).congr
    (Filter.eventually_of_mem hnhds ?_)
  rintro ⟨g, φ⟩ ⟨hg, hφ⟩
  have hφ' : φ = φ₀ := Set.mem_singleton_iff.mp hφ
  rw [hφ']
  exact hg.symm

end Basic

section CompactBiduality

variable {R : Type u} (E : Type v) {G : Type*}
  [CommRing R] [TopologicalSpace R] [CompactSpace R] [Group G]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul R E] [Module.Injective R E] [Small.{v} R]

/-- `G`-equivariant biduality for a compact continuous representation. -/
noncomputable def evalEquivOfCompactRep
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    (hN : IsCompactModule R N) (ρ : ContRepresentation R G N) :
    ρ.Equiv (contragredient E (contragredient E ρ)) :=
  ContRepresentation.Equiv.mk (evalEquivOfCompact (E := E) hE hN) fun g ↦ by
    ext x φ
    simp [evalEquivOfCompact_apply, contragredient_apply]

@[simp]
theorem evalEquivOfCompactRep_apply
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    (hN : IsCompactModule R N) (ρ : ContRepresentation R G N) (x : N)
    (φ : ModulePontryaginDual R E N) :
    evalEquivOfCompactRep E hE hN ρ x φ = φ x :=
  evalEquivOfCompact_apply hE hN x φ

/-- Full faithfulness of `mapIntertwining` on compact continuous `G`-representations. -/
theorem bijective_mapIntertwining_of_compact
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module R N₁] [TopologicalSpace N₁] [IsTopologicalAddGroup N₁]
    [AddCommGroup N₂] [Module R N₂] [TopologicalSpace N₂] [IsTopologicalAddGroup N₂]
    (hN₁ : IsCompactModule R N₁) (hN₂ : IsCompactModule R N₂)
    (ρ₁ : ContRepresentation R G N₁) (ρ₂ : ContRepresentation R G N₂) :
    Function.Bijective (mapIntertwining E (ρ₁ := ρ₁) (ρ₂ := ρ₂)) := by
  let e₁ := evalEquivOfCompactRep E hE hN₁ ρ₁
  let e₂ := evalEquivOfCompactRep E hE hN₂ ρ₂
  refine Function.bijective_iff_has_inverse.mpr ⟨fun g ↦
    e₂.symm.toContIntertwiningMap.comp
      ((mapIntertwining E g).comp e₁.toContIntertwiningMap),
    fun f ↦ ?_, fun g ↦ ?_⟩
  · ext x
    change e₂.symm (mapIntertwining E (mapIntertwining E f) (e₁ x)) = f x
    apply e₂.injective
    change e₂ (e₂.symm (mapIntertwining E (mapIntertwining E f) (e₁ x))) = e₂ (f x)
    rw [e₂.apply_symm_apply]
    ext φ
    simp [e₁, e₂, evalEquivOfCompactRep_apply, mapIntertwining_apply]
  · ext φ x
    simp only [ContIntertwiningMap.toContinuousLinearMap_apply, mapIntertwining_apply]
    change φ (e₂.symm (mapIntertwining E g (e₁ x))) = g φ x
    rw [← evalEquivOfCompactRep_apply E hE hN₂ ρ₂ (e₂.symm (mapIntertwining E g (e₁ x))) φ]
    change (e₂ (e₂.symm (mapIntertwining E g (e₁ x)))) φ = g φ x
    rw [e₂.apply_symm_apply]
    simp [e₁, evalEquivOfCompactRep_apply, mapIntertwining_apply]

end CompactBiduality

section DiscreteBiduality

variable {R : Type u} (E : Type v) {G : Type*}
  [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [TotallyDisconnectedSpace R] [Group G]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [ContinuousSMul R E] [Module.Injective R E] [Small.{v} R]

/-- `G`-equivariant biduality for a discrete continuous representation with continuous
`R`-action. -/
noncomputable def evalEquivOfDiscreteRep
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul R M] (ρ : ContRepresentation R G M) :
    ρ.Equiv (contragredient E (contragredient E ρ)) :=
  ContRepresentation.Equiv.mk (evalEquivOfDiscrete (E := E) hE) fun g ↦ by
    ext x φ
    simp [evalEquivOfDiscrete_apply, contragredient_apply]

@[simp]
theorem evalEquivOfDiscreteRep_apply
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul R M] (ρ : ContRepresentation R G M) (x : M)
    (φ : ModulePontryaginDual R E M) :
    evalEquivOfDiscreteRep E hE ρ x φ = φ x :=
  evalEquivOfDiscrete_apply hE x φ

/-- Full faithfulness of `mapIntertwining` on discrete continuous `G`-representations with
continuous `R`-action. -/
theorem bijective_mapIntertwining_of_discrete
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
    [ContinuousSMul R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
    [ContinuousSMul R M₂]
    (ρ₁ : ContRepresentation R G M₁) (ρ₂ : ContRepresentation R G M₂) :
    Function.Bijective (mapIntertwining E (ρ₁ := ρ₁) (ρ₂ := ρ₂)) := by
  let e₁ := evalEquivOfDiscreteRep E hE ρ₁
  let e₂ := evalEquivOfDiscreteRep E hE ρ₂
  refine Function.bijective_iff_has_inverse.mpr ⟨fun g ↦
    e₂.symm.toContIntertwiningMap.comp
      ((mapIntertwining E g).comp e₁.toContIntertwiningMap),
    fun f ↦ ?_, fun g ↦ ?_⟩
  · ext x
    change e₂.symm (mapIntertwining E (mapIntertwining E f) (e₁ x)) = f x
    apply e₂.injective
    change e₂ (e₂.symm (mapIntertwining E (mapIntertwining E f) (e₁ x))) = e₂ (f x)
    rw [e₂.apply_symm_apply]
    ext φ
    simp [e₁, e₂, evalEquivOfDiscreteRep_apply, mapIntertwining_apply]
  · ext φ x
    simp only [ContIntertwiningMap.toContinuousLinearMap_apply, mapIntertwining_apply]
    change φ (e₂.symm (mapIntertwining E g (e₁ x))) = g φ x
    rw [← evalEquivOfDiscreteRep_apply E hE ρ₂ (e₂.symm (mapIntertwining E g (e₁ x))) φ]
    change (e₂ (e₂.symm (mapIntertwining E g (e₁ x)))) φ = g φ x
    rw [e₂.apply_symm_apply]
    simp [e₁, evalEquivOfDiscreteRep_apply, mapIntertwining_apply]

end DiscreteBiduality

end TauCeti.ModulePontryaginDual
