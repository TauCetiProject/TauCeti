/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Integrability of continuous functions invariant under a cocompact subgroup

This file proves that if a subgroup `Γ` of a topological group `G` admits a compact set meeting
every left orbit `Γ * g`, then any continuous left-`Γ`-invariant function `F : G → E` into a normed
group is uniformly bounded and integrable for every finite measure on `G`. It also proves that the
compact orbit-cover property passes to products of subgroups, and provides the `ENNReal.toReal`
weighting integrability criterion.

## Main results

* `TauCeti.exists_bound_of_isCompact_orbitCover`: a continuous left-`Γ`-invariant function is
  uniformly bounded when a compact set meets every left `Γ`-orbit.
* `TauCeti.integrable_of_isCompact_orbitCover`: such a function is integrable for every finite
  measure on `G`.
* `TauCeti.isCompact_orbitCover_prod`: if `Γ ≤ G` and `Δ ≤ H` admit compact orbit-covers, so does
  `Γ.prod Δ ≤ G × H`.
* `TauCeti.integrable_toReal_smul`: if `∫⁻ y, φ y * ‖F y‖ₑ ∂μ < ⊤`, then `(φ ·).toReal • F` is
  integrable.

## Provenance

Generalized from `New.integrable_of_isCocompact`, `New.isCocompact_prod`, and
`New.integrable_toReal_smul` in `src/Lib/General/Measure/IntegralOperators.lean` of
[grh-lean](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open MeasureTheory

namespace TauCeti

/-- If a compact set `C` meets every left orbit of `Γ` in `G`, then any continuous
left-`Γ`-invariant function `F : G → E` into a normed group is uniformly bounded. -/
theorem exists_bound_of_isCompact_orbitCover {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] {Γ : Subgroup G}
    (hΓ : ∃ C : Set G, IsCompact C ∧ ∀ g : G, ∃ γ ∈ Γ, γ * g ∈ C)
    {F : G → E} (hF_cont : Continuous F) (hF_inv : ∀ γ ∈ Γ, ∀ g : G, F (γ * g) = F g) :
    ∃ M : ℝ, ∀ g : G, ‖F g‖ ≤ M := by
  obtain ⟨C, hC, h_cover⟩ := hΓ
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF_cont.continuousOn
  refine ⟨M, fun g ↦ ?_⟩
  obtain ⟨γ, hγ, h_mem⟩ := h_cover g
  rw [← hF_inv γ hγ g]
  exact hM (γ * g) h_mem

/-- If a compact set meets every left orbit of `Γ` in `G`, then any continuous left-`Γ`-invariant
function `F : G → E` into a normed group is integrable for every finite Borel measure on `G`. -/
theorem integrable_of_isCompact_orbitCover {G E : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [NormedAddCommGroup E]
    [SecondCountableTopologyEither G E] {Γ : Subgroup G} {μ : Measure G} [IsFiniteMeasure μ]
    (hΓ : ∃ C : Set G, IsCompact C ∧ ∀ g : G, ∃ γ ∈ Γ, γ * g ∈ C)
    {F : G → E} (hF_cont : Continuous F) (hF_inv : ∀ γ ∈ Γ, ∀ g : G, F (γ * g) = F g) :
    Integrable F μ := by
  obtain ⟨M, hM⟩ := exists_bound_of_isCompact_orbitCover hΓ hF_cont hF_inv
  exact (integrable_const M).mono' hF_cont.aestronglyMeasurable (.of_forall hM)

/-- If `Γ ≤ G` and `Δ ≤ H` admit compact sets meeting every left orbit, then so does
`Γ.prod Δ ≤ G × H`. -/
theorem isCompact_orbitCover_prod {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] {Γ : Subgroup G} {Δ : Subgroup H}
    (hΓ : ∃ C : Set G, IsCompact C ∧ ∀ g : G, ∃ γ ∈ Γ, γ * g ∈ C)
    (hΔ : ∃ D : Set H, IsCompact D ∧ ∀ h : H, ∃ δ ∈ Δ, δ * h ∈ D) :
    ∃ K : Set (G × H), IsCompact K ∧ ∀ p : G × H, ∃ γ ∈ Γ.prod Δ, γ * p ∈ K := by
  obtain ⟨C, hC, hC_cover⟩ := hΓ
  obtain ⟨D, hD, hD_cover⟩ := hΔ
  refine ⟨C ×ˢ D, hC.prod hD, fun ⟨g, h⟩ ↦ ?_⟩
  obtain ⟨γ, hγ, hγg⟩ := hC_cover g
  obtain ⟨δ, hδ, hδh⟩ := hD_cover h
  exact ⟨(γ, δ), Subgroup.mem_prod.mpr ⟨hγ, hδ⟩, Set.mk_mem_prod hγg hδh⟩

/-- If `φ : Y → ENNReal` is measurable, `F : Y → V` is a.e. strongly measurable, and
`∫⁻ y, φ y * ‖F y‖ₑ ∂μ < ⊤`, then `y ↦ (φ y).toReal • F y` is integrable. -/
theorem integrable_toReal_smul {Y V : Type*} [MeasurableSpace Y] {μ : Measure Y}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : Y → ENNReal} {F : Y → V}
    (hφ : Measurable φ) (hF : AEStronglyMeasurable F μ)
    (h_fin : ∫⁻ y : Y, φ y * ‖F y‖ₑ ∂μ < ⊤) :
    Integrable (fun y : Y ↦ (φ y).toReal • F y) μ := by
  refine ⟨hφ.ennreal_toReal.aestronglyMeasurable.smul hF,
    (lintegral_mono fun y ↦ ?_).trans_lt h_fin⟩
  cases h : φ y with
  | top => simp [h]
  | coe r => simp [h, eNorm_smul]

end TauCeti
