/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.UrysohnsLemma

/-!
# Symmetric bump functions at the identity of a locally compact group

Every neighbourhood `U` of the identity of a locally compact group carries a **symmetric bump**: a
compactly supported continuous function `ψ : G → ℝ` that is nonnegative, invariant under
inversion, positive at `1` and vanishes outside `U`. If the measure `μ` is finite on compact sets
and positive on nonempty open sets, as Haar measure is, the bump can be normalized to have
integral `1`.

Bumps of unit mass whose supports shrink to the identity are the scalar part of approximate
identities for convolution, both for functions on a compact group and for the twisted
convolution algebras of C⋆-dynamical systems. Inversion invariance makes them approximate
identities for convolution on either side, since `∫ ψ (g⁻¹) dμ(g) = ∫ ψ dμ` then holds even when
`μ` is not inversion invariant.

## Main statements

* `TauCeti.exists_symmetric_bump`: a symmetric bump supported in a given neighbourhood of `1`.
* `TauCeti.exists_symmetric_bump_integral_eq_one`: such a bump with unit mass.
-/

public section

open MeasureTheory Set Function
open scoped Topology CompactlySupported

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- **Symmetric bumps.** Every neighbourhood `U` of the identity of a locally compact group
supports a compactly supported continuous function `ψ : G → ℝ` that is nonnegative, invariant
under inversion and positive at `1`. -/
theorem exists_symmetric_bump {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ ψ : C_c(G, ℝ), (∀ g, 0 ≤ ψ g) ∧ (∀ g, ψ g⁻¹ = ψ g) ∧ support ψ ⊆ U ∧ 0 < ψ 1 := by
  obtain ⟨V, hVU, hVopen, hV1⟩ := mem_nhds_iff.1 hU
  -- A Urysohn function at `1` vanishing off the symmetric open neighbourhood `V ∩ V⁻¹`.
  obtain ⟨φ, hφ1, hφ0, hφc, hφIcc⟩ :=
    exists_continuous_one_zero_of_isCompact (X := G) isCompact_singleton
      (hVopen.inter hVopen.inv).isClosed_compl
      (disjoint_compl_right_iff_subset.2 (singleton_subset_iff.2 ⟨hV1, by simpa using hV1⟩))
  have hφU (g : G) (hg : g ∉ V ∩ V⁻¹) : φ g = 0 := hφ0 hg
  -- Symmetrize it by adding its composition with inversion.
  refine ⟨⟨φ + φ.comp ⟨Inv.inv, continuous_inv⟩,
    hφc.add (hφc.comp_homeomorph (Homeomorph.inv G))⟩, fun g => ?_, fun g => ?_, ?_, ?_⟩
  · exact add_nonneg (hφIcc g).1 (hφIcc g⁻¹).1
  · simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.add_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, inv_inv]
    exact add_comm _ _
  · intro g hg
    by_contra hgU
    have hgV : g ∉ V ∩ V⁻¹ := fun h => hgU (hVU h.1)
    have hgV' : g⁻¹ ∉ V ∩ V⁻¹ := fun h => hgV ⟨by simpa using h.2, h.1⟩
    exact hg (by simp [hφU g hgV, hφU g⁻¹ hgV'])
  · simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.add_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, inv_one, hφ1 rfl]
    norm_num

variable [MeasurableSpace G] [OpensMeasurableSpace G]

/-- **Symmetric bumps of unit mass.** If `μ` is finite on compact sets and positive on nonempty
open sets, every neighbourhood `U` of the identity supports a nonnegative, inversion-invariant,
compactly supported continuous function `ψ : G → ℝ` with `∫ ψ dμ = 1`. -/
theorem exists_symmetric_bump_integral_eq_one (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ ψ : C_c(G, ℝ), (∀ g, 0 ≤ ψ g) ∧ (∀ g, ψ g⁻¹ = ψ g) ∧ support ψ ⊆ U ∧
      ∫ g, ψ g ∂μ = 1 := by
  obtain ⟨ψ, hψ0, hψinv, hψU, hψ1⟩ := exists_symmetric_bump hU
  -- The mass is positive because `ψ` is positive on the nonempty open set `support ψ`.
  have hmass : 0 < ∫ g, ψ g ∂μ :=
    (integral_pos_iff_support_of_nonneg hψ0 ψ.integrable).2 <|
      ψ.continuous.isOpen_support.measure_pos μ ⟨1, hψ1.ne'⟩
  refine ⟨(∫ g, ψ g ∂μ)⁻¹ • ψ, fun g => ?_, fun g => ?_, ?_, ?_⟩
  · simpa using mul_nonneg (inv_nonneg.2 hmass.le) (hψ0 g)
  · simp [hψinv]
  · exact (support_const_smul_subset _ _).trans hψU
  · simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, inv_mul_cancel₀ hmass.ne']

end TauCeti
