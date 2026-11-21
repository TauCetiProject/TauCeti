/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Order
public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Basic
import TauCeti.Topology.Algebra.Module.Nakayama
import TauCeti.Topology.Algebra.Ring.Compact

/-!
# Counterexamples separating the hypotheses of profinite flatness

Counterexamples showing none of the defining hypotheses of `TauCeti.IsProfiniteFlat` is redundant:
proper nonzero quotients fail flatness; discrete non-fields fail compactness; the fraction field
of a compact Hausdorff DVR fails compactness; and nontrivial indiscrete modules fail Hausdorffness.
-/

public section

open IsLocalRing Topology

namespace TauCeti

section NonExamples

/-- For any nonzero proper ideal `I` of an integral domain `R`, `R ⧸ I` is not profinite flat
over `R` (for any topologies). -/
theorem not_isProfiniteFlat_quotient_of_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    [TopologicalSpace R] {I : Ideal R} (hI_bot : I ≠ ⊥) (hI_top : I ≠ ⊤)
    [TopologicalSpace (R ⧸ I)] : ¬ IsProfiniteFlat R (R ⧸ I) := fun h ↦ by
  have := h.isTorsionFree
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI_bot
  have hone : (1 : R ⧸ I) = 0 := (smul_eq_zero_iff_right ha0).mp <| by
    simpa [Algebra.smul_def] using Ideal.Quotient.eq_zero_iff_mem.mpr haI
  exact hI_top (Ideal.eq_top_of_isUnit_mem I (Ideal.Quotient.eq_zero_iff_mem.mp hone) isUnit_one)

/-- Over a discrete valuation ring `O`, `O ⧸ maximalIdeal O` is not profinite flat. -/
theorem not_isProfiniteFlat_quotient_maximalIdeal (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (O ⧸ maximalIdeal O)] :
    ¬ IsProfiniteFlat O (O ⧸ maximalIdeal O) :=
  not_isProfiniteFlat_quotient_of_ne_bot (IsDiscreteValuationRing.not_a_field O)
    (maximalIdeal.isMaximal O).ne_top

/-- A discrete integral domain `R` that is not a field is not profinite flat over itself. -/
theorem not_isProfiniteFlat_self_of_discreteTopology {R : Type*} [CommRing R] [IsDomain R]
    [TopologicalSpace R] [DiscreteTopology R] (hnotfield : ¬ IsField R) :
    ¬ IsProfiniteFlat R R := fun h ↦
  have := h.compactSpace; have : Finite R := finite_of_compact_of_discrete
  hnotfield (Finite.isField_of_domain R)

/-- Over a compact Hausdorff discrete valuation ring `O`, its fraction field `K` is never profinite
flat over `O` for any topology on `K`. -/
theorem not_isProfiniteFlat_of_isFractionRing (O K : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
    [T2Space O] [Field K] [Algebra O K] [IsFractionRing O K] [TopologicalSpace K] :
    ¬ IsProfiniteFlat O K := fun hK ↦ by
  have := hK.isTopologicalAddGroup; have := hK.continuousSMul
  have := hK.compactSpace; have := hK.t2Space
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hnil : ∀ a ∈ Ideal.span ({ϖ} : Set O), IsTopologicallyNilpotent a := fun _ ha ↦
    (IsLocalRing.isAdic_maximalIdeal O).isTopologicallyNilpotent_of_mem (hϖ.maximalIdeal_eq ▸ ha)
  have hϖK : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff (algebraMap O K) (IsFractionRing.injective O K)).mpr hϖ.ne_zero
  have htop_le : (⊤ : Submodule O K) ≤ Ideal.span ({ϖ} : Set O) • (⊤ : Submodule O K) := by
    rw [Submodule.ideal_span_singleton_smul]
    exact fun x _ ↦ ⟨(algebraMap O K ϖ)⁻¹ * x, Submodule.mem_top,
      by simp [Algebra.smul_def, mul_inv_cancel_left₀ hϖK]⟩
  have hbot : (⊤ : Submodule O K) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_isCompact (Submodule.fg_span_singleton ϖ) hnil
      isCompact_univ htop_le
  exact one_ne_zero ((Submodule.mem_bot O).mp (hbot ▸ Submodule.mem_top) : (1 : K) = 0)

/-- A nontrivial indiscrete module `M` is never profinite flat over any commutative ring `R`. -/
theorem not_isProfiniteFlat_of_indiscreteTopology (R M : Type*) [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IndiscreteTopology M] [Nontrivial M] :
    ¬ IsProfiniteFlat R M := fun hM ↦
  have := hM.t2Space; have := subsingleton_iff_indiscreteTopology.mpr ‹IndiscreteTopology M›
  false_of_nontrivial_of_subsingleton M

end NonExamples

end TauCeti
