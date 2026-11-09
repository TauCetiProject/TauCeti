/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Measure

/-!
# Restriction of the mass measure to open subsets

Restricting a functional to tests on a smaller open set restricts its mass measure to that
open set. The measures live on different subtypes, so the comparison is a comap along the
inclusion, or, equivalently, a map back followed by measure restriction. In particular, all
Borel subsets of the smaller domain have the same mass before and after restriction.

The local mass comparison and preservation of locally finite mass are provided by
`TauCeti.Analysis.Distribution.Mass.Basic`. The measure comparison here is for real-linear
functionals, as is the construction of `Distribution.massMeasure`.
These identities let local measure representations of currents be compared on overlapping
open sets, without asserting finiteness at the frontier of the smaller domain.

## Main declarations

* `Distribution.massMeasure_comp_monoCLM`: the mass measure commutes with open restriction.
* `Distribution.map_massMeasure_comp_monoCLM`: the same identity on the original domain.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (localization of the mass of a current).
-/

public section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω Ω' : Opens E} {n : ℕ∞}

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ}

/-- The mass measure of an open restriction is the comap of the original mass measure along
the inclusion of open domains. No finiteness near the frontier of `Ω'` is assumed. -/
theorem massMeasure_comp_monoCLM (hT : HasLocallyFiniteMass T) (h : Ω' ≤ Ω) :
    massMeasure (T.comp (TestFunction.monoCLM (n₁ := n) ℝ).toLinearMap) =
      (massMeasure T).comap (Set.inclusion h) := by
  have hi := Opens.isOpenEmbedding_of_le h
  have := Measure.Regular.comap' (massMeasure T) hi
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
  rw [massMeasure_preimage_coe (hT.comp_monoCLM h) hW,
    hi.measurableEmbedding.comap_apply]
  have himage : Set.inclusion h '' ((↑) ⁻¹' W : Set Ω') =
      ((↑) ⁻¹' (W ∩ (Ω' : Set E)) : Set Ω) := by
    -- Expose the inclusion preimage so the image/preimage rewrite can match.
    change Set.inclusion h '' (Set.inclusion h ⁻¹' ((↑) ⁻¹' W : Set Ω)) = _
    rw [Set.image_preimage_eq_inter_range, Set.range_inclusion h, Set.preimage_inter]
    rfl
  rw [himage, massMeasure_preimage_coe hT (hW.inter Ω'.isOpen)]
  exact localMass_comp_monoCLM T h W

/-- Equivalently, mapping the restricted mass measure back to the original domain gives the
restriction of the original measure. This identity applies to every Borel set, not just opens. -/
theorem map_massMeasure_comp_monoCLM (hT : HasLocallyFiniteMass T) (h : Ω' ≤ Ω) :
    (massMeasure (T.comp (TestFunction.monoCLM (n₁ := n) ℝ).toLinearMap)).map (Set.inclusion h) =
      (massMeasure T).restrict ((↑) ⁻¹' (Ω' : Set E)) := by
  rw [massMeasure_comp_monoCLM hT h,
    (Opens.isOpenEmbedding_of_le h).measurableEmbedding.map_comap]
  congr 1
  exact Set.range_inclusion h

/-- On any set in the smaller domain, its mass is unchanged when viewed in the larger domain. -/
theorem massMeasure_comp_monoCLM_apply (hT : HasLocallyFiniteMass T) (h : Ω' ≤ Ω)
    (s : Set Ω') :
    massMeasure (T.comp (TestFunction.monoCLM (n₁ := n) ℝ).toLinearMap) s =
      massMeasure T (Set.inclusion h '' s) := by
  rw [massMeasure_comp_monoCLM hT h,
    (Opens.isOpenEmbedding_of_le h).measurableEmbedding.comap_apply]

end Distribution
