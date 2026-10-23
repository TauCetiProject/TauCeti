/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Integral-one test functions

Every nonempty open subset of a test-function domain contains a nonnegative test of integral
one, for any locally finite measure positive on nonempty open sets. Such tests recover the
coefficient of a constant distribution, including on arbitrarily small overlap neighborhoods.

The construction normalizes Mathlib's `exists_contDiff_tsupport_subset` by its positive integral.
-/

public section

open Set TopologicalSpace MeasureTheory
open scoped Distributions Topology

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {Ω : Opens E} {n : ℕ∞} {μ : Measure E}
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- There is a nonnegative integral-one test supported in any nonempty open subset of the
domain. The measure need not be translation invariant. -/
theorem exists_nonneg_integral_eq_one {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (hUΩ : U ⊆ Ω) :
    ∃ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U ∧ (∀ x, 0 ≤ φ x) ∧ ∫ x, φ x ∂μ = 1 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨f, hfs, hfc, hfd, hf01, hfx⟩ :=
    exists_contDiff_tsupport_subset (n := n) (hU.mem_nhds hx)
  have hfi : Integrable f μ := hfd.continuous.integrable_of_hasCompactSupport hfc
  have hf0 : ∀ y, 0 ≤ f y := fun y ↦ (hf01 (mem_range_self y)).1
  have hpos : 0 < ∫ y, f y ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero (x := x) hfd.continuous hfi hf0
      (by rw [hfx]; exact one_ne_zero)
  let φ : 𝓓^{n}(Ω, ℝ) := ⟨f, hfd, hfc, hfs.trans hUΩ⟩
  refine ⟨(∫ y, f y ∂μ)⁻¹ • φ, ?_, ?_, ?_⟩
  · simpa only [FunLike.coe_smul, Pi.smul_def, φ, coe_mk] using
      (tsupport_smul_subset_right (fun _ : E ↦ (∫ y, f y ∂μ)⁻¹) f).trans hfs
  · exact fun y ↦ mul_nonneg (inv_nonneg.mpr hpos.le) (hf0 y)
  · simp only [smul_apply, smul_eq_mul, φ, coe_mk, integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'

end TestFunction
