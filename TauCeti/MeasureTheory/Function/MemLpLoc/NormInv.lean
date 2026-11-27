/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.MeasureTheory.Function.MemLpLoc
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Local `Lᵖ` membership of the inverse norm

On a nontrivial finite-dimensional real normed space `E` carrying a Borel additive Haar measure,
the singular radial kernel `x ↦ ‖x‖⁻¹` belongs to `TauCeti.MemLpLoc p U` on a neighbourhood `U`
of the origin if and only if `p < Module.finrank ℝ E` (`TauCeti.memLpLoc_norm_inv_iff_lt_finrank`).

This characterization is kept apart from `TauCeti/MeasureTheory/Function/MemLpLoc.lean`
because its proof uses the radial integral bounds in `TauCeti.MeasureTheory.Integral.NormRpow`.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Topology

namespace TauCeti

/-- On a nontrivial finite-dimensional real normed space, `x ↦ ‖x‖⁻¹` belongs to `MemLpLoc p U` on
a neighbourhood `U` of the origin if and only if `p < Module.finrank ℝ E`. -/
theorem memLpLoc_norm_inv_iff_lt_finrank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) μ ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK =>
    hK.isBounded.memLp_norm_inv_restrict h⟩
  by_contra! hp
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hp (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

end TauCeti
