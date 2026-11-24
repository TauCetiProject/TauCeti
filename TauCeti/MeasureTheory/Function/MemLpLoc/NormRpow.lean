/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Function.MemLpLoc
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Local `Lᵖ` membership of the inverse norm

Near the origin of a nontrivial finite-dimensional real normed space `E` of dimension `d`, the
inverse norm `x ↦ ‖x‖⁻¹` belongs to `TauCeti.MemLpLoc p U` if and only if `p < d`
(`TauCeti.memLpLoc_norm_inv_iff`).
-/

public noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology

namespace TauCeti

/-- On any nontrivial finite-dimensional real normed space `E`, `‖x‖⁻¹` is locally `Lᵖ`
near the origin exactly when `p < dim E`. -/
theorem memLpLoc_norm_inv_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {p : ENNReal} {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK =>
    hK.isBounded.memLp_norm_inv_restrict h⟩
  by_contra! hpd
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hpd (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

end TauCeti
