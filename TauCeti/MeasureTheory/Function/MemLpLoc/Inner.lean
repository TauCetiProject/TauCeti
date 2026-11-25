/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.MeasureTheory.Function.MemLpLoc

/-!
# Local `Lᵖ` membership of inner products

For a real inner product space `V`, the pairing `⟪ψ, w⟫` of a field `ψ` continuous on `U` with a
field `w` locally `Lᵖ` on `U` is locally `Lᵖ` on `U` (`TauCeti.MemLpLoc.inner_continuousOn`),
since `ψ` is bounded on every compact subset of `U`. This is kept apart from
`TauCeti.MeasureTheory.Function.MemLpLoc`, which does not import inner product spaces.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

variable {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T2Space X] [NormedAddCommGroup V] [InnerProductSpace ℝ V] {μ : Measure X}
  [IsFiniteMeasureOnCompacts μ] {p : ENNReal} {U : Set X} {ψ w : X → V}

/-- The pairing of a field continuous on `U` with a locally `Lᵖ` field is locally `Lᵖ` on `U`. -/
theorem MemLpLoc.inner_continuousOn (hw : MemLpLoc p U w μ) (hψ : ContinuousOn ψ U) :
    MemLpLoc p U (fun z => ⟪ψ z, w z⟫_ℝ) μ := by
  convert (hw.clm_comp (innerSL ℝ)).clm_apply_continuousOn hψ using 2 with z
  rw [innerSL_apply_apply, real_inner_comm]

end TauCeti
