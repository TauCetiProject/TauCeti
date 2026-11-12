/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Finite families of test functions as `PiLp`-valued functions

A finite family `(φᵢ)` of `F`-valued test functions of class `Cⁿ` assembles into the function
`x ↦ (φᵢ x)ᵢ` with values in the `Lᵖ` product `PiLp p (fun _ ↦ F)`. This function is `Cⁿ`
(`TestFunction.contDiff_toLp_pi`) and has compact support
(`TestFunction.hasCompactSupport_toLp_pi`), the union of the supports of the `φᵢ`.
-/

public section

namespace TestFunction

open TopologicalSpace
open scoped Distributions ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} {ι : Type*}

/-- A finite family of `Cⁿ` test functions assembles into a `Cⁿ` function with values in the
`Lᵖ` product. -/
theorem contDiff_toLp_pi [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : ι → 𝓓^{n}(Ω, F)) :
    ContDiff ℝ n (fun x ↦ WithLp.toLp p fun i ↦ φ i x : E → PiLp p fun _ : ι ↦ F) :=
  (contDiff_piLp p).2 fun i ↦ (φ i).contDiff

/-- A finite family of test functions assembles into a compactly supported function with values
in the `Lᵖ` product. -/
theorem hasCompactSupport_toLp_pi [Finite ι] (p : ℝ≥0∞) (φ : ι → 𝓓^{n}(Ω, F)) :
    HasCompactSupport (fun x ↦ WithLp.toLp p fun i ↦ φ i x : E → PiLp p fun _ : ι ↦ F) := by
  refine (isCompact_iUnion fun i ↦ (φ i).hasCompactSupport).of_isClosed_subset
    (isClosed_tsupport _) (closure_minimal ?_ (isClosed_iUnion_of_finite fun i ↦
      isClosed_tsupport _))
  intro x hx
  by_contra h
  simp only [Set.mem_iUnion, not_exists] at h
  exact hx (by ext i; simpa using image_eq_zero_of_notMem_tsupport (h i))

end TestFunction
