/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.RingTheory.Semisimple.PositiveInvolution.Real

/-!
# Positive involutions after extension to `ℝ`: examples

On `B = ℚ` with the identity involution, positivity `x² > 0` gives, through
`PositiveInvolution.iff_real`, positivity of `v ↦ Trd_ℝ(v v*)` on `ℝ ⊗[ℚ] ℚ`, including at
`√2 ⊗ 1`, which is not of the form `1 ⊗ x`; there the value is `2`.
-/

public section

open TensorProduct TauCeti TauCeti.Algebra

namespace TauCeti.PositiveInvolutionRealExamples

/-- The identity of `ℚ` is a positive involution. -/
theorem rat_pos (x : ℚ) (hx : x ≠ 0) : 0 < semisimpleReducedTrace ℚ ℚ (x * star x) := by
  simpa [Algebra.trace_self_apply] using mul_self_pos.2 hx

/-- Its real extension is positive on `ℝ ⊗[ℚ] ℚ`. -/
example (v : ℝ ⊗[ℚ] ℚ) (hv : v ≠ 0) :
    0 < Module.Dual.baseChange ℝ (semisimpleReducedTrace ℚ ℚ) (v * star v) :=
  PositiveInvolution.iff_real.1 rat_pos v hv

/-- At `√2 ⊗ 1` the real extension takes the value `2`. -/
example : Module.Dual.baseChange ℝ (semisimpleReducedTrace ℚ ℚ)
    ((√2 ⊗ₜ[ℚ] (1 : ℚ)) * star (√2 ⊗ₜ[ℚ] (1 : ℚ))) = 2 := by
  simp

/-- `√2 ⊗ 1` is nonzero, so the value `2` is an instance of the positivity. -/
example : (√2 ⊗ₜ[ℚ] (1 : ℚ)) ≠ 0 := by
  intro h
  have := congrArg (Module.Dual.baseChange ℝ (semisimpleReducedTrace ℚ ℚ)) h
  simp at this

end TauCeti.PositiveInvolutionRealExamples
