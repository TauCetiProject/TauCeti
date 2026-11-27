/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The Sobolev embedding for Schwartz functions

For a Schwartz function `φ` on a finite-dimensional real inner product space `E` and
`s > k + n / 2`, `n = dim E`, the derivatives of `φ` of order at most `k` are bounded by a
constant times the `H^s` norm of `φ`
(`SchwartzMap.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpaceCLM`).
This is `TemperedDistribution.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace`
for the `L²` class of `φ`, whose Bessel-potential element is
`SchwartzMap.toBesselPotentialSpaceCLM s 2 φ`. It turns Sobolev estimates for operators on
Schwartz functions into estimates of derivatives in the sup norm.
-/

public section

open MeasureTheory Module
open scoped SchwartzMap

namespace SchwartzMap

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Sobolev embedding for Schwartz functions**, `s > k + n / 2`. The derivatives of order at most
`k` of a Schwartz function on `E` are bounded by a constant times its `H^s` norm. -/
theorem exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpaceCLM {s : ℝ} {k : ℕ}
    (hs : finrank ℝ E < 2 * (s - k)) :
    ∃ C, 0 ≤ C ∧ ∀ (φ : 𝓢(E, F)), ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ C * ‖toBesselPotentialSpaceCLM s 2 φ‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    TemperedDistribution.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace (F := F) hs
  refine ⟨C, hC0, fun φ j hj x ↦ ?_⟩
  have hφ : TemperedDistribution.MemSobolev s 2
      ((φ.toLp 2 : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    rw [Lp.toTemperedDistribution_toLp_eq]
    exact φ.memSobolev
  have hφB : hφ.toBesselPotentialSpace = toBesselPotentialSpaceCLM s 2 φ :=
    BesselPotentialSpace.ext (by
      rw [TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr,
        toDistr_toBesselPotentialSpaceCLM, Lp.toTemperedDistribution_toLp_eq])
  exact hφB ▸ hC hφ φ.continuous (φ.coeFn_toLp 2 volume) j hj x

end SchwartzMap
