/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.RealAxis
public import TauCeti.Analysis.ODE.DiracSystem.RealPotential

/-!
# Checks for the bounds of the Hermite–Biehler functions on the real axis

For a real constant potential `c ≥ 0` at `z = 0`, `E(t, 0) = e^{ct}` and `E~(t, 0) = -i e^{-ct}`,
while `∫₀ᵗ |q| = ct`. So the upper bound `|E(t, x)| ≤ e^{∫₀ᵗ |q|}` is attained by `E`
(`TauCeti.Examples.DiracSystem.norm_diracHermiteBiehler_ofReal_const_spectralParam_zero`) and
the lower bound `e^{-∫₀ᵗ |q|} ≤ |E~(t, x)|` by `E~`
(`TauCeti.Examples.DiracSystem.norm_diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero`):
both bounds are sharp.
-/

public section

open MeasureTheory Set Matrix Complex

namespace TauCeti.Examples.DiracSystem

/-- `∫₀ᵗ |c| = ct` for a constant `c ≥ 0` and `t ≥ 0`. -/
private theorem integral_norm_const {c t : ℝ} (hc : 0 ≤ c) :
    ∫ _ in (0 : ℝ)..t, ‖(c : ℂ)‖ = c * t := by
  simp [Complex.norm_real, abs_of_nonneg hc, mul_comm]

/-- **The upper bound is attained.** For a real constant `c ≥ 0`,
`|E(t, 0)| = e^{ct} = e^{∫₀ᵗ |q|}`. -/
theorem norm_diracHermiteBiehler_ofReal_const_spectralParam_zero {c t : ℝ} (hc : 0 ≤ c) :
    ‖diracHermiteBiehler (fun _ ↦ (c : ℂ)) t 0‖ = Real.exp (∫ _ in (0 : ℝ)..t, ‖(c : ℂ)‖) := by
  rw [integral_norm_const hc, diracHermiteBiehler_def,
    diracFundamentalMatrix_ofReal_const_spectralParam_zero]
  simp [Complex.norm_exp]

/-- **The lower bound is attained.** For a real constant `c ≥ 0`,
`|E~(t, 0)| = e^{-ct} = e^{-∫₀ᵗ |q|}`. -/
theorem norm_diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero {c t : ℝ} (hc : 0 ≤ c) :
    ‖diracHermiteBiehlerDirichlet (fun _ ↦ (c : ℂ)) t 0‖ =
      Real.exp (-∫ _ in (0 : ℝ)..t, ‖(c : ℂ)‖) := by
  rw [integral_norm_const hc, diracHermiteBiehlerDirichlet_def,
    diracFundamentalMatrix_ofReal_const_spectralParam_zero]
  simp [Complex.norm_exp]

/-- The upper bound of `TauCeti.norm_diracHermiteBiehler_ofReal_le` at this potential. -/
example {c t : ℝ} (ht : 0 ≤ t) :
    ‖diracHermiteBiehler (fun _ ↦ (c : ℂ)) t 0‖ ≤ Real.exp (∫ _ in (0 : ℝ)..t, ‖(c : ℂ)‖) := by
  simpa using norm_diracHermiteBiehler_ofReal_le
    (continuousOn_const.locallyIntegrableOn measurableSet_Ici) ht 0 (q := fun _ ↦ (c : ℂ))

end TauCeti.Examples.DiracSystem
