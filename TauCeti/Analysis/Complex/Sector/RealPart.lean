/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# The real part on a closed sector about the positive real axis

On the closed sector `|arg z| ≤ θ`, with `0 ≤ θ ≤ π`, the real part is at least `‖z‖ cos θ`
(`TauCeti.arg_mem_Icc_iff_norm_mul_cos_le_re`). For `θ < π / 2` the constant `cos θ` is
positive, so on the sector the real part and the norm are comparable, and the real part tends to
`+∞` as `z → ∞` in the sector. This is how a Laplace integral `∫ e^{-zt} q(t) dt`,
whose estimates are in terms of `re z`, is controlled in a sector.

## Main results

* `Complex.isTheta_re_norm_principal_abs_arg_le`: for `θ < π / 2`, `re z = Θ(‖z‖)` on the sector
  `|arg z| ≤ θ`.
* `Complex.tendsto_re_cobounded_inf_principal_abs_arg_le`: for `θ < π / 2`, `re z → +∞` as
  `z → ∞` in the sector `|arg z| ≤ θ`.

The comparison is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMFMathlib/Analysis/Asymptotics/WatsonSector.lean`, where the sector is written
`δ ‖z‖ ≤ re z` (`Asymptotics.sectorAtTop`).
-/

public section

open Filter Asymptotics Bornology Real

namespace Complex

/-- On the closed sector `|arg z| ≤ θ` with `θ < π / 2`, the real part is comparable to the
norm: `re z = Θ(‖z‖)`. -/
theorem isTheta_re_norm_principal_abs_arg_le {θ : ℝ} (hθ : θ < π / 2) :
    (fun z : ℂ => z.re) =Θ[𝓟 {z | |arg z| ≤ θ}] fun z => ‖z‖ := by
  -- on the sector, `|arg z| ≤ max θ 0` and `cos (max θ 0) > 0`
  have hθ' : max θ 0 < π / 2 := max_lt hθ (by positivity)
  have hcos : 0 < Real.cos (max θ 0) :=
    cos_pos_of_mem_Ioo ⟨by linarith [le_max_right θ 0, pi_pos], hθ'⟩
  have hre (z : ℂ) (hz : |arg z| ≤ θ) : ‖z‖ * Real.cos (max θ 0) ≤ z.re :=
    (TauCeti.arg_mem_Icc_iff_norm_mul_cos_le_re ⟨le_max_right θ 0, by linarith [pi_pos]⟩).mp
      (abs_le.mp (hz.trans (le_max_left θ 0)))
  refine ⟨IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_),
    IsBigO.of_bound (Real.cos (max θ 0))⁻¹ (eventually_principal.mpr fun z hz => ?_)⟩
  · simpa using abs_re_le_norm z
  · have h := hre z hz
    rw [norm_norm, Real.norm_of_nonneg ((mul_nonneg (norm_nonneg z) hcos.le).trans h),
      inv_mul_eq_div, le_div_iff₀ hcos]
    exact h

/-- For `θ < π / 2`, the real part tends to `+∞` as `z → ∞` in the closed sector `|arg z| ≤ θ`. -/
theorem tendsto_re_cobounded_inf_principal_abs_arg_le {θ : ℝ} (hθ : θ < π / 2) :
    Tendsto re (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ}) atTop := by
  have h := ((isTheta_re_norm_principal_abs_arg_le hθ).mono inf_le_right).tendsto_norm_atTop_iff.mpr
    (by simpa [Function.comp_def] using tendsto_norm_cobounded_atTop.mono_left inf_le_left)
  refine h.congr' (eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_))
  -- on the sector the real part is nonnegative, so it is its own norm
  exact Real.norm_of_nonneg (abs_arg_le_pi_div_two_iff.mp (hz.trans hθ.le))

end Complex
