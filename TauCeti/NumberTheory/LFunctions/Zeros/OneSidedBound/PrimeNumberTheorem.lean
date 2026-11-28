/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.Analysis.LaplaceTransform.Tauberian
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Laplace
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TauberianInputs

/-!
# Logarithmic savings for the signed prime remainder

For an odd prime `d` coprime to the progression modulus `q`, the remainder of the smoothed
Legendre-weighted prime sum is smaller than every inverse power of `log y` at large `y`.
This estimate is used when evaluating the remainder at a much larger, second cutoff.

This is the application `New.eventually_abs_primeRemainder_le` in
`grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
-/

open Filter

namespace TauCeti.OneSidedBound

/-- At fixed levels `q` and `qd`, the signed prime remainder saves every power of `log y`. -/
public theorem eventually_abs_primeRemainder_le {d q : ℕ} [Fact d.Prime] [NeZero q]
    (hd : d ≠ 2) (hc : q.Coprime d) (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, |primeRemainder d q y| ≤ (Real.log y ^ B)⁻¹ := by
  let f : ℝ → ℂ := Complex.ofReal ∘ fun u ↦ primeRemainder d q (Real.exp u)
  let F : ℂ → ℂ := fun s ↦ logDerivMean d q s / s
  have hf : LipschitzOnWith 26 f (Set.Ici 0) := by
    simpa only [f, one_mul] using (Complex.isometry_ofReal.lipschitzWith.comp
      (lipschitzWith_primeRemainder_exp d q)).lipschitzOnWith (s := Set.Ici 0)
  have hL (z : ℂ) (hz : 0 < z.re) : HasLaplace f z (dslope F 1 (1 + z)) := by
    have hs : 1 < (1 + z).re := by simpa using hz
    have hz₀ : z ≠ 0 := by intro he; simp [he] at hz
    have hs₁ : 1 + z ≠ 1 := by simpa using hz₀
    simpa [f, Function.comp_def, F, dslope_of_ne _ hs₁, slope_def_field] using
      hasLaplace_primeRemainder hd hc hs
  have hF : ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ 26 ≤ s.re → ‖s‖ ≤ Real.exp l →
      DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ 26 := by
    filter_upwards [eventually_analyticAt_and_norm_logDerivMean_div_le d q] with l hl s hs hn
    exact ⟨(hl s hs hn).1.differentiableAt, (hl s hs hn).2⟩
  have h := eventually_norm_le_inv_pow_of_hasLaplace hf hL hF B
  filter_upwards [Real.tendsto_log_atTop.eventually h, eventually_gt_atTop (0 : ℝ)] with y hy hy₀
  simpa only [f, Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, Real.exp_log hy₀]
    using hy

end TauCeti.OneSidedBound
