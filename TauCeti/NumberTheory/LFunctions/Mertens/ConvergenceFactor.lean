/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Mertens

/-!
# Convergence factors for a number field

Let `K` be a number field. On a nonarchimedean local field whose residue field has `q` elements,
the form measure `|dx/x|` built from the additive Haar measure giving the integers mass `1` gives
the units mass `1 - q⁻¹`
(`MeasureTheory.Measure.withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one`). At the
completion of `K` at a nonzero prime `𝔭` of `𝓞 K`, `q` is the absolute norm `N𝔭`. This file proves
that the product of these masses over all primes is `0`: the partial products
`∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)` tend to `0`. This is why the Tamagawa measure of `𝔾ₘ` over `K` uses the
convergence factors `(1 - N𝔭⁻¹)⁻¹`; over `ℚ` it is
`Nat.tendsto_prod_primesLE_filter_notMem_one_sub_inv_atTop_nhds_zero`.

The divergence comes from the pole of the Dedekind zeta function `ζ_K` at `s = 1`, through
Mertens' product `∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)⁻¹ ~ e^γ κ_K log x`
(`TauCeti.LFunctions.tendsto_prod_one_sub_inv_absNorm_div_log`) with `κ_K > 0` the residue of
`ζ_K` at `s = 1`.

## Main statements

* `TauCeti.LFunctions.tendsto_prod_one_sub_inv_absNorm_inv_atTop`: the partial Euler products
  `∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)⁻¹` of `ζ_K` at `s = 1` tend to infinity.
* `TauCeti.LFunctions.tendsto_prod_one_sub_inv_absNorm_nhds_zero`: the partial products
  `∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)` tend to `0`.
-/

public section

open Filter IsDedekindDomain NumberField
open scoped Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- **The Euler product of `ζ_K` diverges at `s = 1`.** The partial products
`∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)⁻¹` over the nonzero primes of `𝓞 K` tend to infinity, being
asymptotic to `e^γ κ_K log x` by Mertens' product. -/
theorem tendsto_prod_one_sub_inv_absNorm_inv_atTop :
    Tendsto (fun x : ℝ ↦
      ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K),
        if (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x then (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ)⁻¹)⁻¹
        else 1)
      atTop atTop := by
  have hc : 0 < Real.exp Real.eulerMascheroniConstant * dedekindZeta_residue K :=
    mul_pos (Real.exp_pos _) (dedekindZeta_residue_pos K)
  refine ((tendsto_prod_one_sub_inv_absNorm_div_log K).pos_mul_atTop one_pos
    (Real.tendsto_log_atTop.const_mul_atTop hc)).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact div_mul_cancel₀ _ (mul_pos hc (Real.log_pos hx)).ne'

/-- **Form measures on `𝔾ₘ` over a number field need convergence factors.** The partial products
`∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)` over the nonzero primes of `𝓞 K` tend to `0`. -/
theorem tendsto_prod_one_sub_inv_absNorm_nhds_zero :
    Tendsto (fun x : ℝ ↦
      ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K),
        if (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x then 1 - (Ideal.absNorm 𝔭.asIdeal : ℝ)⁻¹ else 1)
      atTop (𝓝 0) := by
  refine (tendsto_prod_one_sub_inv_absNorm_inv_atTop K).inv_tendsto_atTop.congr fun x ↦ ?_
  rw [Pi.inv_apply, ← finprod_inv_distrib]
  exact finprod_congr fun 𝔭 ↦ by split_ifs <;> simp

end TauCeti.LFunctions
