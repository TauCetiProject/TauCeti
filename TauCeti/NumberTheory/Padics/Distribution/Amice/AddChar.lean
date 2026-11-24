/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Character
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.RingTheory.PowerSeries.EvalAt

/-!
# Integrating additive characters against locally analytic distributions

Let `K` be a complete nontrivially normed field with contractive `ℤ_p`-action, and let `μ` be a
locally analytic distribution on `ℤ_p` with values in `K`, with moments
`bₙ = μ(x ↦ (x choose n))` and Amice transform `A_μ = ∑ₙ bₙ Tⁿ`. This file shows that `μ` takes
on a locally analytic character `χ_z(x) = (1 + z) ^ x` the value of its Amice transform at `z`:

`μ(x ↦ (1 + z) ^ x) = A_μ(z) = ∑ₙ bₙ zⁿ`.

Write a locally analytic function evaluating to `χ_z` as the class of a vector of a stage
`LA_h(K)`. By Amice's theorem (`TauCeti.AnalyticStage.amiceEquiv`) this vector is the convergent
series `∑ₙ e_{h,n} • dₙ` of Amice's vectors, with `dₙ → 0`, and its Mahler coefficients are
`⌊n / pʰ⌋! dₙ` (`TauCeti.AnalyticStage.mahlerEquiv_eval`). The Mahler coefficients of `χ_z` are
the powers `zⁿ`, so `⌊n / pʰ⌋! dₙ = zⁿ`. On the other hand `μ` takes the value `⌊n / pʰ⌋! dₙ bₙ`
on `e_{h,n} • dₙ` (`TauCeti.LocallyAnalyticDistribution.stage_amiceTerm`), and its restriction to
`LA_h(K)` is continuous, so the value of `μ` is the convergent sum `∑ₙ zⁿ bₙ`. No `ℚ_p`-structure
on `K` is needed for this.

When `K` is moreover a normed `ℚ_p`-module, the character `χ_z` is locally analytic for every `z`
with `‖z‖ < 1`: for `‖z‖ < r_h`, with `r_h = p ^ (-1 / ((p - 1) pʰ))`, it is the evaluation of the
vector `TauCeti.AnalyticStage.addCharExpansion p h z` of `LA_h(K)`, and `r_h → 1`. On that vector
the restriction of `μ` to `LA_h(K)` takes the value `A_μ(z)`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.hasSum_coeff_amiceTransform_smul_pow`: on every locally
  analytic function evaluating to `χ_z`, `μ` takes the value of the convergent series `∑ₙ bₙ zⁿ`.
* `TauCeti.LocallyAnalyticDistribution.apply_eq_evalAt_amiceTransform`: `μ` takes the value
  `A_μ(z)` on every locally analytic function evaluating to `χ_z`.
* `TauCeti.LocallyAnalyticDistribution.stage_addCharExpansion`: on the stage `LA_h(K)`, `μ` takes
  the value `A_μ(z)` on the expansion of `χ_z`, for `‖z‖ < r_h`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2, Lemme II.2.1.
-/

public section

open Filter Topology Nat ZeroAtInftyContinuousMap

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

/-- **Integration of characters, as a convergent series.** On a locally analytic function `f`
evaluating to the character `χ_z(x) = (1 + z) ^ x`, a locally analytic distribution `μ` takes the
value `∑ₙ bₙ zⁿ`, the series of its moments `bₙ` against the powers of `z`, and this series
converges. The hypothesis `hr`, `zⁿ → 0`, names the character. -/
theorem hasSum_coeff_amiceTransform_smul_pow (μ : LocallyAnalyticDistribution p K) {z : K}
    (hr : Tendsto (z ^ ·) atTop (𝓝 0)) {f : LocallyAnalytic p K K}
    (hf : ⇑(LocallyAnalytic.eval K f) = PadicInt.addChar_of_value_at_one z hr) :
    HasSum (fun n ↦ (amiceTransform μ).coeff n • z ^ n)
      ((μ : Module.Dual K (LocallyAnalytic p K K)) f) := by
  obtain ⟨h, c, rfl⟩ := exists_ofStage K f
  rw [eval_ofStage] at hf
  -- The Mahler coefficients `⌊n / pʰ⌋! dₙ` of `χ_z`, with `d` the Amice coordinates of `c`, are
  -- the powers `zⁿ`.
  have hd (n : ℕ) : (n / p ^ h)! • (amiceEquiv p h K).symm c n = z ^ n := by
    rw [← mahlerEquiv_eval, PadicInt.mahlerEquiv_apply, hf, PadicInt.coe_addChar_of_value_at_one]
    exact PadicInt.fwdDiff_mahlerSeries hr n
  have hsum := (hasSum_amiceMap K ((amiceEquiv p h K).symm c)).mapL (stage h μ)
  rw [← amiceEquiv_apply, LinearIsometryEquiv.apply_symm_apply] at hsum
  rw [← stage_apply]
  convert hsum using 2 with n
  rw [stage_amiceTerm, ← nsmul_eq_mul, hd, smul_eq_mul, mul_comm]

/-- **Integration of characters.** A locally analytic distribution `μ` takes on the character
`χ_z(x) = (1 + z) ^ x` the value `A_μ(z)` of its Amice transform at `z`. The hypothesis `hr`,
`zⁿ → 0`, names the character. When `K` is moreover a normed `ℚ_p`-module, `χ_z` is locally
analytic for every `z` with `‖z‖ < 1` (`TauCeti.AnalyticStage.eval_addCharExpansion`). -/
theorem apply_eq_evalAt_amiceTransform (μ : LocallyAnalyticDistribution p K) {z : K}
    (hr : Tendsto (z ^ ·) atTop (𝓝 0)) {f : LocallyAnalytic p K K}
    (hf : ⇑(LocallyAnalytic.eval K f) = PadicInt.addChar_of_value_at_one z hr) :
    (μ : Module.Dual K (LocallyAnalytic p K K)) f = (amiceTransform μ).evalAt z := by
  rw [PowerSeries.evalAt_def, (hasSum_coeff_amiceTransform_smul_pow μ hr hf).tsum_eq]

/-- **Integration of a character on a stage.** For `‖z‖ < r_h`, the restriction of a distribution
`μ` to the stage `LA_h(K)` takes on the expansion of `χ_z(x) = (1 + z) ^ x` the value at `z` of the
Amice transform of `μ`. -/
theorem stage_addCharExpansion [Module ℚ_[p] K] [IsBoundedSMul ℚ_[p] K]
    (μ : LocallyAnalyticDistribution p K) {h : ℕ} {z : K} (hz : ‖z‖ < amiceRadius p h) :
    stage h μ (addCharExpansion p h z hz) = (amiceTransform μ).evalAt z := by
  have hr := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hz.trans (amiceRadius_lt_one h))
  rw [stage_apply, apply_eq_evalAt_amiceTransform μ hr]
  rw [eval_ofStage, eval_addCharExpansion K hz hr]

end LocallyAnalyticDistribution

end TauCeti
