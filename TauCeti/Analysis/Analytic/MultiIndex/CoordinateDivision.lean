/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
import TauCeti.Analysis.Analytic.Constructions

/-!
# Division of a multi-index power series by a coordinate

For a complete target space, suppose a multi-index expansion of `f` at `x` has weighted norm
summability at every positive radius smaller than `r`, and every term has degree at least `m`
in coordinate `i`. Shifting the exponents gives a quotient `g` analytic on the zero-centred
open polydisc of radius `r`, with `f (x + y) = y i ^ m • g y` for `‖y‖ < r`.

## Main results

* `TauCeti.exists_analyticOnNhd_eq_coord_pow_smul`: coordinate division on the whole polydisc.
* `AnalyticAt.exists_eventuallyEq_coord_sub_pow_smul`: for a function analytic at `x` with
  complete target, local coordinate division when Taylor coefficients vanish below the
  specified degree in that coordinate.
* `AnalyticAt.exists_eventuallyEq_coord_sub_smul`: for a function analytic at `x` with complete
  target, local division after subtracting the restriction to the coordinate hyperplane
  through the centre.

## References

The exponent shift follows Michail Karatarakis's formalization of Baker's theorem in
`mkaratarakis/mathlib4`, commit `1d51891b5be7ceeca95b4583cad39e0681c5e453`,
`Mathlib/NumberTheory/Transcendental/Baker/CoordinateDivision.lean` (Apache 2.0).
-/

public section

open Finset Topology
open scoped NNReal ENNReal

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

/-- For a complete target, suppose the expansion of `f` at `x` has weighted norm summability
at every positive radius smaller than `r` and no terms of degree less than `m` in coordinate
`i`. Then there is a quotient `g` analytic on the zero-centred open polydisc of radius `r`,
with `f (x + y) = y i ^ m • g y` for `‖y‖ < r`. -/
theorem exists_analyticOnNhd_eq_coord_pow_smul [CompleteSpace F] {f : (ι → 𝕜) → F}
    {x : ι → 𝕜} {c : (ι → ℕ) → F} {r : ℝ≥0}
    (hc : ∀ s : ℝ≥0, 0 < s → s < r →
      Summable fun α : ι → ℕ ↦ ‖c α‖ * (s : ℝ) ^ (∑ j, α j))
    (hf : ∀ y : ι → 𝕜, ‖y‖ < r →
      HasSum (fun α : ι → ℕ ↦ (∏ j, y j ^ α j) • c α) (f (x + y)))
    (i : ι) (m : ℕ) (hzero : ∀ α, α i < m → c α = 0) :
    ∃ g : (ι → 𝕜) → F, AnalyticOnNhd 𝕜 g (Metric.eball 0 r) ∧
      ∀ y : ι → 𝕜, ‖y‖ < r → f (x + y) = y i ^ m • g y := by
  classical
  let d : (ι → ℕ) → F := fun α ↦ c (α + Pi.single i m)
  have hd (s : ℝ≥0) (hs : 0 < s) (hsr : s < r) :
      Summable fun α : ι → ℕ ↦ ‖d α‖ * (s : ℝ) ^ (∑ j, α j) :=
    summable_norm_shift_single (NNReal.coe_pos.mpr hs) i m (hc s hs hsr)
  refine ⟨fun y ↦ ∑' α : ι → ℕ, (∏ j, y j ^ α j) • d α, ?_, fun y hy ↦ ?_⟩
  · intro y hy
    have hyr : ‖y‖₊ < r := by
      simpa only [mem_eball_zero_iff, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] using hy
    obtain ⟨s, hys, hsr⟩ := exists_between hyr
    have hs : 0 < s := zero_le.trans_lt hys
    obtain ⟨p, hp, -⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) d hs (hd s hs hsr)
    exact hp.analyticOnNhd y (by
      simpa only [mem_eball_zero_iff, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] using hys)
  · obtain ⟨s, hys, hsr⟩ := exists_between (show ‖y‖₊ < r by exact_mod_cast hy)
    have hs : 0 < s := zero_le.trans_lt hys
    exact (hf y hy).unique (hasSum_monomial_shift_single i m hzero
      (summable_norm_prod_pow_smul_of_le (hd s hs hsr) (by exact_mod_cast hys.le)).of_norm.hasSum)

end TauCeti

/-- For a complete target and a function analytic at `x`, vanishing of Taylor coefficients
below order `m` in coordinate `i` gives an analytic factor after removing `(z i - x i)^m`
near the centre `x`. -/
theorem AnalyticAt.exists_eventuallyEq_coord_sub_pow_smul [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (i : ι) (m : ℕ)
    (hzero : ∀ α : ι → ℕ, α i < m → TauCeti.mvTaylorCoeff f x α = 0) :
    ∃ g : (ι → 𝕜) → F, AnalyticAt 𝕜 g x ∧
      f =ᶠ[𝓝 x] fun z ↦ (z i - x i) ^ m • g z := by
  obtain ⟨r, hr, hc, hsum⟩ := hf.exists_hasSum_mvTaylorCoeff
  have hc' (s : ℝ≥0) (_hs : 0 < s) (hsr : s < r) :
      Summable fun α : ι → ℕ ↦
        ‖TauCeti.mvTaylorCoeff f x α‖ * (s : ℝ) ^ (∑ j, α j) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ hc
    intro α
    gcongr
  obtain ⟨g, hg, hfg⟩ := TauCeti.exists_analyticOnNhd_eq_coord_pow_smul hc' hsum i m hzero
  refine ⟨fun z ↦ g (z - x), ?_, ?_⟩
  · exact (hg 0 (Metric.mem_eball_self (ENNReal.coe_pos.2 hr))).comp_of_eq (by fun_prop)
      (sub_self x)
  · filter_upwards [Metric.ball_mem_nhds x (NNReal.coe_pos.mpr hr)] with z hz
    simpa only [add_sub_cancel, Pi.sub_apply] using hfg (z - x)
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)

/-- For a complete target and a function analytic at `x`, subtracting the restriction to the
coordinate hyperplane through `x` gives a function divisible near `x` by the corresponding
coordinate difference, with analytic quotient. -/
theorem AnalyticAt.exists_eventuallyEq_coord_sub_smul [CompleteSpace F] [DecidableEq ι]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (i : ι) :
    ∃ g : (ι → 𝕜) → F, AnalyticAt 𝕜 g x ∧
      (fun z ↦ f z - f (Function.update z i (x i))) =ᶠ[𝓝 x]
        fun z ↦ (z i - x i) • g z := by
  have hupdate : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ Function.update z i (x i)) x :=
    analyticAt_id.update analyticAt_const
  have hrestrict := hf.fun_comp_of_eq hupdate (Function.update_eq_self i x)
  obtain ⟨g, hg, hfg⟩ := (hf.sub hrestrict).exists_eventuallyEq_coord_sub_pow_smul i 1
    (fun α hα ↦ by
      rw [hf.mvTaylorCoeff_sub hrestrict, hf.mvTaylorCoeff_comp_update_same,
        ite_eq_left (Nat.lt_one_iff.1 hα), sub_self])
  exact ⟨g, hg, hfg.mono fun z hz ↦ by simpa only [Pi.sub_apply, pow_one] using hz⟩
