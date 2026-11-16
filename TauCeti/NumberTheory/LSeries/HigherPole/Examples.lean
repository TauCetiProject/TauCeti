/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.LSeries.HigherPole.Boundary
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Riemann zeta powers and dyadic negative control for `PoleBoundary`

This file supplies concrete positive and negative instances of
`TauCeti.HigherPoleTauberian.PoleBoundary`:

* **Positive examples (`riemannZeta` and its positive integer powers):**
  `poleBoundary_riemannZeta` establishes `PoleBoundary riemannZeta 1 0 1` (holomorphic continuation
  across `Re s = 1` away from a simple pole of residue `1` at `s = 1`), and
  `poleBoundary_riemannZeta_pow` deduces `PoleBoundary (fun s ↦ riemannZeta s ^ (k + 1)) 1 k 1` for
  every `k : ℕ`.
* **Necessity of off-real continuation (dyadic negative control):**
  The geometric sum `s ↦ (1 - exp ((1 - s) * log 2))⁻¹` satisfies both the open half-plane
  holomorphy condition on `Re s > 1` (`analyticOnNhd_inv_one_sub_cexp_log_two`) and the local
  simple-pole condition at `s = 1` with residue `(log 2)⁻¹`
  (`exists_pole_germ_inv_one_sub_cexp_log_two`), yet satisfies `PoleBoundary` at abscissa `1` for
  no pole order `k + 1` and no leading coefficient `A`
  (`not_poleBoundary_inv_one_sub_cexp_log_two`) because of its periodic poles on the boundary line
  at `1 + (2π / log 2) i`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242 (§5.2.1, Theorem III, pp. 235–238; §5.3, p. 242).
-/

public section

open Complex Filter Metric Set
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-! ### The Riemann zeta function and its powers -/

/-- The Riemann zeta function satisfies `PoleBoundary riemannZeta 1 0 1` (holomorphic continuation
across `Re s = 1` away from a simple pole of residue `1` at `s = 1`). -/
theorem poleBoundary_riemannZeta : PoleBoundary riemannZeta 1 0 1 := by
  have h1 : AnalyticOnNhd ℂ riemannZeta₁ {s : ℂ | 1 ≤ s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_riemannZeta₁).mono
      (subset_univ _)
  have hp : PoleBoundary (fun s ↦ ((1 : ℝ) : ℂ) / (s - (1 : ℝ)) ^ (0 + 1) * riemannZeta₁ s)
      1 0 1 := by
    simpa using (poleBoundary_div_sub_pow 1 1 0).mul_analytic h1 (C := 1) riemannZeta₁_one
  refine hp.congr fun s hs ↦ ?_
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  simp [riemannZeta_eq_inv_sub_mul hs1]

/-- Every positive integer power `riemannZeta ^ (k + 1)` satisfies `PoleBoundary` at abscissa `1`
with pole order `k + 1` and leading coefficient `1`. -/
theorem poleBoundary_riemannZeta_pow (k : ℕ) :
    PoleBoundary (fun s ↦ riemannZeta s ^ (k + 1)) 1 k 1 := by
  simpa using poleBoundary_riemannZeta.pow_succ_of_zero k

/-! ### Necessity of continuation away from the real pole: the dyadic denominator -/

/-- On `Re s > 1`, `1 - exp ((1 - s) * log 2)` is nonvanishing since
`‖exp ((1 - s) * log 2)‖ < 1`. -/
private theorem one_sub_cexp_log_two_ne_zero {s : ℂ} (hs : 1 < s.re) :
    1 - cexp ((1 - s) * Real.log 2) ≠ 0 := by
  intro h
  have heq : cexp ((1 - s) * Real.log 2) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖cexp ((1 - s) * Real.log 2)‖ = 1 := by rw [heq, norm_one]
  rw [norm_exp] at hnorm
  have hre : ((1 - s) * Real.log 2).re < 0 := by
    rw [mul_comm, re_ofReal_mul, sub_re, one_re]
    exact mul_neg_of_pos_of_neg (Real.log_pos one_lt_two) (sub_neg.mpr hs)
  have hlt : Real.exp (((1 - s) * Real.log 2).re) < 1 := Real.exp_lt_one_iff.mpr hre
  linarith

/-- The dyadic sum `s ↦ (1 - exp ((1 - s) * log 2))⁻¹` is holomorphic on `Re s > 1`, so it
satisfies the `interior` clause of `PoleBoundary` at abscissa `1`. -/
theorem analyticOnNhd_inv_one_sub_cexp_log_two :
    AnalyticOnNhd ℂ (fun s ↦ (1 - cexp ((1 - s) * Real.log 2))⁻¹) {s : ℂ | 1 < s.re} := by
  refine AnalyticOnNhd.inv (analyticOnNhd_const.sub ?_) fun s hs ↦
    one_sub_cexp_log_two_ne_zero hs
  exact fun s _ ↦ ((analyticAt_const.sub analyticAt_id).mul analyticAt_const).cexp

/-- Near `s = 1`, `s ↦ (1 - exp ((1 - s) * log 2))⁻¹` has the local simple-pole form
`g s / (s - 1)` on a disc about `1` with `g` holomorphic and `g 1 = (Real.log 2)⁻¹`, so it
satisfies the `pole` clause of `PoleBoundary` at `a = 1`, `k = 0`, `A = (Real.log 2)⁻¹`. -/
theorem exists_pole_germ_inv_one_sub_cexp_log_two :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball (1 : ℂ) r) ∧
      g 1 = ((Real.log 2)⁻¹ : ℝ) ∧
      ∀ s ∈ ball (1 : ℂ) r, 1 < s.re →
        (1 - cexp ((1 - s) * Real.log 2))⁻¹ = g s / (s - 1) := by
  let denom : ℂ → ℂ := fun s ↦ 1 - cexp ((1 - s) * Real.log 2)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_ne : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2.ne'
  have hderiv : HasDerivAt denom (Real.log 2 : ℂ) 1 := by
    have h1 : HasDerivAt (fun s : ℂ ↦ (1 - s) * (Real.log 2 : ℂ)) (-(Real.log 2 : ℂ)) 1 := by
      simpa using ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 1)).mul_const
        (Real.log 2 : ℂ)
    have h2 : HasDerivAt denom (0 - cexp ((1 - (1 : ℂ)) * Real.log 2) * -(Real.log 2 : ℂ)) 1 :=
      (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub h1.cexp
    simpa [denom] using h2
  have hdenom_an : AnalyticOnNhd ℂ denom univ := fun s _ ↦
    analyticAt_const.sub (((analyticAt_const.sub analyticAt_id).mul analyticAt_const).cexp)
  let q : ℂ → ℂ := dslope denom 1
  have hq_an : AnalyticOnNhd ℂ q univ := hdenom_an.dslope 1
  have hq1_val : q 1 = (Real.log 2 : ℂ) := by
    simp only [q, dslope_same, hderiv.deriv]
  have hq1 : q 1 ≠ 0 := hq1_val ▸ hlog2_ne
  obtain ⟨r, hr, hq_ne⟩ :=
    Metric.eventually_nhds_iff_ball.mp ((hq_an 1 (mem_univ 1)).continuousAt.eventually_ne hq1)
  refine ⟨r, hr, fun s ↦ (q s)⁻¹, (hq_an.mono (subset_univ _)).inv hq_ne,
    by simp [hq1_val], fun s _ hsre ↦ ?_⟩
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hsre
  have hsub0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hqs : q s = denom s / (s - 1) := by
    have hd1 : denom 1 = 0 := by simp [denom]
    simp only [q, dslope_of_ne denom hs1, slope_def_field, hd1, sub_zero]
  dsimp only
  rw [hqs, inv_div, div_right_comm, div_self hsub0, one_div]

/-- Evaluation of `cexp ((1 - s) * log 2)` along the horizontal approach
`s = 1 + (2π / log 2) i + ε` to the off-real boundary pole `1 + (2π / log 2) i`. -/
private theorem cexp_one_sub_two_pi_div_log_two (ε : ℝ) :
    cexp ((1 - (((1 : ℂ) + (2 * Real.pi / Real.log 2 : ℝ) * I) + ε)) * Real.log 2) =
      (Real.exp (-ε * Real.log 2) : ℂ) := by
  have hlog2_ne : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos one_lt_two).ne'
  have harg : (1 - (((1 : ℂ) + (2 * Real.pi / Real.log 2 : ℝ) * I) + ε)) * Real.log 2 =
      ((-ε * Real.log 2 : ℝ) : ℂ) - 2 * Real.pi * I := by
    have hy_mul : ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Real.log 2 = 2 * Real.pi := by
      push_cast
      exact div_mul_cancel₀ _ hlog2_ne
    calc
      (1 - (((1 : ℂ) + (2 * Real.pi / Real.log 2 : ℝ) * I) + ε)) * Real.log 2
          = -(ε : ℂ) * Real.log 2 - ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Real.log 2 * I := by
        ring
      _ = ((-ε * Real.log 2 : ℝ) : ℂ) - 2 * Real.pi * I := by
        rw [hy_mul]
        push_cast
        ring
  rw [harg, Complex.exp_periodic.sub_eq, Complex.ofReal_exp]

/-- Despite being holomorphic on `Re s > 1` with a simple pole at `s = 1`, the dyadic function
`s ↦ (1 - exp ((1 - s) * log 2))⁻¹` satisfies `PoleBoundary` at abscissa `1` for **no** pole order
`k + 1` and **no** leading coefficient `A`: its pole at `1 + (2π / log 2) i` violates the `away`
condition. -/
theorem not_poleBoundary_inv_one_sub_cexp_log_two (k : ℕ) (A : ℝ) :
    ¬ PoleBoundary (fun s ↦ (1 - cexp ((1 - s) * Real.log 2))⁻¹) 1 k A := by
  intro h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  let y : ℝ := 2 * Real.pi / Real.log 2
  have hy : y ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hlog2.ne'
  obtain ⟨r, hr, g, hg, hF⟩ := h.away y hy
  let z₀ : ℂ := (1 : ℂ) + y * I
  -- Along `s_ε = z₀ + ε` (`ε → 0⁺`), `1 - exp ((1 - s_ε) * log 2) = 1 - exp (-ε * log 2) → 0`
  -- while `g (z₀ + ε) → g z₀`, so `(1 - exp (-ε * log 2)) * g (z₀ + ε)` tends both to `1` and `0`.
  have hlim_g : Tendsto (fun ε : ℝ ↦ g (z₀ + ε)) (𝓝[>] 0) (𝓝 (g z₀)) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ g (z₀ + ε)) 0 :=
      (hg z₀ (mem_ball_self hr)).continuousAt.comp_of_eq
        (continuousAt_const.add Complex.continuous_ofReal.continuousAt) (by simp)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlim_d : Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ)) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hprod0 : Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ) * g (z₀ + ε))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim_d.mul hlim_g
  have hev_one : (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ) * g (z₀ + ε)) =ᶠ[𝓝[>] 0]
      fun _ ↦ (1 : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with ε ⟨hε0, hεr⟩
    have hFε := hF (z₀ + ε) (by simp [z₀, dist_eq_norm, abs_of_pos hε0, hεr]) (by simp [z₀, hε0])
    rw [cexp_one_sub_two_pi_div_log_two ε] at hFε
    have hd_ne : (1 - (Real.exp (-ε * Real.log 2) : ℂ)) ≠ 0 := by
      have hlt : Real.exp (-ε * Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
      exact sub_ne_zero.mpr (by exact_mod_cast hlt.ne')
    rw [← hFε, mul_inv_cancel₀ hd_ne]
  exact one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds.congr' hev_one.symm) hprod0)

end TauCeti.HigherPoleTauberian
