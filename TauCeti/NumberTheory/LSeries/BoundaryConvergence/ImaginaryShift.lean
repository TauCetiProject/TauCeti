/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.RejectionTests
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Imaginary shifts and vertical-line sharpness of boundary Tauberian theorems

Newman's Laplace Tauberian theorem (`newmanLaplace_tendsto_integral`), its bounded Dirichlet
consequence (`boundedDirichlet_tendsto_ordered_at_one`), and the Euler-logarithm continuation across
`re s = 1` (`DirichletCharacter.exists_differentiableOn_exp_eq_LFunction` via
`TauCeti.exists_differentiableOn_eqOn_exp_comp_le_re`) all ask for holomorphy or nonvanishing on an
open neighbourhood of the **entire** closed boundary half-plane (`0 ≤ re z` or `1 ≤ re s`), rather
than near the real boundary point (`z = 0` or `s = 1`) alone.

Multiplying by an oscillatory factor `exp (u i t)` on `[0, ∞)` or `n ^ (u i)` on `ℕ` for a nonzero
real frequency `u ≠ 0` translates the Laplace or Dirichlet variable vertically by `u i`, moving a
pole or zero away from the real endpoint to an off-axis boundary point `u i` or `1 + u i` while
preserving unit norm, analyticity at the real endpoint, nonvanishing at `1`, and radial (Abel)
boundary limits:

* **Oscillatory Laplace transforms (`re z = 0`).** For `u ≠ 0`, `f t = exp (u i t)` has unit norm
  everywhere and Laplace transform `(z - u i)⁻¹` on `0 < re z`, which extends holomorphically to
  `{u i}ᶜ` (in particular across `z = 0`) and has radial limit `i / u` as `σ → 0⁺`, yet the finite
  integrals `∫ t in 0..T, exp (u i t)` do not converge as `T → ∞`.
* **Imaginary-power Dirichlet series (`re s = 1`).** For `u ≠ 0`, the unit-norm coefficients
  `n ^ (u i)` sum on `1 < re s` to `ζ(s - u i)`, which is holomorphic on `{1 + u i}ᶜ` (covering
  `{1 ≤ re s} \ {1 + u i}`, including a neighbourhood of `s = 1`), nonzero at `s = 1`, and has the
  radial Abel limit `ζ(1 - u i)` as `σ → 1⁺`. Combining the step-function Laplace identity with the
  pole expansion of `ζ` gives the Euler–Maclaurin boundary asymptotic
  `(∑ n ∈ Icc 1 N, n ^ (u i) / n) - N ^ (u i) / (u i) → ζ(1 - u i)`, from which the ordered partial
  sums diverge. In particular, the Abelian theorem `tendsto_LSeries_nhdsGT_one` admits no converse
  for bounded coefficients without continuation along the whole line `re s = 1`.
* **Imaginary-shifted Euler logarithms (`re s = 1`).** The prime-power coefficients
  `-(Λ n / log n) n ^ (u i)` are bounded by `1` and satisfy
  `exp (LSeries _ s) = (ζ(s - u i))⁻¹` on `1 < re s`. The regularized reciprocal
  `(s - 1 - u i) (riemannZeta₁ (s - u i))⁻¹` continues `(ζ(s - u i))⁻¹` holomorphically across the
  entire closed half-plane `1 ≤ re s` and, when `u ≠ 0`, is nonzero at `s = 1`, yet vanishes at
  `1 + u i`; consequently the logarithm series admits not even a continuous extension to `1 ≤ re s`.

## Main declarations

* `TauCeti.LSeries.integral_cexp_mul_I_mul_cexp_neg_mul`,
  `TauCeti.LSeries.tendsto_integral_cexp_mul_I_mul_cexp_neg_nhdsGT_zero`,
  `TauCeti.LSeries.not_tendsto_intervalIntegral_cexp_mul_I_atTop`: Laplace transform, Abel limit,
  and non-convergence of finite integrals for `t ↦ exp (u i t)`.
* `TauCeti.LSeries.riemannZeta₁_add_one_eq_one_sub_mul_stepCorrection`,
  `TauCeti.LSeries.riemannZeta_add_one_eq_inv_sub_stepCorrection`: analytic continuation of `ζ` on
  `-1 < re z` via `stepCorrection 1`.
* `TauCeti.LSeries.LSeriesHasSum_natCast_cpow_mul_I`,
  `TauCeti.LSeries.tendsto_LSeries_natCast_cpow_mul_I_nhdsGT_one`,
  `TauCeti.LSeries.tendsto_sum_Icc_natCast_cpow_mul_I_div_sub`,
  `TauCeti.LSeries.not_tendsto_sum_Icc_natCast_cpow_mul_I_div_atTop`: shifted `ζ` continuation,
  Abel limit, Euler–Maclaurin boundary asymptotic, and divergence of ordered boundary sums for
  `n ^ (u i)`.
* `TauCeti.LSeries.exp_LSeries_neg_vonMangoldt_div_log_mul_cpow_mul_I`,
  `TauCeti.LSeries.differentiableAt_sub_mul_riemannZeta₁_inv`,
  `TauCeti.LSeries.sub_mul_riemannZeta₁_inv_eq_zero_iff`,
  `TauCeti.LSeries.not_continuousOn_of_LSeriesHasSum_neg_vonMangoldt_div_log_mul_cpow_mul_I`,
  `TauCeti.LSeries.not_differentiableOn_of_LSeriesHasSum_neg_vonMangoldt_div_log_mul_cpow_mul_I`:
  regularized reciprocal-zeta continuation across `1 ≤ re s` (whose unique zero on `1 ≤ re s` is
  `1 + u i`) and non-extendability of its Euler-logarithm Dirichlet series.

## References

* G. H. Hardy and M. Riesz, *The General Theory of Dirichlet's Series*, Cambridge Tracts in
  Mathematics and Mathematical Physics 18, Cambridge University Press, 1915.
* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., Oxford University Press,
  1986, §4.11.
-/

public section

open ArithmeticFunction Complex Filter MeasureTheory Set
open scoped Topology Interval

namespace TauCeti.LSeries

/-! ### Oscillatory Laplace transforms on `[0, ∞)` -/

/-- For `0 < re z`, the Laplace transform of `t ↦ exp (u i t)` on `[0, ∞)` is `(z - u i)⁻¹`. -/
theorem integral_cexp_mul_I_mul_cexp_neg_mul {u : ℝ} {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ici (0 : ℝ), cexp (u * I * t) * cexp (-z * t) = (z - u * I)⁻¹ := by
  have hre : (-(z - u * I)).re < 0 := by simpa using hz
  have hcongr : (fun t : ℝ ↦ cexp (u * I * t) * cexp (-z * t)) =
      fun t : ℝ ↦ cexp (-(z - u * I) * t) := by
    ext t
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hcongr, integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi hre 0,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div]

/-- **Abel limit of the oscillatory Laplace transform.** For `u ≠ 0`, the Laplace transform of
`t ↦ exp (u i t)` converges to `i / u` as real `σ` decreases to `0`, even though the improper
integral at `σ = 0` diverges. -/
theorem tendsto_integral_cexp_mul_I_mul_cexp_neg_nhdsGT_zero {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun σ : ℝ ↦ ∫ t in Ici (0 : ℝ), cexp (u * I * t) * cexp (-(σ : ℂ) * t))
      (𝓝[>] 0) (𝓝 (I / u)) := by
  have hne : (0 : ℂ) - u * I ≠ 0 := by simp [hu]
  have hcont : ContinuousAt (fun σ : ℝ ↦ ((σ : ℂ) - u * I)⁻¹) 0 :=
    ContinuousAt.inv₀ (by fun_prop) hne
  have hval : ((0 : ℂ) - u * I)⁻¹ = I / u := by
    have hu' : (u : ℂ) ≠ 0 := mod_cast hu
    rw [zero_sub, ← one_div]
    field_simp [hu']
    simp
  refine (hval ▸ hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 0 < σ)
  exact (integral_cexp_mul_I_mul_cexp_neg_mul (by simpa using hσ)).symm

/-- For nonzero real `u`, the oscillatory exponential `T ↦ exp (u i T)` has no limit as
`T → ∞`: translating `T` by `π / |u|` negates the value while preserving any limit. -/
theorem not_tendsto_cexp_mul_I_atTop {u : ℝ} (hu : u ≠ 0) (L : ℂ) :
    ¬ Tendsto (fun T : ℝ ↦ cexp (u * I * T)) atTop (𝓝 L) := by
  intro hL
  have hnorm1 : (fun T : ℝ ↦ ‖cexp (u * I * T)‖) = fun _ ↦ (1 : ℝ) := by
    ext T
    have hre : ((u : ℂ) * I * T).re = 0 := by simp
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have hL0 : L ≠ 0 := by
    intro rfl
    have : (1 : ℝ) = 0 :=
      tendsto_nhds_unique (hnorm1 ▸ tendsto_const_nhds) (by simpa using hL.norm)
    norm_num at this
  set δ : ℝ := Real.pi / |u|
  have hshift : Tendsto (fun T : ℝ ↦ cexp (u * I * ((T + δ : ℝ) : ℂ))) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_add_const_right atTop δ tendsto_id)
  have hmul : Tendsto (fun T : ℝ ↦ cexp (u * I * ((T + δ : ℝ) : ℂ))) atTop
      (𝓝 (cexp (u * I * δ) * L)) := by
    refine (hL.const_mul (cexp (u * I * δ))).congr fun T ↦ ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexp1 : cexp (u * I * δ) = 1 :=
    mul_right_cancel₀ hL0 ((tendsto_nhds_unique hmul hshift).trans (one_mul L).symm)
  have hexp_neg1 : cexp (u * I * δ) = -1 := by
    rcases abs_choice u with h | h
    · have hδ : u * δ = Real.pi := by
        simp only [δ, h]
        exact mul_div_cancel₀ Real.pi hu
      have harg : (u : ℂ) * I * (δ : ℂ) = Real.pi * I := by
        calc (u : ℂ) * I * (δ : ℂ) = ((u * δ : ℝ) : ℂ) * I := by push_cast; ring
          _ = Real.pi * I := by rw [hδ]
      rw [harg, Complex.exp_pi_mul_I]
    · have hδ : u * δ = -Real.pi := by
        have hneg : -u ≠ 0 := neg_ne_zero.mpr hu
        calc u * δ = u * (Real.pi / -u) := by simp [δ, h]
          _ = -Real.pi := by field_simp [hneg]
      have harg : (u : ℂ) * I * (δ : ℂ) = -(Real.pi * I) := by
        calc (u : ℂ) * I * (δ : ℂ) = ((u * δ : ℝ) : ℂ) * I := by push_cast; ring
          _ = -(Real.pi * I) := by rw [hδ]; push_cast; ring
      rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  have : (1 : ℂ) = -1 := hexp1.symm.trans hexp_neg1
  norm_num at this

/-- **Sharpness on the imaginary axis in Newman's Laplace theorem.** For `u ≠ 0`, the bounded
integrand `t ↦ exp (u i t)` has Laplace transform `(z - u i)⁻¹`, holomorphic at every point of
`{z | 0 ≤ re z} \ {u i}` (in particular at `z = 0`) with radial limit `i / u` at `0`, yet its
truncated integrals `∫ t in 0..T, exp (u i t)` do not converge as `T → ∞`. -/
theorem not_tendsto_intervalIntegral_cexp_mul_I_atTop {u : ℝ} (hu : u ≠ 0) (L : ℂ) :
    ¬ Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, cexp (u * I * t)) atTop (𝓝 L) := by
  intro hL
  have huI : (u : ℂ) * I ≠ 0 := by simp [hu]
  have h : Tendsto (fun T : ℝ ↦ cexp (u * I * T)) atTop (𝓝 (L * (u * I) + 1)) := by
    refine ((hL.mul_const ((u : ℂ) * I)).add_const 1).congr fun T ↦ ?_
    rw [integral_exp_mul_complex huI, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      div_mul_cancel₀ _ huI, sub_add_cancel]
  exact not_tendsto_cexp_mul_I_atTop hu _ h

/-- No function agreeing with the Laplace transform of `t ↦ exp (u i t)` (`u ≠ 0`) on `0 < re z`
can be holomorphic on an open neighbourhood of the entire closed half-plane `0 ≤ re z`. -/
theorem not_differentiableOn_of_integral_cexp_mul_I {u : ℝ} (hu : u ≠ 0) {Ω : Set ℂ}
    {G : ℂ → ℂ} (hΩ : IsOpen Ω) (hcover : {z : ℂ | 0 ≤ z.re} ⊆ Ω)
    (hLaplace : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Ici (0 : ℝ), cexp (u * I * t) * cexp (-z * t)) :
    ¬ DifferentiableOn ℂ G Ω := by
  intro hG
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ cexp (u * I * t)) (volume.restrict (Ici 0)) :=
    (by fun_prop : Continuous fun t : ℝ ↦ cexp (u * I * t)).aestronglyMeasurable
  have hbound : ∀ t ∈ Ici (0 : ℝ), ‖cexp (u * I * t)‖ ≤ 1 := fun t _ ↦ by
    have hre : ((u : ℂ) * I * t).re = 0 := by simp
    rw [Complex.norm_exp, hre, Real.exp_zero]
  exact not_tendsto_intervalIntegral_cexp_mul_I_atTop hu (G 0)
    (newmanLaplace_tendsto_integral hmeas hbound hΩ hcover hG hLaplace)

/-! ### Imaginary-power Dirichlet series on `re s = 1` -/

/-- On `1 < re s`, the Dirichlet series with unit-norm coefficients `n ^ (u i)` sums to the
vertically shifted zeta function `ζ(s - u i)`. -/
theorem LSeriesHasSum_natCast_cpow_mul_I (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (n : ℂ) ^ ((u : ℂ) * I)) s (riemannZeta (s - u * I)) := by
  simpa using (LSeriesHasSum_mul_natCast_cpow_iff 1 (u * I) s (riemannZeta (s - u * I))).mpr
    (LSeriesHasSum_one (by simpa using hs))

/-- **Abel limit of the imaginary-power Dirichlet series.** For `u ≠ 0`, `LSeries (n ^ (u i)) σ`
converges to the nonzero value `ζ(1 - u i)` as real `σ` decreases to `1`. -/
theorem tendsto_LSeries_natCast_cpow_mul_I_nhdsGT_one {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun σ : ℝ ↦ LSeries (fun n : ℕ ↦ (n : ℂ) ^ ((u : ℂ) * I)) σ)
      (𝓝[>] 1) (𝓝 (riemannZeta (1 - u * I))) := by
  have hne : ((1 : ℝ) : ℂ) - u * I ≠ 1 := by simp [hu]
  have hcont : ContinuousAt (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) - u * I)) 1 :=
    (differentiableAt_riemannZeta hne).continuousAt.comp_of_eq
      (by fun_prop : Continuous fun σ : ℝ ↦ (σ : ℂ) - u * I).continuousAt rfl
  have hlim : Tendsto (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) - u * I))
      (𝓝[>] 1) (𝓝 (riemannZeta (1 - u * I))) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  exact (LSeriesHasSum_natCast_cpow_mul_I u (by simpa using hσ)).LSeries_eq.symm

/-- **Regularized step-correction identity for `ζ`.** Throughout the half-plane `-1 < re z` where
`stepCorrection 1` converges, `riemannZeta₁ (z + 1) = 1 - z * stepCorrection 1 z`. -/
theorem riemannZeta₁_add_one_eq_one_sub_mul_stepCorrection {z : ℂ} (hz : -1 < z.re) :
    riemannZeta₁ (z + 1) = 1 - z * stepCorrection 1 z := by
  have hopen : IsOpen {w : ℂ | -1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hL : AnalyticOnNhd ℂ (fun w : ℂ ↦ riemannZeta₁ (w + 1)) {w : ℂ | -1 < w.re} :=
    (differentiable_riemannZeta₁.comp (by fun_prop)).differentiableOn.analyticOnNhd hopen
  have hR : AnalyticOnNhd ℂ (fun w : ℂ ↦ 1 - w * stepCorrection 1 w) {w : ℂ | -1 < w.re} :=
    ((differentiableOn_const 1).sub
      (differentiableOn_id.mul (differentiableOn_stepCorrection (M := 1) (by simp)))).analyticOnNhd
      hopen
  have heq : (fun w : ℂ ↦ riemannZeta₁ (w + 1)) =ᶠ[𝓝 1]
      fun w : ℂ ↦ 1 - w * stepCorrection 1 w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℂ) ∈ {w : ℂ | 0 < w.re})] with w (hw : 0 < w.re)
    have hw₀ : w ≠ 0 := fun h ↦ by simp [h] at hw
    have hw₁ : w + 1 ≠ 1 := by simpa using hw₀
    have hstep := integral_floor_exp_mul_cexp_neg_mul (a := 1) (M := 1) (by simp) hw
    have hexp : ∫ t in Ici (0 : ℝ), cexp (-w * t) = w⁻¹ := by
      simpa using integral_cexp_mul_I_mul_cexp_neg_mul (u := 0) hw
    simp only [Pi.one_apply, one_mul] at hstep
    rw [hexp, LSeries_one_eq_riemannZeta (by simpa using hw), riemannZeta_eq_inv_sub_mul hw₁,
      add_sub_cancel_right] at hstep
    field_simp [hw₀] at hstep ⊢
    linear_combination -hstep
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR (convex_halfSpace_re_gt (-1)).isPreconnected
    (by norm_num : (1 : ℂ) ∈ {w : ℂ | -1 < w.re}) heq hz

/-- **Step-correction representation of `ζ` on `-1 < re z`.** For `-1 < re z` and `z ≠ 0`,
`ζ(z + 1) = z⁻¹ - stepCorrection 1 z`. -/
theorem riemannZeta_add_one_eq_inv_sub_stepCorrection {z : ℂ} (hz : -1 < z.re) (hz₀ : z ≠ 0) :
    riemannZeta (z + 1) = z⁻¹ - stepCorrection 1 z := by
  have hz₁ : z + 1 ≠ 1 := by simpa using hz₀
  rw [riemannZeta_eq_inv_sub_mul hz₁, add_sub_cancel_right,
    riemannZeta₁_add_one_eq_one_sub_mul_stepCorrection hz]
  field_simp [hz₀]

/-- Adjacent natural numbers have asymptotically equal purely imaginary powers:
`(N + 1) ^ (u i) - N ^ (u i) → 0` as `N → ∞`. -/
private theorem tendsto_natCast_add_one_cpow_sub_cpow_mul_I (u : ℝ) :
    Tendsto (fun N : ℕ ↦ ((N : ℂ) + 1) ^ ((u : ℂ) * I) - (N : ℂ) ^ ((u : ℂ) * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (1 + 1 / (N : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ ↦ 1 + 1 / (N : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
  have hexp : Tendsto (fun N : ℕ ↦
      ‖cexp ((Real.log (1 + 1 / (N : ℝ)) : ℂ) * ((u : ℂ) * I)) - 1‖) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ ↦ ‖cexp ((x : ℂ) * ((u : ℂ) * I)) - 1‖) (𝓝 0) (𝓝 0) := by
      simpa using ((by fun_prop : Continuous fun x : ℝ ↦
        ‖cexp ((x : ℂ) * ((u : ℂ) * I)) - 1‖).tendsto 0)
    exact h0.comp hlog
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hlog_add : Real.log ((N : ℝ) + 1) = Real.log N + Real.log (1 + 1 / (N : ℝ)) := by
    have hmul : (N : ℝ) * (1 + 1 / (N : ℝ)) = N + 1 := by field_simp [hN'.ne']
    rw [← hmul, Real.log_mul hN'.ne' (by positivity)]
  have hpowN : (N : ℂ) ^ ((u : ℂ) * I) = cexp ((Real.log N : ℂ) * ((u : ℂ) * I)) := by
    rw [cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega)), ← Complex.ofReal_natCast,
      ← ofReal_log hN'.le]
  have hpowN1 : ((N : ℂ) + 1) ^ ((u : ℂ) * I) =
      cexp ((Real.log ((N : ℝ) + 1) : ℂ) * ((u : ℂ) * I)) := by
    have hcast : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, cpow_def_of_ne_zero (mod_cast hN1.ne'), ofReal_log hN1.le]
  have hunit : ‖(N : ℂ) ^ ((u : ℂ) * I)‖ = 1 := by
    simpa using norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (by omega)) ((u : ℂ) * I)
  have hfactor : ((N : ℂ) + 1) ^ ((u : ℂ) * I) - (N : ℂ) ^ ((u : ℂ) * I) =
      (N : ℂ) ^ ((u : ℂ) * I) *
        (cexp ((Real.log (1 + 1 / (N : ℝ)) : ℂ) * ((u : ℂ) * I)) - 1) := by
    rw [hpowN1, hpowN, hlog_add, ofReal_add, add_mul, Complex.exp_add]
    ring
  rw [hfactor, norm_mul, hunit, one_mul]

/-- **Euler–Maclaurin boundary asymptotic for `n ^ (u i)`.** For `u ≠ 0`,
`(∑ n ∈ Icc 1 N, n ^ (u i) / n) - N ^ (u i) / (u i)` converges to `ζ(1 - u i)` as `N → ∞`. -/
theorem tendsto_sum_Icc_natCast_cpow_mul_I_div_sub {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun N : ℕ ↦
        (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ ((u : ℂ) * I) / (n : ℂ)) -
          (N : ℂ) ^ ((u : ℂ) * I) / ((u : ℂ) * I))
      atTop (𝓝 (riemannZeta (1 - u * I))) := by
  set z : ℂ := -((u : ℂ) * I)
  have huI : (u : ℂ) * I ≠ 0 := by simp [hu]
  have hz₀ : z ≠ 0 := neg_ne_zero.mpr huI
  -- Step-function Laplace identity at `z = -u i` gives the asymptotic with `N + 1` in place of `N`.
  have hcorr : Tendsto (fun N : ℕ ↦
      z⁻¹ - ∑ n ∈ Finset.range (N + 1), stepCorrectionTerm 1 n z)
      atTop (𝓝 (riemannZeta (1 - u * I))) := by
    have hsum := ((hasSum_stepCorrection (a := 1) (M := 1) (z := z) (by simp)
      (by simp [z])).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hζ : z⁻¹ - stepCorrection 1 z = riemannZeta (1 - u * I) := by
      have := (riemannZeta_add_one_eq_inv_sub_stepCorrection (z := z) (by simp [z]) hz₀).symm
      simpa [z, sub_eq_add_neg, add_comm] using this
    exact hζ ▸ tendsto_const_nhds.sub hsum
  have hsucc : Tendsto (fun N : ℕ ↦
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ ((u : ℂ) * I) / (n : ℂ)) -
        ((N : ℂ) + 1) ^ ((u : ℂ) * I) / ((u : ℂ) * I))
      atTop (𝓝 (riemannZeta (1 - u * I))) := by
    refine hcorr.congr fun N ↦ ?_
    have hstep := intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ 1 N z
    have hint : ∫ t in (0 : ℝ)..Real.log (N + 1), (1 : ℕ → ℂ) ⌊Real.exp t⌋₊ * cexp (-z * t) =
        (((N : ℂ) + 1) ^ ((u : ℂ) * I) - 1) / ((u : ℂ) * I) := by
      have hN1 : (0 : ℝ) < N + 1 := by positivity
      have hpow : cexp (((u : ℂ) * I) * Real.log (N + 1)) = ((N : ℂ) + 1) ^ ((u : ℂ) * I) := by
        have hcast : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast, cpow_def_of_ne_zero (mod_cast hN1.ne'), ofReal_log hN1.le, mul_comm]
      simp [z, integral_exp_mul_complex huI, hpow]
    have hsum_term : ∑ n ∈ Finset.range (N + 1), LSeries.term 1 (z + 1) n =
        ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ ((u : ℂ) * I) / (n : ℂ) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot N.succ_pos, LSeries.term_zero,
        zero_add, Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
      have htw := term_mul_natCast_cpow 1 ((u : ℂ) * I) 1 n
      simp only [Pi.one_apply, one_mul, LSeries.term_of_ne_zero hn0, cpow_one] at htw
      have hz1 : z + 1 = 1 - (u : ℂ) * I := by simp [z, sub_eq_add_neg, add_comm]
      rw [hz1, LSeries.term_of_ne_zero hn0, Pi.one_apply, ← htw]
    rw [hint, Finset.sum_add_distrib, hsum_term, sub_div, one_div] at hstep
    have hinv : z⁻¹ = -((u : ℂ) * I)⁻¹ := by simp [z]
    rw [hinv]
    linear_combination hstep
  have hdiff := (tendsto_natCast_add_one_cpow_sub_cpow_mul_I u).div_const ((u : ℂ) * I)
  rw [zero_div] at hdiff
  simpa [sub_div] using hsucc.add hdiff

/-- Purely imaginary powers `N ^ (u i)` (`u ≠ 0`) do not converge as `N → ∞`: any limit `L` would
have unit norm, satisfy `(m * N) ^ (u i) = m ^ (u i) * N ^ (u i)` to force `m ^ (u i) = 1` for
every `m ≥ 1`, and turn `tendsto_sum_Icc_natCast_cpow_mul_I_div_sub` into convergence of the
harmonic series. -/
theorem not_tendsto_natCast_cpow_mul_I_atTop {u : ℝ} (hu : u ≠ 0) (L : ℂ) :
    ¬ Tendsto (fun N : ℕ ↦ (N : ℂ) ^ ((u : ℂ) * I)) atTop (𝓝 L) := by
  intro hL
  have hnorm : Tendsto (fun N : ℕ ↦ ‖(N : ℂ) ^ ((u : ℂ) * I)‖) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [norm_natCast_cpow_of_pos hN]
    simp
  have hL0 : L ≠ 0 := by
    intro rfl
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hnorm (by simpa using hL.norm)
    norm_num at this
  have hone : ∀ m : ℕ, 1 ≤ m → (m : ℂ) ^ ((u : ℂ) * I) = 1 := by
    intro m hm
    have hsub : Tendsto (fun N : ℕ ↦ ((m * N : ℕ) : ℂ) ^ ((u : ℂ) * I)) atTop (𝓝 L) :=
      hL.comp (tendsto_id.const_mul_atTop' hm)
    have hmul : Tendsto (fun N : ℕ ↦ ((m * N : ℕ) : ℂ) ^ ((u : ℂ) * I)) atTop
        (𝓝 ((m : ℂ) ^ ((u : ℂ) * I) * L)) := by
      refine (hL.const_mul ((m : ℂ) ^ ((u : ℂ) * I))).congr fun N ↦ ?_
      have hcast : ((m * N : ℕ) : ℂ) = ((m : ℝ) : ℂ) * ((N : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, mul_cpow_ofReal_nonneg m.cast_nonneg N.cast_nonneg]
      push_cast
      rfl
    exact mul_right_cancel₀ hL0 ((tendsto_nhds_unique hmul hsub).trans (one_mul L).symm)
  -- With `n ^ (u i) = 1` for all `n ≥ 1`, the Euler–Maclaurin limit makes `∑ 1 / n` converge.
  have hharm_c : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (1 : ℂ) / n) atTop
      (𝓝 (riemannZeta (1 - u * I) + 1 / ((u : ℂ) * I))) := by
    refine ((tendsto_sum_Icc_natCast_cpow_mul_I_div_sub hu).add_const
      (1 / ((u : ℂ) * I))).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsum_eq : (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ ((u : ℂ) * I) / (n : ℂ)) =
        ∑ n ∈ Finset.Icc 1 N, (1 : ℂ) / n :=
      Finset.sum_congr rfl fun n hn ↦ by rw [hone n (Finset.mem_Icc.mp hn).1]
    rw [hsum_eq, hone N hN, sub_add_cancel]
  have hreal : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (riemannZeta (1 - u * I) + 1 / ((u : ℂ) * I)).re) := by
    refine ((Complex.continuous_re.tendsto _).comp hharm_c).congr fun N ↦ ?_
    have hre (n : ℕ) : ((1 : ℂ) / (n : ℂ)).re = 1 / (n : ℝ) := by
      rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.one_re]
    simp only [Function.comp_apply, Complex.re_sum, hre]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_sum_range_one_div_nat_succ_atTop _ hreal

/-- **Ordered boundary sums of `n ^ (u i)` diverge (`u ≠ 0`).** Even though the coefficients have
unit norm, their Dirichlet series extends holomorphically to `{1 + u i}ᶜ` (in particular across
`s = 1`), is nonzero at `s = 1`, and has radial Abel limit `ζ(1 - u i)` at `s = 1`, the ordered
partial sums `∑ n ∈ Icc 1 N, n ^ (u i) / n` have no limit as `N → ∞`. -/
theorem not_tendsto_sum_Icc_natCast_cpow_mul_I_div_atTop {u : ℝ} (hu : u ≠ 0) (L : ℂ) :
    ¬ Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ ((u : ℂ) * I) / (n : ℂ))
      atTop (𝓝 L) := by
  intro hL
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ ((u : ℂ) * I)) atTop
      (𝓝 ((L - riemannZeta (1 - u * I)) * ((u : ℂ) * I))) := by
    have huI : (u : ℂ) * I ≠ 0 := by simp [hu]
    have h := (hL.sub (tendsto_sum_Icc_natCast_cpow_mul_I_div_sub hu)).mul_const ((u : ℂ) * I)
    exact h.congr fun N ↦ by rw [sub_sub_cancel, div_mul_cancel₀ _ huI]
  exact not_tendsto_natCast_cpow_mul_I_atTop hu _ hpow

/-- For every real `u`, no function summing the Dirichlet series of `n ^ (u i)` on `1 < re s` can
be holomorphic on an open neighbourhood of the entire closed half-plane `1 ≤ re s`. -/
theorem not_differentiableOn_of_LSeriesHasSum_natCast_cpow_mul_I (u : ℝ) {Ω : Set ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hcover : {s : ℂ | 1 ≤ s.re} ⊆ Ω)
    (hseries : ∀ s : ℂ, 1 < s.re →
      LSeriesHasSum (fun n : ℕ ↦ (n : ℂ) ^ ((u : ℂ) * I)) s (F s)) :
    ¬ DifferentiableOn ℂ F Ω := by
  rcases eq_or_ne u 0 with rfl | hu
  · refine not_differentiableOn_of_LSeriesHasSum_one hΩ hcover fun s hs ↦ ?_
    exact (LSeriesHasSum_congr s (F s) fun {_} _ ↦ by simp).mp (hseries s hs)
  · intro hF
    have hbound : ∀ n : ℕ, 1 ≤ n → ‖(n : ℂ) ^ ((u : ℂ) * I)‖ ≤ 1 := fun n hn ↦ by
      rw [norm_natCast_cpow_of_pos hn]
      simp
    exact not_tendsto_sum_Icc_natCast_cpow_mul_I_div_atTop hu (F 1)
      (boundedDirichlet_tendsto_ordered_at_one hbound hΩ hcover hF hseries)

/-! ### Imaginary-shifted Euler-logarithm coefficients on `re s = 1` -/

/-- The regularized zeta factor `riemannZeta₁` has no zero anywhere on the closed half-plane
`1 ≤ re s`: at `s = 1` it equals `1`, and elsewhere `ζ(s) = (s - 1)⁻¹ riemannZeta₁ s` is
nonzero by `riemannZeta_ne_zero_of_one_le_re`. -/
private theorem riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp
  · intro h0
    exact riemannZeta_ne_zero_of_one_le_re hs
      (by rw [riemannZeta_eq_inv_sub_mul hs₁, h0, mul_zero])

/-- The prime-power logarithm coefficients `-(Λ n / log n) n ^ (u i)` are bounded by `1` at every
index. -/
theorem norm_neg_vonMangoldt_div_log_mul_cpow_mul_I_le_one (u : ℝ) (n : ℕ) :
    ‖-(Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)‖ ≤ 1 := by
  rcases le_or_gt n 1 with hn | hn
  · interval_cases n <;> simp
  have hlog : 0 < Real.log n := Real.log_pos (mod_cast hn)
  have hunit : ‖(n : ℂ) ^ ((u : ℂ) * I)‖ = 1 := by
    rw [norm_natCast_cpow_of_pos (by omega)]
    simp
  rw [norm_mul, norm_neg, norm_div, norm_real, norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
    Real.norm_of_nonneg hlog.le, hunit, mul_one, div_le_one hlog]
  exact vonMangoldt_le_log

/-- For `1 < re s`, the exponential of the `L`-series of `-(Λ n / log n) n ^ (u i)` is the
reciprocal `(ζ(s - u i))⁻¹` of the vertically shifted Riemann zeta function. -/
theorem exp_LSeries_neg_vonMangoldt_div_log_mul_cpow_mul_I (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    cexp (LSeries (fun n : ℕ ↦ -(Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) s) =
      (riemannZeta (s - u * I))⁻¹ := by
  have hs' : 1 < (s - (u : ℂ) * I).re := by simpa using hs
  have htw : LSeries (fun n : ℕ ↦ -(Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) s =
      -LSeries (fun n : ℕ ↦ (Λ n / Real.log n : ℂ)) (s - u * I) := by
    rw [LSeries_mul_natCast_cpow (fun n : ℕ ↦ -(Λ n / Real.log n : ℂ)), ← LSeries_neg]
    rfl
  rw [htw, Complex.exp_neg, riemannZeta_eq_exp_LSeries hs']

/-- **Holomorphic continuation of `(ζ(s - u i))⁻¹` across `1 ≤ re s`.** The regularized function
`(w - 1 - u i) (riemannZeta₁ (w - u i))⁻¹` is complex-differentiable at every point of the closed
half-plane `1 ≤ re s`. -/
theorem differentiableAt_sub_mul_riemannZeta₁_inv (u : ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (fun w : ℂ ↦ (w - 1 - u * I) * (riemannZeta₁ (w - u * I))⁻¹) s :=
  (by fun_prop : DifferentiableAt ℂ (fun w : ℂ ↦ w - 1 - u * I) s).mul
    ((differentiable_riemannZeta₁.comp (by fun_prop)).differentiableAt.inv
      (riemannZeta₁_ne_zero_of_one_le_re (by simpa using hs)))

/-- On the closed half-plane `1 ≤ re s`, the regularized continuation
`(s - 1 - u i) (riemannZeta₁ (s - u i))⁻¹` of `(ζ(s - u i))⁻¹` vanishes at and only at
`s = 1 + u i`; in particular, it is nonzero at `s = 1` whenever `u ≠ 0`. -/
theorem sub_mul_riemannZeta₁_inv_eq_zero_iff {u : ℝ} {s : ℂ} (hs : 1 ≤ s.re) :
    (s - 1 - u * I) * (riemannZeta₁ (s - u * I))⁻¹ = 0 ↔ s = 1 + u * I := by
  rw [mul_eq_zero, or_iff_left (inv_ne_zero
    (riemannZeta₁_ne_zero_of_one_le_re (by simpa using hs)))]
  exact ⟨fun h ↦ by linear_combination h, fun h ↦ by linear_combination h⟩

/-- **Pointwise nonvanishing at `s = 1` does not continue an Euler logarithm across `re s = 1`.**
For every real `u` (in particular for `u ≠ 0`, where the exponential continuation across
`1 ≤ re s` is nonzero at `s = 1`), no function summing the Euler-logarithm series of
`-(Λ n / log n) n ^ (u i)` on `1 < re s` can even be continuous on the closed half-plane
`1 ≤ re s`. -/
theorem not_continuousOn_of_LSeriesHasSum_neg_vonMangoldt_div_log_mul_cpow_mul_I (u : ℝ)
    {F : ℂ → ℂ}
    (hseries : ∀ s : ℂ, 1 < s.re →
      LSeriesHasSum (fun n : ℕ ↦ -(Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) s (F s)) :
    ¬ ContinuousOn F {s : ℂ | 1 ≤ s.re} := by
  intro hF
  set a : ℕ → ℂ := fun n ↦ -(Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)
  set g : ℂ → ℂ := fun s ↦ (s - 1 - u * I) * (riemannZeta₁ (s - u * I))⁻¹
  set V : Set ℂ := {s : ℂ | riemannZeta₁ (s - u * I) ≠ 0}
  have hVo : IsOpen V :=
    isOpen_compl_singleton.preimage (differentiable_riemannZeta₁.continuous.comp (by fun_prop))
  have hcover : {s : ℂ | 1 ≤ s.re} ⊆ V :=
    fun s hs ↦ riemannZeta₁_ne_zero_of_one_le_re (by simpa using hs)
  have hgd : DifferentiableOn ℂ g V :=
    DifferentiableOn.mul (by fun_prop)
      ((differentiable_riemannZeta₁.comp (by fun_prop)).differentiableOn.inv fun _ hs ↦ hs)
  have hf : DifferentiableOn ℂ (LSeries a) {s : ℂ | 1 < s.re} :=
    (LSeries_differentiableOn a).mono fun s (hs : 1 < s.re) ↦
      (LSeries.abscissaOfAbsConv_le_of_le_const
        ⟨1, fun n _ ↦ norm_neg_vonMangoldt_div_log_mul_cpow_mul_I_le_one u n⟩).trans_lt
        (mod_cast hs)
  have hfg : EqOn (cexp ∘ LSeries a) g {s : ℂ | 1 < s.re} := by
    intro s (hs : 1 < s.re)
    have hne : s - (u : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    calc cexp (LSeries a s) = (riemannZeta (s - u * I))⁻¹ :=
          exp_LSeries_neg_vonMangoldt_div_log_mul_cpow_mul_I u hs
      _ = g s := by
          rw [inv_riemannZeta_eq_sub_mul_of_ne_one hne]
          simp only [g]
          ring
  have hzero : g (1 + u * I) = 0 := (sub_mul_riemannZeta₁_inv_eq_zero_iff (by simp)).mpr rfl
  have hne := (TauCeti.exists_continuousOn_eqOn_le_re_iff hVo hcover hgd hf hfg).mp
    ⟨F, hF, fun s hs ↦ (hseries s hs).LSeries_eq.symm⟩ (1 + u * I) (by simp)
  exact hne hzero

/-- No function summing the Euler-logarithm series of `-(Λ n / log n) n ^ (u i)` on `1 < re s` can
be holomorphic on an open set covering the closed half-plane `1 ≤ re s`. -/
theorem not_differentiableOn_of_LSeriesHasSum_neg_vonMangoldt_div_log_mul_cpow_mul_I (u : ℝ)
    {Ω : Set ℂ} {F : ℂ → ℂ} (hcover : {s : ℂ | 1 ≤ s.re} ⊆ Ω)
    (hseries : ∀ s : ℂ, 1 < s.re →
      LSeriesHasSum (fun n : ℕ ↦ -(Λ n / Real.log n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) s (F s)) :
    ¬ DifferentiableOn ℂ F Ω :=
  fun hF ↦ not_continuousOn_of_LSeriesHasSum_neg_vonMangoldt_div_log_mul_cpow_mul_I u hseries
    (hF.continuousOn.mono hcover)

end TauCeti.LSeries
