/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Complex.PowerSeries.BranchCut
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.ODE.Complex.SecondOrder
import TauCeti.Analysis.ODE.SecondOrder.Operator
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Euler–Frobenius operator identities at a regular singularity

This file records power-series and pointwise identities for the second-order differential operator
`w'' + f(z) w' + g(z) w` applied to Frobenius branch-cut power series
`(z - z₀)^σ ∑ cₛ (z - z₀)ˢ` near a regular singularity `z₀` where
`(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ`:
* `TauCeti.hasSum_eulerOperator_ofScalars` and
  `TauCeti.hasSum_eulerOperator_ofScalars_of_norm_sub_lt`: in terms of the Euler operator `ζ d/dζ`,
  `(z - z₀)^{2 - σ}` times `w'' + f w' + g w` expands as the power series with `s`-th coefficient
  `Q(σ + s) cₛ + ∑_{k < s} ((σ + k) f_{s - k} + g_{s - k}) cₖ`, where
  `Q(α) = TauCeti.indicialPoly (fs 0) (gs 0) α`.
* `TauCeti.deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum`: pointwise operator identity on the
  slit punctured disc `{z | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}`.
* `TauCeti.hasSum_regularSingularLogCoeff_ofScalars` and
  `TauCeti.hasSum_regularSingularLogForcing_ofScalars`: series expansions for the unshifted and
  `N`-shifted logarithmic forcing operators.
* `TauCeti.deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum_add_log`: shared holomorphy, series
  convergence, and pointwise operator identity for the logarithmic second-solution ansatz
  `(z - z₀)^{α₂} ∑ b_s (z - z₀)^s + c ((z - z₀)^{α₂ + N} ∑ a_s (z - z₀)^s) log(z - z₀)`.

## References

* NIST Digital Library of Mathematical Functions, §2.7(i), equations (2.7.2)–(2.7.5),
  <https://dlmf.nist.gov/2.7.i>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, 1955, Ch. 4, §§3–4.
-/

public section

open Complex Filter Finset FormalMultilinearSeries Topology
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Euler–Frobenius operator identities -/

/-- Coefficient expansion for the Euler–Frobenius operator applied to `S(ζ) = ∑ c_s ζ^s`:
inside the radii of convergence of `S`, `fs`, and `gs`,
`σ (σ - 1) S(ζ) + 2 σ ζ S'(ζ) + ζ² S''(ζ) + F (σ S(ζ) + ζ S'(ζ)) + G S(ζ)`
is the sum of the series with `s`-th coefficient
`indicialPoly (fs 0) (gs 0) (σ + s) * c_s + ∑_{k < s} ((σ + k) fs_{s - k} + gs_{s - k}) c_k`. -/
theorem hasSum_eulerOperator_ofScalars {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {σ ζ F G : 𝕜} {fs gs c : ℕ → 𝕜} {S : 𝕜 → 𝕜} {R : ℝ≥0∞}
    (hS : HasFPowerSeriesOnBall S (ofScalars 𝕜 c) 0 R) (hζ : ‖ζ‖ₑ < R)
    (hζf : ‖ζ‖ₑ < (ofScalars 𝕜 fs).radius) (hζg : ‖ζ‖ₑ < (ofScalars 𝕜 gs).radius)
    (hF : HasSum (fun s ↦ fs s * ζ ^ s) F) (hG : HasSum (fun s ↦ gs s * ζ ^ s) G) :
    HasSum (fun s : ℕ ↦ (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
        ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * ζ ^ s)
      (σ * (σ - 1) * S ζ + 2 * σ * (ζ * deriv S ζ) + ζ ^ 2 * deriv (deriv S) ζ +
        F * (σ * S ζ + ζ * deriv S ζ) + G * S ζ) := by
  -- the series of `S`, of `ζ S'` and of `ζ² S''`
  have h0 := hS.hasSum_ofScalars hζ
  have h1 := hS.hasSum_mul_deriv_ofScalars hζ
  have h2 := hS.hasSum_sq_mul_deriv_deriv_ofScalars hζ
  -- absolute convergence of the factors of the two Cauchy products
  have hA := summable_norm_mul_pow_of_lt_radius c (hζ.trans_le hS.r_le)
  have hP : Summable fun n : ℕ ↦ ‖(σ + n) * c n * ζ ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      ((hA.mul_left ‖σ‖).add (summable_norm_natCast_mul_ofScalars c (hζ.trans_le hS.r_le)))
    rw [add_mul, add_mul]
    refine (norm_add_le _ _).trans_eq ?_
    rw [mul_assoc σ, norm_mul]
  have hfN := summable_norm_mul_pow_of_lt_radius fs hζf
  have hgN := summable_norm_mul_pow_of_lt_radius gs hζg
  have hPsum : HasSum (fun n : ℕ ↦ (σ + n) * c n * ζ ^ n) (σ * S ζ + ζ * deriv S ζ) := by
    convert (h0.mul_left σ).add h1 using 1
    ext n
    ring
  have hC1 := hasSum_sum_range_mul_of_summable_norm hP hfN
  have hC2 := hasSum_sum_range_mul_of_summable_norm hA hgN
  rw [hPsum.tsum_eq, hF.tsum_eq] at hC1
  rw [h0.tsum_eq, hG.tsum_eq] at hC2
  -- combine the Euler-operator terms and Cauchy products into the shifted coefficient sum
  have htotal := ((((h0.mul_left (σ * (σ - 1))).add (h1.mul_left (2 * σ))).add h2).add hC1).add hC2
  rw [mul_comm (σ * S ζ + ζ * deriv S ζ) F, mul_comm (S ζ) G] at htotal
  refine htotal.congr_fun fun s ↦ ?_
  rw [sum_range_succ_mul_pow (fun k ↦ (σ + k) * c k) fs ζ s, sum_range_succ_mul_pow c gs ζ s]
  have hsum : ((∑ k ∈ range s, (σ + k) * c k * fs (s - k)) +
      ∑ k ∈ range s, c k * gs (s - k)) * ζ ^ s =
      (∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * ζ ^ s := by
    rw [← sum_add_distrib]
    exact congrArg (· * ζ ^ s) (sum_congr rfl fun _ _ ↦ by ring)
  simp only [indicialPoly_def]
  linear_combination -hsum

/-- Power-series identity for the Euler–Frobenius operator applied to `A(u) = ∑' s, c s * u ^ s`
on `‖u‖ < r`. -/
theorem hasSum_eulerOperator_ofScalars_of_norm_sub_lt {z₀ σ : ℂ} {r : ℝ} {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s ↦ fs s * (z - z₀) ^ s)
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s ↦ gs s * (z - z₀) ^ s)
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ c s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    HasSum (fun s : ℕ ↦ (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
        ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s)
      ((u ^ 2 * deriv (deriv fun w ↦ ∑' s, c s * w ^ s) u +
          2 * σ * (u * deriv (fun w ↦ ∑' s, c s * w ^ s) u) +
          σ * (σ - 1) * ∑' s, c s * u ^ s) +
        (u * deriv (fun w ↦ ∑' s, c s * w ^ s) u + σ * ∑' s, c s * u ^ s) *
          (∑' s, fs s * u ^ s) +
        (∑' s, c s * u ^ s) * (∑' s, gs s * u ^ s)) := by
  have hr : 0 < r := (norm_nonneg u).trans_lt hu
  have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
  have hpA := hasFPowerSeriesOnBall_tsum_mul_pow c (ENNReal.ofReal_pos.mpr hr)
    (le_radius_ofScalars_of_summable_sub c fun z _ hzr ↦ hc z hzr)
  have hfr := le_radius_ofScalars_of_summable_sub fs hf
  have hgr := le_radius_ofScalars_of_summable_sub gs hg
  have hf_sum := (summable_norm_mul_pow_of_lt_radius fs (hue.trans_le hfr)).of_norm
  have hg_sum := (summable_norm_mul_pow_of_lt_radius gs (hue.trans_le hgr)).of_norm
  have heul := hasSum_eulerOperator_ofScalars (σ := σ) hpA hue (hue.trans_le hfr) (hue.trans_le hgr)
    hf_sum.hasSum hg_sum.hasSum
  convert heul using 1
  ring

/-- Operator evaluation for `ψ(z) = (z - z₀)^σ ∑' s, c s * (z - z₀)^s` on the slit punctured
disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`:
`ψ''(z) + f(z) ψ'(z) + g(z) ψ(z)` equals `(z - z₀)^(σ - 2)` times the indicial-operator
power series. -/
theorem deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum {z₀ σ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ c s * (z - z₀) ^ s)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    deriv (deriv fun w ↦ (w - z₀) ^ σ * ∑' s, c s * (w - z₀) ^ s) z +
        f z * deriv (fun w ↦ (w - z₀) ^ σ * ∑' s, c s * (w - z₀) ^ s) z +
        g z * ((z - z₀) ^ σ * ∑' s, c s * (z - z₀) ^ s) =
      (z - z₀) ^ (σ - 2) * ∑' s : ℕ,
        (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
          ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * (z - z₀) ^ s := by
  set ψ : ℂ → ℂ := fun w ↦ (w - z₀) ^ σ * ∑' s, c s * (w - z₀) ^ s
  set A : ℂ → ℂ := fun u ↦ ∑' s, c s * u ^ s
  set u : ℂ := z - z₀
  have hr : 0 < r := (norm_nonneg u).trans_lt hzb
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hzs
  have han := (hasFPowerSeriesOnBall_tsum_mul_pow c (ENNReal.ofReal_pos.mpr hr)
    (le_radius_ofScalars_of_summable_sub c fun w _ hwr ↦ hc w hwr)).analyticOnNhd
  have hu_mem : u ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal r) := by
    simpa [Metric.mem_eball, edist_zero_right] using eNorm_lt_ofReal_iff.mpr hzb
  have hsub : HasDerivAt (fun w : ℂ ↦ w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hinner :=
    (((han u hu_mem).differentiableAt.hasDerivAt.comp_sub_const z z₀).const_mul σ).add
      (hsub.mul ((han.deriv u hu_mem).differentiableAt.hasDerivAt.comp_sub_const z z₀))
  have hev : deriv ψ =ᶠ[𝓝 z] ((fun w : ℂ ↦ (w - z₀) ^ (σ - 1)) *
      ((fun w : ℂ ↦ σ * A (w - z₀)) + (fun w : ℂ ↦ w - z₀) * fun w : ℂ ↦ deriv A (w - z₀))) := by
    filter_upwards [(isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r).mem_nhds ⟨hzs, hzb⟩]
      with w hw
    exact (hasDerivAt_cpow_mul_tsum hc hw.1 hw.2).deriv
  have hσ_sub : σ - 1 - 1 = σ - 2 := by ring
  have hcpow1 : u ^ (σ - 1) = u ^ (σ - 2) * u := by
    simpa [hσ_sub, Nat.cast_one, pow_one] using cpow_eq_cpow_sub_natCast_mul_pow hu0 (σ - 1) 1
  have hcpow2 : u ^ σ = u ^ (σ - 2) * u ^ 2 := by
    simpa using cpow_eq_cpow_sub_natCast_mul_pow hu0 σ 2
  have hderiv2 : deriv (deriv ψ) z =
      u ^ (σ - 2) * (u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) := by
    rw [(((hsub.cpow_const (c := σ - 1) hzs).mul hinner).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.add_apply, Pi.mul_apply]; dsimp only [u] at hcpow1 ⊢
    rw [hσ_sub, hcpow1]; ring
  rw [(hasSum_eulerOperator_ofScalars_of_norm_sub_lt (σ := σ)
        (fun w hw0 hwr ↦ (hf w hw0 hwr).summable)
        (fun w hw0 hwr ↦ (hg w hw0 hwr).summable) hc hzb).tsum_eq,
    (hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq, (hg z (norm_pos_iff.mpr hu0) hzb).tsum_eq, hderiv2,
    (hasDerivAt_cpow_mul_tsum hc hzs hzb).deriv]
  dsimp only [ψ, A, u]; rw [hcpow1, hcpow2]; ring

/-! ### Logarithmic forcing series identities -/

/-- Coefficient expansion for the logarithmic forcing operator
`2 α S(ζ) + 2 ζ S'(ζ) - S(ζ) + F S(ζ)` applied to `S(ζ) = ∑ a_s ζ^s`: inside the radii of
convergence of `S` and `fs`, it is the sum of the series with `n`-th coefficient
`(2 (α + n) - 1) a_n + ∑_{k ≤ n} fs_{n - k} a_k`. -/
theorem hasSum_regularSingularLogCoeff_ofScalars {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] {α ζ F : 𝕜} {fs a : ℕ → 𝕜} {S : 𝕜 → 𝕜} {R : ℝ≥0∞}
    (hS : HasFPowerSeriesOnBall S (ofScalars 𝕜 a) 0 R) (hζ : ‖ζ‖ₑ < R)
    (hζf : ‖ζ‖ₑ < (ofScalars 𝕜 fs).radius) (hF : HasSum (fun s ↦ fs s * ζ ^ s) F) :
    HasSum (fun n ↦ ((2 * (α + n) - 1) * a n + ∑ k ∈ range (n + 1), fs (n - k) * a k) * ζ ^ n)
      (2 * α * S ζ + 2 * (ζ * deriv S ζ) - S ζ + F * S ζ) := by
  have h0 := hS.hasSum_ofScalars hζ
  have h1 := hS.hasSum_mul_deriv_ofScalars hζ
  have hC := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_mul_pow_of_lt_radius a (hζ.trans_le hS.r_le))
    (summable_norm_mul_pow_of_lt_radius fs hζf)
  rw [h0.tsum_eq, hF.tsum_eq, mul_comm] at hC
  convert (((h0.mul_left (2 * α)).add (h1.mul_left 2)).sub h0).add hC using 1
  ext n
  rw [sum_range_succ_mul_pow a fs ζ n, sum_range_succ, Nat.sub_self,
    sum_congr rfl fun k _ ↦ mul_comm (a k) (fs (n - k))]
  ring

/-- Shifted logarithmic forcing series identity: for `S(ζ) = ∑ a_s ζ^s`, the shifted series with
`s`-th term `(c * regularSingularLogForcing fs a α₂ N s) * ζ ^ s` sums to
`c * ζ ^ N * (2 * (α₂ + N) * S ζ + 2 * (ζ * deriv S ζ) - S ζ + F * S ζ)`. -/
theorem hasSum_regularSingularLogForcing_ofScalars {α₂ c ζ F : ℂ} {N : ℕ}
    {fs a : ℕ → ℂ} {S : ℂ → ℂ} {R : ℝ≥0∞}
    (hS : HasFPowerSeriesOnBall S (ofScalars ℂ a) 0 R) (hζ : ‖ζ‖ₑ < R)
    (hζf : ‖ζ‖ₑ < (ofScalars ℂ fs).radius) (hF : HasSum (fun s ↦ fs s * ζ ^ s) F) :
    HasSum (fun s ↦ (c * regularSingularLogForcing fs a α₂ N s) * ζ ^ s)
      (c * ζ ^ N * (2 * (α₂ + N) * S ζ + 2 * (ζ * deriv S ζ) - S ζ + F * S ζ)) := by
  have hD := hasSum_regularSingularLogCoeff_ofScalars (α := α₂ + N) hS hζ hζf hF
  refine (hasSum_nat_add_iff' N).mp ?_
  rw [sum_eq_zero fun i hi ↦ by simp [regularSingularLogForcing_of_lt _ _ _ (mem_range.mp hi)],
    sub_zero]
  convert hD.mul_left (c * ζ ^ N) using 1
  ext n
  rw [regularSingularLogForcing_of_le _ _ _ (Nat.le_add_left N n), Nat.add_sub_cancel,
    sum_range_succ, Nat.sub_self, pow_add]
  push_cast
  ring

/-- Shared holomorphy, coefficient-series convergence, and pointwise operator formula for any
logarithmic second-solution ansatz
`w₂(z) = (z - z₀)^α₂ ∑ b_s (z - z₀)^s + c ((z - z₀)^{α₂ + N} ∑ a_s (z - z₀)^s) log(z - z₀)`
when `w₁(z) = (z - z₀)^{α₂ + N} ∑ a_s (z - z₀)^s` solves `w₁'' + f w₁' + g w₁ = 0` on the slit
punctured disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum_add_log {z₀ α₂ c : ℂ} {N : ℕ} {r : ℝ}
    {f g : ℂ → ℂ} {fs gs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (ha_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ a s * (z - z₀) ^ s)
    (hb_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ b s * (z - z₀) ^ s)
    (hw₁_op : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv fun w ↦ (w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s) z +
        f z * deriv (fun w ↦ (w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s) z +
        g z * ((z - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (z - z₀) ^ s) = 0) :
    DifferentiableOn ℂ (fun w ↦ (w - z₀) ^ α₂ * (∑' s, b s * (w - z₀) ^ s) +
        c * ((w - z₀) ^ (α₂ + (N : ℂ)) * (∑' s, a s * (w - z₀) ^ s) * log (w - z₀)))
      {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
    (∀ u : ℂ, ‖u‖ < r →
      Summable fun s : ℕ ↦ ((indicialPoly (fs 0) (gs 0) (α₂ + s) * b s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) +
        c * regularSingularLogForcing fs a α₂ N s) * u ^ s) ∧
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv fun w ↦ (w - z₀) ^ α₂ * (∑' s, b s * (w - z₀) ^ s) +
          c * ((w - z₀) ^ (α₂ + (N : ℂ)) * (∑' s, a s * (w - z₀) ^ s) * log (w - z₀))) z +
        f z * deriv (fun w ↦ (w - z₀) ^ α₂ * (∑' s, b s * (w - z₀) ^ s) +
          c * ((w - z₀) ^ (α₂ + (N : ℂ)) * (∑' s, a s * (w - z₀) ^ s) * log (w - z₀))) z +
        g z * ((z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) +
          c * ((z - z₀) ^ (α₂ + (N : ℂ)) * (∑' s, a s * (z - z₀) ^ s) * log (z - z₀))) =
      (z - z₀) ^ (α₂ - 2) * ∑' s : ℕ,
        ((indicialPoly (fs 0) (gs 0) (α₂ + s) * b s +
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) +
          c * regularSingularLogForcing fs a α₂ N s) * (z - z₀) ^ s := by
  set U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
  set w₁ : ℂ → ℂ := fun w ↦ (w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s
  set ψ : ℂ → ℂ := fun w ↦ (w - z₀) ^ α₂ * ∑' s, b s * (w - z₀) ^ s
  set Φ : ℂ → ℂ := fun w ↦ w₁ w * log (w - z₀)
  have hopen : IsOpen U := isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  have hw₁_diff : DifferentiableOn ℂ w₁ U := fun w hw ↦
    (hasDerivAt_cpow_mul_tsum ha_sum hw.1 hw.2).differentiableAt.differentiableWithinAt
  have hψ_diff : DifferentiableOn ℂ ψ U := fun w hw ↦
    (hasDerivAt_cpow_mul_tsum hb_sum hw.1 hw.2).differentiableAt.differentiableWithinAt
  obtain ⟨hΦ_diff, hΦ_op⟩ :=
    operator_mul_log (z₀ := z₀) hopen (fun _ hz ↦ hz.1) hw₁_diff (fun z hz ↦ hw₁_op z hz.1 hz.2)
  have hfr := le_radius_ofScalars_of_summable_sub fs fun w hw0 hwr ↦ (hf w hw0 hwr).summable
  have har := le_radius_ofScalars_of_summable_sub a fun w _ hwr ↦ ha_sum w hwr
  have hlog_hasSum : ∀ {u F : ℂ} (hu : ‖u‖ < r) (hF : HasSum (fun s ↦ fs s * u ^ s) F),
      HasSum (fun s ↦ (c * regularSingularLogForcing fs a α₂ N s) * u ^ s)
        (c * u ^ N * (2 * (α₂ + N) * (∑' s, a s * u ^ s) +
          2 * (u * deriv (fun w ↦ ∑' s, a s * w ^ s) u) -
          (∑' s, a s * u ^ s) + F * ∑' s, a s * u ^ s)) := fun {u F} hu hF ↦ by
    have hr : 0 < r := (norm_nonneg u).trans_lt hu
    have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
    have hpA := hasFPowerSeriesOnBall_tsum_mul_pow a (ENNReal.ofReal_pos.mpr hr) har
    exact hasSum_regularSingularLogForcing_ofScalars (α₂ := α₂) (c := c) (N := N) hpA hue
      (hue.trans_le hfr) hF
  have hD_hasSum : ∀ {u F : ℂ} (hu : ‖u‖ < r) (hF : HasSum (fun s ↦ fs s * u ^ s) F),
      HasSum (fun s : ℕ ↦ ((indicialPoly (fs 0) (gs 0) (α₂ + s) * b s +
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) +
          c * regularSingularLogForcing fs a α₂ N s) * u ^ s)
        ((∑' s : ℕ, (indicialPoly (fs 0) (gs 0) (α₂ + s) * b s +
            ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) * u ^ s) +
          c * u ^ N * (2 * (α₂ + N) * (∑' s, a s * u ^ s) +
            2 * (u * deriv (fun w ↦ ∑' s, a s * w ^ s) u) -
            (∑' s, a s * u ^ s) + F * ∑' s, a s * u ^ s)) := fun {u F} hu hF ↦ by
    have heul := (hasSum_eulerOperator_ofScalars_of_norm_sub_lt (σ := α₂)
      (fun w hw0 hwr ↦ (hf w hw0 hwr).summable)
      (fun w hw0 hwr ↦ (hg w hw0 hwr).summable) hb_sum hu).summable.hasSum
    refine (heul.add (hlog_hasSum hu hF)).congr_fun fun _ ↦ by ring
  have hw₂_eq : (fun w ↦ (w - z₀) ^ α₂ * (∑' s, b s * (w - z₀) ^ s) +
      c * ((w - z₀) ^ (α₂ + (N : ℂ)) * (∑' s, a s * (w - z₀) ^ s) * log (w - z₀))) =
      fun w ↦ ψ w + c * Φ w := by
    ext w; simp only [ψ, Φ, w₁, mul_assoc]
  refine ⟨by rw [hw₂_eq]; exact hψ_diff.add (hΦ_diff.const_mul c), fun u hu ↦ ?_,
    fun z hzs hzb ↦ ?_⟩
  · have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
    have hf_sum := (summable_norm_mul_pow_of_lt_radius fs (hue.trans_le hfr)).of_norm
    exact (hD_hasSum hu hf_sum.hasSum).summable
  · have hzU : z ∈ U := ⟨hzs, hzb⟩
    have hu0 : z - z₀ ≠ 0 := slitPlane_ne_zero hzs
    have hlin := secondOrder_operator_add_const_mul (f := f) (g := g) (c' := c) (z := z)
      (Eventually.mono (hopen.mem_nhds hzU) fun _ hw ↦ hψ_diff.differentiableAt (hopen.mem_nhds hw))
      (Eventually.mono (hopen.mem_nhds hzU) fun _ hw ↦ hΦ_diff.differentiableAt (hopen.mem_nhds hw))
      ((hψ_diff.deriv hopen).differentiableAt (hopen.mem_nhds hzU))
      ((hΦ_diff.deriv hopen).differentiableAt (hopen.mem_nhds hzU))
    have hdw₁ : deriv w₁ z = (z - z₀) ^ (α₂ + (N : ℂ) - 1) *
        ((α₂ + N) * (∑' s, a s * (z - z₀) ^ s) +
          (z - z₀) * deriv (fun w ↦ ∑' s, a s * w ^ s) (z - z₀)) :=
      (hasDerivAt_cpow_mul_tsum ha_sum hzs hzb).deriv
    have e1 : (z - z₀) ^ (α₂ + (N : ℂ) - 1) = (z - z₀) ^ (α₂ - 2) * (z - z₀) ^ N * (z - z₀) := by
      rw [show α₂ + (N : ℂ) - 1 = α₂ - 2 + (N : ℂ) + 1 by ring, cpow_add _ _ hu0,
        cpow_add _ _ hu0, cpow_natCast, cpow_one]
    have e2 : (z - z₀) ^ (α₂ + (N : ℂ)) = (z - z₀) ^ (α₂ - 2) * (z - z₀) ^ N * (z - z₀) ^ 2 := by
      rw [show α₂ + (N : ℂ) = α₂ - 2 + (N : ℂ) + 2 by ring, cpow_add _ _ hu0,
        cpow_add _ _ hu0, cpow_natCast, show (2 : ℂ) = (2 : ℕ) by norm_num, cpow_natCast]
    rw [hw₂_eq, hlin,
      deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum (σ := α₂) hf hg hb_sum hzs hzb,
      hΦ_op z hzU, (hD_hasSum hzb (hf z (norm_pos_iff.mpr hu0) hzb)).tsum_eq, hdw₁]
    dsimp only [w₁]
    rw [e1, e2]
    field_simp [hu0]
    ring

end TauCeti
