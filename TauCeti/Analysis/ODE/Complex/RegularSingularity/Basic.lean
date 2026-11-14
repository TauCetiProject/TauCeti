/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Analytic.OfScalars

/-!
# Convergent series solutions and Wronskian at a regular singularity

Let `f` and `g` be complex functions around `z₀` such that `(z - z₀) f(z) = ∑ f_s (z - z₀)^s`
and `(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` converge on a punctured disc `0 < ‖z - z₀‖ < r`. On the
slit punctured disc `{z | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}`, using principal complex
powers and the principal logarithm:
* For every root `ρ` of `TauCeti.indicialPoly` such that `Q(ρ + s) ≠ 0` for all `s ≥ 1` (which
  always holds for `ρ = α₁`, and holds for `ρ = α₂` whenever `α₁ - α₂ ∉ ℕ`), any sequence `a`
  satisfying the two-coefficient indicial convolution recursion defines a power series
  `∑ a_s (z - z₀)^s` convergent on the full open disc `‖z - z₀‖ < r`, and
  `w(z) = (z - z₀)^ρ ∑ a_s (z - z₀)^s` is a holomorphic solution of `w'' + f w' + g w = 0` on
  the slit punctured disc (`TauCeti.regularSingular_solution`). With `a₀ = 1`, the canonical
  sequence `TauCeti.regularSingularCoeff` is uniquely determined by the differential equation
  (`TauCeti.eq_regularSingularCoeff_of_solution`).
* When `α₁ - α₂ = N ∈ ℕ`, there is a second holomorphic solution
  `w₂(z) = (z - z₀)^{α₂} ∑ b_s (z - z₀)^s + c w₁(z) log(z - z₀)` with `b_N = 0`, normalized by
  `c = 1` when `N = 0` and by `b₀ = 1` when `N ≥ 1`, where `∑ b_s (z - z₀)^s` converges on the
  whole disc `‖z - z₀‖ < r` (`TauCeti.regularSingular_second_solution`), and both `b` and `c`
  are uniquely determined by the differential equation
  (`TauCeti.eq_regularSingularSecondCoeff_of_solution`).
* In both regimes, the Wronskian `w₁ w₂' - w₁' w₂` satisfies an explicit Abel–Liouville identity
  on the slit punctured disc and never vanishes there (`TauCeti.wronskian_regularSingular_ne_zero`,
  `TauCeti.wronskian_regularSingular_second_ne_zero`), yielding a fundamental pair at every regular
  singularity (`TauCeti.exists_regularSingular_fundamental_pair`).
* For the Euler–Cauchy equation with `f = 0` and `g(z) = -2 z⁻²` at `z₀ = 0`, the indicial roots
  are `2` and `-1` (`N = 3`), the primary solution is `z²`, the logarithmic multiplier `c`
  vanishes, and the second solution is `z⁻¹` (`TauCeti.eulerCauchy_two_neg_one_example`).

## References

* NIST *Digital Library of Mathematical Functions*, §2.7(ii), formulas 2.7.1–2.7.6,
  <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex Filter Finset Metric Set
open scoped Topology ENNReal NNReal

namespace TauCeti

/-! ### Internal analytic and majorant helpers -/

private theorem isOpen_slitBall (z₀ : ℂ) (r : ℝ) :
    IsOpen {z : ℂ | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} :=
  (Complex.isOpen_slitPlane.preimage (continuous_id.sub continuous_const)).inter
    (by simpa only [Metric.ball, dist_eq_norm] using Metric.isOpen_ball (x := z₀) (ε := r))

private theorem enorm_lt_ofReal_iff {u : ℂ} {r : ℝ} :
    ‖u‖ₑ < ENNReal.ofReal r ↔ ‖u‖ < r := by
  rw [← mem_eball_zero_iff, Metric.eball_ofReal, mem_ball_zero_iff]

private theorem hasFPowerSeriesOnBall_of_punctured {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (c : ℕ → ℂ)
    (hc : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s) :
    HasFPowerSeriesOnBall (fun u : ℂ => ∑' s, c s * u ^ s)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 (ENNReal.ofReal r) :=
  FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_of_summable c (ENNReal.ofReal_pos.mpr hr)
    fun u hu0 hur => by
      simpa using hc (z₀ + u) (by simpa using hu0) (by simpa using enorm_lt_ofReal_iff.mp hur)

private theorem analyticOnNhd_tsum_of_summable {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (c : ℕ → ℂ)
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s) :
    AnalyticOnNhd ℂ (fun u : ℂ => ∑' s, c s * u ^ s) (ball 0 r) :=
  Metric.eball_ofReal (x := (0 : ℂ)) (ε := r) ▸
    (hasFPowerSeriesOnBall_of_punctured hr c fun z _ hzr => hc z hzr).analyticOnNhd

private theorem exists_norm_mul_pow_le_of_punctured {z₀ : ℂ} {r ρ : ℝ} (hρ0 : 0 < ρ) (hρr : ρ < r)
    (c : ℕ → ℂ)
    (hc : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℕ, ‖c s‖ * ρ ^ s ≤ M := by
  have hrad : ENNReal.ofReal r ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    FormalMultilinearSeries.le_radius_ofScalars_of_summable c fun u hu0 hur => by
      simpa using hc (z₀ + u) (by simpa using hu0) (by simpa using enorm_lt_ofReal_iff.mp hur)
  let ρ_nn : ℝ≥0 := ⟨ρ, hρ0.le⟩
  have hcoe : (ρ_nn : ℝ) = ρ := rfl
  have hlt : (ρ_nn : ℝ≥0∞) < ENNReal.ofReal r := by
    rw [show (ρ_nn : ℝ≥0∞) = ENNReal.ofReal ρ from (ENNReal.ofReal_eq_coe_nnreal hρ0.le).symm]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans hρ0 hρr)).mpr hρr
  obtain ⟨M, hM, hMb⟩ :=
    (FormalMultilinearSeries.ofScalars ℂ c).norm_mul_pow_le_of_lt_radius (hlt.trans_le hrad)
  exact ⟨M, hM, fun s => by simpa [FormalMultilinearSeries.ofScalars_norm, hcoe] using hMb s⟩

private theorem sum_range_succ_mul_pow (p q : ℕ → ℂ) (u : ℂ) (s : ℕ) :
    (∑ k ∈ range (s + 1), (p k * u ^ k) * (q (s - k) * u ^ (s - k))) =
      ((∑ k ∈ range s, p k * q (s - k)) + p s * q 0) * u ^ s := by
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one]
  conv_rhs => rw [add_mul, Finset.sum_mul]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    have hpow : u ^ k * u ^ (s - k) = u ^ s := by
      rw [← pow_add, Nat.add_sub_of_le (mem_range.mp hk).le]
    calc (p k * u ^ k) * (q (s - k) * u ^ (s - k))
        = p k * q (s - k) * (u ^ k * u ^ (s - k)) := by ring
      _ = p k * q (s - k) * u ^ s := by rw [hpow]
  · ring

/-- Lower bound `s² / 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖` for sufficiently large `s : ℕ`. -/
private theorem exists_sq_div_two_le_norm_indicialPoly (f₀ g₀ σ : ℂ) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖ := by
  set B : ℝ := ‖2 * σ + f₀ - 1‖ + ‖indicialPoly f₀ g₀ σ‖
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B + 1)
  refine ⟨max N 1, le_max_right _ _, fun s hs => ?_⟩
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (le_max_right N 1).trans hs
  have hNs : (N : ℝ) ≤ s := by exact_mod_cast (le_max_left N 1).trans hs
  have hdecomp : (s : ℂ) ^ 2 =
      indicialPoly f₀ g₀ (σ + s) - ((2 * σ + f₀ - 1) * s + indicialPoly f₀ g₀ σ) := by
    rw [indicialPoly_add]; ring
  have htri : (s : ℝ) ^ 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖ +
      ‖(2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ‖ := by
    have h := norm_add_le (indicialPoly f₀ g₀ (σ + s))
      (-((2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ))
    rwa [norm_neg, ← sub_eq_add_neg, ← hdecomp, norm_pow, Complex.norm_natCast] at h
  have hrem : ‖(2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ‖ ≤ B * s := by
    calc ‖(2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ‖
        ≤ ‖2 * σ + f₀ - 1‖ * ‖(s : ℂ)‖ + ‖indicialPoly f₀ g₀ σ‖ * 1 := by
          simpa using norm_add_le ((2 * σ + f₀ - 1) * (s : ℂ)) (indicialPoly f₀ g₀ σ)
      _ ≤ ‖2 * σ + f₀ - 1‖ * s + ‖indicialPoly f₀ g₀ σ‖ * s := by
          rw [Complex.norm_natCast]; gcongr
      _ = B * s := by simp [B, add_mul]
  nlinarith [hs1, hNs, hN, htri, hrem]

/-- Perturbed indicial majorant convergence: if `Q(σ + s) d_s = -∑_{k < s} ((σ + k) f_{s - k} +
g_{s - k}) d_k + E_s` for `s ≥ s₁`, where `‖E_s‖ ρ^s` grows at most linearly in `s` on every
sub-radius `0 < ρ < r`, then `∑ d_s (z - z₀)^s` converges on the entire open disc `‖z - z₀‖ < r`. -/
private theorem summable_of_perturbed_indicial_rec {z₀ σ : ℂ} {r : ℝ}
    {fs gs d E : ℕ → ℂ} {s₁ : ℕ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => gs s * (z - z₀) ^ s)
    (hE : ∀ ρ : ℝ, 0 < ρ → ρ < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, ‖E s‖ * ρ ^ s ≤ C * (s + 1))
    (hd : ∀ s : ℕ, s₁ ≤ s → indicialPoly (fs 0) (gs 0) (σ + s) * d s =
      -(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s) :
    ∀ z, ‖z - z₀‖ < r → Summable fun s => d s * (z - z₀) ^ s := by
  intro z hz
  set ρ : ℝ := (‖z - z₀‖ + r) / 2 with hρ_def
  have hρ_gt : ‖z - z₀‖ < ρ := by linarith [norm_nonneg (z - z₀)]
  have hρ_pos : 0 < ρ := (norm_nonneg (z - z₀)).trans_lt hρ_gt
  have hρ_lt : ρ < r := by linarith
  obtain ⟨Mf, hMf_pos, hMf⟩ := exists_norm_mul_pow_le_of_punctured hρ_pos hρ_lt fs hf
  obtain ⟨Mg, hMg_pos, hMg⟩ := exists_norm_mul_pow_le_of_punctured hρ_pos hρ_lt gs hg
  obtain ⟨CE, hCE0, hCE⟩ := hE ρ hρ_pos hρ_lt
  obtain ⟨s₂, hs₂1, hQ⟩ := exists_sq_div_two_le_norm_indicialPoly (fs 0) (gs 0) σ
  set s₀ : ℕ := max s₁ s₂
  have hs₀1 : 1 ≤ s₀ := hs₂1.trans (le_max_right _ _)
  set C₁ : ℝ := (Mf + Mg) * (‖σ‖ + 1)
  have hC₁0 : 0 ≤ C₁ := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * (C₁ + 2 * CE))
  set μ : ℕ → ℝ := fun s => ‖d s‖ * ρ ^ s
  set S : ℕ → ℝ := fun s => 1 + ∑ k ∈ range s, μ k
  have hμ_nonneg : ∀ s, 0 ≤ μ s := fun _ => by positivity
  have hS_pos : ∀ s, 1 ≤ S s := fun s => by
    dsimp [S]; linarith [sum_nonneg fun k (_ : k ∈ range s) => hμ_nonneg k]
  have hstep : ∀ s : ℕ, s₀ ≤ s → μ s ≤ (K : ℝ) / s * S s := by
    intro s hs
    have hs1 : 1 ≤ s := hs₀1.trans hs
    have hs_pos : (0 : ℝ) < s := by exact_mod_cast hs1
    have hs_ge1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    have hQs := hQ s ((le_max_right _ _).trans hs)
    have hrec := congrArg (fun w => ‖w‖ * ρ ^ s) (hd s ((le_max_left _ _).trans hs))
    simp only [norm_mul, mul_assoc] at hrec
    have hconv : (∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s) ≤
        (C₁ * s) * ∑ k ∈ range s, μ k := by
      rw [mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_lt : k < s := mem_range.mp hk
      have hks : (k : ℝ) ≤ s := by exact_mod_cast hk_lt.le
      have hpow : ρ ^ s = ρ ^ (s - k) * ρ ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hk_lt.le]
      have htri : ‖(σ + k) * fs (s - k) + gs (s - k)‖ ≤
          (‖σ‖ + k) * ‖fs (s - k)‖ + ‖gs (s - k)‖ := by
        have h1 := norm_add_le ((σ + k) * fs (s - k)) (gs (s - k))
        have h2 := norm_add_le σ (k : ℂ)
        rw [norm_mul] at h1; rw [Complex.norm_natCast] at h2
        nlinarith [norm_nonneg (fs (s - k))]
      have hfgk : ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k) ≤ C₁ * s := by
        calc ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k)
            ≤ (‖σ‖ + k) * (‖fs (s - k)‖ * ρ ^ (s - k)) + ‖gs (s - k)‖ * ρ ^ (s - k) := by
              have hm := mul_le_mul_of_nonneg_right htri (pow_nonneg hρ_pos.le (s - k))
              linarith
          _ ≤ (‖σ‖ + s) * Mf + Mg := by
              nlinarith [hMf (s - k), hMg (s - k), norm_nonneg σ, hks]
          _ ≤ (‖σ‖ * s + s) * Mf + (‖σ‖ * s + s) * Mg := by
              have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg σ
              have hσs : ‖σ‖ ≤ ‖σ‖ * s := le_mul_of_one_le_right hσ0 hs_ge1
              nlinarith [hMf_pos, hMg_pos, hs_ge1]
          _ = C₁ * s := by dsimp [C₁]; ring
      rw [norm_mul, hpow]
      calc ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ‖d k‖ * (ρ ^ (s - k) * ρ ^ k)
          = (‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k)) * μ k := by dsimp [μ]; ring
        _ ≤ (C₁ * s) * μ k := mul_le_mul_of_nonneg_right hfgk (hμ_nonneg k)
    have hsum_bound : ‖-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s‖ * ρ ^ s ≤
        ((K : ℝ) / 2 * s) * S s := by
      have h1 := mul_le_mul_of_nonneg_right
        (norm_add_le (-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k)) (E s))
        (pow_nonneg hρ_pos.le s)
      rw [norm_neg, add_mul] at h1
      have h2 : ‖∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s ≤
          ∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
      have hsum_nn : 0 ≤ ∑ k ∈ range s, μ k := sum_nonneg fun k _ => hμ_nonneg k
      have hCE_le : CE * ((s : ℝ) + 1) ≤ (2 * CE) * s := by nlinarith [hCE0, hs_ge1]
      have hK_half : C₁ + 2 * CE ≤ (K : ℝ) / 2 := by linarith [hK]
      calc ‖-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s‖ * ρ ^ s
          ≤ C₁ * s * (∑ k ∈ range s, μ k) + (2 * CE) * s := by
            linarith [h1, h2, hconv, hCE s, hCE_le]
        _ = (C₁ + 2 * CE) * (s * S s) - C₁ * s - 2 * CE * s * ∑ k ∈ range s, μ k := by
            dsimp only [S]; ring
        _ ≤ (C₁ + 2 * CE) * (s * S s) := by
            have hnn1 : 0 ≤ C₁ * s := mul_nonneg hC₁0 hs_pos.le
            have hnn2 : 0 ≤ 2 * CE * s * ∑ k ∈ range s, μ k := by positivity
            linarith
        _ ≤ ((K : ℝ) / 2) * (s * S s) :=
            mul_le_mul_of_nonneg_right hK_half (mul_nonneg hs_pos.le (by linarith [hS_pos s]))
        _ = ((K : ℝ) / 2 * s) * S s := by ring
    have hprod_le : ((s : ℝ) ^ 2 / 2) * μ s ≤ ((K : ℝ) / 2 * s) * S s :=
      (mul_le_mul_of_nonneg_right hQs (hμ_nonneg s)).trans (hrec.trans_le hsum_bound)
    rw [div_mul_eq_mul_div, le_div_iff₀ hs_pos]
    nlinarith [hprod_le, hs_pos]
  have hpoly : ∀ s : ℕ, s₀ ≤ s → S s ≤ S s₀ * (s : ℝ) ^ K := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      have h1 : (1 : ℝ) ≤ (s₀ : ℝ) ^ K := one_le_pow₀ (by exact_mod_cast hs₀1)
      nlinarith [hS_pos s₀, h1]
    | succ s hs ih =>
      have hs_pos : (0 : ℝ) < s := by exact_mod_cast (hs₀1.trans hs)
      have hbern : 1 + (K : ℝ) * (s : ℝ)⁻¹ ≤ (1 + (s : ℝ)⁻¹) ^ K :=
        one_add_mul_le_pow (by linarith [inv_nonneg.mpr hs_pos.le]) K
      have hpow_step : (s : ℝ) ^ K * (1 + (K : ℝ) / s) ≤ ((s + 1 : ℕ) : ℝ) ^ K := by
        calc (s : ℝ) ^ K * (1 + (K : ℝ) / s)
            = (s : ℝ) ^ K * (1 + (K : ℝ) * (s : ℝ)⁻¹) := by rw [div_eq_mul_inv]
          _ ≤ (s : ℝ) ^ K * (1 + (s : ℝ)⁻¹) ^ K :=
              mul_le_mul_of_nonneg_left hbern (pow_nonneg hs_pos.le K)
          _ = ((s : ℝ) * (1 + (s : ℝ)⁻¹)) ^ K := (mul_pow _ _ _).symm
          _ = ((s + 1 : ℕ) : ℝ) ^ K := by
              push_cast; rw [mul_add, mul_one, mul_inv_cancel₀ hs_pos.ne']
      have hSs : S (s + 1) = S s + μ s := by simp [S, sum_range_succ, add_assoc]
      calc S (s + 1) ≤ S s * (1 + (K : ℝ) / s) := by linarith [hSs, hstep s hs]
        _ ≤ (S s₀ * (s : ℝ) ^ K) * (1 + (K : ℝ) / s) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = S s₀ * ((s : ℝ) ^ K * (1 + (K : ℝ) / s)) := by ring
        _ ≤ S s₀ * ((s + 1 : ℕ) : ℝ) ^ K :=
            mul_le_mul_of_nonneg_left hpow_step (by linarith [hS_pos s₀])
  set q : ℝ := ‖z - z₀‖ / ρ
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hρ_pos.le
  have hq1 : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0, div_lt_one hρ_pos]; exact hρ_gt
  refine Summable.of_norm_bounded_eventually_nat (f := fun s => d s * (z - z₀) ^ s)
    ((summable_pow_mul_geometric_of_norm_lt_one K hq1).mul_left (S s₀ * 2 ^ K)) ?_
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (hs₀1.trans hs)
  have h2s : ((s + 1 : ℕ) : ℝ) ^ K ≤ 2 ^ K * (s : ℝ) ^ K := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) K
  have hμ_le : μ s ≤ S s₀ * (2 ^ K * (s : ℝ) ^ K) := by
    have h1 : μ s ≤ S (s + 1) := by
      have hSs : S (s + 1) = S s + μ s := by simp [S, sum_range_succ, add_assoc]
      linarith [hS_pos s, hSs]
    exact (h1.trans (hpoly (s + 1) (hs.trans (Nat.le_succ s)))).trans
      (mul_le_mul_of_nonneg_left h2s (by linarith [hS_pos s₀]))
  have hpow_z : ‖z - z₀‖ ^ s = ρ ^ s * q ^ s := by
    rw [← mul_pow, mul_div_cancel₀ _ hρ_pos.ne']
  calc ‖d s * (z - z₀) ^ s‖
      = μ s * q ^ s := by rw [norm_mul, norm_pow, hpow_z, ← mul_assoc]
    _ ≤ (S s₀ * (2 ^ K * (s : ℝ) ^ K)) * q ^ s :=
        mul_le_mul_of_nonneg_right hμ_le (pow_nonneg hq0 s)
    _ = (S s₀ * 2 ^ K) * ((s : ℝ) ^ K * q ^ s) := by ring

/-! ### Differential operator on `(z - z₀)^σ ∑ c_s (z - z₀)^s` and `w₁(z) log(z - z₀)` -/

/-- Derivatives and operator expansion of `ψ(z) = (z - z₀)^σ ∑' s, c s * (z - z₀)^s` on the slit
punctured disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
private theorem hasDerivAt_and_operator_cpow_mul_tsum {z₀ σ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s) :
    let A : ℂ → ℂ := fun u => ∑' s, c s * u ^ s
    let ψ : ℂ → ℂ := fun z => (z - z₀) ^ σ * A (z - z₀)
    let U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
    DifferentiableOn ℂ ψ U ∧
      (∀ z ∈ U, HasDerivAt ψ
        ((z - z₀) ^ (σ - 1) * (σ * A (z - z₀) + (z - z₀) * deriv A (z - z₀))) z) ∧
      (∀ u : ℂ, ‖u‖ < r → Summable fun s : ℕ =>
        (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
          ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s) ∧
      ∀ z ∈ U,
        deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z =
          (z - z₀) ^ (σ - 2) * ∑' s : ℕ,
            (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
              ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * (z - z₀) ^ s := by
  intro A ψ U
  have hopen : IsOpen U := isOpen_slitBall z₀ r
  have hpA : 0 < r → HasFPowerSeriesOnBall A
      (FormalMultilinearSeries.ofScalars ℂ c) 0 (ENNReal.ofReal r) :=
    fun hr => hasFPowerSeriesOnBall_of_punctured hr c fun z _ hzr => hc z hzr
  have hpF : 0 < r → HasFPowerSeriesOnBall (fun u : ℂ => ∑' s, fs s * u ^ s)
      (FormalMultilinearSeries.ofScalars ℂ fs) 0 (ENNReal.ofReal r) :=
    fun hr => hasFPowerSeriesOnBall_of_punctured hr fs fun z hz0 hzr => (hf z hz0 hzr).summable
  have hpG : 0 < r → HasFPowerSeriesOnBall (fun u : ℂ => ∑' s, gs s * u ^ s)
      (FormalMultilinearSeries.ofScalars ℂ gs) 0 (ENNReal.ofReal r) :=
    fun hr => hasFPowerSeriesOnBall_of_punctured hr gs fun z hz0 hzr => (hg z hz0 hzr).summable
  have hderiv1 : ∀ z ∈ U, HasDerivAt ψ
      ((z - z₀) ^ (σ - 1) * (σ * A (z - z₀) + (z - z₀) * deriv A (z - z₀))) z := by
    rintro z ⟨hzs, hzb⟩
    have hr : 0 < r := (norm_nonneg _).trans_lt hzb
    have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
    have han := analyticOnNhd_tsum_of_summable hr c hc
    have hA_diff : DifferentiableAt ℂ A (z - z₀) :=
      (han (z - z₀) (mem_ball_zero_iff.mpr hzb)).differentiableAt
    have hsub : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
    have hpow := hsub.cpow_const (c := σ) hzs
    have hAcomp : HasDerivAt (fun w : ℂ => A (w - z₀)) (deriv A (z - z₀)) z :=
      hA_diff.hasDerivAt.comp_sub_const z z₀
    have hcpow_split : (z - z₀) ^ σ = (z - z₀) ^ (σ - 1) * (z - z₀) := by
      conv_lhs => rw [show σ = σ - 1 + 1 by ring]
      rw [Complex.cpow_add _ _ hzu0, Complex.cpow_one]
    refine (hpow.mul hAcomp).congr_deriv ?_
    rw [hcpow_split]; ring
  have hop_series : ∀ u : ℂ, ‖u‖ < r →
      HasSum (fun s : ℕ => (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
          ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s)
        ((u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) +
          (u * deriv A u + σ * A u) * (∑' s, fs s * u ^ s) +
          A u * (∑' s, gs s * u ^ s)) := by
    intro u hu
    have hr : 0 < r := (norm_nonneg u).trans_lt hu
    have hue : ‖u‖ₑ < ENNReal.ofReal r := enorm_lt_ofReal_iff.mpr hu
    have hc_norm : Summable fun s : ℕ => ‖c s * u ^ s‖ := by
      simpa using (hpA hr).summable_norm_descFactorial_mul_pow hue 0
    have hsc_norm : Summable fun s : ℕ => ‖(s : ℂ) * c s * u ^ s‖ := by
      simpa using (hpA hr).summable_norm_descFactorial_mul_pow hue 1
    have hf_norm : Summable fun s : ℕ => ‖fs s * u ^ s‖ := by
      simpa using (hpF hr).summable_norm_descFactorial_mul_pow hue 0
    have hg_norm : Summable fun s : ℕ => ‖gs s * u ^ s‖ := by
      simpa using (hpG hr).summable_norm_descFactorial_mul_pow hue 0
    have hA0 : HasSum (fun s : ℕ => c s * u ^ s) (A u) := by
      simpa using (hpA hr).hasSum_descFactorial_mul_pow hue 0
    have hA1 : HasSum (fun s : ℕ => (s : ℂ) * c s * u ^ s) (u * deriv A u) := by
      simpa [iteratedDeriv_one] using (hpA hr).hasSum_descFactorial_mul_pow hue 1
    have hA2 : HasSum (fun s : ℕ => (s : ℂ) * ((s : ℂ) - 1) * c s * u ^ s)
        (u ^ 2 * deriv (deriv A) u) := by
      have hraw := (hpA hr).hasSum_descFactorial_mul_pow hue 2
      rw [show iteratedDeriv 2 A = deriv (deriv A) by simp [iteratedDeriv_succ]] at hraw
      refine hraw.congr_fun fun s => ?_
      rcases s with _ | s
      · simp
      · simp only [Nat.descFactorial_succ, Nat.add_sub_cancel, Nat.descFactorial_zero, mul_one]
        push_cast; ring
    have hσc_norm : Summable fun s : ℕ => ‖((σ + s) * c s) * u ^ s‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_)
        ((hc_norm.mul_left ‖σ‖).add hsc_norm)
      calc ‖((σ + s) * c s) * u ^ s‖
          = ‖σ * (c s * u ^ s) + (s : ℂ) * c s * u ^ s‖ := by congr 1; ring
        _ ≤ ‖σ‖ * ‖c s * u ^ s‖ + ‖(s : ℂ) * c s * u ^ s‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
    have hlead : HasSum (fun s : ℕ => (σ + s) * (σ + s - 1) * c s * u ^ s)
        (u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) :=
      (((hA2.add (hA1.mul_left (2 * σ))).add (hA0.mul_left (σ * (σ - 1)))).congr_fun
        fun s => by ring)
    have hP_prod := hasSum_sum_range_mul_of_summable_norm hσc_norm hf_norm
    have hP_val : ∑' s : ℕ, ((σ + s) * c s) * u ^ s = u * deriv A u + σ * A u :=
      ((hA1.add (hA0.mul_left σ)).congr_fun fun s => by ring).tsum_eq
    rw [hP_val] at hP_prod
    have hR_prod := hasSum_sum_range_mul_of_summable_norm hc_norm hg_norm
    have hA_val : ∑' s : ℕ, c s * u ^ s = A u := rfl
    rw [hA_val] at hR_prod
    refine ((hlead.add hP_prod).add hR_prod).congr_fun fun s => ?_
    rw [sum_range_succ_mul_pow (fun k => (σ + k) * c k) fs u s,
      sum_range_succ_mul_pow c gs u s]
    have hsum_add : (∑ k ∈ range s, (σ + k) * c k * fs (s - k)) * u ^ s +
        (∑ k ∈ range s, c k * gs (s - k)) * u ^ s =
        (∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s := by
      rw [← add_mul, ← sum_add_distrib]
      congr 1; exact sum_congr rfl fun _ _ => by ring
    rw [indicialPoly_def]
    linear_combination -hsum_add
  refine ⟨fun z hz => (hderiv1 z hz).differentiableAt.differentiableWithinAt,
    hderiv1, fun u hu => (hop_series u hu).summable, ?_⟩
  rintro z ⟨hzs, hzb⟩
  set u : ℂ := z - z₀
  have hr : 0 < r := (norm_nonneg u).trans_lt hzb
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hzs
  have han := analyticOnNhd_tsum_of_summable hr c hc
  have hA_diff : DifferentiableAt ℂ A u := (han u (mem_ball_zero_iff.mpr hzb)).differentiableAt
  have hA'_diff : DifferentiableAt ℂ (deriv A) u :=
    (han.deriv u (mem_ball_zero_iff.mpr hzb)).differentiableAt
  have hsub : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hpow2 := hsub.cpow_const (c := σ - 1) hzs
  have h1 : HasDerivAt (fun w : ℂ => σ * A (w - z₀)) (σ * deriv A u) z :=
    (hA_diff.hasDerivAt.comp_sub_const z z₀).const_mul σ
  have h2 : HasDerivAt (fun w : ℂ => deriv A (w - z₀)) (deriv (deriv A) u) z :=
    hA'_diff.hasDerivAt.comp_sub_const z z₀
  have hinner := h1.add (hsub.mul h2)
  have hev : deriv ψ =ᶠ[𝓝 z]
      ((fun w : ℂ => (w - z₀) ^ (σ - 1)) *
        ((fun w : ℂ => σ * A (w - z₀)) +
          (fun w : ℂ => w - z₀) * fun w : ℂ => deriv A (w - z₀))) := by
    filter_upwards [hopen.mem_nhds ⟨hzs, hzb⟩] with w hw
    exact (hderiv1 w hw).deriv
  have hcpow1 : u ^ (σ - 1) = u ^ (σ - 2) * u := by
    conv_lhs => rw [show σ - 1 = σ - 2 + 1 by ring]
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hcpow2 : u ^ σ = u ^ (σ - 2) * u ^ 2 := by
    conv_lhs => rw [show σ = σ - 2 + (2 : ℕ) by push_cast; ring]
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_natCast]
  have hderiv2 : deriv (deriv ψ) z =
      u ^ (σ - 2) * (u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) := by
    rw [((hpow2.mul hinner).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.add_apply, Pi.mul_apply]
    dsimp only [u] at hcpow1 ⊢
    rw [show σ - 1 - 1 = σ - 2 by ring, hcpow1]
    ring
  rw [(hop_series u hzb).tsum_eq, (hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq,
    (hg z (norm_pos_iff.mpr hu0) hzb).tsum_eq, hderiv2, (hderiv1 z ⟨hzs, hzb⟩).deriv]
  dsimp only [ψ, u]
  rw [hcpow1, hcpow2]
  ring

/-- Operator identity for `Φ(z) = w₁(z) log(z - z₀)` when `w₁` solves `w₁'' + f w₁' + g w₁ = 0` on
the slit punctured disc. -/
private theorem hasDerivAt_and_operator_mul_log {z₀ : ℂ} {r : ℝ} {f g w₁ : ℂ → ℂ}
    (hw₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hsol₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0) :
    let Φ : ℂ → ℂ := fun z => w₁ z * Complex.log (z - z₀)
    let U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
    DifferentiableOn ℂ Φ U ∧
      (∀ z ∈ U, HasDerivAt Φ (deriv w₁ z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w₁ z) z) ∧
      ∀ z ∈ U, deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z =
        ((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w₁ z + ((z - z₀) * f z - 1) * w₁ z) := by
  intro Φ U
  have hopen : IsOpen U := isOpen_slitBall z₀ r
  have hw₁_at : ∀ z ∈ U, DifferentiableAt ℂ w₁ z := fun z hz =>
    hw₁.differentiableAt (hopen.mem_nhds hz)
  have hdw₁_on : DifferentiableOn ℂ (deriv w₁) U := hw₁.deriv hopen
  have hderiv1 : ∀ z ∈ U,
      HasDerivAt Φ (deriv w₁ z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w₁ z) z := by
    rintro z ⟨hzs, hzb⟩
    have hsub : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
    exact ((hw₁_at z ⟨hzs, hzb⟩).hasDerivAt.mul (hsub.clog hzs)).congr_deriv (by
      rw [one_div]; ring)
  refine ⟨fun z hz => (hderiv1 z hz).differentiableAt.differentiableWithinAt, hderiv1, ?_⟩
  rintro z ⟨hzs, hzb⟩
  have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hsub : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hlog := hsub.clog hzs
  have hinv := hsub.inv hzu0
  have hdw₁_at : HasDerivAt (deriv w₁) (deriv (deriv w₁) z) z :=
    (hdw₁_on.differentiableAt (hopen.mem_nhds ⟨hzs, hzb⟩)).hasDerivAt
  have hev : deriv Φ =ᶠ[𝓝 z]
      (deriv w₁ * (fun w : ℂ => Complex.log (w - z₀)) +
        (fun w : ℂ => (w - z₀)⁻¹) * w₁) := by
    filter_upwards [hopen.mem_nhds ⟨hzs, hzb⟩] with w hw
    exact (hderiv1 w hw).deriv
  have hd2 : deriv (deriv Φ) z =
      deriv (deriv w₁) z * Complex.log (z - z₀) + 2 * (z - z₀)⁻¹ * deriv w₁ z -
        ((z - z₀) ^ 2)⁻¹ * w₁ z := by
    rw [(((hdw₁_at.mul hlog).add (hinv.mul (hw₁_at z ⟨hzs, hzb⟩).hasDerivAt)).congr_of_eventuallyEq
      hev).deriv]
    simp only [Pi.inv_apply]
    field_simp [hzu0]
    ring
  rw [hd2, (hderiv1 z ⟨hzs, hzb⟩).deriv]
  dsimp only [Φ]
  have hode := hsol₁ z hzs hzb
  field_simp [hzu0]
  linear_combination (z - z₀) ^ 2 * Complex.log (z - z₀) * hode

/-- Analytic uniqueness for branch-cut power series: if `∑' s, d s * u ^ s` converges on `‖u‖ < r`
(`0 < r`) and `(z - z₀)^α ∑' s, d s * (z - z₀)^s = 0` on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`,
then every coefficient `d s` vanishes. -/
private theorem eq_zero_of_cpow_mul_tsum_eq_zero_on_slitBall {z₀ α : ℂ} {d : ℕ → ℂ} {r : ℝ}
    (hr : 0 < r) (hd : ∀ u : ℂ, ‖u‖ < r → Summable fun s => d s * u ^ s)
    (hzero : ∀ z : ℂ, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      (z - z₀) ^ α * (∑' s, d s * (z - z₀) ^ s) = 0) :
    ∀ s : ℕ, d s = 0 := by
  have hp := FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_of_summable d
    (ENNReal.ofReal_pos.mpr hr) fun u _ hur => hd u (enorm_lt_ofReal_iff.mp hur)
  set D : ℂ → ℂ := FormalMultilinearSeries.ofScalarsSum (E := ℂ) d
  have hD_eq : D = fun u : ℂ => ∑' s, d s * u ^ s := by
    ext u; simp [D, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  have han : AnalyticOnNhd ℂ D (ball 0 r) :=
    Metric.eball_ofReal (x := (0 : ℂ)) (ε := r) ▸ (hD_eq.symm ▸ hp).analyticOnNhd
  set u₀ : ℂ := ((r / 2 : ℝ) : ℂ)
  have hu₀_ball : u₀ ∈ ball (0 : ℂ) r := by
    simp [u₀, abs_of_pos hr, half_lt_self hr]
  have hev : D =ᶠ[𝓝 u₀] 0 := by
    have hopen : IsOpen (slitPlane ∩ ball (0 : ℂ) r) :=
      Complex.isOpen_slitPlane.inter Metric.isOpen_ball
    filter_upwards [hopen.mem_nhds ⟨Complex.ofReal_mem_slitPlane.mpr (half_pos hr), hu₀_ball⟩]
      with u ⟨hus, hub⟩
    have hz := hzero (z₀ + u) (by simpa using hus) (by simpa using hub)
    simp only [add_sub_cancel_left] at hz
    have hpow_ne : u ^ α ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hus)]
      exact Complex.exp_ne_zero _
    rw [hD_eq]
    exact (mul_eq_zero.mp hz).resolve_left hpow_ne
  have hD0 : EqOn D 0 (ball 0 r) :=
    han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) r).isPreconnected hu₀_ball hev
  intro s
  have hiter0 : iteratedDeriv s D 0 = 0 := by
    have hd_ev : D =ᶠ[𝓝 0] (0 : ℂ → ℂ) :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨ball 0 r, Metric.ball_mem_nhds 0 hr, fun u hu => hD0 hu⟩
    rw [hd_ev.iteratedDeriv_eq]
    simp
  have hcoeff := FormalMultilinearSeries.iteratedDeriv_ofScalarsSum_zero d
    ((ENNReal.ofReal_pos.mpr hr).trans_le hp.r_le) s
  rw [hiter0] at hcoeff
  exact (mul_eq_zero.mp hcoeff.symm).resolve_left
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))

/-! ### Primary series solution at a regular singularity -/

/-- **Series solution at a regular singularity** (DLMF 2.7.2–2.7.5). Let `(z - z₀) f(z)` and
`(z - z₀)² g(z)` have power series `∑ fs s * (z - z₀)^s` and `∑ gs s * (z - z₀)^s` on the
punctured disc `0 < ‖z - z₀‖ < r`. If `ρ` is a root of `indicialPoly (fs 0) (gs 0)` and `a : ℕ → ℂ`
satisfies the indicial recursion, then `∑ a_s (z - z₀)^s` converges on the full disc `‖z - z₀‖ < r`,
and `w(z) = (z - z₀)^ρ ∑' s, a s * (z - z₀)^s` is a holomorphic solution of `w'' + f w' + g w = 0`
on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem regularSingular_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) :
    let w : ℂ → ℂ := fun z => (z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s
    (∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  have hsum : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s :=
    summable_of_perturbed_indicial_rec (σ := ρ) (E := 0) (s₁ := 1)
      (fun z hz0 hzr => (hf z hz0 hzr).summable)
      (fun z hz0 hzr => (hg z hz0 hzr).summable)
      (fun _ _ _ => ⟨0, le_rfl, fun _ => by simp⟩)
      (fun s hs => by simp [ha s hs])
  obtain ⟨hdiff, _, _, hop⟩ := hasDerivAt_and_operator_cpow_mul_tsum (σ := ρ) hf hg hsum
  refine ⟨hsum, hdiff, fun z hzs hzb => ?_⟩
  rw [hop z ⟨hzs, hzb⟩]
  have hcoeff : ∀ s : ℕ, (indicialPoly (fs 0) (gs 0) (ρ + s) * a s +
      ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) = 0 := fun s => by
    rcases eq_or_ne s 0 with rfl | hs
    · simp [hρ]
    · rw [ha s (Nat.pos_of_ne_zero hs), neg_add_cancel]
  simp [hcoeff]

/-- Specialization of `regularSingular_solution` to the canonical normalized sequence
`regularSingularCoeff fs gs ρ` (`a₀ = 1`) attached to a non-resonant indicial root `ρ`. -/
theorem regularSingularCoeff_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0) :
    let a := regularSingularCoeff fs gs ρ
    let w : ℂ → ℂ := fun z => (z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s
    (∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 :=
  regularSingular_solution hf hg hρ fun _ hs =>
    indicialPoly_mul_regularSingularCoeff hs (hres _ hs)

/-- **Analytic uniqueness of the normalized series coefficients**: for `0 < r` and a non-resonant
indicial root `ρ`, any convergent power series `∑ a_s (z - z₀)^s` with `a 0 = 1` such that
`(z - z₀)^ρ ∑ a_s (z - z₀)^s` solves `w'' + f w' + g w = 0` on the slit punctured disc has
`a = regularSingularCoeff fs gs ρ`. -/
theorem eq_regularSingularCoeff_of_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs a : ℕ → ℂ}
    (hr : 0 < r)
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0)
    (ha0 : a 0 = 1)
    (hsum : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    (hsol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv (fun w => (w - z₀) ^ ρ * ∑' s, a s * (w - z₀) ^ s)) z +
        f z * deriv (fun w => (w - z₀) ^ ρ * ∑' s, a s * (w - z₀) ^ s) z +
        g z * ((z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s) = 0) :
    a = regularSingularCoeff fs gs ρ := by
  obtain ⟨_, _, hop_sum, hop_eq⟩ := hasDerivAt_and_operator_cpow_mul_tsum (σ := ρ) hf hg hsum
  have hall := eq_zero_of_cpow_mul_tsum_eq_zero_on_slitBall (z₀ := z₀) (α := ρ - 2) hr hop_sum
    fun z hzs hzb => (hop_eq z ⟨hzs, hzb⟩).symm.trans (hsol z hzs hzb)
  exact eq_regularSingularCoeff_of_rec hres ha0 fun s _ => by linear_combination hall s

/-! ### Second solution when the indicial roots differ by a natural number -/

/-- Power-series expansion and linear growth bound for the shifted logarithmic forcing terms
`u ^ N * (2 u A₁'(u) + (2(α₂ + N) + P(u) - 1) A₁(u))` in the resonant case `α₁ = α₂ + N`. -/
private theorem hasSum_log_forcing_series {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ} {f : ℂ → ℂ}
    {fs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (ha_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s) :
    let A₁ : ℂ → ℂ := fun u => ∑' s, a s * u ^ s
    let F_term : ℕ → ℂ := fun s =>
      if s < N then 0
      else (2 * (α₂ + s) + fs 0 - 1) * a (s - N) +
        ∑ k ∈ range (s - N), fs (s - N - k) * a k
    (∀ ρ : ℝ, 0 < ρ → ρ < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, ‖F_term s‖ * ρ ^ s ≤ C * (s + 1)) ∧
      ∀ u : ℂ, ‖u‖ < r →
        HasSum (fun s => F_term s * u ^ s)
          (u ^ N * (2 * u * deriv A₁ u +
            (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u)) := by
  intro A₁ F_term
  refine ⟨?_, ?_⟩
  · intro ρ hρ0 hρr
    obtain ⟨Mf, hMf_pos, hMf⟩ := exists_norm_mul_pow_le_of_punctured hρ0 hρr fs
      fun z hz0 hzr => (hf z hz0 hzr).summable
    obtain ⟨Ma, _, hMa⟩ := exists_norm_mul_pow_le_of_punctured hρ0 hρr a
      fun z _ hzr => ha_sum z hzr
    set C : ℝ := ρ ^ N * ((2 * ‖α₂‖ + ‖fs 0 - 1‖ + 2) * Ma + Mf * Ma)
    refine ⟨C, by positivity, fun s => ?_⟩
    dsimp only [F_term]
    split_ifs with hsN
    · simp only [norm_zero, zero_mul]; positivity
    · have hsN' : N ≤ s := not_lt.mp hsN
      have hpow : ρ ^ s = ρ ^ N * ρ ^ (s - N) := by rw [← pow_add, Nat.add_sub_of_le hsN']
      have hcoef : ‖2 * (α₂ + s) + fs 0 - 1‖ ≤ (2 * ‖α₂‖ + ‖fs 0 - 1‖ + 2) * (s + 1) := by
        rw [show 2 * (α₂ + (s : ℂ)) + fs 0 - 1 = 2 * α₂ + (fs 0 - 1) + 2 * (s : ℂ) by ring]
        have htri1 := norm_add_le (2 * α₂ + (fs 0 - 1)) (2 * (s : ℂ))
        have htri2 := norm_add_le (2 * α₂) (fs 0 - 1)
        rw [norm_mul, Complex.norm_ofNat] at htri2
        have h2s : ‖(2 : ℂ) * (s : ℂ)‖ = 2 * (s : ℝ) := by simp
        nlinarith [norm_nonneg α₂, norm_nonneg (fs 0 - 1), htri1, htri2, h2s]
      have h1 : ‖(2 * (α₂ + s) + fs 0 - 1) * a (s - N)‖ * ρ ^ (s - N) ≤
          (2 * ‖α₂‖ + ‖fs 0 - 1‖ + 2) * Ma * (s + 1) := by
        rw [norm_mul, mul_assoc]
        nlinarith [mul_le_mul hcoef (hMa (s - N)) (by positivity) (by positivity)]
      have h2 : ‖∑ k ∈ range (s - N), fs (s - N - k) * a k‖ * ρ ^ (s - N) ≤
          Mf * Ma * (s + 1) := by
        have hsum_le : (∑ k ∈ range (s - N), ‖fs (s - N - k) * a k‖ * ρ ^ (s - N)) ≤
            ∑ _k ∈ range (s - N), Mf * Ma := Finset.sum_le_sum fun k hk => by
          have hp2 : ρ ^ (s - N) = ρ ^ (s - N - k) * ρ ^ k := by
            rw [← pow_add, Nat.sub_add_cancel (mem_range.mp hk).le]
          rw [norm_mul, hp2]
          calc ‖fs (s - N - k)‖ * ‖a k‖ * (ρ ^ (s - N - k) * ρ ^ k)
              = (‖fs (s - N - k)‖ * ρ ^ (s - N - k)) * (‖a k‖ * ρ ^ k) := by ring
            _ ≤ Mf * Ma := mul_le_mul (hMf _) (hMa _) (by positivity) hMf_pos.le
        have hle : ((s - N : ℕ) : ℝ) ≤ s + 1 := by
          exact_mod_cast (Nat.sub_le s N).trans (Nat.le_succ s)
        calc ‖∑ k ∈ range (s - N), fs (s - N - k) * a k‖ * ρ ^ (s - N)
            ≤ ∑ k ∈ range (s - N), ‖fs (s - N - k) * a k‖ * ρ ^ (s - N) := by
              rw [← Finset.sum_mul]
              exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
          _ ≤ ∑ _k ∈ range (s - N), Mf * Ma := hsum_le
          _ = ((s - N : ℕ) : ℝ) * (Mf * Ma) := by simp
          _ ≤ (s + 1) * (Mf * Ma) := mul_le_mul_of_nonneg_right hle (by positivity)
          _ = Mf * Ma * (s + 1) := by ring
      have htri := norm_add_le ((2 * (α₂ + s) + fs 0 - 1) * a (s - N))
        (∑ k ∈ range (s - N), fs (s - N - k) * a k)
      have htri_ρ := mul_le_mul_of_nonneg_right htri (pow_nonneg hρ0.le (s - N))
      rw [hpow]
      dsimp [C]
      nlinarith [pow_nonneg hρ0.le N, htri_ρ, h1, h2]
  · intro u hu
    have hr : 0 < r := (norm_nonneg u).trans_lt hu
    have hue : ‖u‖ₑ < ENNReal.ofReal r := enorm_lt_ofReal_iff.mpr hu
    have hpA := hasFPowerSeriesOnBall_of_punctured hr a fun z _ hzr => ha_sum z hzr
    have hpF := hasFPowerSeriesOnBall_of_punctured hr fs fun z hz0 hzr => (hf z hz0 hzr).summable
    have ha_norm : Summable fun s : ℕ => ‖a s * u ^ s‖ := by
      simpa using hpA.summable_norm_descFactorial_mul_pow hue 0
    have hf_norm : Summable fun s : ℕ => ‖fs s * u ^ s‖ := by
      simpa using hpF.summable_norm_descFactorial_mul_pow hue 0
    have hA0 : HasSum (fun s : ℕ => a s * u ^ s) (A₁ u) := by
      simpa using hpA.hasSum_descFactorial_mul_pow hue 0
    have hA1 : HasSum (fun s : ℕ => (s : ℂ) * a s * u ^ s) (u * deriv A₁ u) := by
      simpa [iteratedDeriv_one] using hpA.hasSum_descFactorial_mul_pow hue 1
    have hprod := hasSum_sum_range_mul_of_summable_norm ha_norm hf_norm
    have hA_val : ∑' s : ℕ, a s * u ^ s = A₁ u := rfl
    rw [hA_val] at hprod
    have hunshifted : HasSum (fun m : ℕ =>
        ((2 * (α₂ + N + m) + fs 0 - 1) * a m + ∑ k ∈ range m, fs (m - k) * a k) * u ^ m)
        (2 * u * deriv A₁ u + (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u) := by
      have htot := ((hA1.mul_left 2).add (hA0.mul_left (2 * (α₂ + N) - 1))).add hprod
      rw [show 2 * (u * deriv A₁ u) + (2 * (α₂ + N) - 1) * A₁ u + A₁ u * ∑' s, fs s * u ^ s =
        2 * u * deriv A₁ u + (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u by ring] at htot
      refine htot.congr_fun fun m => ?_
      rw [sum_range_succ_mul_pow a fs u m]
      have hcomm : (∑ k ∈ range m, a k * fs (m - k)) = ∑ k ∈ range m, fs (m - k) * a k :=
        sum_congr rfl fun _ _ => mul_comm _ _
      rw [hcomm]; ring
    refine ((add_left_injective N).hasSum_iff fun s hs => ?_).mp
      ((hunshifted.mul_left (u ^ N)).congr_fun fun m => ?_)
    · have hsN : s < N := by
        by_contra hge
        exact hs ⟨s - N, Nat.sub_add_cancel (not_lt.mp hge)⟩
      simp [F_term, hsN]
    · have hnlt : ¬m + N < N := by omega
      simp only [Function.comp_apply, F_term, hnlt, ↓reduceIte, Nat.add_sub_cancel, pow_add]
      push_cast; ring

/-- Shared operator formula for any second-solution candidate
`w₂'(z) = (z - z₀)^{α₂} ∑ b' s * (z - z₀)^s + c' * w₁(z) * log(z - z₀)` when `α₁ = α₂ + N`. -/
private theorem operator_second_ansatz_eq {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs b' : ℕ → ℂ} {c' : ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂))
    (hb'_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b' s * (z - z₀) ^ s) :
    let a := regularSingularCoeff fs gs (α₂ + N)
    let w₁ : ℂ → ℂ := fun w => (w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s
    let w₂' : ℂ → ℂ := fun w =>
      (w - z₀) ^ α₂ * (∑' s, b' s * (w - z₀) ^ s) + c' * w₁ w * Complex.log (w - z₀)
    let D : ℕ → ℂ := fun s =>
      (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) +
      c' * (if s < N then 0
        else (2 * (α₂ + s) + fs 0 - 1) * a (s - N) +
          ∑ k ∈ range (s - N), fs (s - N - k) * a k)
    let U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
    DifferentiableOn ℂ w₂' U ∧
      (∀ u : ℂ, ‖u‖ < r → Summable fun s => D s * u ^ s) ∧
      ∀ z ∈ U, deriv (deriv w₂') z + f z * deriv w₂' z + g z * w₂' z =
        (z - z₀) ^ (α₂ - 2) * ∑' s, D s * (z - z₀) ^ s := by
  intro a w₁ w₂' D U
  have hre : α₂.re ≤ (α₂ + (N : ℂ)).re := by simp
  have hρ₁ : indicialPoly (fs 0) (gs 0) (α₂ + N) = 0 := by simp [hfact]
  have hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + N + s) ≠ 0 :=
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact hre hs
  obtain ⟨ha_sum, hw₁_diff, hw₁_sol⟩ := regularSingularCoeff_solution hf hg hρ₁ hres₁
  obtain ⟨_, hF_hasSum⟩ := hasSum_log_forcing_series (α₂ := α₂) (N := N) hf ha_sum
  obtain ⟨hψ_diff, _, hψ_sum, hψ_op⟩ :=
    hasDerivAt_and_operator_cpow_mul_tsum (σ := α₂) hf hg hb'_sum
  obtain ⟨hΦ_diff, _, hΦ_op⟩ := hasDerivAt_and_operator_mul_log hw₁_diff hw₁_sol
  obtain ⟨_, hw₁_d1, _, _⟩ := hasDerivAt_and_operator_cpow_mul_tsum (σ := α₂ + N) hf hg ha_sum
  set ψ : ℂ → ℂ := fun w => (w - z₀) ^ α₂ * ∑' s, b' s * (w - z₀) ^ s
  set Φ : ℂ → ℂ := fun w => w₁ w * Complex.log (w - z₀)
  have hw₂'_eq : w₂' = fun w => ψ w + c' * Φ w := by ext w; dsimp [w₂', ψ, Φ]; ring
  have hw₂'_diff : DifferentiableOn ℂ w₂' U := by
    rw [hw₂'_eq]
    exact hψ_diff.add (hΦ_diff.const_mul c')
  have hD_hasSum : ∀ u : ℂ, ‖u‖ < r → HasSum (fun s => D s * u ^ s)
      ((∑' s : ℕ, (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) * u ^ s) +
        c' * (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
          (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s))) := fun u hu =>
    (((hψ_sum u hu).hasSum.add ((hF_hasSum u hu).mul_left c')).congr_fun fun s => by
      dsimp [D]; ring)
  refine ⟨hw₂'_diff, fun u hu => (hD_hasSum u hu).summable, ?_⟩
  rintro z ⟨hzs, hzb⟩
  have hopen : IsOpen U := isOpen_slitBall z₀ r
  have hmem : U ∈ 𝓝 z := hopen.mem_nhds ⟨hzs, hzb⟩
  have hdψ_at : DifferentiableAt ℂ (deriv ψ) z := (hψ_diff.deriv hopen).differentiableAt hmem
  have hdΦ_at : DifferentiableAt ℂ (deriv Φ) z := (hΦ_diff.deriv hopen).differentiableAt hmem
  have hd1_ev : deriv (fun w => ψ w + c' * Φ w) =ᶠ[𝓝 z] (deriv ψ + fun w => c' * deriv Φ w) := by
    filter_upwards [hmem] with w hw
    exact (((hψ_diff.differentiableAt (hopen.mem_nhds hw)).hasDerivAt).add
      (((hΦ_diff.differentiableAt (hopen.mem_nhds hw)).hasDerivAt).const_mul c')).deriv
  have hd2_z : deriv (deriv (fun w => ψ w + c' * Φ w)) z =
      deriv (deriv ψ) z + c' * deriv (deriv Φ) z := by
    rw [(((hdψ_at.hasDerivAt).add ((hdΦ_at.hasDerivAt).const_mul c')).congr_of_eventuallyEq
      hd1_ev).deriv]
  rw [hw₂'_eq, hd1_ev.self_of_nhds, hd2_z]
  simp only [Pi.add_apply]
  have hsplit : (deriv (deriv ψ) z + c' * deriv (deriv Φ) z) +
      f z * (deriv ψ z + c' * deriv Φ z) + g z * (ψ z + c' * Φ z) =
      (deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z) +
        c' * (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) := by ring
  rw [hsplit, hψ_op z ⟨hzs, hzb⟩, hΦ_op z ⟨hzs, hzb⟩, (hD_hasSum (z - z₀) hzb).tsum_eq]
  set u : ℂ := z - z₀
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hzs
  set A₁ : ℂ → ℂ := fun w => ∑' s, a s * w ^ s
  have hdw₁ : deriv w₁ z = u ^ (α₂ + (N : ℂ) - 1) * ((α₂ + N) * A₁ u + u * deriv A₁ u) :=
    (hw₁_d1 z ⟨hzs, hzb⟩).deriv
  have hPf : ∑' s, fs s * u ^ s = u * f z := (hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq
  have hcpow_N : (u ^ 2)⁻¹ * u ^ (α₂ + (N : ℂ)) = u ^ (α₂ - 2) * u ^ N := by
    have h1 : u ^ (α₂ + (N : ℂ)) = u ^ (α₂ - 2) * u ^ 2 * u ^ N := by
      conv_lhs => rw [show α₂ + (N : ℂ) = α₂ - 2 + (2 : ℕ) + (N : ℕ) by push_cast; ring]
      rw [Complex.cpow_add _ _ hu0, Complex.cpow_add _ _ hu0, Complex.cpow_natCast,
        Complex.cpow_natCast]
    rw [h1]
    field_simp [hu0]
  have hcpow_N1 : u * u ^ (α₂ + (N : ℂ) - 1) = u ^ (α₂ + (N : ℂ)) := by
    conv_rhs => rw [show α₂ + (N : ℂ) = α₂ + (N : ℂ) - 1 + 1 by ring]
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]; ring
  rw [hPf]
  dsimp only [w₁, A₁, u] at hdw₁ ⊢
  rw [hdw₁]
  have hmul : 2 * u * (u ^ (α₂ + (N : ℂ) - 1) * ((α₂ + ↑N) * A₁ u + u * deriv A₁ u)) =
      2 * (u * u ^ (α₂ + (N : ℂ) - 1)) * ((α₂ + ↑N) * A₁ u + u * deriv A₁ u) := by ring
  rw [hmul, hcpow_N1]
  have hfact_u : (u ^ 2)⁻¹ *
      (2 * u ^ (α₂ + (N : ℂ)) * ((α₂ + ↑N) * A₁ u + u * deriv A₁ u) +
        (u * f z - 1) * (u ^ (α₂ + (N : ℂ)) * A₁ u)) =
      ((u ^ 2)⁻¹ * u ^ (α₂ + (N : ℂ))) *
        (2 * u * deriv A₁ u + (2 * (α₂ + ↑N) + u * f z - 1) * A₁ u) := by ring
  rw [hfact_u, hcpow_N]; ring

/-- **Logarithmic second solution at a regular singularity** (DLMF 2.7.6). When the indicial
polynomial factors as `(α - α₁)(α - α₂)` with `α₁ - α₂ = N ∈ ℕ`, the series
`∑ regularSingularSecondCoeff fs gs α₂ N s * (z - z₀)^s` converges on `‖z - z₀‖ < r`, and
`w₂(z) = (z - z₀)^{α₂} ∑' s, b s * (z - z₀)^s + c * w₁(z) * Complex.log (z - z₀)` is a
holomorphic solution of `w'' + f w' + g w = 0` on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem regularSingular_second_solution {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    let a := regularSingularCoeff fs gs α₁
    let b := regularSingularSecondCoeff fs gs α₂ N
    let c := regularSingularLogMultiplier fs gs α₂ N
    let w₁ : ℂ → ℂ := fun z => (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s
    let w₂ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) + c * w₁ z * Complex.log (z - z₀)
    (∀ z, ‖z - z₀‖ < r → Summable fun s => b s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0 := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  have hre : α₂.re ≤ (α₂ + (N : ℂ)).re := by simp
  have hρ₁ : indicialPoly (fs 0) (gs 0) (α₂ + N) = 0 := by simp [hfact]
  have hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + N + s) ≠ 0 :=
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact hre hs
  obtain ⟨ha_sum, _, _⟩ := regularSingularCoeff_solution hf hg hρ₁ hres₁
  set a := regularSingularCoeff fs gs (α₂ + N)
  set b := regularSingularSecondCoeff fs gs α₂ N
  set c := regularSingularLogMultiplier fs gs α₂ N
  set F_term : ℕ → ℂ := fun s =>
    if s < N then 0
    else (2 * (α₂ + s) + fs 0 - 1) * a (s - N) + ∑ k ∈ range (s - N), fs (s - N - k) * a k
  obtain ⟨hF_bound, _⟩ := hasSum_log_forcing_series (α₂ := α₂) (N := N) hf ha_sum
  have hb_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b s * (z - z₀) ^ s := by
    refine summable_of_perturbed_indicial_rec (σ := α₂) (E := fun s => -c * F_term s)
      (s₁ := N + 1) (fun z hz0 hzr => (hf z hz0 hzr).summable)
      (fun z hz0 hzr => (hg z hz0 hzr).summable) (fun ρ hρ0 hρr => ?_) (fun s hs => ?_)
    · obtain ⟨CF, _, hCF⟩ := hF_bound ρ hρ0 hρr
      refine ⟨‖c‖ * CF, by positivity, fun s => ?_⟩
      calc ‖-c * F_term s‖ * ρ ^ s
          = ‖c‖ * (‖F_term s‖ * ρ ^ s) := by rw [norm_mul, norm_neg, mul_assoc]
        _ ≤ ‖c‖ * (CF * (s + 1)) := mul_le_mul_of_nonneg_left (hCF s) (norm_nonneg c)
        _ = (‖c‖ * CF) * (s + 1) := by ring
    · have hsN : N < s := by omega
      have hQ := indicialPoly_add_nat_ne_zero_of_ne hfact (by omega) hsN.ne'
      have hrec := indicialPoly_mul_regularSingularSecondCoeff_of_gt (fs := fs) (gs := gs)
        (α₂ := α₂) hsN hQ
      have hnlt : ¬s < N := by omega
      dsimp only [F_term]
      simp only [hnlt, ↓reduceIte]
      linear_combination hrec
  obtain ⟨hw₂_diff, _, hw₂_op⟩ := operator_second_ansatz_eq (c' := c) hf hg hfact hb_sum
  refine ⟨hb_sum, hw₂_diff, fun z hzs hzb => ?_⟩
  rw [hw₂_op z ⟨hzs, hzb⟩]
  have hvieta := (indicialPoly_eq_mul_sub_iff.mp hfact).1
  have hcoeff0 : ∀ s : ℕ,
      (indicialPoly (fs 0) (gs 0) (α₂ + s) * b s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) +
      c * F_term s = 0 := by
    intro s
    dsimp only [F_term]
    rcases lt_trichotomy s N with hsN | hEq | hsN
    · simp only [hsN, ↓reduceIte, mul_zero, add_zero]
      rcases eq_or_ne s 0 with rfl | hs0
      · simp [hfact]
      · have hQ := indicialPoly_add_nat_ne_zero_of_ne hfact hs0 hsN.ne
        rw [indicialPoly_mul_regularSingularSecondCoeff_of_lt (Nat.pos_of_ne_zero hs0) hsN hQ]
        ring
    · subst s
      have hQN : indicialPoly (fs 0) (gs 0) (α₂ + N) = 0 := by simp [hfact]
      have ha0_eq : a 0 = 1 := regularSingularCoeff_zero fs gs (α₂ + N)
      have h2N : 2 * (α₂ + (N : ℂ)) + fs 0 - 1 = N := by linear_combination hvieta
      simp only [lt_irrefl, ↓reduceIte, Nat.sub_self, Finset.range_zero, Finset.sum_empty,
        add_zero, hQN, zero_mul, zero_add, ha0_eq, mul_one, h2N]
      rcases eq_or_ne N 0 with rfl | hN0
      · simp
      · have hsum_eq : (∑ k ∈ range N, ((α₂ + k) * fs (N - k) + gs (N - k)) * b k) =
            ∑ k ∈ range N, ((α₂ + k) * fs (N - k) + gs (N - k)) *
              regularSingularCoeff fs gs α₂ k :=
          sum_congr rfl fun k hk => by
            dsimp [b]
            rw [regularSingularSecondCoeff_eq_regularSingularCoeff_of_lt fs gs α₂ (mem_range.mp hk)]
        rw [hsum_eq]
        linear_combination
          natCast_mul_regularSingularLogMultiplier fs gs α₂ (Nat.pos_of_ne_zero hN0)
    · have hnlt : ¬s < N := by omega
      have hQ := indicialPoly_add_nat_ne_zero_of_ne hfact (by omega) hsN.ne'
      simp only [hnlt, ↓reduceIte]
      linear_combination indicialPoly_mul_regularSingularSecondCoeff_of_gt (fs := fs) (gs := gs)
        (α₂ := α₂) hsN hQ
  have htsum : (∑' s : ℕ, ((indicialPoly (fs 0) (gs 0) (α₂ + s) * b s +
      ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) + c * F_term s) *
      (z - z₀) ^ s) = 0 := by simp only [hcoeff0, zero_mul, tsum_zero]
  exact mul_eq_zero_of_right _ htsum

/-- **Analytic uniqueness of the second solution's coefficients**: for `0 < r` and
`α₁ - α₂ = N ∈ ℕ`, if `b' : ℕ → ℂ` and `c' : ℂ` satisfy `b' N = 0`, the normalization
`(N = 0 → c' = 1) ∧ (1 ≤ N → b' 0 = 1)`, convergence of `∑ b'_s (z - z₀)^s` on `‖z - z₀‖ < r`,
and `(z - z₀)^{α₂} ∑ b'_s (z - z₀)^s + c' w₁(z) log(z - z₀)` solves `w'' + f w' + g w = 0` on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, then `b' = regularSingularSecondCoeff fs gs α₂ N` and
`c' = regularSingularLogMultiplier fs gs α₂ N`. -/
theorem eq_regularSingularSecondCoeff_of_solution {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ}
    {f g : ℂ → ℂ} {fs gs b' : ℕ → ℂ} {c' : ℂ} (hr : 0 < r)
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N)
    (hb'N : b' N = 0)
    (hc'0 : N = 0 → c' = 1)
    (hb'0 : 1 ≤ N → b' 0 = 1)
    (hb'_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b' s * (z - z₀) ^ s)
    (hsol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      let w₁ := fun w => (w - z₀) ^ α₁ * ∑' s, regularSingularCoeff fs gs α₁ s * (w - z₀) ^ s
      let w₂' := fun w =>
        (w - z₀) ^ α₂ * (∑' s, b' s * (w - z₀) ^ s) + c' * w₁ w * Complex.log (w - z₀)
      deriv (deriv w₂') z + f z * deriv w₂' z + g z * w₂' z = 0) :
    b' = regularSingularSecondCoeff fs gs α₂ N ∧
      c' = regularSingularLogMultiplier fs gs α₂ N := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  obtain ⟨_, hD_sum, hD_op⟩ := operator_second_ansatz_eq (c' := c') hf hg hfact hb'_sum
  have hD0 := eq_zero_of_cpow_mul_tsum_eq_zero_on_slitBall (z₀ := z₀) (α := α₂ - 2) hr hD_sum
    fun z hzs hzb => (hD_op z ⟨hzs, hzb⟩).symm.trans (hsol z hzs hzb)
  exact eq_regularSingularSecondCoeff_of_rec hfact hb'N hc'0 hb'0 hD0

/-! ### Abel–Liouville Wronskian identity and nonvanishing -/

/-- Integrating factor `H(u) = ∑' s, (if s = 0 then 0 else fs s / s) * u ^ s` for
`(z - z₀) f(z) - fs 0` on `‖u‖ < r`. -/
private theorem hasDerivAt_regularSingular_integratingExponent {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {f : ℂ → ℂ} {fs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z)) :
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    H 0 = 0 ∧
      ContinuousOn H (ball 0 r) ∧
      ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
        HasDerivAt (fun w => H (w - z₀)) (f z - fs 0 * (z - z₀)⁻¹) z := by
  intro H
  set hc : ℕ → ℂ := fun s => if s = 0 then 0 else fs s / s
  have hpF := hasFPowerSeriesOnBall_of_punctured hr fs fun z hz0 hzr => (hf z hz0 hzr).summable
  have hpH : HasFPowerSeriesOnBall H (FormalMultilinearSeries.ofScalars ℂ hc) 0
      (ENNReal.ofReal r) := by
    refine FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_of_summable hc
      (ENNReal.ofReal_pos.mpr hr) fun u _ hur => ?_
    have hf_u : Summable fun s : ℕ => ‖fs s * u ^ s‖ := by
      simpa using hpF.summable_norm_descFactorial_mul_pow hur 0
    refine Summable.of_norm_bounded hf_u fun s => ?_
    dsimp [hc]
    split_ifs with hs0
    · simp only [zero_mul, norm_zero]; positivity
    · have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast Nat.pos_of_ne_zero hs0
      rw [div_mul_eq_mul_div, norm_div, Complex.norm_natCast]
      exact div_le_self (norm_nonneg _) hs1
  have han : AnalyticOnNhd ℂ H (ball 0 r) :=
    Metric.eball_ofReal (x := (0 : ℂ)) (ε := r) ▸ hpH.analyticOnNhd
  have hH0 : H 0 = 0 := by
    dsimp [H]; rw [tsum_eq_single 0]
    · simp
    · intro s hs; simp [zero_pow hs]
  refine ⟨hH0, han.continuousOn, fun z hz0 hzr => ?_⟩
  have hfz : HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z) := hf z hz0 hzr
  set u : ℂ := z - z₀
  have hu0 : u ≠ 0 := norm_pos_iff.mp hz0
  have hue : ‖u‖ₑ < ENNReal.ofReal r := enorm_lt_ofReal_iff.mpr hzr
  have hH1 : HasSum (fun s : ℕ => (s : ℂ) * hc s * u ^ s) (u * deriv H u) := by
    simpa [iteratedDeriv_one] using hpH.hasSum_descFactorial_mul_pow hue 1
  have hterm : (fun s : ℕ => (s : ℂ) * hc s * u ^ s) =
      fun s : ℕ => if s = 0 then 0 else fs s * u ^ s := by
    ext s; dsimp [hc]; split_ifs with hs0
    · simp
    · have hs_ne : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs0
      field_simp [hs_ne]
  rw [hterm] at hH1
  have hhead : HasSum (fun s : ℕ => if s = 0 then fs 0 * u ^ 0 else 0) (fs 0) := by
    convert hasSum_ite_eq (0 : ℕ) (fs 0 * u ^ 0) using 1; simp
  have hdiff_has : HasSum (fun s : ℕ => if s = 0 then 0 else fs s * u ^ s) (u * f z - fs 0) := by
    refine (hfz.sub hhead).congr_fun fun s => ?_
    split_ifs with hs0
    · subst hs0; simp
    · simp
  have huH' : u * deriv H u = u * f z - fs 0 := hH1.unique hdiff_has
  have hH' : deriv H u = f z - fs 0 * u⁻¹ := by
    apply mul_left_cancel₀ hu0; rw [huH']; field_simp [hu0]
  exact hH' ▸ (han u (mem_ball_zero_iff.mpr hzr)).differentiableAt.hasDerivAt.comp_sub_const z z₀

/-- Abel–Liouville constancy: `(z - z₀)^{fs 0} exp(H(z - z₀)) W(w₁, w₂)(z)` is constant across the
preconnected slit punctured disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}` (`0 < r`). -/
private theorem abel_liouville_wronskian_const {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {f g w₁ w₂ : ℂ → ℂ} {fs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hw₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hsol₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (hw₂ : DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hsol₂ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0) :
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    let F : ℂ → ℂ := fun z =>
      (z - z₀) ^ fs 0 * cexp (H (z - z₀)) * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z)
    ∀ z₁ z₂, z₁ ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} →
      z₂ ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} → F z₁ = F z₂ := by
  intro H F
  set U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
  have hopen : IsOpen U := isOpen_slitBall z₀ r
  have hconn : IsPreconnected U := by
    have hu₀_ball : (((r / 2 : ℝ) : ℂ)) ∈ ball (0 : ℂ) r := by
      simp [abs_of_pos hr, half_lt_self hr]
    have hstar0 : StarConvex ℝ ((r / 2 : ℝ) : ℂ) (slitPlane ∩ ball (0 : ℂ) r) :=
      (Complex.starConvex_ofReal_slitPlane (half_pos hr)).inter
        ((convex_ball (0 : ℂ) r).starConvex hu₀_ball)
    have hconn0 : IsPreconnected (slitPlane ∩ ball (0 : ℂ) r) :=
      (hstar0.isPathConnected ⟨Complex.ofReal_mem_slitPlane.mpr (half_pos hr),
        hu₀_ball⟩).isConnected.isPreconnected
    have himg : (fun u : ℂ => u + z₀) '' (slitPlane ∩ ball (0 : ℂ) r) = U := by
      ext z; constructor
      · rintro ⟨u, ⟨hus, hub⟩, rfl⟩; exact ⟨by simpa using hus, by simpa using hub⟩
      · rintro ⟨hzs, hzb⟩; exact ⟨z - z₀, ⟨hzs, by simpa using hzb⟩, sub_add_cancel z z₀⟩
    rw [← himg]
    exact hconn0.image _ (continuous_id.add continuous_const).continuousOn
  obtain ⟨_, _, hH_deriv⟩ := hasDerivAt_regularSingular_integratingExponent hr hf
  have hF_deriv : ∀ z ∈ U, HasDerivAt F 0 z := by
    rintro z ⟨hzs, hzb⟩
    have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
    have hmem : U ∈ 𝓝 z := hopen.mem_nhds ⟨hzs, hzb⟩
    have hd1 : HasDerivAt w₁ (deriv w₁ z) z := (hw₁.differentiableAt hmem).hasDerivAt
    have hd2 : HasDerivAt w₂ (deriv w₂ z) z := (hw₂.differentiableAt hmem).hasDerivAt
    have hdd1 : HasDerivAt (deriv w₁) (deriv (deriv w₁) z) z :=
      ((hw₁.deriv hopen).differentiableAt hmem).hasDerivAt
    have hdd2 : HasDerivAt (deriv w₂) (deriv (deriv w₂) z) z :=
      ((hw₂.deriv hopen).differentiableAt hmem).hasDerivAt
    have hW : HasDerivAt (fun w => w₁ w * deriv w₂ w - deriv w₁ w * w₂ w)
        (-f z * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z)) z :=
      (((hd1.mul hdd2).sub (hdd1.mul hd2)).congr_deriv (by
        linear_combination w₁ z * hsol₂ z hzs hzb - w₂ z * hsol₁ z hzs hzb))
    have hsub : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
    have hpow := hsub.cpow_const (c := fs 0) hzs
    have hexp := (hH_deriv z (norm_pos_iff.mpr hzu0) hzb).cexp
    have hcpow_split : (z - z₀) ^ fs 0 = (z - z₀) ^ (fs 0 - 1) * (z - z₀) := by
      conv_lhs => rw [show fs 0 = fs 0 - 1 + 1 by ring]
      rw [Complex.cpow_add _ _ hzu0, Complex.cpow_one]
    refine ((hpow.mul hexp).mul hW).congr_deriv ?_
    simp only [Pi.mul_apply]
    rw [hcpow_split]
    field_simp [hzu0]
    ring
  exact fun z₁ z₂ hz₁ hz₂ => hopen.is_const_of_deriv_eq_zero hconn
    (fun z hz => (hF_deriv z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF_deriv z hz).deriv) hz₁ hz₂

/-- Unified Abel–Liouville Wronskian evaluation for any pair of solutions of the form
`w₁(z) = (z - z₀)^{α₁} ∑ a_s (z - z₀)^s` and
`w₂(z) = (z - z₀)^{α₂} ∑ b_s (z - z₀)^s + c * w₁(z) * log(z - z₀)` when `α₁ + α₂ = 1 - fs 0`
and either `c = 0` or `α₁ - α₂ = N`. -/
private theorem abel_liouville_wronskian_ansatz_eq {z₀ α₁ α₂ c : ℂ} {N : ℕ} {r : ℝ}
    {f g : ℂ → ℂ} {fs gs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hvieta : α₁ + α₂ = 1 - fs 0)
    (hcN : c = 0 ∨ α₁ - α₂ = N)
    (ha_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    (hb_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b s * (z - z₀) ^ s)
    (hw₁_sol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      let w₁ := fun w => (w - z₀) ^ α₁ * ∑' s, a s * (w - z₀) ^ s
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (hw₂_sol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      let w₁ := fun w => (w - z₀) ^ α₁ * ∑' s, a s * (w - z₀) ^ s
      let w₂ := fun w =>
        (w - z₀) ^ α₂ * (∑' s, b s * (w - z₀) ^ s) + c * w₁ w * Complex.log (w - z₀)
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0) :
    let w₁ : ℂ → ℂ := fun z => (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s
    let w₂ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) + c * w₁ z * Complex.log (z - z₀)
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      (z - z₀) ^ fs 0 * cexp (H (z - z₀)) * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z) =
        (α₂ - α₁) * a 0 * b 0 + c * (0 : ℂ) ^ N * a 0 ^ 2 := by
  intro w₁ w₂ H z hzs hzb
  have hr : 0 < r := (norm_nonneg (z - z₀)).trans_lt hzb
  obtain ⟨hw₁_diff, hw₁_d1, _, _⟩ := hasDerivAt_and_operator_cpow_mul_tsum (σ := α₁) hf hg ha_sum
  obtain ⟨hψ_diff, hψ_d1, _, _⟩ := hasDerivAt_and_operator_cpow_mul_tsum (σ := α₂) hf hg hb_sum
  obtain ⟨hΦ_diff, hΦ_d1, _⟩ := hasDerivAt_and_operator_mul_log hw₁_diff hw₁_sol
  set A₁ : ℂ → ℂ := fun u => ∑' s, a s * u ^ s
  set B : ℂ → ℂ := fun u => ∑' s, b s * u ^ s
  have hw₂_eq : w₂ =
      ((fun w => (w - z₀) ^ α₂ * B (w - z₀)) +
        fun w => c * ((w - z₀) ^ α₁ * A₁ (w - z₀) * Complex.log (w - z₀))) := by
    ext w; simp only [Pi.add_apply, w₂, w₁, A₁, B]; ring
  have hw₂_diff : DifferentiableOn ℂ w₂ {w | w - z₀ ∈ slitPlane ∧ ‖w - z₀‖ < r} := by
    rw [hw₂_eq]; exact hψ_diff.add (hΦ_diff.const_mul c)
  have hconst := abel_liouville_wronskian_const hr hf hw₁_diff hw₁_sol hw₂_diff hw₂_sol
  obtain ⟨hH0, hH_cont, _⟩ := hasDerivAt_regularSingular_integratingExponent hr hf
  have hA₁_an := analyticOnNhd_tsum_of_summable hr a ha_sum
  have hB_an := analyticOnNhd_tsum_of_summable hr b hb_sum
  have hA₁0 : A₁ 0 = a 0 := by
    dsimp [A₁]; rw [tsum_eq_single 0]; · simp
    · intro s hs; simp [zero_pow hs]
  have hB0 : B 0 = b 0 := by
    dsimp [B]; rw [tsum_eq_single 0]; · simp
    · intro s hs; simp [zero_pow hs]
  set G : ℂ → ℂ := fun u =>
    cexp (H u) * ((α₂ - α₁) * A₁ u * B u + u * (A₁ u * deriv B u - deriv A₁ u * B u) +
      c * u ^ N * A₁ u ^ 2)
  have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hG_cont0 : ContinuousAt G 0 :=
    (Complex.continuous_exp.continuousAt.comp (hH_cont.continuousAt (ball_mem_nhds 0 hr))).mul
      ((((continuousAt_const.mul (hA₁_an 0 h0_mem).continuousAt).mul
            (hB_an 0 h0_mem).continuousAt).add
          (continuousAt_id.mul
            (((hA₁_an 0 h0_mem).continuousAt.mul (hB_an.deriv 0 h0_mem).continuousAt).sub
              ((hA₁_an.deriv 0 h0_mem).continuousAt.mul (hB_an 0 h0_mem).continuousAt)))).add
        ((continuousAt_const.mul (continuousAt_id.pow N)).mul
          ((hA₁_an 0 h0_mem).continuousAt.pow 2)))
  have hG0 : G 0 = (α₂ - α₁) * a 0 * b 0 + c * (0 : ℂ) ^ N * a 0 ^ 2 := by
    dsimp [G, H] at hH0 ⊢
    rw [hH0, Complex.exp_zero, one_mul, hA₁0, hB0, zero_mul, add_zero]
  have hFG : ∀ t ∈ Ioo (0 : ℝ) r,
      (z - z₀) ^ fs 0 * cexp (H (z - z₀)) * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z) =
        G (t : ℂ) := by
    rintro t ⟨ht0, htr⟩
    have hts : ((t : ℝ) : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr ht0
    have htb : ‖((t : ℝ) : ℂ)‖ < r := by simpa [abs_of_pos ht0] using htr
    have ht_ne : ((t : ℝ) : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hts
    have hpt : z₀ + (t : ℂ) ∈ {w | w - z₀ ∈ slitPlane ∧ ‖w - z₀‖ < r} :=
      ⟨by simpa using hts, by simpa using htb⟩
    have hstep := hconst z (z₀ + t) ⟨hzs, hzb⟩ hpt
    dsimp only [H] at hstep ⊢
    rw [hstep]
    have hdw₁ : deriv w₁ (z₀ + t) =
        (t : ℂ) ^ (α₁ - 1) * (α₁ * A₁ t + t * deriv A₁ t) := by
      simpa [w₁, A₁] using (hw₁_d1 (z₀ + t) hpt).deriv
    have hdw₂ : deriv w₂ (z₀ + t) =
        (t : ℂ) ^ (α₂ - 1) * (α₂ * B t + t * deriv B t) +
          c * (deriv w₁ (z₀ + t) * Complex.log t + (t : ℂ)⁻¹ * w₁ (z₀ + t)) := by
      have hd_sum := ((hψ_d1 (z₀ + t) hpt).add ((hΦ_d1 (z₀ + t) hpt).const_mul c)).deriv
      rw [hw₂_eq, hd_sum]
      simp [B, w₁, A₁]
    rw [hdw₂, hdw₁]
    dsimp only [w₁, w₂, A₁, B, G]
    simp only [add_sub_cancel_left]
    have hp1 : (t : ℂ) ^ fs 0 * ((t : ℂ) ^ α₁ * (t : ℂ) ^ (α₂ - 1)) = 1 := by
      rw [← Complex.cpow_add _ _ ht_ne, ← Complex.cpow_add _ _ ht_ne,
        show fs 0 + (α₁ + (α₂ - 1)) = 0 by linear_combination hvieta, Complex.cpow_zero]
    have hp2 : (t : ℂ) ^ fs 0 * ((t : ℂ) ^ (α₁ - 1) * (t : ℂ) ^ α₂) = 1 := by
      rw [← Complex.cpow_add _ _ ht_ne, ← Complex.cpow_add _ _ ht_ne,
        show fs 0 + (α₁ - 1 + α₂) = 0 by linear_combination hvieta, Complex.cpow_zero]
    have hc_pow : c * ((t : ℂ) ^ fs 0 * ((t : ℂ)⁻¹ * ((t : ℂ) ^ α₁ * (t : ℂ) ^ α₁))) =
        c * (t : ℂ) ^ N := by
      rcases hcN with rfl | hdiff
      · simp
      · congr 1
        rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ ht_ne, ← Complex.cpow_add _ _ ht_ne,
          ← Complex.cpow_add _ _ ht_ne, ← Complex.cpow_natCast]
        congr 1; linear_combination hvieta + hdiff
    have hW_simp : ((t : ℂ) ^ α₁ * A₁ t) *
          ((t : ℂ) ^ (α₂ - 1) * (α₂ * B t + t * deriv B t) +
            c * (((t : ℂ) ^ (α₁ - 1) * (α₁ * A₁ t + t * deriv A₁ t)) * Complex.log t +
              (t : ℂ)⁻¹ * ((t : ℂ) ^ α₁ * A₁ t))) -
        ((t : ℂ) ^ (α₁ - 1) * (α₁ * A₁ t + t * deriv A₁ t)) *
          ((t : ℂ) ^ α₂ * B t + c * ((t : ℂ) ^ α₁ * A₁ t) * Complex.log t) =
        ((t : ℂ) ^ α₁ * (t : ℂ) ^ (α₂ - 1)) * (A₁ t * (α₂ * B t + t * deriv B t)) -
          ((t : ℂ) ^ (α₁ - 1) * (t : ℂ) ^ α₂) * ((α₁ * A₁ t + t * deriv A₁ t) * B t) +
          c * ((t : ℂ)⁻¹ * ((t : ℂ) ^ α₁ * (t : ℂ) ^ α₁)) * A₁ t ^ 2 := by ring
    rw [hW_simp]
    linear_combination
      cexp (H t) * (A₁ t * (α₂ * B t + t * deriv B t)) * hp1 -
        cexp (H t) * ((α₁ * A₁ t + t * deriv A₁ t) * B t) * hp2 +
        cexp (H t) * A₁ t ^ 2 * hc_pow
  exact tendsto_nhds_unique
    (tendsto_const_nhds.congr' (by filter_upwards [Ioo_mem_nhdsGT hr] with t ht; exact hFG t ht))
    (hG0 ▸ hG_cont0.tendsto.comp
      ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds))

/-- **Abel–Liouville Wronskian formula** in the non-resonant case: for the normalized solutions
`w₁`, `w₂` attached to the two indicial roots `α₁`, `α₂`,
`(z - z₀)^{fs 0} exp(H(z - z₀)) (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z) = α₂ - α₁` at every point
of the slit punctured disc, where `H(u) = ∑_{s ≥ 1} (fs s / s) u^s`. -/
theorem wronskian_regularSingular_eq {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0)
    (hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0) :
    let w₁ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₁ * ∑' s, regularSingularCoeff fs gs α₁ s * (z - z₀) ^ s
    let w₂ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₂ * ∑' s, regularSingularCoeff fs gs α₂ s * (z - z₀) ^ s
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      (z - z₀) ^ fs 0 * cexp (H (z - z₀)) * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z) =
        α₂ - α₁ := by
  intro w₁ w₂ H z hzs hzb
  obtain ⟨ha₁_sum, _, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact]) hres₁
  obtain ⟨ha₂_sum, _, hw₂_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact]) hres₂
  have hId := abel_liouville_wronskian_ansatz_eq (c := 0) (N := 1) hf hg
    (indicialPoly_eq_mul_sub_iff.mp hfact).1 (Or.inl rfl) ha₁_sum ha₂_sum hw₁_sol
    (fun w hws hwb => by simpa using hw₂_sol w hws hwb) z hzs hzb
  simpa [w₁, w₂, H] using hId

/-- When `α₁ - α₂ ∉ ℕ`, the two series solutions attached to `α₁` and `α₂` have nowhere-vanishing
Wronskian on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_ne_zero {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hre : α₂.re ≤ α₁.re)
    (hnat : ∀ N : ℕ, α₁ - α₂ ≠ N) :
    let w₁ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₁ * ∑' s, regularSingularCoeff fs gs α₁ s * (z - z₀) ^ s
    let w₂ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₂ * ∑' s, regularSingularCoeff fs gs α₂ s * (z - z₀) ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  intro w₁ w₂ z hzs hzb hw0
  have hId := wronskian_regularSingular_eq hf hg hfact
    (fun _ hs => indicialPoly_add_nat_ne_zero_of_re_le hfact hre hs)
    (fun _ hs => indicialPoly_add_nat_ne_zero_of_sub_ne_nat hfact hnat hs)
    z hzs hzb
  rw [hw0, mul_zero] at hId
  exact hnat 0 (by simp only [Nat.cast_zero]; linear_combination hId)

/-- **Abel–Liouville Wronskian formula** in the resonant/logarithmic case `α₁ - α₂ = N ∈ ℕ`:
`(z - z₀)^{fs 0} exp(H(z - z₀)) (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z)` equals `1` if `N = 0`
and `-N` if `N ≥ 1`. -/
theorem wronskian_regularSingular_second_eq {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    let a := regularSingularCoeff fs gs α₁
    let b := regularSingularSecondCoeff fs gs α₂ N
    let c := regularSingularLogMultiplier fs gs α₂ N
    let w₁ : ℂ → ℂ := fun z => (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s
    let w₂ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) + c * w₁ z * Complex.log (z - z₀)
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      (z - z₀) ^ fs 0 * cexp (H (z - z₀)) * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z) =
        if N = 0 then 1 else -(N : ℂ) := by
  intro a b c w₁ w₂ H z hzs hzb
  have hre : α₂.re ≤ α₁.re := by
    rw [show α₁ = α₂ + N by linear_combination hdiff]; simp
  obtain ⟨ha_sum, _, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact hre hs
  obtain ⟨hb_sum, _, hw₂_sol⟩ := regularSingular_second_solution hf hg hfact hdiff
  have hId := abel_liouville_wronskian_ansatz_eq (c := c) (N := N) hf hg
    (indicialPoly_eq_mul_sub_iff.mp hfact).1 (Or.inr hdiff) ha_sum hb_sum hw₁_sol hw₂_sol z hzs hzb
  rw [show α₂ - α₁ = -(N : ℂ) by linear_combination -hdiff] at hId
  rcases eq_or_ne N 0 with rfl | hN0
  · simpa [a, b, c, w₁, w₂, H] using hId
  · simpa [a, b, c, w₁, w₂, H, hN0,
      regularSingularSecondCoeff_zero_of_pos fs gs α₂ (Nat.pos_of_ne_zero hN0),
      zero_pow hN0] using hId

/-- When `α₁ - α₂ = N ∈ ℕ`, the primary series solution `w₁` and the second solution `w₂` have
nowhere-vanishing Wronskian on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_second_ne_zero {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    let a := regularSingularCoeff fs gs α₁
    let b := regularSingularSecondCoeff fs gs α₂ N
    let c := regularSingularLogMultiplier fs gs α₂ N
    let w₁ : ℂ → ℂ := fun z => (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s
    let w₂ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) + c * w₁ z * Complex.log (z - z₀)
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  intro a b c w₁ w₂ z hzs hzb hw0
  have hId := wronskian_regularSingular_second_eq hf hg hfact hdiff z hzs hzb
  rw [hw0, mul_zero] at hId
  rcases eq_or_ne N 0 with rfl | hN0
  · simp at hId
  · simp [hN0] at hId

/-- **Existence of a fundamental pair at every regular singularity**: on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, `w'' + f w' + g w = 0` always possesses two holomorphic
solutions with nowhere-vanishing Wronskian. -/
theorem exists_regularSingular_fundamental_pair {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z)) :
    ∃ w₁ w₂ : ℂ → ℂ,
      DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      (∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0) ∧
      (∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0) ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  obtain ⟨α₁, α₂, hre, hfact⟩ := exists_indicialPoly_roots (fs 0) (gs 0)
  obtain ⟨_, hw₁_diff, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun _ hs => indicialPoly_add_nat_ne_zero_of_re_le hfact hre hs
  by_cases hnat : ∃ N : ℕ, α₁ - α₂ = N
  · obtain ⟨N, hN⟩ := hnat
    obtain ⟨_, hw₂_diff, hw₂_sol⟩ := regularSingular_second_solution hf hg hfact hN
    exact ⟨_, _, hw₁_diff, hw₂_diff, hw₁_sol, hw₂_sol,
      wronskian_regularSingular_second_ne_zero hf hg hfact hN⟩
  · have hnat' : ∀ N : ℕ, α₁ - α₂ ≠ N := not_exists.mp hnat
    obtain ⟨_, hw₂_diff, hw₂_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
      fun _ hs => indicialPoly_add_nat_ne_zero_of_sub_ne_nat hfact hnat' hs
    exact ⟨_, _, hw₁_diff, hw₂_diff, hw₁_sol, hw₂_sol,
      wronskian_regularSingular_ne_zero hf hg hfact hre hnat'⟩

/-! ### Worked example: Euler–Cauchy equation `w'' - 2 z⁻² w = 0` at `z₀ = 0` -/

/-- For `f = 0` and `g(z) = -2 z⁻²` at `z₀ = 0` (`f₀ = 0`, `g₀ = -2`), the indicial polynomial
factors as `(α - 2)(α + 1)` with roots `2` and `-1` differing by `N = 3`, all higher series
coefficients vanish, the logarithmic multiplier `c` is `0`, the primary solution on `slitPlane`
is `z²`, and the second solution is `z⁻¹`. -/
theorem eulerCauchy_two_neg_one_example :
    let fs : ℕ → ℂ := 0
    let gs : ℕ → ℂ := Pi.single 0 (-2)
    (∀ α, indicialPoly (fs 0) (gs 0) α = (α - 2) * (α - (-1))) ∧
      (∀ s : ℕ, 1 ≤ s → regularSingularCoeff fs gs 2 s = 0) ∧
      regularSingularLogMultiplier fs gs (-1) 3 = 0 ∧
      (∀ s : ℕ, 1 ≤ s → regularSingularSecondCoeff fs gs (-1) 3 s = 0) ∧
      (∀ z ∈ slitPlane,
        (z ^ (2 : ℂ) * ∑' s, regularSingularCoeff fs gs 2 s * z ^ s) = z ^ 2) ∧
      ∀ z ∈ slitPlane,
        (z ^ (-1 : ℂ) * (∑' s, regularSingularSecondCoeff fs gs (-1) 3 s * z ^ s) +
          regularSingularLogMultiplier fs gs (-1) 3 *
            (z ^ (2 : ℂ) * ∑' s, regularSingularCoeff fs gs 2 s * z ^ s) * Complex.log z) =
          z⁻¹ := by
  intro fs gs
  have hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - 2) * (α - (-1)) := fun α => by
    simp only [indicialPoly_def, fs, gs, Pi.zero_apply, Pi.single_eq_same]; ring
  have hconv0 (σ : ℂ) (d : ℕ → ℂ) (m : ℕ) :
      (∑ k ∈ range m, ((σ + (k : ℂ)) * fs (m - k) + gs (m - k)) * d k) = 0 :=
    sum_eq_zero fun k hk => by
      have hmk : m - k ≠ 0 := by have := mem_range.mp hk; omega
      simp [fs, gs, Pi.single_eq_of_ne hmk]
  have ha_zero : ∀ s : ℕ, 1 ≤ s → regularSingularCoeff fs gs 2 s = 0 := fun s hs => by
    rw [regularSingularCoeff_of_ne_zero fs gs 2 (by omega), hconv0, mul_zero]
  have hc_zero : regularSingularLogMultiplier fs gs (-1) 3 = 0 := by
    rw [regularSingularLogMultiplier_of_ne_zero fs gs (-1) (by decide), hconv0, mul_zero]
  have hb_zero : ∀ s : ℕ, 1 ≤ s → regularSingularSecondCoeff fs gs (-1) 3 s = 0 := by
    intro s hs
    rcases lt_trichotomy s 3 with hs3 | rfl | hs3
    · rw [regularSingularSecondCoeff_eq_regularSingularCoeff_of_lt fs gs (-1) hs3,
        regularSingularCoeff_of_ne_zero fs gs (-1) (by omega), hconv0, mul_zero]
    · exact regularSingularSecondCoeff_self fs gs (-1) 3
    · have hfact' : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (-1 + (3 : ℕ))) * (α - (-1)) :=
        fun α => by push_cast; simpa [show (-1 : ℂ) + 3 = 2 by norm_num] using hfact α
      have hQ := indicialPoly_add_nat_ne_zero_of_ne hfact' (by omega) hs3.ne'
      apply mul_left_cancel₀ hQ
      rw [indicialPoly_mul_regularSingularSecondCoeff_of_gt hs3 hQ, hc_zero, zero_mul, sub_zero,
        mul_zero, hconv0, neg_zero]
  refine ⟨hfact, ha_zero, hc_zero, hb_zero, fun z _ => ?_, fun z _ => ?_⟩
  · have htsum : (∑' s, regularSingularCoeff fs gs 2 s * z ^ s) = 1 := by
      rw [tsum_eq_single 0]; · simp
      · intro s hs; simp [ha_zero s (Nat.pos_of_ne_zero hs)]
    rw [htsum, mul_one]; exact Complex.cpow_natCast z 2
  · have htsum : (∑' s, regularSingularSecondCoeff fs gs (-1) 3 s * z ^ s) = 1 := by
      rw [tsum_eq_single 0]; · simp
      · intro s hs; simp [hb_zero s (Nat.pos_of_ne_zero hs)]
    rw [htsum, hc_zero, zero_mul, zero_mul, add_zero, mul_one, Complex.cpow_neg_one]

end TauCeti
