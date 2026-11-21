/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Convergent series solutions at a regular singularity

Let `f` and `g` be complex functions around `z₀` such that `(z - z₀) f(z) = ∑ f_s (z - z₀)^s`
and `(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` converge on a punctured disc `0 < ‖z - z₀‖ < r`, and let
`Q(α) = TauCeti.indicialPoly (fs 0) (gs 0) α = α(α - 1) + f₀ α + g₀ = (α - α₁)(α - α₂)` be the
indicial polynomial with roots ordered so that `Re α₂ ≤ Re α₁`. On the slit punctured disc
`{z | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}`, using principal complex powers and the principal
logarithm:
* `TauCeti.hasDerivAt_cpow_mul_tsum` differentiates `(z - z₀)^σ ∑ c_s (z - z₀)^s` on the slit disc,
  and `TauCeti.eq_zero_of_cpow_mul_tsum_eq_zero` gives branch-cut power-series uniqueness.
* For any root `ρ` of `Q` and any sequence `a` satisfying the two-coefficient indicial convolution
  recursion, `∑ a_s (z - z₀)^s` converges on the full open disc `‖z - z₀‖ < r`, and
  `w(z) = (z - z₀)^ρ ∑ a_s (z - z₀)^s` is a holomorphic solution of `w'' + f w' + g w = 0` on the
  slit punctured disc (`TauCeti.regularSingular_solution`). Whenever `Q(ρ + s) ≠ 0` for all `s ≥ 1`,
  this applies to `TauCeti.regularSingularCoeff` (`TauCeti.regularSingularCoeff_solution`), which is
  uniquely determined by the equation (`TauCeti.eq_regularSingularCoeff_of_solution`).
* When `α₁ - α₂ = N ∈ ℕ`, there is a second holomorphic solution
  `w₂(z) = (z - z₀)^{α₂} ∑ b_s (z - z₀)^s + c w₁(z) log(z - z₀)` with `b_N = 0`, normalized by
  `c = 1` when `N = 0` and `b₀ = 1` when `N ≥ 1`, where `∑ b_s (z - z₀)^s` converges on the whole
  disc `‖z - z₀‖ < r` (`TauCeti.regularSingular_second_solution`), and both `b` and `c` are
  uniquely determined (`TauCeti.eq_regularSingularSecondCoeff_of_solution`).
* A worked example at the end verifies the Euler–Cauchy equation `w'' - 2 z⁻² w = 0` at `z₀ = 0`,
  where the indicial roots are `2` and `-1` (`N = 3`), `c = 0`, and the canonical solutions reduce
  to `z²` and `z⁻¹`.

Abel–Liouville Wronskian formulas, nonvanishing, and fundamental pair existence are proved in
`TauCeti.Analysis.ODE.Complex.RegularSingularity.Wronskian`.

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

private theorem cpow_eq_cpow_sub_one_mul {u : ℂ} (hu : u ≠ 0) (σ : ℂ) :
    u ^ σ = u ^ (σ - 1) * u := by
  rw [Complex.cpow_sub _ _ hu, Complex.cpow_one, div_mul_cancel₀ _ hu]

private theorem cpow_eq_cpow_sub_two_mul_sq {u : ℂ} (hu : u ≠ 0) (σ : ℂ) :
    u ^ σ = u ^ (σ - 2) * u ^ 2 := by
  rw [Complex.cpow_sub _ _ hu, Complex.cpow_two, div_mul_cancel₀ _ (pow_ne_zero 2 hu)]

private theorem hasFPowerSeriesOnBall_of_punctured {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (c : ℕ → ℂ)
    (hc : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s) :
    HasFPowerSeriesOnBall (fun u : ℂ => ∑' s, c s * u ^ s)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 (ENNReal.ofReal r) :=
  FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_summable c
    (ENNReal.ofReal_pos.mpr hr) fun u hu0 hur => by
      simpa using hc (z₀ + u) (by simpa using hu0) (by simpa using eNorm_lt_ofReal_iff.mp hur)

private theorem analyticOnNhd_tsum_of_summable {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (c : ℕ → ℂ)
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s) :
    AnalyticOnNhd ℂ (fun u : ℂ => ∑' s, c s * u ^ s) (ball 0 r) :=
  Metric.eball_ofReal (x := (0 : ℂ)) (ε := r) ▸
    (hasFPowerSeriesOnBall_of_punctured hr c fun z _ hzr => hc z hzr).analyticOnNhd

private theorem exists_norm_mul_pow_le_of_punctured {z₀ : ℂ} {r ρ : ℝ} (hρ0 : 0 < ρ) (hρr : ρ < r)
    (c : ℕ → ℂ)
    (hc : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℕ, ‖c s‖ * ρ ^ s ≤ M := by
  have hrad := (hasFPowerSeriesOnBall_of_punctured (hρ0.trans hρr) c hc).r_le
  lift ρ to ℝ≥0 using hρ0.le
  obtain ⟨M, hM, hMb⟩ := (FormalMultilinearSeries.ofScalars ℂ c).norm_mul_pow_le_of_lt_radius
    ((ENNReal.coe_lt_ofReal.mpr hρr).trans_le hrad)
  exact ⟨M, hM, fun s => by simpa [FormalMultilinearSeries.ofScalars_norm] using hMb s⟩

private theorem sum_range_succ_mul_pow (p q : ℕ → ℂ) (u : ℂ) (s : ℕ) :
    (∑ k ∈ range (s + 1), (p k * u ^ k) * (q (s - k) * u ^ (s - k))) =
      ((∑ k ∈ range s, p k * q (s - k)) + p s * q 0) * u ^ s := by
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, add_mul, Finset.sum_mul]
  refine congrArg₂ (· + ·) (sum_congr rfl fun k hk => ?_) (by ring)
  have hpow : u ^ k * u ^ (s - k) = u ^ s := by
    rw [← pow_add, Nat.add_sub_of_le (mem_range.mp hk).le]
  linear_combination p k * q (s - k) * hpow

/-- Lower bound `s² / 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖` for sufficiently large `s : ℕ`. -/
private theorem exists_sq_div_two_le_norm_indicialPoly (f₀ g₀ σ : ℂ) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖ := by
  set B : ℝ := ‖2 * σ + f₀ - 1‖ + ‖indicialPoly f₀ g₀ σ‖
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B + 1)
  refine ⟨max N 1, le_max_right _ _, fun s hs => ?_⟩
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (le_max_right N 1).trans hs
  have hNs : (N : ℝ) ≤ s := by exact_mod_cast (le_max_left N 1).trans hs
  have htri : (s : ℝ) ^ 2 ≤ ‖indicialPoly f₀ g₀ (σ + s)‖ +
      ‖(2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ‖ := by
    have h := norm_sub_le (indicialPoly f₀ g₀ (σ + s))
      ((2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ)
    rwa [show indicialPoly f₀ g₀ (σ + s) - ((2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ) =
      (s : ℂ) ^ 2 by rw [indicialPoly_add]; ring, norm_pow, Complex.norm_natCast] at h
  have hrem : ‖(2 * σ + f₀ - 1) * (s : ℂ) + indicialPoly f₀ g₀ σ‖ ≤ B * s := by
    have h := norm_add_le ((2 * σ + f₀ - 1) * (s : ℂ)) (indicialPoly f₀ g₀ σ)
    rw [norm_mul, Complex.norm_natCast] at h
    nlinarith [norm_nonneg (indicialPoly f₀ g₀ σ)]
  nlinarith [hs1, hNs, hN, htri, hrem]

/-- Discrete Grönwall polynomial-growth bound: if `μ s ≥ 0` and
`μ s ≤ (K / s) * (1 + ∑_{k < s} μ k)` for all `s ≥ s₀ ≥ 1`, then the partial sums grow at most
like `s ^ K`. -/
private theorem discrete_gronwall_poly_bound {μ : ℕ → ℝ} {s₀ K : ℕ} (hs₀1 : 1 ≤ s₀)
    (hμ0 : ∀ s, 0 ≤ μ s)
    (hstep : ∀ s : ℕ, s₀ ≤ s → μ s ≤ (K : ℝ) / s * (1 + ∑ k ∈ range s, μ k)) :
    ∀ s : ℕ, s₀ ≤ s → 1 + ∑ k ∈ range s, μ k ≤ (1 + ∑ k ∈ range s₀, μ k) * (s : ℝ) ^ K := by
  set S : ℕ → ℝ := fun s => 1 + ∑ k ∈ range s, μ k
  have hS_pos : ∀ s, 1 ≤ S s := fun s => by
    dsimp [S]; linarith [sum_nonneg fun k (_ : k ∈ range s) => hμ0 k]
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    nlinarith [hS_pos s₀, one_le_pow₀ (n := K) (show (1 : ℝ) ≤ s₀ by exact_mod_cast hs₀1)]
  | succ s hs ih =>
    have hs_pos : (0 : ℝ) < s := by exact_mod_cast (hs₀1.trans hs)
    have hpow_step : (s : ℝ) ^ K * (1 + (K : ℝ) / s) ≤ ((s + 1 : ℕ) : ℝ) ^ K := by
      rw [div_eq_mul_inv]
      refine (mul_le_mul_of_nonneg_left
        (one_add_mul_le_pow (by linarith [inv_nonneg.mpr hs_pos.le]) K) (by positivity)).trans_eq ?_
      rw [← mul_pow]; push_cast; rw [mul_add, mul_one, mul_inv_cancel₀ hs_pos.ne']
    have hSs : S (s + 1) = S s + μ s := by simp [S, sum_range_succ, add_assoc]
    calc S (s + 1) ≤ S s * (1 + (K : ℝ) / s) := by linarith [hSs, hstep s hs]
      _ ≤ (S s₀ * (s : ℝ) ^ K) * (1 + (K : ℝ) / s) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ S s₀ * ((s + 1 : ℕ) : ℝ) ^ K := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow_step (by linarith [hS_pos s₀])

/-- One-step majorant inequality for a perturbed indicial convolution recursion at radius
`ρ > 0`. -/
private theorem indicial_rec_step_bound {σ : ℂ} {ρ Mf Mg CE : ℝ} {fs gs d E : ℕ → ℂ} {s K : ℕ}
    (hρ_pos : 0 < ρ) (hMf_pos : 0 < Mf) (hMg_pos : 0 < Mg) (hCE0 : 0 ≤ CE) (hs1 : 1 ≤ s)
    (hMf : ∀ k, ‖fs k‖ * ρ ^ k ≤ Mf) (hMg : ∀ k, ‖gs k‖ * ρ ^ k ≤ Mg)
    (hCE : ‖E s‖ * ρ ^ s ≤ CE * (s + 1))
    (hK : 2 * ((Mf + Mg) * (‖σ‖ + 1) + 2 * CE) < K)
    (hQs : (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly (fs 0) (gs 0) (σ + s)‖)
    (hds : indicialPoly (fs 0) (gs 0) (σ + s) * d s =
      -(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s) :
    ‖d s‖ * ρ ^ s ≤ (K : ℝ) / s * (1 + ∑ k ∈ range s, ‖d k‖ * ρ ^ k) := by
  set C₁ : ℝ := (Mf + Mg) * (‖σ‖ + 1); set μ : ℕ → ℝ := fun k => ‖d k‖ * ρ ^ k
  set S : ℝ := 1 + ∑ k ∈ range s, μ k
  have hs_pos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hs_ge1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hμ_nn : ∀ k, 0 ≤ μ k := fun _ => by positivity
  have hsum_nn : 0 ≤ ∑ k ∈ range s, μ k := sum_nonneg fun k _ => hμ_nn k
  have hconv : (∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s) ≤
      (C₁ * s) * ∑ k ∈ range s, μ k := by
    rw [mul_sum]; refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt := mem_range.mp hk
    have hks : (k : ℝ) ≤ s := by exact_mod_cast hk_lt.le
    have hpow : ρ ^ s = ρ ^ (s - k) * ρ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_lt.le]
    have htri : ‖(σ + k) * fs (s - k) + gs (s - k)‖ ≤ (‖σ‖ + k) * ‖fs (s - k)‖ + ‖gs (s - k)‖ := by
      have h1 := norm_add_le ((σ + k) * fs (s - k)) (gs (s - k))
      have h2 := norm_add_le σ (k : ℂ)
      rw [norm_mul] at h1; rw [Complex.norm_natCast] at h2
      nlinarith [norm_nonneg (fs (s - k))]
    have hfgk : ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k) ≤ C₁ * s := by
      have hm := mul_le_mul_of_nonneg_right htri (pow_nonneg hρ_pos.le (s - k))
      have hMf' := hMf (s - k); have hMg' := hMg (s - k)
      dsimp only [C₁]; nlinarith [norm_nonneg σ, le_mul_of_one_le_right (norm_nonneg σ) hs_ge1]
    rw [norm_mul, hpow, show ‖(σ + k) * fs (s - k) + gs (s - k)‖ * ‖d k‖ * (ρ ^ (s - k) * ρ ^ k) =
      (‖(σ + k) * fs (s - k) + gs (s - k)‖ * ρ ^ (s - k)) * μ k by dsimp [μ]; ring]
    exact mul_le_mul_of_nonneg_right hfgk (hμ_nn k)
  have hrec : ‖indicialPoly (fs 0) (gs 0) (σ + s)‖ * μ s =
      ‖-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k) + E s‖ * ρ ^ s := by
    simpa [μ, norm_mul, mul_assoc] using congrArg (fun w => ‖w‖ * ρ ^ s) hds
  have htri_tot := mul_le_mul_of_nonneg_right
    (norm_add_le (-(∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k)) (E s))
    (pow_nonneg hρ_pos.le s)
  rw [norm_neg, add_mul] at htri_tot
  have hnorm_sum : ‖∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s ≤
      ∑ k ∈ range s, ‖((σ + k) * fs (s - k) + gs (s - k)) * d k‖ * ρ ^ s := by
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
  have hsum_le : C₁ * s * (∑ k ∈ range s, μ k) + CE * (s + 1) ≤ (C₁ + 2 * CE) * s * S := by
    dsimp only [S]
    nlinarith [show 0 ≤ C₁ by positivity, mul_nonneg hCE0 (mul_nonneg hs_pos.le hsum_nn),
      mul_le_mul_of_nonneg_left hs_ge1 hCE0]
  have hprod_le : ((s : ℝ) ^ 2 / 2) * μ s ≤ ((K : ℝ) / 2 * s) * S := by
    have h1 := (mul_le_mul_of_nonneg_right hQs (hμ_nn s)).trans_eq hrec
    have hK' : (C₁ + 2 * CE) * s * S ≤ ((K : ℝ) / 2 * s) * S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hs_pos.le)
        (by dsimp [S]; linarith)
    linarith [h1, htri_tot, hnorm_sum, hconv, hCE, hsum_le, hK']
  rw [div_mul_eq_mul_div, le_div_iff₀ hs_pos]; nlinarith [hprod_le, hs_pos]

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
  set ρ : ℝ := (‖z - z₀‖ + r) / 2
  have hρ_gt : ‖z - z₀‖ < ρ := by dsimp [ρ]; linarith
  have hρ_pos : 0 < ρ := (norm_nonneg _).trans_lt hρ_gt
  have hρ_lt : ρ < r := by dsimp [ρ]; linarith
  obtain ⟨Mf, hMf_pos, hMf⟩ := exists_norm_mul_pow_le_of_punctured hρ_pos hρ_lt fs hf
  obtain ⟨Mg, hMg_pos, hMg⟩ := exists_norm_mul_pow_le_of_punctured hρ_pos hρ_lt gs hg
  obtain ⟨CE, hCE0, hCE⟩ := hE ρ hρ_pos hρ_lt
  obtain ⟨s₂, hs₂1, hQ⟩ := exists_sq_div_two_le_norm_indicialPoly (fs 0) (gs 0) σ
  set s₀ : ℕ := max s₁ s₂; have hs₀1 : 1 ≤ s₀ := hs₂1.trans (le_max_right _ _)
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * ((Mf + Mg) * (‖σ‖ + 1) + 2 * CE))
  set μ : ℕ → ℝ := fun s => ‖d s‖ * ρ ^ s; set S₀ : ℝ := 1 + ∑ k ∈ range s₀, μ k
  have hμ0 : ∀ s, 0 ≤ μ s := fun _ => by positivity
  have hS₀_pos : 1 ≤ S₀ := by dsimp [S₀]; linarith [sum_nonneg fun k (_ : k ∈ range s₀) => hμ0 k]
  have hpoly := discrete_gronwall_poly_bound hs₀1 hμ0 fun s hs =>
    indicial_rec_step_bound hρ_pos hMf_pos hMg_pos hCE0 (hs₀1.trans hs) hMf hMg (hCE s) hK
      (hQ s ((le_max_right _ _).trans hs)) (hd s ((le_max_left _ _).trans hs))
  set q : ℝ := ‖z - z₀‖ / ρ; have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hρ_pos.le
  have hq1 : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0, div_lt_one hρ_pos]; exact hρ_gt
  refine Summable.of_norm_bounded_eventually_nat (f := fun s => d s * (z - z₀) ^ s)
    ((summable_pow_mul_geometric_of_norm_lt_one K hq1).mul_left (S₀ * 2 ^ K)) ?_
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (hs₀1.trans hs)
  have h2s : ((s + 1 : ℕ) : ℝ) ^ K ≤ 2 ^ K * (s : ℝ) ^ K := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) K
  have hμ_le : μ s ≤ S₀ * (2 ^ K * (s : ℝ) ^ K) :=
    ((show μ s ≤ 1 + ∑ k ∈ range (s + 1), μ k by
        rw [sum_range_succ]; linarith [sum_nonneg fun k (_ : k ∈ range s) => hμ0 k]).trans
      (hpoly (s + 1) (hs.trans (Nat.le_succ s)))).trans
      (mul_le_mul_of_nonneg_left h2s (by linarith))
  have hpow_z : ‖z - z₀‖ ^ s = ρ ^ s * q ^ s := by rw [← mul_pow, mul_div_cancel₀ _ hρ_pos.ne']
  rw [norm_mul, norm_pow, hpow_z, ← mul_assoc]
  calc μ s * q ^ s ≤ S₀ * (2 ^ K * (s : ℝ) ^ K) * q ^ s :=
        mul_le_mul_of_nonneg_right hμ_le (pow_nonneg hq0 s)
    _ = S₀ * 2 ^ K * ((s : ℝ) ^ K * q ^ s) := by ring

/-! ### Differential operator on `(z - z₀)^σ ∑ c_s (z - z₀)^s` and `w₁(z) log(z - z₀)` -/

/-- First derivative of `(z - z₀)^σ ∑' s, c s * (z - z₀)^s` on the slit punctured disc,
requiring only convergence of `∑ c_s (z - z₀)^s` on `‖z - z₀‖ < r`. -/
theorem hasDerivAt_cpow_mul_tsum {z₀ σ : ℂ} {r : ℝ} {c : ℕ → ℂ}
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    let A : ℂ → ℂ := fun u => ∑' s, c s * u ^ s
    HasDerivAt (fun w : ℂ => (w - z₀) ^ σ * A (w - z₀))
      ((z - z₀) ^ (σ - 1) * (σ * A (z - z₀) + (z - z₀) * deriv A (z - z₀))) z := by
  intro A
  have hr : 0 < r := (norm_nonneg _).trans_lt hzb
  have hA_diff := (analyticOnNhd_tsum_of_summable hr c hc (z - z₀)
    (mem_ball_zero_iff.mpr hzb)).differentiableAt
  have hpow := ((hasDerivAt_id z).sub_const z₀).cpow_const (c := σ) hzs
  refine (hpow.mul (hA_diff.hasDerivAt.comp_sub_const z z₀)).congr_deriv ?_
  dsimp only [id]; rw [cpow_eq_cpow_sub_one_mul (Complex.slitPlane_ne_zero hzs) σ]; ring

/-- Power-series identity for the indicial operator applied to `A(u) = ∑' s, c s * u ^ s` on
`‖u‖ < r`. -/
private theorem hasSum_operator_cpow_series {z₀ σ : ℂ} {r : ℝ} {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => gs s * (z - z₀) ^ s)
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    let A : ℂ → ℂ := fun w => ∑' s, c s * w ^ s
    HasSum (fun s : ℕ => (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
        ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s)
      ((u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) +
        (u * deriv A u + σ * A u) * (∑' s, fs s * u ^ s) +
        A u * (∑' s, gs s * u ^ s)) := by
  intro A
  have hr : 0 < r := (norm_nonneg u).trans_lt hu
  have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
  have hpA := hasFPowerSeriesOnBall_of_punctured hr c fun z _ hzr => hc z hzr
  have hpF := hasFPowerSeriesOnBall_of_punctured hr fs hf
  have hpG := hasFPowerSeriesOnBall_of_punctured hr gs hg
  have hc_norm : Summable fun s : ℕ => ‖c s * u ^ s‖ := by
    simpa using FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
      c (hue.trans_le hpA.r_le) 0
  have hsc_norm : Summable fun s : ℕ => ‖(s : ℂ) * c s * u ^ s‖ := by
    simpa using FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
      c (hue.trans_le hpA.r_le) 1
  have hf_norm : Summable fun s : ℕ => ‖fs s * u ^ s‖ := by
    simpa using FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
      fs (hue.trans_le hpF.r_le) 0
  have hg_norm : Summable fun s : ℕ => ‖gs s * u ^ s‖ := by
    simpa using FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
      gs (hue.trans_le hpG.r_le) 0
  have hA0 : HasSum (fun s : ℕ => c s * u ^ s) (A u) := by
    simpa using hpA.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv hue 0
  have hA1 : HasSum (fun s : ℕ => (s : ℂ) * c s * u ^ s) (u * deriv A u) := by
    simpa [iteratedDeriv_one] using hpA.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv hue 1
  have hA2 : HasSum (fun s : ℕ => (s : ℂ) * ((s : ℂ) - 1) * c s * u ^ s)
      (u ^ 2 * deriv (deriv A) u) := by
    have hraw := hpA.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv hue 2
    rw [show iteratedDeriv 2 A = deriv (deriv A) by simp [iteratedDeriv_succ], zero_add] at hraw
    refine hraw.congr_fun fun s => ?_
    rcases s with _ | s
    · simp
    · simp only [Nat.descFactorial_succ, Nat.add_sub_cancel, Nat.descFactorial_zero, mul_one]
      push_cast; ring
  have hσc_norm : Summable fun s : ℕ => ‖((σ + s) * c s) * u ^ s‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => by
      rw [show ((σ + s) * c s) * u ^ s = σ * (c s * u ^ s) + (s : ℂ) * c s * u ^ s by ring]
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul])) ((hc_norm.mul_left ‖σ‖).add hsc_norm)
  have hlead : HasSum (fun s : ℕ => (σ + s) * (σ + s - 1) * c s * u ^ s)
      (u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) :=
    (((hA2.add (hA1.mul_left (2 * σ))).add (hA0.mul_left (σ * (σ - 1)))).congr_fun fun _ => by ring)
  have hP_prod := hasSum_sum_range_mul_of_summable_norm hσc_norm hf_norm
  rw [((hA1.add (hA0.mul_left σ)).congr_fun fun _ => by ring).tsum_eq] at hP_prod
  refine ((hlead.add hP_prod).add (hasSum_sum_range_mul_of_summable_norm hc_norm hg_norm)).congr_fun
    fun s => ?_
  rw [sum_range_succ_mul_pow (fun k => (σ + k) * c k) fs u s, sum_range_succ_mul_pow c gs u s]
  have hsum_add : (∑ k ∈ range s, (σ + k) * c k * fs (s - k)) * u ^ s +
      (∑ k ∈ range s, c k * gs (s - k)) * u ^ s =
      (∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * u ^ s := by
    rw [← add_mul, ← sum_add_distrib]; exact congrArg (· * u ^ s) (sum_congr rfl fun _ _ => by ring)
  rw [indicialPoly_def]; linear_combination -hsum_add

/-- Operator evaluation for `ψ(z) = (z - z₀)^σ ∑' s, c s * (z - z₀)^s` on the slit punctured
disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
private theorem operator_cpow_mul_tsum_eq {z₀ σ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs c : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s => c s * (z - z₀) ^ s)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    let ψ : ℂ → ℂ := fun w => (w - z₀) ^ σ * ∑' s, c s * (w - z₀) ^ s
    deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z =
      (z - z₀) ^ (σ - 2) * ∑' s : ℕ,
        (indicialPoly (fs 0) (gs 0) (σ + s) * c s +
          ∑ k ∈ range s, ((σ + k) * fs (s - k) + gs (s - k)) * c k) * (z - z₀) ^ s := by
  intro ψ
  set A : ℂ → ℂ := fun u => ∑' s, c s * u ^ s; set u : ℂ := z - z₀
  have hr : 0 < r := (norm_nonneg u).trans_lt hzb
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hzs
  have han := analyticOnNhd_tsum_of_summable hr c hc
  have hA_diff := (han u (mem_ball_zero_iff.mpr hzb)).differentiableAt
  have hA'_diff := (han.deriv u (mem_ball_zero_iff.mpr hzb)).differentiableAt
  have hsub : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hinner := ((hA_diff.hasDerivAt.comp_sub_const z z₀).const_mul σ).add
    (hsub.mul (hA'_diff.hasDerivAt.comp_sub_const z z₀))
  have hev : deriv ψ =ᶠ[𝓝 z] ((fun w : ℂ => (w - z₀) ^ (σ - 1)) *
      ((fun w : ℂ => σ * A (w - z₀)) + (fun w : ℂ => w - z₀) * fun w : ℂ => deriv A (w - z₀))) := by
    filter_upwards [(isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r).mem_nhds ⟨hzs, hzb⟩]
      with w hw
    exact (hasDerivAt_cpow_mul_tsum hc hw.1 hw.2).deriv
  have hcpow1 : u ^ (σ - 1) = u ^ (σ - 2) * u := by
    simpa [show σ - 1 - 1 = σ - 2 by ring] using cpow_eq_cpow_sub_one_mul hu0 (σ - 1)
  have hcpow2 : u ^ σ = u ^ (σ - 2) * u ^ 2 := cpow_eq_cpow_sub_two_mul_sq hu0 σ
  have hderiv2 : deriv (deriv ψ) z =
      u ^ (σ - 2) * (u ^ 2 * deriv (deriv A) u + 2 * σ * (u * deriv A u) + σ * (σ - 1) * A u) := by
    rw [(((hsub.cpow_const (c := σ - 1) hzs).mul hinner).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.add_apply, Pi.mul_apply]; dsimp only [u] at hcpow1 ⊢
    rw [show σ - 1 - 1 = σ - 2 by ring, hcpow1]; ring
  have hop := hasSum_operator_cpow_series (σ := σ) (fun w hw0 hwr => (hf w hw0 hwr).summable)
    (fun w hw0 hwr => (hg w hw0 hwr).summable) hc hzb
  rw [hop.tsum_eq, (hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq,
    (hg z (norm_pos_iff.mpr hu0) hzb).tsum_eq, hderiv2, (hasDerivAt_cpow_mul_tsum hc hzs hzb).deriv]
  dsimp only [ψ, A, u]; rw [hcpow1, hcpow2]; ring

/-- Open-set linearity of first and second derivatives for `ψ + c * Φ`. -/
private theorem deriv_deriv_add_const_mul {U : Set ℂ} (hU : IsOpen U) {ψ Φ : ℂ → ℂ} (c : ℂ)
    (hψ : DifferentiableOn ℂ ψ U) (hΦ : DifferentiableOn ℂ Φ U) {z : ℂ} (hz : z ∈ U) :
    deriv (fun w => ψ w + c * Φ w) z = deriv ψ z + c * deriv Φ z ∧
      deriv (deriv (fun w => ψ w + c * Φ w)) z = deriv (deriv ψ) z + c * deriv (deriv Φ) z := by
  have hmem := hU.mem_nhds hz
  have hd1_ev : deriv (fun w => ψ w + c * Φ w) =ᶠ[𝓝 z] (deriv ψ + fun w => c * deriv Φ w) := by
    filter_upwards [hmem] with w hw
    exact ((hψ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.add
      ((hΦ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.const_mul c)).deriv
  exact ⟨hd1_ev.self_of_nhds,
    ((((hψ.deriv hU).differentiableAt hmem).hasDerivAt.add
      (((hΦ.deriv hU).differentiableAt hmem).hasDerivAt.const_mul c)).congr_of_eventuallyEq
        hd1_ev).deriv⟩

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
  have hopen : IsOpen U := isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  have hw₁_at : ∀ z ∈ U, DifferentiableAt ℂ w₁ z := fun z hz =>
    hw₁.differentiableAt (hopen.mem_nhds hz)
  have hderiv1 : ∀ z ∈ U,
      HasDerivAt Φ (deriv w₁ z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w₁ z) z := fun z hz =>
    ((hw₁_at z hz).hasDerivAt.mul (((hasDerivAt_id z).sub_const z₀).clog hz.1)).congr_deriv
      (by dsimp only [id]; rw [one_div]; ring)
  refine ⟨fun z hz => (hderiv1 z hz).differentiableAt.differentiableWithinAt, hderiv1, ?_⟩
  rintro z ⟨hzs, hzb⟩
  have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hsub : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hdw₁_at := ((hw₁.deriv hopen).differentiableAt (hopen.mem_nhds ⟨hzs, hzb⟩)).hasDerivAt
  have hev : deriv Φ =ᶠ[𝓝 z]
      (deriv w₁ * (fun w : ℂ => Complex.log (w - z₀)) + (fun w : ℂ => (w - z₀)⁻¹) * w₁) := by
    filter_upwards [hopen.mem_nhds ⟨hzs, hzb⟩] with w hw; exact (hderiv1 w hw).deriv
  have hd2 : deriv (deriv Φ) z = deriv (deriv w₁) z * Complex.log (z - z₀) +
      2 * (z - z₀)⁻¹ * deriv w₁ z - ((z - z₀) ^ 2)⁻¹ * w₁ z := by
    rw [(((hdw₁_at.mul (hsub.clog hzs)).add
      ((hsub.inv hzu0).mul (hw₁_at z ⟨hzs, hzb⟩).hasDerivAt)).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.inv_apply]; field_simp [hzu0]; ring
  rw [hd2, (hderiv1 z ⟨hzs, hzb⟩).deriv]; dsimp only [Φ]
  have hode := hsol₁ z hzs hzb; field_simp [hzu0]
  linear_combination (z - z₀) ^ 2 * Complex.log (z - z₀) * hode

/-- Analytic uniqueness for branch-cut power series: if `∑' s, d s * u ^ s` converges on
`0 < ‖u‖ < r` (`0 < r`) and `(z - z₀)^α ∑' s, d s * (z - z₀)^s = 0` on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, then every coefficient `d s` vanishes. -/
theorem eq_zero_of_cpow_mul_tsum_eq_zero {z₀ α : ℂ} {d : ℕ → ℂ} {r : ℝ}
    (hr : 0 < r) (hd : ∀ u : ℂ, u ≠ 0 → ‖u‖ < r → Summable fun s => d s * u ^ s)
    (hzero : ∀ z : ℂ, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      (z - z₀) ^ α * (∑' s, d s * (z - z₀) ^ s) = 0) :
    ∀ s : ℕ, d s = 0 := by
  have hp := FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_summable d
    (ENNReal.ofReal_pos.mpr hr) fun u hu0 hur => hd u hu0 (eNorm_lt_ofReal_iff.mp hur)
  set u₀ : ℂ := ((r / 2 : ℝ) : ℂ)
  have hu₀_ball : u₀ ∈ ball (0 : ℂ) r := by simp [u₀, abs_of_pos hr, half_lt_self hr]
  have hev : (fun u : ℂ => ∑' s, d s * u ^ s) =ᶠ[𝓝 u₀] 0 := by
    filter_upwards [(Complex.isOpen_slitPlane.inter Metric.isOpen_ball).mem_nhds
      ⟨Complex.ofReal_mem_slitPlane.mpr (half_pos hr), hu₀_ball⟩] with u ⟨hus, hub⟩
    have hz := hzero (z₀ + u) (by simpa using hus) (by simpa using hub)
    simp only [add_sub_cancel_left] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.slitPlane_ne_zero hus)))
  exact congrFun (hp.ofScalars_eq_zero_of_eventuallyEq_zero
    (Metric.eball_ofReal (x := (0 : ℂ)) (ε := r) ▸ (convex_ball (0 : ℂ) r).isPreconnected)
    (by rwa [Metric.eball_ofReal]) hev)

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
  have hsum := summable_of_perturbed_indicial_rec (σ := ρ) (d := a) (E := 0) (s₁ := 1)
    (fun z hz0 hzr => (hf z hz0 hzr).summable) (fun z hz0 hzr => (hg z hz0 hzr).summable)
    (fun _ _ _ => ⟨0, le_rfl, fun _ => by simp⟩) (fun s hs => by simp [ha s hs])
  refine ⟨hsum, fun z hz =>
      (hasDerivAt_cpow_mul_tsum hsum hz.1 hz.2).differentiableAt.differentiableWithinAt,
    fun z hzs hzb => ?_⟩
  rw [operator_cpow_mul_tsum_eq hf hg hsum hzs hzb]
  have hcoeff : ∀ s : ℕ, indicialPoly (fs 0) (gs 0) (ρ + s) * a s +
      ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k = 0 := fun s => by
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
  have hall := eq_zero_of_cpow_mul_tsum_eq_zero (z₀ := z₀) (α := ρ - 2) hr
    (fun u _ hu => (hasSum_operator_cpow_series (σ := ρ)
      (fun w hw0 hwr => (hf w hw0 hwr).summable)
      (fun w hw0 hwr => (hg w hw0 hwr).summable) hsum hu).summable)
    fun z hzs hzb => (operator_cpow_mul_tsum_eq hf hg hsum hzs hzb).symm.trans (hsol z hzs hzb)
  exact eq_regularSingularCoeff_of_rec hres ha0 fun s _ => by linear_combination hall s

/-! ### Second solution when the indicial roots differ by a natural number -/

/-- Shifted logarithmic forcing coefficients for `α₁ = α₂ + N`. -/
private def logForcingCoeff (fs a : ℕ → ℂ) (α₂ : ℂ) (N s : ℕ) : ℂ :=
  if s < N then 0
  else (2 * (α₂ + s) + fs 0 - 1) * a (s - N) + ∑ k ∈ range (s - N), fs (s - N - k) * a k

/-- Sub-radius linear growth bound for `logForcingCoeff fs a α₂ N`. -/
private theorem exists_norm_logForcingCoeff_mul_pow_le {z₀ α₂ : ℂ} {N : ℕ} {r ρ : ℝ}
    {fs a : ℕ → ℂ} (hρ0 : 0 < ρ) (hρr : ρ < r)
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (ha : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, ‖logForcingCoeff fs a α₂ N s‖ * ρ ^ s ≤ C * (s + 1) := by
  obtain ⟨Mf, hMf_pos, hMf⟩ := exists_norm_mul_pow_le_of_punctured hρ0 hρr fs hf
  obtain ⟨Ma, _, hMa⟩ := exists_norm_mul_pow_le_of_punctured hρ0 hρr a fun z _ hzr => ha z hzr
  set C : ℝ := ρ ^ N * ((2 * ‖α₂‖ + ‖fs 0 - 1‖ + 2) * Ma + Mf * Ma)
  refine ⟨C, by positivity, fun s => ?_⟩
  dsimp only [logForcingCoeff]; split_ifs with hsN
  · simp only [norm_zero, zero_mul]; positivity
  · have hsN' : N ≤ s := not_lt.mp hsN
    have hpow : ρ ^ s = ρ ^ N * ρ ^ (s - N) := by rw [← pow_add, Nat.add_sub_of_le hsN']
    have hcoef : ‖2 * (α₂ + s) + fs 0 - 1‖ ≤ (2 * ‖α₂‖ + ‖fs 0 - 1‖ + 2) * (s + 1) := by
      rw [show 2 * (α₂ + (s : ℂ)) + fs 0 - 1 = 2 * α₂ + (fs 0 - 1) + 2 * (s : ℂ) by ring]
      have h1 := norm_add_le (2 * α₂ + (fs 0 - 1)) (2 * (s : ℂ))
      have h2 := norm_add_le (2 * α₂) (fs 0 - 1); rw [norm_mul, Complex.norm_ofNat] at h2
      nlinarith [norm_nonneg α₂, norm_nonneg (fs 0 - 1), h1, h2,
        show ‖(2 : ℂ) * (s : ℂ)‖ = 2 * (s : ℝ) by simp]
    have h1 : ‖(2 * (α₂ + s) + fs 0 - 1) * a (s - N)‖ * ρ ^ (s - N) ≤
        (2 * ‖α₂‖ + ‖fs 0 - 1‖ + 2) * Ma * (s + 1) := by
      rw [norm_mul, mul_assoc]
      nlinarith [mul_le_mul hcoef (hMa (s - N)) (by positivity) (by positivity)]
    have h2 : ‖∑ k ∈ range (s - N), fs (s - N - k) * a k‖ * ρ ^ (s - N) ≤ Mf * Ma * (s + 1) := by
      have hsum_le : (∑ k ∈ range (s - N), ‖fs (s - N - k) * a k‖ * ρ ^ (s - N)) ≤
          ∑ _k ∈ range (s - N), Mf * Ma := Finset.sum_le_sum fun k hk => by
        rw [norm_mul, show ρ ^ (s - N) = ρ ^ (s - N - k) * ρ ^ k by
          rw [← pow_add, Nat.sub_add_cancel (mem_range.mp hk).le],
          show ‖fs (s - N - k)‖ * ‖a k‖ * (ρ ^ (s - N - k) * ρ ^ k) =
            (‖fs (s - N - k)‖ * ρ ^ (s - N - k)) * (‖a k‖ * ρ ^ k) by ring]
        exact mul_le_mul (hMf _) (hMa _) (by positivity) hMf_pos.le
      calc ‖∑ k ∈ range (s - N), fs (s - N - k) * a k‖ * ρ ^ (s - N)
          ≤ ∑ k ∈ range (s - N), ‖fs (s - N - k) * a k‖ * ρ ^ (s - N) := by
            rw [← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
        _ ≤ ((s - N : ℕ) : ℝ) * (Mf * Ma) := by simpa using hsum_le
        _ ≤ Mf * Ma * (s + 1) := by
            rw [mul_comm (Mf * Ma)]
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast (Nat.sub_le s N).trans (Nat.le_succ s)) (by positivity)
    have htri_ρ := mul_le_mul_of_nonneg_right
      (norm_add_le ((2 * (α₂ + s) + fs 0 - 1) * a (s - N))
        (∑ k ∈ range (s - N), fs (s - N - k) * a k)) (pow_nonneg hρ0.le (s - N))
    rw [hpow]; dsimp [C]; nlinarith [pow_nonneg hρ0.le N, htri_ρ, h1, h2]

/-- Power-series expansion for the shifted logarithmic forcing terms
`u ^ N * (2 u A₁'(u) + (2(α₂ + N) + P(u) - 1) A₁(u))` on `‖u‖ < r`. -/
private theorem hasSum_logForcingCoeff_mul_pow {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ} {fs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (ha : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    let A₁ : ℂ → ℂ := fun w => ∑' s, a s * w ^ s
    HasSum (fun s => logForcingCoeff fs a α₂ N s * u ^ s)
      (u ^ N * (2 * u * deriv A₁ u +
        (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u)) := by
  intro A₁
  have hr : 0 < r := (norm_nonneg u).trans_lt hu
  have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
  have hpA := hasFPowerSeriesOnBall_of_punctured hr a fun z _ hzr => ha z hzr
  have hpF := hasFPowerSeriesOnBall_of_punctured hr fs hf
  have ha_norm : Summable fun s : ℕ => ‖a s * u ^ s‖ := by
    simpa using FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
      a (hue.trans_le hpA.r_le) 0
  have hf_norm : Summable fun s : ℕ => ‖fs s * u ^ s‖ := by
    simpa using FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
      fs (hue.trans_le hpF.r_le) 0
  have hA0 : HasSum (fun s : ℕ => a s * u ^ s) (A₁ u) := by
    simpa using hpA.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv hue 0
  have hA1 : HasSum (fun s : ℕ => (s : ℂ) * a s * u ^ s) (u * deriv A₁ u) := by
    simpa [iteratedDeriv_one] using hpA.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv hue 1
  have hprod : HasSum (fun n => ∑ k ∈ range (n + 1), (a k * u ^ k) * (fs (n - k) * u ^ (n - k)))
      (A₁ u * ∑' s, fs s * u ^ s) := hasSum_sum_range_mul_of_summable_norm ha_norm hf_norm
  have hunshifted : HasSum (fun m : ℕ =>
      ((2 * (α₂ + N + m) + fs 0 - 1) * a m + ∑ k ∈ range m, fs (m - k) * a k) * u ^ m)
      (2 * u * deriv A₁ u + (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u) := by
    have htot := ((hA1.mul_left 2).add (hA0.mul_left (2 * (α₂ + N) - 1))).add hprod
    rw [show 2 * (u * deriv A₁ u) + (2 * (α₂ + N) - 1) * A₁ u + A₁ u * ∑' s, fs s * u ^ s =
      2 * u * deriv A₁ u + (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * A₁ u by ring] at htot
    refine htot.congr_fun fun m => ?_
    rw [sum_range_succ_mul_pow a fs u m,
      show (∑ k ∈ range m, a k * fs (m - k)) = ∑ k ∈ range m, fs (m - k) * a k from
        sum_congr rfl fun _ _ => mul_comm _ _]; ring
  refine ((add_left_injective N).hasSum_iff fun s hs => ?_).mp
    ((hunshifted.mul_left (u ^ N)).congr_fun fun m => ?_)
  · simp [logForcingCoeff,
      show s < N by by_contra h; exact hs ⟨s - N, Nat.sub_add_cancel (not_lt.mp h)⟩]
  · simp only [Function.comp_apply, logForcingCoeff, show ¬m + N < N by omega, ↓reduceIte,
      Nat.add_sub_cancel, pow_add]; push_cast; ring

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
      c' * logForcingCoeff fs a α₂ N s
    let U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
    DifferentiableOn ℂ w₂' U ∧
      (∀ u : ℂ, ‖u‖ < r → Summable fun s => D s * u ^ s) ∧
      ∀ z ∈ U, deriv (deriv w₂') z + f z * deriv w₂' z + g z * w₂' z =
        (z - z₀) ^ (α₂ - 2) * ∑' s, D s * (z - z₀) ^ s := by
  intro a w₁ w₂' D U
  obtain ⟨ha_sum, hw₁_diff, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs
  obtain ⟨hΦ_diff, _, hΦ_op⟩ := hasDerivAt_and_operator_mul_log hw₁_diff hw₁_sol
  set ψ : ℂ → ℂ := fun w => (w - z₀) ^ α₂ * ∑' s, b' s * (w - z₀) ^ s
  set Φ : ℂ → ℂ := fun w => w₁ w * Complex.log (w - z₀)
  have hψ_diff : DifferentiableOn ℂ ψ U := fun w hw =>
    (hasDerivAt_cpow_mul_tsum hb'_sum hw.1 hw.2).differentiableAt.differentiableWithinAt
  have hw₂'_eq : w₂' = fun w => ψ w + c' * Φ w := by ext w; dsimp [w₂', ψ, Φ]; ring
  have hD_hasSum : ∀ u : ℂ, ‖u‖ < r → HasSum (fun s => D s * u ^ s)
      ((∑' s : ℕ, (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) * u ^ s) +
        c' * (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
          (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s))) := fun u hu =>
    (((hasSum_operator_cpow_series (σ := α₂) (fun w hw0 hwr => (hf w hw0 hwr).summable)
        (fun w hw0 hwr => (hg w hw0 hwr).summable) hb'_sum hu).summable.hasSum).add
      ((hasSum_logForcingCoeff_mul_pow (α₂ := α₂) (N := N)
        (fun w hw0 hwr => (hf w hw0 hwr).summable) ha_sum hu).mul_left c')).congr_fun
      fun _ => by dsimp [D]; ring
  refine ⟨by rw [hw₂'_eq]; exact hψ_diff.add (hΦ_diff.const_mul c'),
    fun u hu => (hD_hasSum u hu).summable, fun z ⟨hzs, hzb⟩ => ?_⟩
  obtain ⟨hd1, hd2⟩ := deriv_deriv_add_const_mul
    (isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r) c' hψ_diff hΦ_diff ⟨hzs, hzb⟩
  rw [hw₂'_eq, hd1, hd2, show (deriv (deriv ψ) z + c' * deriv (deriv Φ) z) +
      f z * (deriv ψ z + c' * deriv Φ z) + g z * (ψ z + c' * Φ z) =
      (deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z) +
        c' * (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) by ring,
    operator_cpow_mul_tsum_eq (σ := α₂) hf hg hb'_sum hzs hzb,
    hΦ_op z ⟨hzs, hzb⟩, (hD_hasSum (z - z₀) hzb).tsum_eq]
  set u : ℂ := z - z₀; have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hzs
  set A₁ : ℂ → ℂ := fun w => ∑' s, a s * w ^ s
  have hdw₁ : deriv w₁ z = u ^ (α₂ + (N : ℂ) - 1) * ((α₂ + N) * A₁ u + u * deriv A₁ u) :=
    (hasDerivAt_cpow_mul_tsum ha_sum hzs hzb).deriv
  have hcpow_N : (u ^ 2)⁻¹ * u ^ (α₂ + (N : ℂ)) = u ^ (α₂ - 2) * u ^ N := by
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_natCast, cpow_eq_cpow_sub_two_mul_sq hu0 α₂]
    field_simp [hu0]
  rw [(hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq]; dsimp only [w₁, A₁, u] at hdw₁ ⊢; rw [hdw₁]
  linear_combination
    c' * (2 * (u ^ 2)⁻¹ * ((α₂ + ↑N) * A₁ u + u * deriv A₁ u)) *
      (cpow_eq_cpow_sub_one_mul hu0 (α₂ + (N : ℂ))).symm +
    c' * (2 * u * deriv A₁ u + (2 * (α₂ + ↑N) + u * f z - 1) * A₁ u) * hcpow_N

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
  obtain ⟨ha_sum, _, _⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs
  set a := regularSingularCoeff fs gs (α₂ + N)
  set b := regularSingularSecondCoeff fs gs α₂ N
  set c := regularSingularLogMultiplier fs gs α₂ N
  have hb_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b s * (z - z₀) ^ s := by
    refine summable_of_perturbed_indicial_rec (σ := α₂)
      (E := fun s => -c * logForcingCoeff fs a α₂ N s) (s₁ := 0)
      (fun z hz0 hzr => (hf z hz0 hzr).summable) (fun z hz0 hzr => (hg z hz0 hzr).summable)
      (fun ρ hρ0 hρr => ?_) (fun s _ => by
        dsimp only [logForcingCoeff]; linear_combination regularSingularSecondCoeff_rec hfact s)
    obtain ⟨CF, _, hCF⟩ := exists_norm_logForcingCoeff_mul_pow_le (α₂ := α₂) (N := N) hρ0 hρr
      (fun z hz0 hzr => (hf z hz0 hzr).summable) ha_sum
    refine ⟨‖c‖ * CF, by positivity, fun s => ?_⟩
    rw [norm_mul, norm_neg, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hCF s) (norm_nonneg c)
  obtain ⟨hw₂_diff, _, hw₂_op⟩ := operator_second_ansatz_eq (c' := c) hf hg hfact hb_sum
  refine ⟨hb_sum, hw₂_diff, fun z hzs hzb => ?_⟩
  rw [hw₂_op z ⟨hzs, hzb⟩]
  simp only [b, c, logForcingCoeff, regularSingularSecondCoeff_rec hfact, zero_mul, tsum_zero,
    mul_zero]

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
  exact eq_regularSingularSecondCoeff_of_rec hfact hb'N hc'0 hb'0 <|
    eq_zero_of_cpow_mul_tsum_eq_zero (z₀ := z₀) (α := α₂ - 2) hr (fun u _ hu => hD_sum u hu)
      fun z hzs hzb => (hD_op z ⟨hzs, hzb⟩).symm.trans (hsol z hzs hzb)

/-! ### Worked example: Euler–Cauchy equation `w'' - 2 z⁻² w = 0` at `z₀ = 0` -/

-- For `f = 0` and `g(z) = -2 z⁻²` at `z₀ = 0` (`f₀ = 0`, `g₀ = -2`), the indicial polynomial
-- factors as `(α - 2)(α + 1)` with roots `2` and `-1` differing by `N = 3`, all higher series
-- coefficients vanish, `c = 0`, and the canonical solutions on `slitPlane` are `z²` and `z⁻¹`.
example :
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
      simp [fs, gs, Pi.single_eq_of_ne (show m - k ≠ 0 by have := mem_range.mp hk; omega)]
  have ha_zero : ∀ s : ℕ, 1 ≤ s → regularSingularCoeff fs gs 2 s = 0 := fun s hs => by
    rw [regularSingularCoeff_of_ne_zero fs gs 2 (by omega), hconv0, mul_zero]
  have hc_zero : regularSingularLogMultiplier fs gs (-1) 3 = 0 := by
    rw [regularSingularLogMultiplier_of_ne_zero fs gs (-1) (by decide), hconv0, mul_zero]
  have hb_zero : ∀ s : ℕ, 1 ≤ s → regularSingularSecondCoeff fs gs (-1) 3 s = 0 := fun s hs => by
    rcases lt_trichotomy s 3 with hs3 | rfl | hs3
    · rw [regularSingularSecondCoeff_eq_regularSingularCoeff_of_lt fs gs (-1) hs3,
        regularSingularCoeff_of_ne_zero fs gs (-1) (by omega), hconv0, mul_zero]
    · exact regularSingularSecondCoeff_self fs gs (-1) 3
    · have hQ := indicialPoly_add_nat_ne_zero_of_ne (α₂ := -1) (N := 3)
        (fun α => by push_cast; simpa [show (-1 : ℂ) + 3 = 2 by norm_num] using hfact α)
        (by omega) hs3.ne'
      exact mul_left_cancel₀ hQ (by
        simp [indicialPoly_mul_regularSingularSecondCoeff_of_gt hs3 hQ, hc_zero, hconv0])
  refine ⟨hfact, ha_zero, hc_zero, hb_zero, fun z _ => ?_, fun z _ => ?_⟩
  · rw [tsum_eq_single 0 fun s hs => by simp [ha_zero s (Nat.pos_of_ne_zero hs)]]
    simp
  · rw [tsum_eq_single 0 fun s hs => by simp [hb_zero s (Nat.pos_of_ne_zero hs)]]
    simp [hc_zero, Complex.cpow_neg_one]

end TauCeti
