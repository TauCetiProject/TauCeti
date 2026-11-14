/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.Complex.CanonicalFactor
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Landau's local logarithmic-derivative lemma

Let `f` be analytic on `closedBall z₀ R`, with a relative bound
`‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`. For every `0 < r < R` and `d = ‖z - z₀‖ < r`, away
from the zeros of `f`, its logarithmic derivative differs from the partial-fraction sum over the
zeros in `closedBall z₀ r` by at most
`(4 (r + d) / (r - d)² + r / ((R² - r d) log(R/r))) log M`.
Multiplicities are Mathlib's divisor values. When `2 r ≤ R`, ordinary zero removal gives the
sharper bound `4 (r + d) / (r - d)² log M`. The classical radii `R/2` and `R/4` retain the bound
`48 log M / R`. Jensen's companion zero count is `AnalyticOnNhd.sum_divisor_le_log_div_log`.

The lemma turns an upper bound for `‖f‖` on a circle, relative to the value at a single point
where `f` does not vanish, into a local description of `logDeriv f` by its nearby zeros, without
any lower bound for `‖f‖`. This is how growth bounds for entire functions of finite order, and
for L-functions in particular, become bounds for their logarithmic derivatives: the zeros near a
point are counted by Jensen's formula, and the remaining part of `logDeriv f` is bounded.

## Main results

* `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le`: arbitrary nested radii `r < R`.
* `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le`: the sharper bound when
  `2 r ≤ R`.
* `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_half_le`: the classical `48 / R * log M` bound.

## Implementation notes

`AnalyticOnNhd.exists_eq_finprod_zpow_mul` writes `f = P G`, removing the inner-disc zeros.
For arbitrary radii, multiply `G` by the numerators of `Complex.canonicalFactor`; their circle
norm agrees with that of `P`, and their central norm dominates it. The maximum modulus principle
transfers the relative bound to this product. `TauCeti.exists_differentiableOn_eqOn_exp_comp`
provides a logarithm, normalized by subtracting its value at `z₀`, and
`Complex.norm_deriv_le_of_forall_mem_ball_re_le` bounds its derivative.
`Function.FactorizedRational.logDeriv_eq_finsum` identifies the divisor contribution;
`AnalyticOnNhd.sum_divisor_le_log_div_log` bounds the reflected-factor error. If `2 r ≤ R`, the
ordinary factors of `P` already dominate their central values on the outer sphere, and the
reflected-factor error is unnecessary; this gives the sharper companion theorem.

## References

* Preston Walker's `FinalBound` in Alex Kontorovich, Terence Tao and contributors,
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), commit
  [7302b6c9ad6eec18a2107f21dbb75c5ff496e4d7](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/7302b6c9ad6eec18a2107f21dbb75c5ff496e4d7/PrimeNumberTheoremAnd/StrongPNT.lean).
  The arbitrary-radius theorem adapts its finite-Blaschke reflected-zero argument to Mathlib's
  divisor and canonical-factor APIs.
* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 8.5, pp.89–90:
  Borel–Carathéodory derivative bounds; Lemma 8.6, pp.90–91: fixed-ratio Landau and Jensen
  arguments with reflected factors.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Lemma 6.3, pp.170–171:
  finite Blaschke products for arbitrary fixed nested radii, with an implicit constant.
* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §3.9, Lemma α, p.56: the classical fixed-ratio estimate.

The explicit coefficients in the statements below are established by the Lean proofs.
-/

public section

open Metric MeromorphicOn Filter Topology Set

namespace AnalyticOnNhd

variable {f : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}

open Complex
open scoped ComplexConjugate

-- The boundary bound and a nonzero value force a nonzero central value, even at radius zero.
private lemma ne_zero_center_of_boundary_bound {z : ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    (hz : z ∈ closedBall z₀ R) (hfz : f z ≠ 0) : f z₀ ≠ 0 := by
  intro hzero
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
    (by apply DifferentiableOn.diffContOnCl
        simpa only [closure_closedBall] using hf.differentiableOn)
    (fun w hw ↦ hM w (frontier_closedBall_subset_sphere hw)) (subset_closure hz)
  rw [hzero, norm_zero, mul_zero] at hbound
  exact hfz (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))

-- Normalize a logarithm at the centre once, then apply the real-part derivative estimate.
private lemma norm_logDeriv_le_of_relative_norm_bound {B : ℂ → ℂ} {z : ℂ} {M : ℝ}
    (hB : AnalyticOnNhd ℂ B (closedBall z₀ r))
    (hB0 : ∀ w ∈ closedBall z₀ r, B w ≠ 0)
    (hM : ∀ w ∈ closedBall z₀ r, ‖B w‖ ≤ M * ‖B z₀‖)
    (hz : ‖z - z₀‖ < r) :
    ‖logDeriv B z‖ ≤ 4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * Real.log M := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hzb : z ∈ ball z₀ r := by rwa [mem_ball, dist_eq_norm]
  have hBz₀ : B z₀ ≠ 0 := hB0 z₀ (mem_closedBall_self hr.le)
  have hMpos : 0 < M := by
    have hc := hM z₀ (mem_closedBall_self hr.le)
    have hn := norm_pos_iff.mpr hBz₀
    nlinarith
  obtain ⟨L, hLd, hL⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp (U := ball z₀ r)
    ((convex_ball z₀ r).isSimplyConnected ⟨z₀, mem_ball_self hr⟩) isOpen_ball
    ((hB.differentiableOn.mono ball_subset_closedBall).div_const (B z₀))
    (fun ⟨w, hw, h0⟩ ↦ div_ne_zero (hB0 w (ball_subset_closedBall hw)) hBz₀ h0)
  let H : ℂ → ℂ := fun w ↦ L w - L z₀
  have hre (w : ℂ) (hw : w ∈ ball z₀ r) : (H w).re ≤ Real.log M := by
    have hexp : exp (H w) = B w / B z₀ := by
      have h₁ := hL hw
      have h₂ := hL (mem_ball_self hr)
      simp only [Function.comp_apply, div_self hBz₀] at h₁ h₂
      simp [H, Complex.exp_sub, h₁, h₂]
    rw [Real.le_log_iff_exp_le hMpos, ← Complex.norm_exp, hexp, norm_div,
      div_le_iff₀ (norm_pos_iff.2 hBz₀)]
    exact hM w (ball_subset_closedBall hw)
  have hlogB : deriv H z = logDeriv B z := by
    simp only [H, deriv_sub_const]
    rw [TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball hLd hL hzb]
    simp only [div_eq_mul_inv]
    exact logDeriv_mul_const z _ (inv_ne_zero hBz₀)
  rw [← hlogB]
  exact Complex.norm_deriv_le_of_forall_mem_ball_re_le (hLd.sub_const _)
    (sub_self _) hre hz

-- Remove the inner-disc zeros and identify the remaining logarithmic derivative once.
private lemma exists_factor_logDeriv_eq {z : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R)) (hrR : r ≤ R)
    (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (closedBall z₀ R) ∧
      (∀ w ∈ closedBall z₀ r, G w ≠ 0) ∧
      (∀ w ∈ closedBall z₀ R,
        f w = (∏ᶠ ρ, (· - ρ) ^ divisor f (closedBall z₀ r) ρ) w * G w) ∧
      logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ r) ρ : ℂ) / (z - ρ) =
        logDeriv G z := by
  classical
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hR : 0 < R := hr.trans_le hrR
  have hzb : z ∈ ball z₀ r := by rwa [mem_ball, dist_eq_norm]
  have hzR : z ∈ ball z₀ R := ball_subset_ball hrR hzb
  obtain ⟨G, hG, hG0, hfG⟩ := hf.exists_eq_finprod_zpow_mul hR hrR
    ⟨z, ball_subset_closedBall hzR, hfz⟩
  refine ⟨G, hG, hG0, hfG, ?_⟩
  let D := divisor f (closedBall z₀ r)
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hD (ρ : ℂ) : 0 ≤ D ρ := (hf.mono (closedBall_subset_closedBall hrR)).divisor_nonneg ρ
  let P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D ρ
  have hDz : D z = 0 := (hf z (ball_subset_closedBall hzR)).divisor_apply_eq_zero hfz
  have hPz : P z ≠ 0 := Function.FactorizedRational.ne_zero hDz
  have hlogf : logDeriv f z = logDeriv P z + logDeriv G z := by
    have hfPG : f =ᶠ[𝓝 z] P * G := eventuallyEq_of_mem (isOpen_ball.mem_nhds hzR)
      fun w hw ↦ hfG w (ball_subset_closedBall hw)
    rw [(logDeriv_congr_nhds hfPG).eq_of_nhds,
      logDeriv_mul z hPz (hG0 z (ball_subset_closedBall hzb))
        (Function.FactorizedRational.analyticAt (hD z)).differentiableAt
        (hG z (ball_subset_closedBall hzR)).differentiableAt]
  rw [hlogf, ← Function.FactorizedRational.logDeriv_eq_finsum hfin hDz, add_sub_cancel_left]

-- Sum the logarithmic derivatives of the finite reflected product with integer multiplicities.
private lemma norm_logDeriv_reflected_prod_le {S : Finset ℂ} {n : ℂ → ℤ} {z : ℂ}
    (hrR : r < R) (hn : ∀ ρ ∈ S, 0 ≤ n ρ)
    (hρnorm : ∀ ρ ∈ S, ‖ρ - z₀‖ ≤ r) (hz : ‖z - z₀‖ < r) :
    ‖logDeriv (fun w : ℂ ↦ ∏ ρ ∈ S,
      (((R : ℂ) ^ 2 - conj (ρ - z₀) * (w - z₀)) / (R : ℂ)) ^ n ρ) z‖ ≤
      (∑ ρ ∈ S, (n ρ : ℝ)) * (r / (R ^ 2 - r * ‖z - z₀‖)) := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  let q (ρ w : ℂ) := ((R : ℂ) ^ 2 - conj (ρ - z₀) * (w - z₀)) / (R : ℂ)
  have hq (ρ : ℂ) : Differentiable ℂ (q ρ) := by dsimp [q]; fun_prop
  have hq0 (ρ : ℂ) (hρ : ρ ∈ S) : q ρ z ≠ 0 :=
    div_ne_zero (norm_pos_iff.mp (norm_canonicalFactor_numerator_pos hrR (hρnorm ρ hρ)
      (hz.le.trans hrR.le))) (Complex.ofReal_ne_zero.mpr (hr.trans hrR).ne')
  rw [logDeriv_fun_prod (f := fun ρ (w : ℂ) ↦ q ρ w ^ n ρ)
    (fun ρ hρ ↦ zpow_ne_zero _ (hq0 ρ hρ))
    (fun ρ hρ ↦ ((hq ρ) z).zpow (.inr (hn ρ hρ)))]
  simp_rw [logDeriv_fun_zpow ((hq _) z)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (Int.cast_nonneg (hn ρ hρ))]
  exact mul_le_mul_of_nonneg_left
    (norm_logDeriv_canonicalFactor_numerator_le hrR (hρnorm ρ hρ) hz)
    (Int.cast_nonneg (hn ρ hρ))

-- Package the reflected product's analytic, boundary, central and logarithmic-derivative data.
private lemma exists_reflected_prod {S : Finset ℂ} {n : ℂ → ℤ} {z : ℂ}
    (hrR : r < R) (hn : ∀ ρ ∈ S, 0 ≤ n ρ)
    (hρnorm : ∀ ρ ∈ S, ‖ρ - z₀‖ ≤ r) (hz : ‖z - z₀‖ < r) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧
      (∀ w ∈ closedBall z₀ R, Q w ≠ 0) ∧
      (∀ w ∈ sphere z₀ R, ‖Q w‖ = ‖∏ ρ ∈ S, (w - ρ) ^ n ρ‖) ∧
      ‖∏ ρ ∈ S, (z₀ - ρ) ^ n ρ‖ ≤ ‖Q z₀‖ ∧
      ‖logDeriv Q z‖ ≤ (∑ ρ ∈ S, (n ρ : ℝ)) *
        (r / (R ^ 2 - r * ‖z - z₀‖)) := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hR : 0 < R := hr.trans hrR
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  let q (ρ w : ℂ) := ((R : ℂ) ^ 2 - conj (ρ - z₀) * (w - z₀)) / (R : ℂ)
  let Q (w : ℂ) := ∏ ρ ∈ S, q ρ w ^ n ρ
  have hq (ρ : ℂ) : Differentiable ℂ (q ρ) := by dsimp [q]; fun_prop
  have hq0 (ρ w : ℂ) (hρ : ρ ∈ S) (hw : w ∈ closedBall z₀ R) : q ρ w ≠ 0 :=
    div_ne_zero (norm_pos_iff.mp (norm_canonicalFactor_numerator_pos hrR (hρnorm ρ hρ)
      (by simpa [mem_closedBall, dist_eq_norm] using hw))) hRne
  refine ⟨Q, ?_, ?_, ?_, ?_, norm_logDeriv_reflected_prod_le hrR hn hρnorm hz⟩
  · intro w
    exact DifferentiableAt.fun_finsetProd fun ρ hρ ↦ ((hq ρ) w).zpow (.inr (hn ρ hρ))
  · exact fun w hw ↦ Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦ zpow_ne_zero _ (hq0 ρ w hρ hw)
  · intro w hw
    simp only [Q, norm_prod, norm_zpow]
    apply Finset.prod_congr rfl
    intro ρ _hρ
    congr 1
    have h := norm_canonicalFactor_numerator_eval_circle (a := ρ - z₀) hR.ne'
      (by simpa [mem_sphere, dist_eq_norm] using hw)
    have heq : w - z₀ - (ρ - z₀) = w - ρ := by ring
    rw [heq] at h
    exact h
  · simp only [Q, norm_prod, norm_zpow]
    refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun ρ hρ ↦ ?_
    simp only [q, sub_self, mul_zero, sub_zero, pow_two, mul_div_cancel_right₀ _ hRne,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply zpow_le_zpow_left₀ (hn ρ hρ) (norm_nonneg _)
    rw [norm_sub_rev]
    exact (hρnorm ρ hρ).trans hrR.le

-- Multiply the zero-free cofactor by the reflected product and transfer the boundary bound.
private lemma exists_reflected_cofactor {z : ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R)) (hrR : r < R)
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) :
    ∃ B Q : ℂ → ℂ, AnalyticOnNhd ℂ B (closedBall z₀ r) ∧
      (∀ w ∈ closedBall z₀ r, B w ≠ 0) ∧
      (∀ w ∈ closedBall z₀ r, ‖B w‖ ≤ M * ‖B z₀‖) ∧
      logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ r) ρ : ℂ) / (z - ρ) =
        logDeriv B z - logDeriv Q z ∧
      ‖logDeriv Q z‖ ≤ ((∑ᶠ ρ, divisor f (closedBall z₀ r) ρ : ℤ) : ℝ) *
        (r / (R ^ 2 - r * ‖z - z₀‖)) := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hR : 0 < R := hr.trans hrR
  have hz₀R := mem_closedBall_self hR.le (x := z₀)
  have hzR : z ∈ closedBall z₀ R := by simpa [mem_closedBall, dist_eq_norm] using hz.le.trans hrR.le
  have hz₀ := ne_zero_center_of_boundary_bound hf hM hzR hfz
  have hM1 : 1 ≤ M :=
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      hR hz₀ hM
  obtain ⟨G, hG, hG0, hfG, hlogf⟩ := exists_factor_logDeriv_eq hf hrR.le hz hfz
  let D := divisor f (closedBall z₀ r)
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hD (ρ : ℂ) : 0 ≤ D ρ := (hf.mono (closedBall_subset_closedBall hrR.le)).divisor_nonneg ρ
  obtain ⟨Q, hQ, hQ0, hQouter, hPcenter, hQbound⟩ := exists_reflected_prod (n := D) hrR
    (fun ρ _ ↦ hD ρ) (S := hfin.toFinset)
    (fun ρ hρ ↦ by simpa [dist_eq_norm] using D.supportWithinDomain (hfin.mem_toFinset.1 hρ)) hz
  let P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D ρ
  have hPs (w : ℂ) : P w = ∏ ρ ∈ hfin.toFinset, (w - ρ) ^ D ρ :=
    Function.FactorizedRational.finprod_apply_eq_prod hfin w
  let B : ℂ → ℂ := G * Q
  have hBa : AnalyticOnNhd ℂ B (closedBall z₀ R) := fun w hw ↦ (hG w hw).mul (hQ.analyticAt w)
  have hB0 : ∀ w ∈ closedBall z₀ r, B w ≠ 0 :=
    fun w hw ↦ mul_ne_zero (hG0 w hw) (hQ0 w (closedBall_subset_closedBall hrR.le hw))
  have hcenter : ‖f z₀‖ ≤ ‖B z₀‖ := by
    rw [hfG z₀ hz₀R, show (∏ᶠ ρ, (· - ρ) ^ D ρ) z₀ = P z₀ from rfl, hPs, norm_mul]
    exact (mul_le_mul_of_nonneg_right hPcenter (norm_nonneg _)).trans_eq (by simp [B, mul_comm])
  have hBbound (w : ℂ) (hw : w ∈ closedBall z₀ R) : ‖B w‖ ≤ M * ‖B z₀‖ := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
      (by apply DifferentiableOn.diffContOnCl
          simpa only [closure_closedBall] using hBa.differentiableOn)
      (fun u hu ↦ ?_) (subset_closure hw)
    have hu' := frontier_closedBall_subset_sphere hu
    have heq : ‖B u‖ = ‖f u‖ := by
      rw [hfG u (sphere_subset_closedBall hu'), ← show P u = (∏ᶠ ρ, (· - ρ) ^ D ρ) u from rfl,
        hPs, norm_mul]
      simp only [B, Pi.mul_apply, norm_mul, hQouter u hu', mul_comm]
    rw [heq]
    exact (hM u hu').trans (mul_le_mul_of_nonneg_left hcenter (by linarith))
  refine ⟨B, Q, hBa.mono (closedBall_subset_closedBall hrR.le), hB0,
    fun w hw ↦ hBbound w (closedBall_subset_closedBall hrR.le hw), ?_, ?_⟩
  · rw [hlogf, show logDeriv B z = logDeriv G z + logDeriv Q z from
      logDeriv_mul z (hG0 z (by simpa [mem_closedBall, dist_eq_norm] using hz.le))
        (hQ0 z hzR) (hG z hzR).differentiableAt (hQ z)]
    ring
  · simpa only [← Int.cast_sum, ← finsum_eq_sum D hfin] using hQbound

/-- Let `f` be analytic on `closedBall z₀ R` and satisfy
`‖f w‖ ≤ M * ‖f z₀‖` on `sphere z₀ R`. If `‖z - z₀‖ < r < R` and `f z ≠ 0`, then
`logDeriv f z` minus the divisor sum over `closedBall z₀ r` has norm at most
`(4 * (r + d) / (r - d)^2 + r / ((R^2 - r*d) * log (R/r))) * log M`, where `d = ‖z - z₀‖`.
Zeros on the inner boundary are included with their full analytic multiplicity. -/
theorem norm_logDeriv_sub_finsum_divisor_le {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R)) (hrR : r < R)
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ r) ρ : ℂ) / (z - ρ)‖ ≤
      (4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 +
        r / ((R ^ 2 - r * ‖z - z₀‖) * Real.log (R / r))) * Real.log M := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  obtain ⟨B, Q, hB, hB0, hBM, hlogf, hQbound⟩ := exists_reflected_cofactor hf hrR hM hz hfz
  have hden : 0 < R ^ 2 - r * ‖z - z₀‖ := by
    have : r * ‖z - z₀‖ < r * r := mul_lt_mul_of_pos_left hz hr
    nlinarith [hr.trans hrR]
  have hz₀ := ne_zero_center_of_boundary_bound hf hM
    (by simpa [mem_closedBall, dist_eq_norm] using hz.le.trans hrR.le) hfz
  have hN := hf.sum_divisor_le_log_div_log hr hrR hz₀ hM
  have hQB : ‖logDeriv Q z‖ ≤
      (r / ((R ^ 2 - r * ‖z - z₀‖) * Real.log (R / r))) * Real.log M := by
    refine hQbound.trans ((mul_le_mul_of_nonneg_right hN (div_nonneg hr.le hden.le)).trans_eq ?_)
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hlogf]
  exact (norm_sub_le _ _).trans
    ((add_le_add (norm_logDeriv_le_of_relative_norm_bound hB hB0 hBM hz) hQB).trans_eq (by ring))

/-- **Landau's local logarithmic-derivative lemma.** Let `f` be analytic on `closedBall z₀ R`
with `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`, and let `2 r ≤ R`. At every `z` with
`‖z - z₀‖ < r` and `f z ≠ 0`, the logarithmic derivative of `f` differs from `∑ m_ρ / (z - ρ)`
over the zeros `ρ` in `closedBall z₀ r`, with multiplicities `m_ρ` given by the divisor, by at
most `4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * log M`. -/
theorem norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hrR : 2 * r ≤ R) {M : ℝ}
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) {z : ℂ} (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ r) ρ : ℂ) / (z - ρ)‖ ≤
      4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * Real.log M := by
  classical
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hR : 0 < R := by linarith
  have hz₀R : z₀ ∈ closedBall z₀ R := mem_closedBall_self hR.le
  -- Factor `f = P G` on `closedBall z₀ R`, with `P` the product over the zeros in
  -- `closedBall z₀ r` and `G` zero-free there.
  obtain ⟨G, hG, hG0, hfG, hlogf⟩ := exists_factor_logDeriv_eq hf
    (by linarith) hz hfz
  set D' := divisor f (closedBall z₀ r)
  have hfin : D'.support.Finite := D'.finiteSupport (isCompact_closedBall _ _)
  have hD' (ρ : ℂ) : 0 ≤ D' ρ :=
    (hf.mono (closedBall_subset_closedBall (by linarith))).divisor_nonneg ρ
  set P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D' ρ
  have hfPG (w : ℂ) (hw : w ∈ closedBall z₀ R) : f w = P w * G w := by
    simpa only [P, D'] using hfG w hw
  have hPs (w : ℂ) : P w = ∏ ρ ∈ hfin.toFinset, (w - ρ) ^ D' ρ :=
    Function.FactorizedRational.finprod_apply_eq_prod hfin w
  -- On the outer sphere each factor of `P` is at least as large as at the centre, so the maximum
  -- modulus principle bounds `G` by `M ‖G z₀‖`.
  have hdist (w : ℂ) (hw : w ∈ sphere z₀ R) (ρ : ℂ) (hρ : ρ ∈ hfin.toFinset) :
      ‖z₀ - ρ‖ ≤ ‖w - ρ‖ ∧ 0 < ‖w - ρ‖ := by
    have h1 : ‖ρ - z₀‖ ≤ r := by
      simpa [dist_eq_norm] using D'.supportWithinDomain (hfin.mem_toFinset.1 hρ)
    have h2 : ‖w - z₀‖ = R := by simpa [dist_eq_norm] using hw
    have h3 : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := norm_sub_le_norm_sub_add_norm_sub w ρ z₀
    rw [norm_sub_rev]
    constructor <;> linarith
  have hGle (w : ℂ) (hw : w ∈ closedBall z₀ R) : ‖G w‖ ≤ M * ‖G z₀‖ := by
    refine Complex.norm_le_of_forall_mem_sphere_norm_mul_le (P := P) hR
      (hG.differentiableOn.diffContOnCl_ball Subset.rfl) (fun u hu ↦ ?_) (fun u hu ↦ ?_)
      (fun u hu ↦ ?_) hw
    · rw [hPs]
      exact Finset.prod_ne_zero_iff.2 fun ρ hρ ↦ zpow_ne_zero _ (norm_pos_iff.1 (hdist u hu ρ hρ).2)
    · simp only [hPs, norm_prod, norm_zpow]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
        fun ρ hρ ↦ zpow_le_zpow_left₀ (hD' ρ) (norm_nonneg _) (hdist u hu ρ hρ).1
    · rw [← hfPG u (sphere_subset_closedBall hu), ← hfPG z₀ hz₀R]
      exact hM u hu
  rw [hlogf]
  exact norm_logDeriv_le_of_relative_norm_bound
    (hG.mono (closedBall_subset_closedBall (by linarith))) hG0
    (fun w hw ↦ hGle w (closedBall_subset_closedBall (by linarith) hw)) hz

/-- **Landau's local logarithmic-derivative lemma** in the classical normalization. Let `f` be
analytic on `closedBall z₀ R` with `0 < R` and `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`.
At every `z` with `‖z - z₀‖ ≤ R / 4` and `f z ≠ 0`, the logarithmic derivative of `f` differs
from `∑ m_ρ / (z - ρ)` over the zeros `ρ` in `closedBall z₀ (R / 2)`, with multiplicities `m_ρ`
given by the divisor, by at most `48 / R * log M`. This is
`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le` with `r = R / 2`. -/
theorem norm_logDeriv_sub_finsum_divisor_half_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : 0 < R) {M : ℝ} (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    {z : ℂ} (hz : ‖z - z₀‖ ≤ R / 4) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ (R / 2)) ρ : ℂ) / (z - ρ)‖ ≤
      48 / R * Real.log M := by
  have hz₀ := ne_zero_center_of_boundary_bound hf hM
    (by simpa [mem_closedBall, dist_eq_norm] using hz.trans (by linarith : R / 4 ≤ R)) hfz
  have hM1 : 1 ≤ M :=
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      hR hz₀ hM
  refine (hf.norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le
    (by linarith) hM (by linarith) hfz).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg hM1))
  calc 4 * (R / 2 + ‖z - z₀‖) / (R / 2 - ‖z - z₀‖) ^ 2
      ≤ 4 * (R / 2 + R / 4) / (R / 2 - R / 4) ^ 2 := by
        have h4 : 0 < R / 2 - R / 4 := by linarith
        gcongr
    _ = 48 / R := by
        field_simp
        ring

end AnalyticOnNhd

/-! ### Example

For the polynomial `f z = z - 1` on `closedBall 0 4` one may take `M = 5`, since
`‖w - 1‖ ≤ 5 = 5 ‖f 0‖` on `sphere 0 4`. Near `0` the logarithmic derivative is then its
partial-fraction part over the zeros in `closedBall 0 2` up to `12 log 5`. -/

example {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    ‖logDeriv (· - 1) z - ∑ᶠ ρ, (divisor (· - 1 : ℂ → ℂ) (closedBall 0 2) ρ : ℂ) / (z - ρ)‖ ≤
      12 * Real.log 5 := by
  have hf : AnalyticOnNhd ℂ (· - 1 : ℂ → ℂ) (closedBall 0 4) := fun _ _ ↦ by fun_prop
  have hM (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 4) : ‖w - 1‖ ≤ 5 * ‖(0 : ℂ) - 1‖ := by
    rw [mem_sphere_zero_iff_norm] at hw
    have := norm_sub_le w 1
    norm_num [hw] at this ⊢
    linarith
  have h₁ := hf.norm_logDeriv_sub_finsum_divisor_half_le (by norm_num) hM
    (by simpa using hz) (sub_ne_zero.2 hz1)
  have h42 : (4 : ℝ) / 2 = 2 := by norm_num
  rw [h42] at h₁
  norm_num at h₁
  exact h₁
