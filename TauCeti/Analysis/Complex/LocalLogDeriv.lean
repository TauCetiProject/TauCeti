/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.CanonicalDecomposition
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Landau's local logarithmic-derivative lemma

Let `f` be analytic on `closedBall z₀ R`, with `f z₀ ≠ 0` and a relative bound
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

Native divisor factorization writes `f = P G`, where `P` removes just the zeros in the smaller
disc and `G` is zero-free there. For arbitrary radii, multiply `G` by the analytic numerators of
Mathlib's canonical factors. Their circle-modulus identity preserves the boundary norm of `f`,
and their value at the centre dominates the factors of `P`. The maximum modulus principle and
the native normalized holomorphic logarithm then give Borel–Carathéodory's derivative bound.
Jensen's count bounds the logarithmic derivatives of the reflected factors. If `2 r ≤ R`, the
ordinary factors of `P` already dominate their central values on the outer sphere, and the
reflected-factor error is unnecessary; this gives the sharper companion theorem.

## References

* P. Walker, the flexible-radius `FinalBound` in
  [PrimeNumberTheoremAnd](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/079c333edd2d0b146b918ecef8645a6f1ce1e2e4/PrimeNumberTheoremAnd/StrongPNT.lean),
  the motivating nested-disc estimate.
* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §3.9, Lemma α.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Lemma 6.3.
-/

public section

open Metric MeromorphicOn Filter Topology Set

namespace AnalyticOnNhd

variable {f : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}

open Complex
open scoped ComplexConjugate

private lemma reflected_factor_norm {R : ℝ} {a w : ℂ}
    (ha : ‖a‖ < R) (hw : ‖w‖ = R) :
    ‖((R : ℂ) ^ 2 - conj a * w) / (R : ℂ)‖ = ‖w - a‖ := by
  have hR : 0 < R := (norm_nonneg a).trans_lt ha
  have hwa : w - a ≠ 0 := by
    intro h
    have : w = a := sub_eq_zero.mp h
    rw [this] at hw
    linarith
  have he : ((R : ℂ) ^ 2 - conj a * w) / (R : ℂ) =
      canonicalFactor R a w * (w - a) := by
    rw [canonicalFactor_apply]
    field_simp
  rw [he, norm_mul, norm_canonicalFactor_eval_circle_eq_one
    (by simpa only [mem_ball_zero_iff] using ha)
    (by simpa only [mem_sphere_zero_iff_norm] using hw), one_mul]

private lemma reflected_denom_pos {R r : ℝ} {a t : ℂ} (hr : 0 < r) (hrR : r < R)
    (ha : ‖a‖ ≤ r) (ht : ‖t‖ ≤ R) :
    0 < ‖(R : ℂ) ^ 2 - conj a * t‖ := by
  have hR : 0 < R := hr.trans hrR
  have hprod : ‖conj a * t‖ ≤ r * R := by
    rw [norm_mul, norm_conj]
    exact mul_le_mul ha ht (norm_nonneg _) hr.le
  have hsub := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * t)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hsub
  nlinarith

private lemma reflected_logDeriv_le {R r : ℝ} {a z₀ z : ℂ} (hr : 0 < r) (hrR : r < R)
    (ha : ‖a‖ ≤ r) (hz : ‖z - z₀‖ < r) :
    ‖logDeriv (fun w : ℂ ↦ ((R : ℂ) ^ 2 - conj a * (w - z₀)) / (R : ℂ)) z‖ ≤
      r / (R ^ 2 - r * ‖z - z₀‖) := by
  have hR : 0 < R := hr.trans hrR
  have hder : HasDerivAt
      (fun w : ℂ ↦ ((R : ℂ) ^ 2 - conj a * (w - z₀)) / (R : ℂ))
      (-conj a / (R : ℂ)) z := by
    convert ((hasDerivAt_const z ((R : ℂ) ^ 2)).sub
      (((hasDerivAt_id z).sub_const z₀).const_mul (conj a))).div_const (R : ℂ) using 1 <;> simp
  have hden : 0 < R ^ 2 - r * ‖z - z₀‖ := by
    have : r * ‖z - z₀‖ < r * r := mul_lt_mul_of_pos_left hz hr
    nlinarith
  have hbound : R ^ 2 - r * ‖z - z₀‖ ≤ ‖(R : ℂ) ^ 2 - conj a * (z - z₀)‖ := by
    have hprod := mul_le_mul_of_nonneg_right ha (norm_nonneg (z - z₀))
    have hsub := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * (z - z₀))
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      norm_mul, norm_conj] at hsub
    linarith
  rw [logDeriv_apply, hder.deriv, div_div_div_cancel_right₀ (Complex.ofReal_ne_zero.mpr hR.ne'),
    norm_div, norm_neg, norm_conj]
  exact (div_le_div_of_nonneg_right ha (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left hr.le hden hbound)

/-- **Landau's local logarithmic-derivative lemma at arbitrary nested radii.** The inner
zero-disc radius `r` may be any radius strictly smaller than `R`. The reflected-factor term
accounts for removing the zeros by a finite Blaschke product. -/
theorem norm_logDeriv_sub_finsum_divisor_le {f : ℂ → ℂ} {z₀ z : ℂ} {r R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R)) (hrR : r < R) (hz₀ : f z₀ ≠ 0)
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ r) ρ : ℂ) / (z - ρ)‖ ≤
      (4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 +
        r / ((R ^ 2 - r * ‖z - z₀‖) * Real.log (R / r))) * Real.log M := by
  classical
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hR : 0 < R := hr.trans hrR
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hz₀R : z₀ ∈ closedBall z₀ R := mem_closedBall_self hR.le
  have hzb : z ∈ ball z₀ r := by rwa [mem_ball, dist_eq_norm]
  have hballR : ball z₀ r ⊆ ball z₀ R := ball_subset_ball hrR.le
  have hM1 : 1 ≤ M :=
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      hR hz₀ hM
  obtain ⟨G, hG, hG0, hfG⟩ := hf.exists_eq_finprod_zpow_mul hR hrR.le ⟨z₀, hz₀R, hz₀⟩
  set D := divisor f (closedBall z₀ r)
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  let S := hfin.toFinset
  have hD (ρ : ℂ) : 0 ≤ D ρ := (hf.mono (closedBall_subset_closedBall hrR.le)).divisor_nonneg ρ
  let n (ρ : ℂ) := (D ρ).toNat
  have hn (ρ : ℂ) : (n ρ : ℤ) = D ρ := Int.toNat_of_nonneg (hD ρ)
  have hρnorm (ρ : ℂ) (hρ : ρ ∈ S) : ‖ρ - z₀‖ ≤ r := by
    simpa [dist_eq_norm] using D.supportWithinDomain (hfin.mem_toFinset.1 hρ)
  set P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D ρ
  have hPs (w : ℂ) : P w = ∏ ρ ∈ S, (w - ρ) ^ n ρ := by
    dsimp only [P]
    rw [Function.FactorizedRational.finprod_apply_eq_prod hfin w]
    exact Finset.prod_congr rfl fun ρ _ ↦ by rw [← hn ρ, zpow_natCast]
  let q (ρ w : ℂ) := ((R : ℂ) ^ 2 - conj (ρ - z₀) * (w - z₀)) / (R : ℂ)
  let Q (w : ℂ) := ∏ ρ ∈ S, q ρ w ^ n ρ
  have hq (ρ : ℂ) : Differentiable ℂ (q ρ) := by dsimp [q]; fun_prop
  have hq0 (ρ w : ℂ) (hρ : ρ ∈ S) (hw : w ∈ closedBall z₀ R) : q ρ w ≠ 0 := by
    apply div_ne_zero _ hRne
    exact norm_pos_iff.mp (reflected_denom_pos hr hrR (hρnorm ρ hρ)
      (by simpa [mem_closedBall, dist_eq_norm] using hw))
  have hQ : Differentiable ℂ Q := by
    intro w
    dsimp [Q]
    exact DifferentiableAt.fun_finsetProd fun ρ _ ↦ ((hq ρ) w).pow _
  have hQ0 (w : ℂ) (hw : w ∈ closedBall z₀ R) : Q w ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦ pow_ne_zero _ (hq0 ρ w hρ hw)
  have hQouter (w : ℂ) (hw : w ∈ sphere z₀ R) : ‖Q w‖ = ‖P w‖ := by
    simp only [Q, hPs, norm_prod, norm_pow]
    apply Finset.prod_congr rfl
    intro ρ hρ
    congr 1
    have h := reflected_factor_norm ((hρnorm ρ hρ).trans_lt hrR)
      (by simpa [mem_sphere, dist_eq_norm] using hw)
    simpa only [q, sub_sub_sub_cancel_right] using h
  have hPcenter : ‖P z₀‖ ≤ ‖Q z₀‖ := by
    simp only [hPs, Q, norm_prod, norm_pow]
    refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun ρ hρ ↦ ?_
    simp only [q, sub_self, mul_zero, sub_zero, pow_two, mul_div_cancel_right₀ _ hRne,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_sub_rev]
    exact (hρnorm ρ hρ).trans hrR.le
  let B : ℂ → ℂ := G * Q
  have hBa : AnalyticOnNhd ℂ B (closedBall z₀ R) := by
    intro w hw
    exact (hG w hw).mul ((hQ.analyticAt w))
  have hB0 (w : ℂ) (hw : w ∈ closedBall z₀ r) : B w ≠ 0 :=
    mul_ne_zero (hG0 w hw) (hQ0 w (closedBall_subset_closedBall hrR.le hw))
  have hcenter : ‖f z₀‖ ≤ ‖B z₀‖ := by
    rw [hfG z₀ hz₀R, norm_mul]
    change ‖P z₀‖ * ‖G z₀‖ ≤ ‖G z₀ * Q z₀‖
    rw [norm_mul, mul_comm ‖G z₀‖]
    exact mul_le_mul_of_nonneg_right hPcenter (norm_nonneg _)
  have hBbound (w : ℂ) (hw : w ∈ closedBall z₀ R) : ‖B w‖ ≤ M * ‖B z₀‖ := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
      (by apply DifferentiableOn.diffContOnCl;
          simpa only [closure_closedBall] using hBa.differentiableOn)
      (fun u hu ↦ ?_) (subset_closure hw)
    have hu' : u ∈ sphere z₀ R := frontier_closedBall_subset_sphere hu
    have hnorm : ‖B u‖ = ‖f u‖ := by
      rw [hfG u (sphere_subset_closedBall hu'), norm_mul]
      change ‖G u * Q u‖ = ‖P u‖ * ‖G u‖
      rw [norm_mul, hQouter u hu', mul_comm]
    rw [hnorm]
    exact (hM u hu').trans (mul_le_mul_of_nonneg_left hcenter (by linarith))
  obtain ⟨L, hLd, hL⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp (U := ball z₀ r)
    ((convex_ball z₀ r).isSimplyConnected ⟨z₀, mem_ball_self hr⟩) isOpen_ball
    ((hBa.differentiableOn.mono (hballR.trans ball_subset_closedBall)).div_const (B z₀))
    (fun ⟨w, hw, h0⟩ ↦ div_ne_zero (hB0 w (ball_subset_closedBall hw))
      (hB0 z₀ (mem_closedBall_self hr.le)) h0)
  set H : ℂ → ℂ := fun w ↦ L w - L z₀
  have hre (w : ℂ) (hw : w ∈ ball z₀ r) : (H w).re ≤ Real.log M := by
    have hexp : exp (H w) = B w / B z₀ := by
      have h₁ := hL hw
      have h₂ := hL (mem_ball_self hr)
      simp only [Function.comp_apply, div_self (hB0 z₀ (mem_closedBall_self hr.le))] at h₁ h₂
      simp [H, Complex.exp_sub, h₁, h₂]
    rw [Real.le_log_iff_exp_le (by linarith), ← Complex.norm_exp, hexp, norm_div,
      div_le_iff₀ (norm_pos_iff.2 (hB0 z₀ (mem_closedBall_self hr.le)))]
    exact hBbound w (closedBall_subset_closedBall hrR.le (ball_subset_closedBall hw))
  have hPz : P z ≠ 0 := fun h0 ↦ hfz (by
    rw [hfG z (ball_subset_closedBall (hballR hzb)), h0, zero_mul])
  have hDz : D z = 0 := by
    by_contra hne
    refine hPz ?_
    dsimp only [P]
    rw [Function.FactorizedRational.finprod_apply_eq_prod hfin z]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.2 hne) (by rw [sub_self, zero_zpow _ hne])
  have hlogf : logDeriv f z = logDeriv P z + logDeriv G z := by
    have hfPG : f =ᶠ[𝓝 z] P * G := eventuallyEq_of_mem (isOpen_ball.mem_nhds (hballR hzb))
      fun w hw ↦ hfG w (ball_subset_closedBall hw)
    rw [(logDeriv_congr_nhds hfPG).eq_of_nhds,
      logDeriv_mul z hPz (hG0 z (ball_subset_closedBall hzb))
        (Function.FactorizedRational.analyticAt (hD z)).differentiableAt
        (hG z (ball_subset_closedBall (hballR hzb))).differentiableAt]
  have hlogB : deriv H z = logDeriv G z + logDeriv Q z := by
    simp only [H, deriv_sub_const]
    rw [TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball hLd hL hzb]
    simp only [div_eq_mul_inv]
    rw [logDeriv_mul_const z _ (inv_ne_zero (hB0 z₀ (mem_closedBall_self hr.le)))]
    exact logDeriv_mul z (hG0 z (ball_subset_closedBall hzb))
      (hQ0 z (ball_subset_closedBall (hballR hzb)))
      (hG z (ball_subset_closedBall (hballR hzb))).differentiableAt (hQ z)
  have hQbound : ‖logDeriv Q z‖ ≤
      (((∑ᶠ ρ, D ρ : ℤ) : ℝ)) * (r / (R ^ 2 - r * ‖z - z₀‖)) := by
    have hlogQ : logDeriv Q z = ∑ ρ ∈ S, (n ρ : ℂ) * logDeriv (q ρ) z := by
      change logDeriv (fun w : ℂ ↦ ∏ ρ ∈ S, q ρ w ^ n ρ) z = _
      rw [logDeriv_fun_prod (f := fun ρ (w : ℂ) ↦ q ρ w ^ n ρ)
        (fun ρ hρ ↦ pow_ne_zero _ (hq0 ρ z hρ
          (ball_subset_closedBall (hballR hzb))))
        (fun ρ _ ↦ ((hq ρ) z).pow _)]
      exact Finset.sum_congr rfl fun ρ _ ↦ logDeriv_fun_pow ((hq ρ) z) (n ρ)
    rw [hlogQ]
    apply (norm_sum_le _ _).trans
    have hsum : (∑ ρ ∈ S, (n ρ : ℝ)) = ((∑ᶠ ρ, D ρ : ℤ) : ℝ) := by
      rw [finsum_eq_sum_of_support_subset _ (by intro ρ hρ; exact hfin.mem_toFinset.2 hρ)]
      simp only [Int.cast_sum]
      exact Finset.sum_congr rfl fun ρ _ ↦ by exact_mod_cast hn ρ
    rw [← hsum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ρ hρ
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (reflected_logDeriv_le hr hrR (hρnorm ρ hρ) hz)
      (Nat.cast_nonneg _)
  have hden : 0 < R ^ 2 - r * ‖z - z₀‖ := by
    have : r * ‖z - z₀‖ < r * r := mul_lt_mul_of_pos_left hz hr
    nlinarith
  have hN := hf.sum_divisor_le_log_div_log hr hrR hz₀ hM
  have hQB : ‖logDeriv Q z‖ ≤
      (r / ((R ^ 2 - r * ‖z - z₀‖) * Real.log (R / r))) * Real.log M := by
    refine hQbound.trans ((mul_le_mul_of_nonneg_right hN (div_nonneg hr.le hden.le)).trans_eq ?_)
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hHbound := Complex.norm_deriv_le_of_forall_mem_ball_re_le (hLd.sub_const _)
    (sub_self _) hre hz
  rw [hlogf, ← Function.FactorizedRational.logDeriv_eq_finsum hfin hDz, add_sub_cancel_left]
  have heq : logDeriv G z = deriv H z - logDeriv Q z := by rw [hlogB]; ring
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add hHbound hQB).trans_eq (by ring))


/-- **Landau's local logarithmic-derivative lemma.** Let `f` be analytic on `closedBall z₀ R`
with `f z₀ ≠ 0` and `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`, and let `2 r ≤ R`. At every `z` with
`‖z - z₀‖ < r` and `f z ≠ 0`, the logarithmic derivative of `f` differs from `∑ m_ρ / (z - ρ)`
over the zeros `ρ` in `closedBall z₀ r`, with multiplicities `m_ρ` given by the divisor, by at
most `4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * log M`. -/
theorem norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hrR : 2 * r ≤ R) (hz₀ : f z₀ ≠ 0) {M : ℝ}
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) {z : ℂ} (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ r) ρ : ℂ) / (z - ρ)‖ ≤
      4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * Real.log M := by
  classical
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hR : 0 < R := by linarith
  have hz₀R : z₀ ∈ closedBall z₀ R := mem_closedBall_self hR.le
  have hzb : z ∈ ball z₀ r := by rwa [mem_ball, dist_eq_norm]
  have hballR : ball z₀ r ⊆ ball z₀ R := ball_subset_ball (by linarith)
  have hM1 : 1 ≤ M :=
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      hR hz₀ hM
  -- Factor `f = P G` on `closedBall z₀ R`, with `P` the product over the zeros in
  -- `closedBall z₀ r` and `G` zero-free there.
  obtain ⟨G, hG, hG0, hfG⟩ := hf.exists_eq_finprod_zpow_mul (r := r) hR (by linarith)
    ⟨z₀, hz₀R, hz₀⟩
  set D' := divisor f (closedBall z₀ r)
  have hfin : D'.support.Finite := D'.finiteSupport (isCompact_closedBall _ _)
  have hD' (ρ : ℂ) : 0 ≤ D' ρ :=
    (hf.mono (closedBall_subset_closedBall (by linarith))).divisor_nonneg ρ
  set P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D' ρ
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
    · rw [← hfG u (sphere_subset_closedBall hu), ← hfG z₀ hz₀R]
      exact hM u hu
  -- A holomorphic logarithm `h` of `G / G z₀` on `ball z₀ r`, normalized by `h z₀ = 0`, has
  -- real part at most `log M`.
  have hGz₀ : G z₀ ≠ 0 := hG0 z₀ (mem_closedBall_self hr.le)
  obtain ⟨L, hLd, hL⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp (U := ball z₀ r)
    ((convex_ball z₀ r).isSimplyConnected ⟨z₀, mem_ball_self hr⟩) isOpen_ball
    ((hG.differentiableOn.mono (hballR.trans ball_subset_closedBall)).div_const (G z₀))
    (fun ⟨w, hw, h0⟩ ↦ div_ne_zero (hG0 w (ball_subset_closedBall hw)) hGz₀ h0)
  set h : ℂ → ℂ := fun w ↦ L w - L z₀
  have hre (w : ℂ) (hw : w ∈ ball z₀ r) : (h w).re ≤ Real.log M := by
    have hexp : Complex.exp (h w) = G w / G z₀ := by
      have h₁ := hL hw
      have h₂ := hL (mem_ball_self hr)
      simp only [Function.comp_apply, div_self hGz₀] at h₁ h₂
      simp [h, Complex.exp_sub, h₁, h₂]
    rw [Real.le_log_iff_exp_le (by linarith), ← Complex.norm_exp, hexp, norm_div,
      div_le_iff₀ (norm_pos_iff.2 hGz₀)]
    exact hGle w (ball_subset_closedBall (hballR hw))
  -- Split `logDeriv f z = logDeriv P z + h' z` and evaluate `logDeriv P z`.
  have hPz : P z ≠ 0 := fun h0 ↦
    hfz (by rw [hfG z (ball_subset_closedBall (hballR hzb)), h0, zero_mul])
  have hDz : D' z = 0 := by
    by_contra hne
    refine hPz ?_
    rw [hPs]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.2 hne) (by rw [sub_self, zero_zpow _ hne])
  have hlogf : logDeriv f z = logDeriv P z + logDeriv G z := by
    have hfPG : f =ᶠ[𝓝 z] P * G := eventuallyEq_of_mem (isOpen_ball.mem_nhds (hballR hzb))
      fun w hw ↦ hfG w (ball_subset_closedBall hw)
    rw [(logDeriv_congr_nhds hfPG).eq_of_nhds,
      logDeriv_mul z hPz (hG0 z (ball_subset_closedBall hzb))
        (Function.FactorizedRational.analyticAt (hD' z)).differentiableAt
        (hG z (ball_subset_closedBall (hballR hzb))).differentiableAt]
  have hlogG : deriv h z = logDeriv G z := by
    simp only [h, deriv_sub_const]
    rw [TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball hLd hL hzb]
    simp only [div_eq_mul_inv]
    exact logDeriv_mul_const z _ (inv_ne_zero hGz₀)
  rw [hlogf, ← Function.FactorizedRational.logDeriv_eq_finsum hfin hDz, add_sub_cancel_left,
    ← hlogG]
  exact Complex.norm_deriv_le_of_forall_mem_ball_re_le (hLd.sub_const _) (sub_self _) hre hz

/-- **Landau's local logarithmic-derivative lemma** in the classical normalization. Let `f` be
analytic on `closedBall z₀ R` with `0 < R`, `f z₀ ≠ 0` and `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`.
At every `z` with `‖z - z₀‖ ≤ R / 4` and `f z ≠ 0`, the logarithmic derivative of `f` differs
from `∑ m_ρ / (z - ρ)` over the zeros `ρ` in `closedBall z₀ (R / 2)`, with multiplicities `m_ρ`
given by the divisor, by at most `48 / R * log M`. This is
`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le` with `r = R / 2`. -/
theorem norm_logDeriv_sub_finsum_divisor_half_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : 0 < R) (hz₀ : f z₀ ≠ 0) {M : ℝ} (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    {z : ℂ} (hz : ‖z - z₀‖ ≤ R / 4) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ (R / 2)) ρ : ℂ) / (z - ρ)‖ ≤
      48 / R * Real.log M := by
  have hM1 : 1 ≤ M :=
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      hR hz₀ hM
  refine (hf.norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le
    (by linarith) hz₀ hM (by linarith) hfz).trans
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
  have h₁ := hf.norm_logDeriv_sub_finsum_divisor_half_le (by norm_num) (by norm_num) hM
    (by simpa using hz) (sub_ne_zero.2 hz1)
  have h42 : (4 : ℝ) / 2 = 2 := by norm_num
  rw [h42] at h₁
  norm_num at h₁
  exact h₁
