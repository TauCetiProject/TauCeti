/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.Analysis.Complex.CanonicalFactor
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Meromorphic.FactorizedRational
import TauCeti.Analysis.RCLike.Basic

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
  `2 r ≤ R`, with bound `4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * log M`.
* `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_half_le`: the classical `48 / R * log M` bound
  at `R / 2` and `R / 4`.
* `AnalyticOnNhd.neg_re_logDeriv_add_sum_divisor_le`,
  `AnalyticOnNhd.neg_re_logDeriv_add_sum_divisor_half_le`,
  `AnalyticOnNhd.sub_inv_re_le_divisor_mul`, and
  `AnalyticOnNhd.neg_re_logDeriv_add_sub_inv_le`: the retained-zero real-part inequalities summing
  over an arbitrary `S : Finset ℂ` when all omitted zeros in the inner disc (`ρ ∉ S`) have real
  part at most `z.re`, for general `2 r ≤ R` and at `r = R / 2`, together with the single-zero term
  bound `((z - ρ)⁻¹).re ≤ m_ρ ((z - ρ)⁻¹).re` and its horizontal-line specialization.
* `TauCeti.exists_neg_re_logDeriv_add_sum_divisor_half_le`: the uniform disc form converting a
  centre lower bound `b ≤ ‖f z₀‖` and sphere bound `‖f w‖ ≤ c * K` (`1 < K₀ ≤ K`) into an
  `O(log K)` bound with constant depending only on `(R, b, c, K₀)`.

## Implementation notes

`AnalyticOnNhd.finprod_zpow_factorization` writes `f = P G`, removing the inner-disc zeros.
For arbitrary radii, multiply `G` by the numerators of `Complex.canonicalFactor`; their circle
norm agrees with that of `P`, and their central norm dominates it. The maximum modulus principle
transfers the relative bound to this product.
`Complex.norm_logDeriv_le_of_forall_mem_ball_norm_le_mul` bounds its logarithmic derivative using
a normalized holomorphic logarithm and the Borel–Carathéodory derivative estimate.
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

-- Remove the inner-disc zeros and identify the remaining logarithmic derivative once.
private lemma exists_factor_logDeriv_eq {z : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R)) (hrR : r ≤ R)
    (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) :
    let D := divisor f (closedBall z₀ r)
    ∃ (G : ℂ → ℂ) (hfin : D.support.Finite), (∀ ρ, 0 ≤ D ρ) ∧
      (∀ w : ℂ, (∏ᶠ ρ, (· - ρ) ^ D ρ) w = ∏ ρ ∈ hfin.toFinset, (w - ρ) ^ D ρ) ∧
      AnalyticOnNhd ℂ G (closedBall z₀ R) ∧
      (∀ w ∈ closedBall z₀ r, G w ≠ 0) ∧
      (∀ w ∈ closedBall z₀ R,
        f w = (∏ᶠ ρ, (· - ρ) ^ divisor f (closedBall z₀ r) ρ) w * G w) ∧
      logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ r) ρ : ℂ) / (z - ρ) =
        logDeriv G z := by
  classical
  have hzb : z ∈ ball z₀ r := by rwa [mem_ball, dist_eq_norm]
  have hzR : z ∈ ball z₀ R := ball_subset_ball hrR hzb
  let D := divisor f (closedBall z₀ r)
  let G := toMeromorphicNFOn ((∏ᶠ ρ, (· - ρ) ^ D ρ)⁻¹ • f) D.support
  obtain ⟨hG, hG0, hglobal, _⟩ := hf.finprod_zpow_factorization hrR
    ⟨z, ball_subset_closedBall hzR, hfz⟩
  have hfG : ∀ w ∈ closedBall z₀ R,
      f w = (∏ᶠ ρ, (· - ρ) ^ D ρ) w * G w := fun w _ ↦ by
    exact congrFun hglobal w
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hD (ρ : ℂ) : 0 ≤ D ρ := (hf.mono (closedBall_subset_closedBall hrR)).divisor_nonneg ρ
  refine ⟨G, hfin, hD, Function.FactorizedRational.finprod_apply_eq_prod hfin, hG, hG0, hfG, ?_⟩
  have hDz : D z = 0 := (hf z (ball_subset_closedBall hzR)).divisor_apply_eq_zero hfz
  have hfPG : f =ᶠ[𝓝 z] (∏ᶠ ρ, (· - ρ) ^ D ρ) * G :=
    .of_eq (funext fun w ↦ congrFun hglobal w)
  have h := Function.FactorizedRational.logDeriv_sub_sum_eq hfin hDz
    (hG z (ball_subset_closedBall hzR)).differentiableAt (hG0 z (ball_subset_closedBall hzb)) hfPG
  rw [← finsum_eq_sum_of_support_subset (fun ρ ↦ (D ρ : ℂ) / (z - ρ))
    (s := hfin.toFinset)
    (fun ρ hρ ↦ hfin.mem_toFinset.mpr fun hzero ↦ hρ (by simp [hzero]))] at h
  simpa only [D] using h

-- Sum the logarithmic derivatives of the finite reflected product with integer multiplicities.
private lemma norm_logDeriv_reflected_prod_le {S : Finset ℂ} {n : ℂ → ℤ} {z : ℂ}
    (hrR : r < R) (hn : ∀ ρ ∈ S, 0 ≤ n ρ)
    (hρnorm : ∀ ρ ∈ S, ‖ρ - z₀‖ ≤ r) (hz : ‖z - z₀‖ ≤ r) :
    ‖logDeriv (fun w : ℂ ↦ ∏ ρ ∈ S,
      (canonicalFactorNumerator R (ρ - z₀) (w - z₀)) ^ n ρ) z‖ ≤
      (∑ ρ ∈ S, (n ρ : ℝ)) * (r / (R ^ 2 - r * ‖z - z₀‖)) := by
  let q (ρ w : ℂ) := canonicalFactorNumerator R (ρ - z₀) (w - z₀)
  have hq (ρ : ℂ) : Differentiable ℂ (q ρ) :=
    (differentiable_canonicalFactorNumerator R (ρ - z₀)).comp (differentiable_id.sub_const z₀)
  have hq0 (ρ : ℂ) (hρ : ρ ∈ S) : q ρ z ≠ 0 :=
    canonicalFactorNumerator_ne_zero ((hρnorm ρ hρ).trans_lt hrR) (hz.trans hrR.le)
  rw [logDeriv_fun_prod (f := fun ρ (w : ℂ) ↦ q ρ w ^ n ρ)
    (fun ρ hρ ↦ zpow_ne_zero _ (hq0 ρ hρ))
    (fun ρ hρ ↦ ((hq ρ) z).zpow (.inr (hn ρ hρ)))]
  simp_rw [logDeriv_fun_zpow ((hq _) z)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (Int.cast_nonneg (hn ρ hρ))]
  apply mul_le_mul_of_nonneg_left _ (Int.cast_nonneg (hn ρ hρ))
  simpa only [q] using
    norm_logDeriv_canonicalFactorNumerator_comp_sub_le hrR (hρnorm ρ hρ) hz

-- Package the reflected product's analytic, boundary, central and logarithmic-derivative data.
private lemma exists_reflected_prod {S : Finset ℂ} {n : ℂ → ℤ} {z : ℂ}
    (hrR : r < R) (hn : ∀ ρ ∈ S, 0 ≤ n ρ)
    (hρnorm : ∀ ρ ∈ S, ‖ρ - z₀‖ ≤ r) (hz : ‖z - z₀‖ ≤ r) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧
      (∀ w ∈ closedBall z₀ R, Q w ≠ 0) ∧
      (∀ w ∈ sphere z₀ R, ‖Q w‖ = ‖∏ ρ ∈ S, (w - ρ) ^ n ρ‖) ∧
      ‖∏ ρ ∈ S, (z₀ - ρ) ^ n ρ‖ ≤ ‖Q z₀‖ ∧
      ‖logDeriv Q z‖ ≤ (∑ ρ ∈ S, (n ρ : ℝ)) *
        (r / (R ^ 2 - r * ‖z - z₀‖)) := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  have hR : 0 < R := hr.trans_lt hrR
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  let q (ρ w : ℂ) := canonicalFactorNumerator R (ρ - z₀) (w - z₀)
  let Q (w : ℂ) := ∏ ρ ∈ S, q ρ w ^ n ρ
  have hq (ρ : ℂ) : Differentiable ℂ (q ρ) :=
    (differentiable_canonicalFactorNumerator R (ρ - z₀)).comp (differentiable_id.sub_const z₀)
  have hq0 (ρ w : ℂ) (hρ : ρ ∈ S) (hw : w ∈ closedBall z₀ R) : q ρ w ≠ 0 :=
    canonicalFactorNumerator_ne_zero ((hρnorm ρ hρ).trans_lt hrR)
      (by simpa [mem_closedBall, dist_eq_norm] using hw)
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    exact DifferentiableAt.fun_finsetProd fun ρ hρ ↦ ((hq ρ) w).zpow (.inr (hn ρ hρ))
  · exact fun w hw ↦ Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦ zpow_ne_zero _ (hq0 ρ w hρ hw)
  · intro w hw
    simp only [Q, norm_prod, norm_zpow]
    apply Finset.prod_congr rfl
    intro ρ _hρ
    congr 1
    have h := norm_canonicalFactorNumerator_eval_circle (a := ρ - z₀) hR.ne'
      (by simpa [mem_sphere, dist_eq_norm] using hw)
    have heq : w - z₀ - (ρ - z₀) = w - ρ := by ring
    rw [heq] at h
    simpa only [q] using h
  · simp only [Q, norm_prod, norm_zpow]
    refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun ρ hρ ↦ ?_
    simp only [q, canonicalFactorNumerator_apply, sub_self, mul_zero, sub_zero, pow_two,
      mul_div_cancel_right₀ _ hRne,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply zpow_le_zpow_left₀ (hn ρ hρ) (norm_nonneg _)
    rw [norm_sub_rev]
    exact (hρnorm ρ hρ).trans hrR.le
  · simpa only [Q, q] using norm_logDeriv_reflected_prod_le hrR hn hρnorm hz

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
        (r / (R ^ 2 - r * ‖z - z₀‖)) ∧
      ((∑ᶠ ρ, divisor f (closedBall z₀ r) ρ : ℤ) : ℝ) ≤
        Real.log M / Real.log (R / r) := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hR : 0 < R := hr.trans hrR
  have hz₀R := mem_closedBall_self hR.le (x := z₀)
  have hzR : z ∈ closedBall z₀ R := by simpa [mem_closedBall, dist_eq_norm] using hz.le.trans hrR.le
  have hz₀ := DiffContOnCl.ne_zero_of_forall_mem_sphere_norm_le_mul
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl) hM hzR hfz
  have hM1 : 1 ≤ M :=
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      hR hz₀ hM
  obtain ⟨G, hfin, hD, hPs, hG, hG0, hfG, hlogf⟩ :=
    exists_factor_logDeriv_eq hf hrR.le hz hfz
  let D := divisor f (closedBall z₀ r)
  obtain ⟨Q, hQ, hQ0, hQouter, hPcenter, hQbound⟩ := exists_reflected_prod (n := D) hrR
    (fun ρ _ ↦ hD ρ) (S := hfin.toFinset)
    (fun ρ hρ ↦ by simpa [dist_eq_norm] using D.supportWithinDomain (hfin.mem_toFinset.1 hρ)) hz.le
  let B : ℂ → ℂ := G * Q
  have hBa : AnalyticOnNhd ℂ B (closedBall z₀ R) := fun w hw ↦ (hG w hw).mul (hQ.analyticAt w)
  have hB0 : ∀ w ∈ closedBall z₀ r, B w ≠ 0 :=
    fun w hw ↦ mul_ne_zero (hG0 w hw) (hQ0 w (closedBall_subset_closedBall hrR.le hw))
  have hcenter : ‖f z₀‖ ≤ ‖B z₀‖ := by
    rw [hfG z₀ hz₀R, hPs, norm_mul]
    exact (mul_le_mul_of_nonneg_right hPcenter (norm_nonneg _)).trans_eq (by simp [B, mul_comm])
  have hBbound (w : ℂ) (hw : w ∈ closedBall z₀ R) : ‖B w‖ ≤ M * ‖B z₀‖ := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
      (by apply DifferentiableOn.diffContOnCl
          simpa only [closure_closedBall] using hBa.differentiableOn)
      (fun u hu ↦ ?_) (subset_closure hw)
    have hu' := frontier_closedBall_subset_sphere hu
    have heq : ‖B u‖ = ‖f u‖ := by
      rw [hfG u (sphere_subset_closedBall hu'), hPs, norm_mul]
      simp only [B, D, Pi.mul_apply, norm_mul, hQouter u hu', mul_comm]
    rw [heq]
    exact (hM u hu').trans (mul_le_mul_of_nonneg_left hcenter (by linarith))
  refine ⟨B, Q, hBa.mono (closedBall_subset_closedBall hrR.le), hB0,
    fun w hw ↦ hBbound w (closedBall_subset_closedBall hrR.le hw), ?_, ?_,
    hf.sum_divisor_le_log_div_log hr hrR hz₀ hM⟩
  · dsimp only [B]
    rw [hlogf, logDeriv_mul z
      (hG0 z (by simpa [mem_closedBall, dist_eq_norm] using hz.le))
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
  obtain ⟨B, Q, hB, hB0, hBM, hlogf, hQbound, hN⟩ :=
    exists_reflected_cofactor hf hrR hM hz hfz
  have hden := sq_sub_mul_norm_pos (hr.trans hrR) hrR (hz.le.trans hrR.le)
  have hQB : ‖logDeriv Q z‖ ≤
      (r / ((R ^ 2 - r * ‖z - z₀‖) * Real.log (R / r))) * Real.log M := by
    refine hQbound.trans ((mul_le_mul_of_nonneg_right hN (div_nonneg hr.le hden.le)).trans_eq ?_)
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hlogf]
  exact (norm_sub_le _ _).trans
    ((add_le_add (Complex.norm_logDeriv_le_of_forall_mem_ball_norm_le_mul
      (hB.differentiableOn.mono ball_subset_closedBall)
      (fun w hw ↦ hB0 w (ball_subset_closedBall hw))
      (fun w hw ↦ hBM w (ball_subset_closedBall hw)) hz) hQB).trans_eq (by ring))

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
  obtain ⟨G, hfin, hD', hPs, hG, hG0, hfG, hlogf⟩ := exists_factor_logDeriv_eq hf
    (by linarith) hz hfz
  set D' := divisor f (closedBall z₀ r)
  set P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D' ρ
  have hfPG (w : ℂ) (hw : w ∈ closedBall z₀ R) : f w = P w * G w := by
    simpa only [P, D'] using hfG w hw
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
  exact Complex.norm_logDeriv_le_of_forall_mem_ball_norm_le_mul
    (hG.differentiableOn.mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith))))
    (fun w hw ↦ hG0 w (ball_subset_closedBall hw))
    (fun w hw ↦ hGle w (closedBall_subset_closedBall (by linarith)
      (ball_subset_closedBall hw))) hz

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
  have hz₀ := DiffContOnCl.ne_zero_of_forall_mem_sphere_norm_le_mul
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl) hM
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

/-- At a zero `ρ ∈ U` of an analytic function `f` on a preconnected set `U` where `f` is not
identically zero, if `ρ.re ≤ z.re` then `((z - ρ)⁻¹).re` is bounded above by the divisor-weighted
term `(divisor f U ρ : ℝ) * ((z - ρ)⁻¹).re`. -/
theorem sub_inv_re_le_divisor_mul {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (h0 : ∃ w ∈ U, f w ≠ 0) {ρ z : ℂ} (hρ : ρ ∈ U) (hfρ : f ρ = 0) (hre : ρ.re ≤ z.re) :
    ((z - ρ)⁻¹).re ≤ (divisor f U ρ : ℝ) * ((z - ρ)⁻¹).re := by
  have hD : (1 : ℝ) ≤ (divisor f U ρ : ℝ) :=
    mod_cast hf.one_le_divisor_of_eq_zero hU h0 hρ hfρ
  have hnonneg : 0 ≤ ((z - ρ)⁻¹).re :=
    Complex.inv_re_nonneg.2 (by simpa using sub_nonneg.2 hre)
  exact le_mul_of_one_le_left hnonneg hD

/-- **Retained-zero real-part form of Landau's lemma.** Let `f` be analytic on `closedBall z₀ R`
with `2 r ≤ R` and `‖f w‖ ≤ M * ‖f z₀‖` on `sphere z₀ R`. Suppose `‖z - z₀‖ < r`, `f z ≠ 0`, and
for a finite set `S : Finset ℂ`, every omitted zero `ρ ∈ closedBall z₀ r` (`ρ ∉ S`) of `f`
satisfies `ρ.re ≤ z.re`. Then
`-(logDeriv f z).re + ∑ ρ ∈ S, (divisor f (closedBall z₀ r) ρ : ℝ) * ((z - ρ)⁻¹).re ≤
  4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * Real.log M`. -/
theorem neg_re_logDeriv_add_sum_divisor_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hrR : 2 * r ≤ R) {M : ℝ} (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    {z : ℂ} (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) (S : Finset ℂ)
    (hre : ∀ ρ ∈ closedBall z₀ r, ρ ∉ S → f ρ = 0 → ρ.re ≤ z.re) :
    -(logDeriv f z).re +
        ∑ ρ ∈ S, (divisor f (closedBall z₀ r) ρ : ℝ) * ((z - ρ)⁻¹).re ≤
      4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * Real.log M :=
  have _ : 0 < r := (norm_nonneg _).trans_lt hz
  AnalyticOnNhd.neg_re_logDeriv_add_sum_divisor_le_of_norm_le
    (hf.mono (closedBall_subset_closedBall (by linarith)))
    (isCompact_closedBall _ _) S hre
    (hf.norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le hrR hM hz hfz)

/-- **Retained-zero real-part form of Landau's lemma** in the classical normalization. Let `f` be
analytic on `closedBall z₀ R` with `R ≠ 0` and `‖f w‖ ≤ M * ‖f z₀‖` on `sphere z₀ R`. Suppose
`‖z - z₀‖ ≤ R / 4`, `f z ≠ 0`, and for a finite set `S : Finset ℂ`, every omitted zero
`ρ ∈ closedBall z₀ (R / 2)` (`ρ ∉ S`) of `f` satisfies `ρ.re ≤ z.re`. Then
`-(logDeriv f z).re + ∑ ρ ∈ S, (divisor f (closedBall z₀ (R / 2)) ρ : ℝ) * ((z - ρ)⁻¹).re ≤
  48 / R * Real.log M`. This is `AnalyticOnNhd.neg_re_logDeriv_add_sum_divisor_le` at `r = R / 2`.
-/
theorem neg_re_logDeriv_add_sum_divisor_half_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : R ≠ 0) {M : ℝ} (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    {z : ℂ} (hz : ‖z - z₀‖ ≤ R / 4) (hfz : f z ≠ 0) (S : Finset ℂ)
    (hre : ∀ ρ ∈ closedBall z₀ (R / 2), ρ ∉ S → f ρ = 0 → ρ.re ≤ z.re) :
    -(logDeriv f z).re +
        ∑ ρ ∈ S, (divisor f (closedBall z₀ (R / 2)) ρ : ℝ) * ((z - ρ)⁻¹).re ≤
      48 / R * Real.log M :=
  have hRpos : 0 < R := lt_of_le_of_ne (by linarith [norm_nonneg (z - z₀)]) hR.symm
  AnalyticOnNhd.neg_re_logDeriv_add_sum_divisor_le_of_norm_le
    (hf.mono (closedBall_subset_closedBall (by linarith)))
    (isCompact_closedBall _ _) S hre
    (hf.norm_logDeriv_sub_finsum_divisor_half_le hRpos hM hz hfz)

/-- Retaining a single zero `ρ` on the horizontal line `Im = ρ.im` inside a divisor-sum upper
bound: if `f` is analytic on `closedBall (σ₀ + ρ.im * I) r`, nonzero at the centre, and vanishes at
`ρ` with `|ρ.re - σ₀| ≤ r` and `ρ.re ≤ σ`, then the `S = {ρ}` sum contributes at least
`(σ - ρ.re)⁻¹`. -/
theorem neg_re_logDeriv_add_sub_inv_le {σ₀ σ B : ℝ} {ρ : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall ((σ₀ : ℂ) + ρ.im * Complex.I) r))
    (hfz₀ : f ((σ₀ : ℂ) + ρ.im * Complex.I) ≠ 0) (hρ : |ρ.re - σ₀| ≤ r) (hfρ : f ρ = 0)
    (hre : ρ.re ≤ σ)
    (hsum : -(logDeriv f ((σ : ℂ) + ρ.im * Complex.I)).re +
        ∑ w ∈ ({ρ} : Finset ℂ),
          (divisor f (closedBall ((σ₀ : ℂ) + ρ.im * Complex.I) r) w : ℝ) *
            ((((σ : ℂ) + ρ.im * Complex.I) - w)⁻¹).re ≤ B) :
    -(logDeriv f ((σ : ℂ) + ρ.im * Complex.I)).re + (σ - ρ.re)⁻¹ ≤ B := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hρ
  have hmem : ρ ∈ closedBall ((σ₀ : ℂ) + ρ.im * Complex.I) r := by
    rw [mem_closedBall, dist_eq_norm, RCLike.norm_sub_eq_abs_re_sub_of_im_eq (by simp)]
    simpa using hρ
  have hterm := hf.sub_inv_re_le_divisor_mul (z := (σ : ℂ) + ρ.im * Complex.I)
    (convex_closedBall _ _).isPreconnected ⟨_, mem_closedBall_self hr, hfz₀⟩
    hmem hfρ (by simpa using hre)
  have hdiff : ((σ : ℂ) + ρ.im * Complex.I) - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    simpa using RCLike.sub_eq_ofReal_re_sub_of_im_eq (z := (σ : ℂ) + ρ.im * Complex.I) (w := ρ)
      (by simp)
  rw [Finset.sum_singleton] at hsum
  rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re] at hterm hsum
  linarith

end AnalyticOnNhd

namespace TauCeti

/-- **Uniform disc form of Landau's retained-zero inequality.** Fix a nonzero radius `R ≠ 0`, a
centre lower bound `b > 0`, a growth factor `c`, and a base `K₀ > 1`. There is a constant `A > 0`
depending only on `(R, b, c, K₀)` such that for every `f` analytic on `closedBall z₀ R` with
`b ≤ ‖f z₀‖` and `‖f w‖ ≤ c * K` on `sphere z₀ R` (`K₀ ≤ K`), at every `z` with `‖z - z₀‖ ≤ R / 4`,
`f z ≠ 0`, and for every finite set `S : Finset ℂ` such that every omitted zero
`ρ ∈ closedBall z₀ (R / 2)` (`ρ ∉ S`) satisfies `ρ.re ≤ z.re`,
`-(logDeriv f z).re + ∑ ρ ∈ S, (divisor f (closedBall z₀ (R / 2)) ρ : ℝ) * ((z - ρ)⁻¹).re ≤
  A * Real.log K`. -/
theorem exists_neg_re_logDeriv_add_sum_divisor_half_le
    {R b c K₀ : ℝ} (hR : R ≠ 0) (hb : 0 < b) (hK₀ : 1 < K₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ {f : ℂ → ℂ} {z₀ z : ℂ} {K : ℝ},
      AnalyticOnNhd ℂ f (closedBall z₀ R) →
      b ≤ ‖f z₀‖ →
      (∀ w ∈ sphere z₀ R, ‖f w‖ ≤ c * K) →
      ‖z - z₀‖ ≤ R / 4 →
      f z ≠ 0 →
      ∀ S : Finset ℂ,
        (∀ ρ ∈ closedBall z₀ (R / 2), ρ ∉ S → f ρ = 0 → ρ.re ≤ z.re) →
        K₀ ≤ K →
        -(logDeriv f z).re +
            ∑ ρ ∈ S, (divisor f (closedBall z₀ (R / 2)) ρ : ℝ) * ((z - ρ)⁻¹).re ≤
          A * Real.log K := by
  have : 0 < |R| := abs_pos.2 hR
  set C₀ : ℝ := max 1 c / b
  have hC₀ : 0 < C₀ := by positivity
  have hlogK₀ : 0 < Real.log K₀ := Real.log_pos hK₀
  refine ⟨48 / |R| * (max 0 (Real.log C₀) / Real.log K₀ + 1), by positivity,
    fun {f z₀ z K} hf hb₀ hM₀ hz hfz S hre hK ↦ ?_⟩
  have hRpos : 0 < R := lt_of_le_of_ne (by linarith [norm_nonneg (z - z₀)]) hR.symm
  have hK_pos : 0 < K := (zero_lt_one.trans hK₀).trans_le hK
  have h1le : 1 ≤ b⁻¹ * ‖f z₀‖ := (le_inv_mul_iff₀ hb).2 (by simpa using hb₀)
  have hM (w : ℂ) (hw : w ∈ sphere z₀ R) : ‖f w‖ ≤ C₀ * K * ‖f z₀‖ := by
    calc ‖f w‖ ≤ c * K := hM₀ w hw
      _ ≤ max 1 c * K := mul_le_mul_of_nonneg_right (le_max_right _ _) hK_pos.le
      _ ≤ max 1 c * K * (b⁻¹ * ‖f z₀‖) := le_mul_of_one_le_right (by positivity) h1le
      _ = C₀ * K * ‖f z₀‖ := by simp only [C₀, div_eq_mul_inv]; ring
  have hmain := hf.neg_re_logDeriv_add_sum_divisor_half_le hR hM hz hfz S hre
  have hlog_ge : Real.log K₀ ≤ Real.log K := Real.log_le_log (zero_lt_one.trans hK₀) hK
  have hmax : Real.log C₀ ≤ max 0 (Real.log C₀) / Real.log K₀ * Real.log K :=
    (le_max_right _ _).trans (le_div_mul_of_le (le_max_left _ _) hlogK₀ hlog_ge)
  rw [Real.log_mul hC₀.ne' hK_pos.ne'] at hmain
  rw [abs_of_pos hRpos]
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_left hmax (Real.log K))
    (by positivity : (0 : ℝ) ≤ 48 / R)
  linarith

end TauCeti

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
