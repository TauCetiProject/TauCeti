/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Landau's local logarithmic-derivative lemma

Let `f` be analytic on `closedBall z₀ R`, with `0 < R`, `f z₀ ≠ 0` and `‖f w‖ ≤ M ‖f z₀‖` on
`sphere z₀ R`. Near `z₀` the logarithmic derivative of `f` is then its partial-fraction part over
the zeros close to `z₀`, up to an error of size `log M / R`:
for `‖z - z₀‖ ≤ R / 4` with `f z ≠ 0`,
`‖logDeriv f z - ∑_{‖ρ - z₀‖ ≤ R / 2} m_ρ / (z - ρ)‖ ≤ 48 log M / R`.
Multiplicities are the values of Mathlib's divisor
`MeromorphicOn.divisor f (closedBall z₀ (R / 2))`. The companion bound of at most
`log M / log 2` such zeros, counted with multiplicity, is
`AnalyticOnNhd.sum_divisor_half_le` in `TauCeti.Analysis.Complex.JensenFormula`.

The lemma turns an upper bound for `‖f‖` on a circle, relative to the value at a single point
where `f` does not vanish, into a local description of `logDeriv f` by its nearby zeros, without
any lower bound for `‖f‖`. This is how growth bounds for entire functions of finite order, and
for L-functions in particular, become bounds for their logarithmic derivatives: the zeros near a
point are counted by Jensen's formula, and the remaining part of `logDeriv f` is bounded.

## Main results

* `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le`: the lemma for zeros in `closedBall z₀ r`
  with `2 r ≤ R` and any `z` with `‖z - z₀‖ < r`, with the bound
  `4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * log M`.
* `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_half_le`: the classical radii `R / 2` and
  `R / 4`, with the bound `48 / R * log M`.

## Implementation notes

The proof is the classical one. Write `f = P G` on `closedBall z₀ R`, where `P` is the finite
product of the factors `(z - ρ) ^ m_ρ` over the zeros in the smaller disc and `G` has no zeros
there (`AnalyticOnNhd.exists_eq_finprod_zpow_mul`). On the outer sphere every factor of `P` is at
least as large as at the centre, so the maximum modulus principle gives `‖G‖ ≤ M ‖G z₀‖` on the
whole disc (`Complex.norm_le_of_forall_mem_sphere_norm_mul_le`). The logarithmic derivative of
`P` is `∑ m_ρ / (z - ρ)` (`Function.FactorizedRational.logDeriv_eq_finsum`). A holomorphic
logarithm `h` of `G / G z₀` on the smaller disc has `h z₀ = 0` and `re h ≤ log M`, so the
Borel–Carathéodory theorem and the Cauchy estimate bound `h' = logDeriv f - logDeriv P`
(`Complex.norm_deriv_le_of_forall_mem_ball_re_le`).

## References

* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §3.9, Lemma α.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Lemma 6.3.
-/

public section

open Metric MeromorphicOn Filter Topology Set

namespace AnalyticOnNhd

variable {f : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}

/-- **Landau's local logarithmic-derivative lemma.** Let `f` be analytic on `closedBall z₀ R`
with `f z₀ ≠ 0` and `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`, and let `2 r ≤ R`. At every `z` with
`‖z - z₀‖ < r` and `f z ≠ 0`, the logarithmic derivative of `f` differs from `∑ m_ρ / (z - ρ)`
over the zeros `ρ` in `closedBall z₀ r`, with multiplicities `m_ρ` given by the divisor, by at
most `4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * log M`. -/
theorem norm_logDeriv_sub_finsum_divisor_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
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
`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le` with `r = R / 2`. -/
theorem norm_logDeriv_sub_finsum_divisor_half_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : 0 < R) (hz₀ : f z₀ ≠ 0) {M : ℝ} (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    {z : ℂ} (hz : ‖z - z₀‖ ≤ R / 4) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ (R / 2)) ρ : ℂ) / (z - ρ)‖ ≤
      48 / R * Real.log M := by
  have hM1 : 1 ≤ M :=
    (hf.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      hR hz₀ hM
  refine (hf.norm_logDeriv_sub_finsum_divisor_le (by linarith) hz₀ hM (by linarith) hfz).trans
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
