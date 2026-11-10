/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.FactorizedRational
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Landau's local logarithmic-derivative lemma

Let `f` be analytic on `closedBall z₀ R` with `f z₀ ≠ 0` and `‖f w‖ ≤ M ‖f z₀‖` on
`sphere z₀ R`. Near `z₀` the logarithmic derivative of `f` is then its partial-fraction part over
the zeros close to `z₀`, up to an error of size `log M / R`:
for `‖z - z₀‖ ≤ R / 4` with `f z ≠ 0`,
`‖logDeriv f z - ∑_{‖ρ - z₀‖ ≤ R / 2} m_ρ / (z - ρ)‖ ≤ 48 log M / R`,
and there are at most `log M / log 2` such zeros, counted with multiplicity. Multiplicities are
the values of Mathlib's divisor `MeromorphicOn.divisor f (closedBall z₀ (R / 2))`.

The proof is the classical one (Titchmarsh, §3.9; Montgomery–Vaughan, Lemma 6.3). Write
`f = P G` on `closedBall z₀ R`, where `P` is the finite product of the factors `(z - ρ) ^ m_ρ`
over the zeros in the smaller disc and `G` has no zeros there. On the outer sphere every factor of
`P` is at least as large as at the centre, so the maximum modulus principle gives
`‖G‖ ≤ M ‖G z₀‖` on the whole disc. A holomorphic logarithm `h` of `G / G z₀` on the smaller disc
has `h z₀ = 0` and `re h ≤ log M`, so the Borel–Carathéodory theorem bounds `‖h‖`, and the Cauchy
estimate bounds `h' = logDeriv f - logDeriv P`.

## Main results

* `AnalyticOnNhd.exists_eq_finprod_zpow_mul`: dividing out the zeros in a smaller closed disc.
* `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le`: the lemma for zeros in `closedBall z₀ r`
  with `2 r ≤ R` and any `z` with `‖z - z₀‖ < r`, with the bound
  `4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * log M`.
* `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_half_le`: the classical radii `R / 2` and
  `R / 4`, with the bound `48 / R * log M`.
* `AnalyticOnNhd.finsum_divisor_le_log_div_log`, `AnalyticOnNhd.finsum_divisor_half_le`: Jensen's
  count of the zeros under the same relative bound.

## References

* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., §3.9.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Lemma 6.3.
-/

public section

open Metric MeromorphicOn Filter Topology Set

namespace AnalyticOnNhd

variable {f : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}

/-- **Dividing out the zeros in a smaller disc.** If `f` is analytic on `closedBall z₀ R` and not
identically zero there, and `r ≤ R`, then `f = (∏ᶠ ρ, (· - ρ) ^ m_ρ) * G` on `closedBall z₀ R`,
where `m_ρ` is the divisor of `f` on `closedBall z₀ r` and `G` is analytic on `closedBall z₀ R`
without zeros in `closedBall z₀ r`. -/
theorem exists_eq_finprod_zpow_mul (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : 0 < R) (hrR : r ≤ R) (h₀ : ∃ u ∈ closedBall z₀ R, f u ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (closedBall z₀ R) ∧ (∀ z ∈ closedBall z₀ r, G z ≠ 0) ∧
      ∀ z ∈ closedBall z₀ R,
        f z = (∏ᶠ ρ, (z - ρ) ^ divisor f (closedBall z₀ r) ρ) * G z := by
  classical
  set D := divisor f (closedBall z₀ R)
  set D' := divisor f (closedBall z₀ r)
  have hz₀R : z₀ ∈ closedBall z₀ R := mem_closedBall_self hR.le
  have hconn : IsConnected (closedBall z₀ R) :=
    (convex_closedBall z₀ R).isConnected ⟨z₀, hz₀R⟩
  obtain ⟨g, hg, hg0, hfg⟩ := hf.meromorphicOn.extract_zeros_poles
    (fun u ↦ hf.meromorphicOrderAt_ne_top_of_exists_ne_zero hconn h₀ u.2)
    (D.finiteSupport (isCompact_closedBall z₀ R))
  have hD' (ρ : ℂ) : D' ρ = if ρ ∈ closedBall z₀ r then D ρ else 0 := by
    rw [show D' = divisor f (closedBall z₀ r) from rfl,
      ← hf.meromorphicOn.divisor_restrict (closedBall_subset_closedBall hrR),
      Function.locallyFinsuppWithin.restrict_apply]
  have hD (ρ : ℂ) : 0 ≤ D ρ := hf.divisor_nonneg ρ
  have hD'D (ρ : ℂ) : 0 ≤ D' ρ ∧ D' ρ ≤ D ρ := by
    rw [hD']; split_ifs <;> simp [hD ρ]
  have hfin {d : ℂ → ℤ} (hd : d.support.Finite) :
      (fun u ↦ (· - u) ^ d u : ℂ → ℂ → ℂ).HasFiniteMulSupport := by
    rw [Function.HasFiniteMulSupport, Function.FactorizedRational.mulSupport]
    exact hd
  have hfinD : (fun u ↦ D u).support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hfinE : (fun u ↦ D u - D' u).support.Finite := hfinD.subset fun u hu h ↦ hu <| by
    have := hD'D u
    simp only [Function.mem_support] at h hu ⊢
    omega
  have hsplit : (∏ᶠ u, (· - u) ^ D u) =
      (∏ᶠ u, (· - u) ^ D' u) * ∏ᶠ u, (· - u) ^ (D u - D' u) := by
    rw [← finprod_mul_distrib (hfin (D'.finiteSupport (isCompact_closedBall _ _))) (hfin hfinE)]
    refine finprod_congr fun u ↦ funext fun x ↦ ?_
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [← zpow_add']
    · simp
    · have := hD'D u
      rcases eq_or_ne (D u) 0 with h | h
      · exact .inr (.inr (by omega))
      · exact .inr (.inl (by omega))
  refine ⟨(∏ᶠ u, (· - u) ^ (D u - D' u)) * g, fun z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · exact (Function.FactorizedRational.analyticAt (d := fun u ↦ D u - D' u)
      (sub_nonneg.2 (hD'D z).2)).mul (hg z hz)
  · refine mul_ne_zero (Function.FactorizedRational.ne_zero (d := fun u ↦ D u - D' u) ?_)
      (hg0 ⟨z, closedBall_subset_closedBall hrR hz⟩)
    simp [hD' z, hz]
  · have hQ : AnalyticOnNhd ℂ ((∏ᶠ u, (· - u) ^ D u) • g) (closedBall z₀ R) := fun x hx ↦
      (Function.FactorizedRational.analyticAt (d := fun u ↦ D u) (hD x)).smul (hg x hx)
    have hfreq : ∃ᶠ x in 𝓝[≠] z₀, f x = ((∏ᶠ u, (· - u) ^ D u) • g) x := by
      have := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hfg z₀ hz₀R
      refine Eventually.frequently ?_
      filter_upwards [this, nhdsWithin_le_nhds (closedBall_mem_nhds z₀ hR)] with x hx hxU
      exact hx.resolve_right (not_not_intro hxU)
    rw [hf.eqOn_of_preconnected_of_frequently_eq hQ hconn.isPreconnected hz₀R hfreq hz, hsplit,
      Function.FactorizedRational.finprod_eq_fun (D'.finiteSupport (isCompact_closedBall _ _))]
    simp only [Pi.mul_apply, smul_eq_mul, mul_assoc]

/-- A relative bound `‖f w‖ ≤ M ‖f z₀‖` on the sphere `sphere z₀ R` about a point where `f` does
not vanish forces `1 ≤ M`, by the maximum modulus principle. -/
theorem one_le_of_forall_mem_sphere_norm_le_mul (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : 0 < R) (hz₀ : f z₀ ≠ 0) {M : ℝ} (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) :
    1 ≤ M := by
  have := Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball z₀ R) isBounded_ball
    (DifferentiableOn.diffContOnCl (by rw [closure_ball z₀ hR.ne']; exact hf.differentiableOn))
    (by rwa [frontier_ball z₀ hR.ne'])
    (by rw [closure_ball z₀ hR.ne']; exact mem_closedBall_self hR.le)
  rwa [le_mul_iff_one_le_left (norm_pos_iff.2 hz₀)] at this

/-- **Landau's local logarithmic-derivative lemma.** Let `f` be analytic on `closedBall z₀ R`
with `f z₀ ≠ 0` and `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`, and let `0 < r` with `2 r ≤ R`. At every
`z` with `‖z - z₀‖ < r` and `f z ≠ 0`, the logarithmic derivative of `f` differs from
`∑ m_ρ / (z - ρ)` over the zeros `ρ` in `closedBall z₀ r`, with multiplicities `m_ρ` given by the
divisor, by at most `4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * log M`. -/
theorem norm_logDeriv_sub_finsum_divisor_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hr : 0 < r) (hrR : 2 * r ≤ R) (hz₀ : f z₀ ≠ 0) {M : ℝ}
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) {z : ℂ} (hz : ‖z - z₀‖ < r) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ r) ρ : ℂ) / (z - ρ)‖ ≤
      4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * Real.log M := by
  classical
  have hR : 0 < R := by linarith
  obtain ⟨G, hG, hG0, hfG⟩ := hf.exists_eq_finprod_zpow_mul (r := r) hR (by linarith)
    ⟨z₀, mem_closedBall_self hR.le, hz₀⟩
  set D' := divisor f (closedBall z₀ r)
  have hfin : D'.support.Finite := D'.finiteSupport (isCompact_closedBall _ _)
  set s := hfin.toFinset
  have hs (ρ : ℂ) (hρ : ρ ∈ s) : ‖ρ - z₀‖ ≤ r := by
    simpa [dist_eq_norm] using D'.supportWithinDomain (hfin.mem_toFinset.1 hρ)
  have hD' (ρ : ℂ) : 0 ≤ D' ρ :=
    (hf.mono (closedBall_subset_closedBall (by linarith))).divisor_nonneg ρ
  have hs0 (ρ : ℂ) (hρ : ρ ∉ s) : D' ρ = 0 := by simpa [s] using hρ
  set P : ℂ → ℂ := ∏ ρ ∈ s, fun w ↦ (w - ρ) ^ D' ρ
  have hP (w : ℂ) : ∏ᶠ ρ, (w - ρ) ^ D' ρ = P w := by
    simp only [P, Finset.prod_apply]
    exact finprod_eq_prod_of_mulSupport_subset _ fun ρ hρ ↦ by_contra fun h ↦ hρ (by simp [hs0 ρ h])
  simp only [hP] at hfG
  have hPw (w : ℂ) (hw : w ∈ sphere z₀ R) : P w ≠ 0 ∧ ‖P z₀‖ ≤ ‖P w‖ := by
    have hdist (ρ : ℂ) (hρ : ρ ∈ s) : ‖z₀ - ρ‖ ≤ ‖w - ρ‖ ∧ 0 < ‖w - ρ‖ := by
      have h1 := hs ρ hρ
      have h2 : ‖w - z₀‖ = R := by simpa [dist_eq_norm] using hw
      have h3 : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := norm_sub_le_norm_sub_add_norm_sub w ρ z₀
      rw [norm_sub_rev]
      constructor <;> linarith
    simp only [P, Finset.prod_apply, norm_prod, norm_zpow]
    refine ⟨Finset.prod_ne_zero_iff.2 fun ρ hρ ↦ zpow_ne_zero _
      (norm_pos_iff.1 (hdist ρ hρ).2), Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
      fun ρ hρ ↦ zpow_le_zpow_left₀ (hD' ρ) (norm_nonneg _) (hdist ρ hρ).1⟩
  have hz₀R : z₀ ∈ closedBall z₀ R := mem_closedBall_self hR.le
  have hM1 : 1 ≤ M := hf.one_le_of_forall_mem_sphere_norm_le_mul hR hz₀ hM
  have hM0 : 0 ≤ M := by linarith
  have hGle (w : ℂ) (hw : w ∈ closedBall z₀ R) : ‖G w‖ ≤ M * ‖G z₀‖ := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball z₀ R) isBounded_ball
      (DifferentiableOn.diffContOnCl ?_) (fun u hu ↦ ?_) ?_
    · rw [closure_ball z₀ hR.ne']
      exact hG.differentiableOn
    · rw [frontier_ball z₀ hR.ne'] at hu
      have hPu := hPw u hu
      have hpos : 0 < ‖P u‖ := norm_pos_iff.2 hPu.1
      have h1 := hM u hu
      rw [hfG u (sphere_subset_closedBall hu), hfG z₀ hz₀R, norm_mul, norm_mul] at h1
      have h2 : M * (‖P z₀‖ * ‖G z₀‖) ≤ M * (‖P u‖ * ‖G z₀‖) := by gcongr; exact hPu.2
      exact le_of_mul_le_mul_left (h1.trans (h2.trans_eq (by ring))) hpos
    · rwa [closure_ball z₀ hR.ne']
  have hGz₀ : G z₀ ≠ 0 := hG0 z₀ (mem_closedBall_self hr.le)
  have hballR : ball z₀ r ⊆ closedBall z₀ R := ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith))
  obtain ⟨L, hLd, hL⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp (U := ball z₀ r)
    ((convex_ball z₀ r).isSimplyConnected ⟨z₀, mem_ball_self hr⟩) isOpen_ball
    ((hG.differentiableOn.mono hballR).div_const (G z₀))
    (fun ⟨w, hw, h0⟩ ↦ div_ne_zero (hG0 w (ball_subset_closedBall hw)) hGz₀ h0)
  set h : ℂ → ℂ := fun w ↦ L w - L z₀
  have hhd : DifferentiableOn ℂ h (ball z₀ r) := hLd.sub_const _
  have hh₀ : h z₀ = 0 := sub_self _
  have hre (w : ℂ) (hw : w ∈ ball z₀ r) : (h w).re ≤ Real.log M := by
    have hexp : Complex.exp (h w) = G w / G z₀ := by
      have h₁ := hL hw
      have h₂ := hL (mem_ball_self hr)
      simp only [Function.comp_apply, div_self hGz₀] at h₁ h₂
      simp [h, Complex.exp_sub, h₁, h₂]
    rw [Real.le_log_iff_exp_le (by linarith), ← Complex.norm_exp, hexp, norm_div,
      div_le_iff₀ (norm_pos_iff.2 hGz₀)]
    exact hGle w (hballR hw)
  have hBC (K : ℝ) (hK : Real.log M < K) (w : ℂ) (hw : w ∈ ball z₀ r) :
      ‖h w‖ ≤ 2 * K * ‖w - z₀‖ / (r - ‖w - z₀‖) := by
    have hball (u : ℂ) (hu : u ∈ ball (0 : ℂ) r) : z₀ + u ∈ ball z₀ r := by
      simpa [dist_eq_norm] using hu
    have := Complex.borelCaratheodory_zero (f := fun u ↦ h (z₀ + u)) (M := K)
      ((Real.log_nonneg hM1).trans_lt hK)
      (hhd.comp (by fun_prop) fun u hu ↦ hball u hu)
      (fun u hu ↦ (hre _ (hball u hu)).trans hK.le) hr
      (by simpa [dist_eq_norm] using hw) (by simpa using hh₀)
    simpa using this
  set d := ‖z - z₀‖
  have hd : 0 ≤ d := norm_nonneg _
  have hderiv (K : ℝ) (hK : Real.log M < K) :
      ‖deriv h z‖ ≤ 4 * (r + d) / (r - d) ^ 2 * K := by
    have hK0 : 0 < K := (Real.log_nonneg hM1).trans_lt hK
    have hδ : 0 < (r - d) / 2 := by linarith
    have hsub : closedBall z ((r - d) / 2) ⊆ ball z₀ r := fun w hw ↦ by
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball, dist_eq_norm]
      linarith [norm_sub_le_norm_sub_add_norm_sub w z z₀]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (DifferentiableOn.diffContOnCl (by rw [closure_ball z hδ.ne']; exact hhd.mono hsub))
      (C := 2 * K * ((r + d) / 2) / (r - (r + d) / 2)) fun w hw ↦ by
        have hw' : ‖w - z₀‖ ≤ (r + d) / 2 := by
          rw [mem_sphere, dist_eq_norm] at hw
          linarith [norm_sub_le_norm_sub_add_norm_sub w z z₀]
        refine (hBC K hK w (hsub (sphere_subset_closedBall hw))).trans ?_
        gcongr
        linarith
    refine this.trans_eq ?_
    have hrd : r - d ≠ 0 := by linarith
    rw [show r - (r + d) / 2 = (r - d) / 2 by ring]
    field_simp
    ring
  have hzb : z ∈ ball z₀ r := by rwa [mem_ball, dist_eq_norm]
  have hPz : P z ≠ 0 := by
    intro h0
    exact hfz (by rw [hfG z (hballR hzb), h0, zero_mul])
  have hzρ (ρ : ℂ) (hρ : ρ ∈ s) : z - ρ ≠ 0 := by
    intro h0
    refine hPz ?_
    simp only [P, Finset.prod_apply]
    exact Finset.prod_eq_zero hρ (by rw [h0, zero_zpow _ (hfin.mem_toFinset.1 hρ)])
  have hPd : DifferentiableAt ℂ P z :=
    .finsetProd fun ρ hρ ↦ (differentiableAt_id.sub_const ρ).zpow (.inl (hzρ ρ hρ))
  have hlogP : logDeriv P z = ∑ᶠ ρ, (D' ρ : ℂ) / (z - ρ) := by
    rw [logDeriv_prod (f := fun ρ w ↦ (w - ρ) ^ D' ρ) (fun ρ hρ ↦ zpow_ne_zero _ (hzρ ρ hρ))
      fun ρ _ ↦ (differentiableAt_id.sub_const ρ).zpow (.inr (hD' ρ)),
      finsum_eq_sum_of_support_subset (s := s)]
    · refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      rw [logDeriv_fun_zpow (f := fun w ↦ w - ρ) (by fun_prop)]
      simp [logDeriv_apply, div_eq_mul_inv]
    · exact fun ρ hρ ↦ by_contra fun h ↦ hρ (by simp [hs0 ρ h])
  have hzR : z ∈ ball z₀ R := ball_subset_ball (by linarith) hzb
  have hGd : DifferentiableAt ℂ G z := (hG z (ball_subset_closedBall hzR)).differentiableAt
  have hlogf : logDeriv f z = logDeriv P z + logDeriv G z := by
    have hfPG : f =ᶠ[𝓝 z] P * G := eventuallyEq_of_mem (isOpen_ball.mem_nhds hzR)
      fun w hw ↦ hfG w (ball_subset_closedBall hw)
    rw [(logDeriv_congr_nhds hfPG).eq_of_nhds,
      logDeriv_mul z hPz (hG0 z (ball_subset_closedBall hzb)) hPd hGd]
  have hlogG : deriv h z = logDeriv G z := by
    simp only [h, deriv_sub_const]
    rw [TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball hLd hL hzb]
    simp only [div_eq_mul_inv]
    exact logDeriv_mul_const z _ (inv_ne_zero hGz₀)
  rw [hlogf, ← hlogP, add_sub_cancel_left, ← hlogG]
  have hc : 0 < 4 * (r + d) / (r - d) ^ 2 := by
    have : 0 < r - d := by linarith
    positivity
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  have := hderiv (a / (4 * (r + d) / (r - d) ^ 2)) (by rwa [lt_div_iff₀' hc])
  rwa [mul_div_cancel₀ _ hc.ne'] at this
/-- **Landau's local logarithmic-derivative lemma** in the classical normalization: zeros in
`closedBall z₀ (R / 2)`, points `z` with `‖z - z₀‖ ≤ R / 4`, and the constant `48`. -/
theorem norm_logDeriv_sub_finsum_divisor_half_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : 0 < R) (hz₀ : f z₀ ≠ 0) {M : ℝ} (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖)
    {z : ℂ} (hz : ‖z - z₀‖ ≤ R / 4) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ, (divisor f (closedBall z₀ (R / 2)) ρ : ℂ) / (z - ρ)‖ ≤
      48 / R * Real.log M := by
  refine (hf.norm_logDeriv_sub_finsum_divisor_le (by linarith) (by linarith) hz₀ hM
    (by linarith) hfz).trans (mul_le_mul_of_nonneg_right ?_
      (Real.log_nonneg (hf.one_le_of_forall_mem_sphere_norm_le_mul hR hz₀ hM)))
  calc 4 * (R / 2 + ‖z - z₀‖) / (R / 2 - ‖z - z₀‖) ^ 2
      ≤ 4 * (R / 2 + R / 4) / (R / 2 - R / 4) ^ 2 := by
        have h4 : 0 < R / 2 - R / 4 := by linarith
        gcongr
    _ = 48 / R := by
        field_simp
        ring

/-- **Jensen's count with a relative bound.** If `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`, then the
number of zeros of `f` in `closedBall z₀ r`, counted with multiplicity, is at most
`log M / log (R / r)`. -/
theorem finsum_divisor_le_log_div_log (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hr : 0 < r) (hrR : r < R) (hz₀ : f z₀ ≠ 0) {M : ℝ}
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) :
    ((∑ᶠ ρ, divisor f (closedBall z₀ r) ρ : ℤ) : ℝ) ≤ Real.log M / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hc : (f z₀)⁻¹ ≠ 0 := inv_ne_zero hz₀
  have := AnalyticOnNhd.sum_divisor_le (f := (f z₀)⁻¹ • f) (c := z₀) (r := r) (R := R) (M := M)
    (by rwa [abs_of_pos hr]) (by rwa [abs_of_pos hr, abs_of_pos hR])
    (hf.one_le_of_forall_mem_sphere_norm_le_mul hR hz₀ hM)
    (by rw [abs_of_pos hR]; exact fun x hx ↦ analyticAt_const.smul (hf x hx))
    (by simp [hz₀]) fun w hw ↦ by
      rw [abs_of_pos hR] at hw
      rw [Pi.smul_apply, norm_smul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hz₀), mul_comm]
      exact hM w hw
  rwa [abs_of_pos hr, divisor_const_smul hc, Pi.smul_apply, smul_eq_mul,
    inv_mul_cancel₀ hz₀, norm_one, div_one] at this

/-- **Jensen's count in the classical normalization**: at most `log M / log 2` zeros of `f` in
`closedBall z₀ (R / 2)` when `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`. -/
theorem finsum_divisor_half_le (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : 0 < R) (hz₀ : f z₀ ≠ 0) {M : ℝ} (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) :
    ((∑ᶠ ρ, divisor f (closedBall z₀ (R / 2)) ρ : ℤ) : ℝ) ≤ Real.log M / Real.log 2 := by
  have := hf.finsum_divisor_le_log_div_log (r := R / 2) (by linarith) (by linarith) hz₀ hM
  rwa [div_div_cancel₀ hR.ne'] at this

end AnalyticOnNhd

/-! ### Example

For the polynomial `f z = z - 1` on `closedBall 0 4` one may take `M = 5`, since
`‖w - 1‖ ≤ 5 = 5 ‖f 0‖` on `sphere 0 4`. Near `0` the logarithmic derivative is then its
partial-fraction part over the zeros in `closedBall 0 2` up to `12 log 5`, and there are at most
`log 5 / log 2` such zeros. -/

example {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    ‖logDeriv (· - 1) z - ∑ᶠ ρ, (divisor (· - 1 : ℂ → ℂ) (closedBall 0 2) ρ : ℂ) / (z - ρ)‖ ≤
      12 * Real.log 5 ∧
    ((∑ᶠ ρ, divisor (· - 1 : ℂ → ℂ) (closedBall 0 2) ρ : ℤ) : ℝ) ≤ Real.log 5 / Real.log 2 := by
  have hf : AnalyticOnNhd ℂ (· - 1 : ℂ → ℂ) (closedBall 0 4) := fun _ _ ↦ by fun_prop
  have hM (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 4) : ‖w - 1‖ ≤ 5 * ‖(0 : ℂ) - 1‖ := by
    rw [mem_sphere_zero_iff_norm] at hw
    have := norm_sub_le w 1
    norm_num [hw] at this ⊢
    linarith
  have h₁ := hf.norm_logDeriv_sub_finsum_divisor_half_le (by norm_num) (by norm_num) hM
    (by simpa using hz) (sub_ne_zero.2 hz1)
  have h₂ := hf.finsum_divisor_half_le (by norm_num) (by norm_num) hM
  rw [show (4 : ℝ) / 2 = 2 by norm_num] at h₁ h₂
  norm_num at h₁
  exact ⟨h₁, h₂⟩
