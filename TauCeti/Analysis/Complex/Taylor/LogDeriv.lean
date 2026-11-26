/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.LocalLogDeriv
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Calculus.IteratedDeriv.PartialFractions
import TauCeti.Analysis.Complex.CanonicalFactor
import TauCeti.Analysis.Meromorphic.Divisor

/-!
# Taylor coefficients of a logarithmic derivative

Removing the simple fractions contributed by the zeros in a closed disc leaves a holomorphic
remainder. Applying Landau's local logarithmic-derivative bound to this remainder and using
Cauchy's inequality gives geometric decay of its normalized Taylor coefficients. In particular,
a relative growth estimate on an outer circle controls the error when replacing the Taylor
coefficients of a logarithmic derivative by inverse powers of the displacements of its zeros.

The pointwise estimate used here is the finite Blaschke product form of Landau's lemma
(Montgomery and Vaughan, *Multiplicative Number Theory I*, Lemma 6.3).
-/

public section

open Filter Function Metric Set
open scoped Nat Topology

namespace AnalyticOnNhd

variable {f : ℂ → ℂ} {c : ℂ} {r R t M : ℝ}

-- Extend the pointwise estimate to a zero on the Cauchy circle by continuity from the disc.
private theorem norm_extension_le_on_sphere
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf₀ : f c ≠ 0)
    (htr : t < r) (hrR : r < R)
    (hM : ∀ w ∈ sphere c R, ‖f w‖ ≤ M * ‖f c‖)
    {g : ℂ → ℂ} {z : ℂ} (hz : z ∈ sphere c t) (hg : ContinuousAt g z)
    (heq : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 →
      logDeriv f w - ∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall c r) ρ : ℂ) / (w - ρ) = g w) :
    ‖g z‖ ≤ (4 * (r + t) / (r - t) ^ 2 + r / ((R ^ 2 - r * t) * Real.log (R / r))) *
      Real.log M := by
  have hfR : AnalyticOnNhd ℂ f (ball c R) := hf.mono ball_subset_closedBall
  have hzNorm := mem_sphere_iff_norm.mp hz
  have hr : 0 < r := (hzNorm ▸ norm_nonneg (z - c)).trans_lt htr
  have hzr : z ∈ ball c r := mem_ball_iff_norm.mpr (hzNorm ▸ htr)
  have hzR := ball_subset_ball hrR.le hzr
  have hne : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    rcases hfR.eqOn_zero_or_eventually_ne_zero_of_preconnected (convex_ball c R).isPreconnected
      with h | h
    · exact (hf₀ (h (mem_ball_self (by linarith)))).elim
    · filter_upwards [eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp h z hzR,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hzR)] with w hw hwR using hw hwR
  let B (d : ℝ) := (4 * (r + d) / (r - d) ^ 2 +
    r / ((R ^ 2 - r * d) * Real.log (R / r))) * Real.log M
  have hcont : ContinuousAt (fun w : ℂ ↦ B ‖w - c‖) z := by
    have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div (by linarith)).mpr hrR)
    have hR := hr.trans hrR
    have hd := Complex.sq_sub_mul_norm_pos hR hrR (mem_ball_iff_norm.mp hzR).le
    have hsub : (r - ‖z - c‖) ^ 2 ≠ 0 := pow_ne_zero _ (sub_pos.mpr (mem_ball_iff_norm.mp hzr)).ne'
    have hden := mul_ne_zero hd.ne' hlog.ne'
    dsimp only [B]
    fun_prop
  have hgLim : Tendsto (fun w ↦ ‖g w‖) (𝓝[≠] z) (𝓝 ‖g z‖) :=
    hg.norm.tendsto.mono_left nhdsWithin_le_nhds
  have hb : ‖g z‖ ≤ B ‖z - c‖ := by
    refine le_of_tendsto_of_tendsto hgLim (hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [hne, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hzr), heq]
      with w hw hwr he
    rw [← he hw]
    exact hf.norm_logDeriv_sub_finsum_divisor_le hrR hM (mem_ball_iff_norm.mp hwr) hw
  simpa only [hzNorm, B] using hb

-- Apply Cauchy directly to the analytic remainder before expanding its coefficients.
private theorem norm_iteratedDeriv_logDeriv_sub_finsum_divisor_le
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf₀ : f c ≠ 0)
    (ht : 0 < t) (htr : t < r) (hrR : r < R)
    (hM : ∀ w ∈ sphere c R, ‖f w‖ ≤ M * ‖f c‖) (k : ℕ) :
    ‖iteratedDeriv k (fun z ↦ logDeriv f z -
        ∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall c r) ρ : ℂ) / (z - ρ)) c / (k ! : ℂ)‖ ≤
      ((4 * (r + t) / (r - t) ^ 2 + r / ((R ^ 2 - r * t) * Real.log (R / r))) *
        Real.log M) / t ^ k := by
  have hr : 0 < r := ht.trans htr
  have hc := mem_closedBall_self (x := c) hr.le
  have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR.le)
  obtain ⟨g, hg, heq⟩ := hfr.exists_logDeriv_sub_finsum_divisor_extension
  have heq' : (fun z ↦ logDeriv f z -
      ∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall c r) ρ : ℂ) / (z - ρ)) =ᶠ[𝓝 c] g := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr),
      (hf c (closedBall_subset_closedBall hrR.le hc)).continuousAt.eventually_ne hf₀] with z hz hn
    exact heq z (ball_subset_closedBall hz) hn
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k ht
    ((hg.mono (closedBall_subset_closedBall htr.le)).differentiableOn.diffContOnCl_ball Subset.rfl)
    (fun z hz ↦ by
      have hzr : z ∈ ball c r := mem_ball_iff_norm.mpr (mem_sphere_iff_norm.mp hz ▸ htr)
      have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ ball c r :=
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hzr)
      exact norm_extension_le_on_sphere hf hf₀ htr hrR hM hz
        (hg z (ball_subset_closedBall hzr)).continuousAt
        (hmem.mono fun w hw ↦ heq w (ball_subset_closedBall hw)))
  rw [heq'.iteratedDeriv_eq, norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  convert hcauchy using 1
  ring

/-- The reflected Taylor coefficient of `logDeriv f` at `c` differs from the inverse-power sum
of the displacements of the zeros in the closed disc of radius `r` by a geometrically bounded
error. The bound is the local Landau estimate at distance `t`, divided by `t ^ k`. -/
theorem norm_reflectedTaylorCoeff_logDeriv_sub_finsum_divisor_le
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf₀ : f c ≠ 0)
    (ht : 0 < t) (htr : t < r) (hrR : r < R)
    (hM : ∀ w ∈ sphere c R, ‖f w‖ ≤ M * ‖f c‖) (k : ℕ) :
    ‖(-1 : ℂ) ^ k * iteratedDeriv k (logDeriv f) c / (k ! : ℂ) -
        ∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall c r) ρ : ℂ) / (c - ρ) ^ (k + 1)‖ ≤
      ((4 * (r + t) / (r - t) ^ 2 + r / ((R ^ 2 - r * t) * Real.log (R / r))) *
        Real.log M) / t ^ k := by
  let D := MeromorphicOn.divisor f (closedBall c r)
  let S := (D.finiteSupport (isCompact_closedBall _ _)).toFinset
  have hS (j : ℕ) (z : ℂ) : ∑ᶠ ρ, (D ρ : ℂ) / (z - ρ) ^ j =
      ∑ ρ ∈ S, (D ρ : ℂ) / (z - ρ) ^ j :=
    finsum_eq_sum_of_support_subset _ (s := S) (fun ρ hρ ↦ by
      by_contra hn
      have hzero : D ρ = 0 := by simpa [S, mem_support] using hn
      exact hρ (by simp [hzero]))
  have hfc := hf c (mem_closedBall_self (by linarith))
  have hDc : D c = 0 := hfc.divisor_apply_eq_zero hf₀
  have hsum : ContDiffAt ℂ k (fun z ↦ ∑ ρ ∈ S, (D ρ : ℂ) / (z - ρ)) c := by
    have hterm (ρ : ℂ) (hρ : ρ ∈ S) : ContDiffAt ℂ k (fun z ↦ (D ρ : ℂ) / (z - ρ)) c := by
      have hcρ : c ≠ ρ := by
        rintro rfl
        simp [S, mem_support, hDc] at hρ
      have hne := sub_ne_zero.mpr hcρ
      fun_prop
    simpa only [Finset.sum_apply] using (ContDiffAt.sum hterm)
  have h := hf.norm_iteratedDeriv_logDeriv_sub_finsum_divisor_le hf₀ ht htr hrR hM k
  have heq (z : ℂ) : ∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall c r) ρ : ℂ) / (z - ρ) =
      ∑ ρ ∈ S, (D ρ : ℂ) / (z - ρ) := by
    simpa only [pow_one] using hS 1 z
  simp only [heq] at h
  have hlog : ContDiffAt ℂ k (logDeriv f) c := by
    rw [funext (logDeriv_apply f)]
    exact (hfc.deriv.div hfc hf₀).contDiffAt
  rw [iteratedDeriv_fun_sub hlog hsum,
    S.iteratedDeriv_sum_div_sub _ _ _ (fun _ ↦ by simp [hDc])] at h
  have hSk : ∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall c r) ρ : ℂ) / (c - ρ) ^ (k + 1) =
      ∑ ρ ∈ S, (D ρ : ℂ) / (c - ρ) ^ (k + 1) := hS (k + 1) c
  rw [hSk]
  have hm : ‖(-1 : ℂ) ^ k‖ = 1 := by simp
  have hs : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; simp
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  calc
    _ = ‖(-1 : ℂ) ^ k * ((iteratedDeriv k (logDeriv f) c -
          ((-1 : ℂ) ^ k * k !) * ∑ ρ ∈ S, (D ρ : ℂ) / (c - ρ) ^ (k + 1)) / (k ! : ℂ))‖ := by
        congr 1
        rw [← mul_div_assoc, mul_sub]
        simp only [← mul_assoc, hs, one_mul, sub_div, mul_div_cancel_left₀ _ hk]
    _ ≤ _ := by simpa only [norm_mul, hm, one_mul] using h

end AnalyticOnNhd
