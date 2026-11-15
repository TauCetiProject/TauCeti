/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville

/-!
# Consequences of the Borel–Carathéodory theorem

Two consequences of Mathlib's Borel–Carathéodory theorem, which bounds a holomorphic function on
a disc by an upper bound on its real part.

For an entire `H`, an upper bound `Complex.exp(H(z)) = O(Complex.exp(‖z‖^p))` with `p ≥ 0` forces
`H(z) = O(‖z‖^p)`. An upper bound on the real part therefore controls the entire complex
function at the same power. This supplies the growth transfer needed to identify the
exponential factor in Hadamard's theorem.

Combined with the Cauchy estimate, the same theorem bounds the derivative: if `g` is holomorphic
on `ball z₀ r`, vanishes at `z₀` and has real part at most `A`, then
`‖deriv g z‖ ≤ 4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * A` for `‖z - z₀‖ < r`.

## Main results

* `Differentiable.isBigO_of_cexp_isBigO`: polynomial growth of an entire logarithm.
* `Complex.norm_deriv_le_of_forall_mem_ball_re_le`: the derivative bound from a one-sided
  real-part bound.
-/

public section

open Complex Filter Bornology Topology Asymptotics

/-- **Maximum modulus for the real part of an entire logarithm.** A bound `B` on
`‖Complex.exp (H z)‖` over the circle of radius `R` bounds `Re (H w)` by `log B` on the open disk
it encloses. -/
theorem Differentiable.re_le_log_of_forall_mem_sphere_norm_cexp_le {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) {R B : ℝ} (hB : 0 < B)
    (h : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖Complex.exp (H z)‖ ≤ B)
    {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R) : (H w).re ≤ Real.log B := by
  have hexp : Differentiable ℂ (fun z ↦ Complex.exp (H z)) := hH.cexp
  have he : ‖Complex.exp (H w)‖ ≤ B :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      ⟨hexp.differentiableOn, hexp.continuous.continuousOn⟩
      (fun z hz ↦ h z (Metric.frontier_ball_subset_sphere hz)) (subset_closure hw)
  rw [norm_exp] at he
  exact (Real.le_log_iff_exp_le hB).mpr he

/-- An entire logarithm inherits a polynomial norm bound from an exponential norm bound
on its exponential, for every nonnegative real exponent. -/
theorem Differentiable.isBigO_of_cexp_isBigO {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {p : ℝ} (hp : 0 ≤ p)
    (h : (fun z ↦ Complex.exp (H z)) =O[cobounded ℂ] (fun z ↦ Real.exp (‖z‖ ^ p))) :
    H =O[cobounded ℂ] (fun z ↦ ‖z‖ ^ p) := by
  obtain ⟨C, hC, hb⟩ := h.exists_pos
  obtain ⟨L, _, hL⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hb.bound
  -- Maximum modulus extends the large-circle bound to the enclosed disk.
  have hreal (R : ℝ) (hRL : L ≤ R) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      (H w).re ≤ Real.log C + R ^ p := by
    have hlog : Real.log (C * Real.exp (R ^ p)) = Real.log C + R ^ p := by
      rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [← hlog]
    refine hH.re_le_log_of_forall_mem_sphere_norm_cexp_le (by positivity) (fun z hz ↦ ?_) hw
    have hzR : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hzL : L ≤ ‖z‖ := hzR ▸ hRL
    simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, Real.abs_exp, hzR] using hL hzL
  -- Borel–Carathéodory on a disk twice as large controls the full complex norm.
  let A : ℝ := 2 * (|Real.log C| + 1) + 3 * ‖H 0‖
  apply Asymptotics.IsBigO.of_bound (A + 2 * 2 ^ p)
  filter_upwards [eventually_cobounded_le_norm (max L 1)] with z hz
  have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hz0 : 0 < ‖z‖ := zero_lt_one.trans_le hz1
  have hzL : L ≤ 2 * ‖z‖ := by have := (le_max_left _ _).trans hz; linarith
  let M : ℝ := |Real.log C| + (2 * ‖z‖) ^ p + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMbound : Set.MapsTo H (Metric.ball 0 (2 * ‖z‖)) {w | w.re ≤ M} := by
    intro w hw
    have hr := hreal _ hzL w hw
    have habs := le_abs_self (Real.log C)
    rw [Set.mem_ofPred_eq]
    dsimp [M]
    linarith
  have hball : z ∈ Metric.ball 0 (2 * ‖z‖) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hbc := Complex.borelCaratheodory hM hH.differentiableOn hMbound
    (by positivity : 0 < 2 * ‖z‖) hball
  have hden : 2 * ‖z‖ - ‖z‖ = ‖z‖ := by ring
  rw [hden, mul_div_cancel_right₀ _ hz0.ne'] at hbc
  have hlast : ‖H 0‖ * (2 * ‖z‖ + ‖z‖) / ‖z‖ = 3 * ‖H 0‖ := by
    field_simp
    ring
  rw [hlast] at hbc
  -- With `R = 2 ‖z‖` and `r = ‖z‖`, the estimate reads `‖H z‖ ≤ 2 M + 3 ‖H 0‖`.
  have hM2 : 2 * M + 3 * ‖H 0‖ = A + 2 * 2 ^ p * ‖z‖ ^ p := by
    simp only [M, A, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z)]
    ring
  -- Since `1 ≤ ‖z‖ ^ p`, the constant `A` is absorbed into `A * ‖z‖ ^ p`.
  have hA : A ≤ A * ‖z‖ ^ p :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hz1 hp)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) p)]
  calc ‖H z‖ ≤ 2 * M + 3 * ‖H 0‖ := hbc
    _ = A + 2 * 2 ^ p * ‖z‖ ^ p := hM2
    _ ≤ A * ‖z‖ ^ p + 2 * 2 ^ p * ‖z‖ ^ p := by linarith
    _ = (A + 2 * 2 ^ p) * ‖z‖ ^ p := by ring

section DerivBound

open Metric

/-- **Derivative bound from a one-sided real-part bound.** Let `g` be holomorphic on
`ball z₀ r` with `g z₀ = 0` and `re (g w) ≤ A` there. Then at every `z` with
`‖z - z₀‖ < r`, `‖deriv g z‖ ≤ 4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * A`. -/
theorem Complex.norm_deriv_le_of_forall_mem_ball_re_le {g : ℂ → ℂ} {z₀ : ℂ} {r A : ℝ}
    (hg : DifferentiableOn ℂ g (ball z₀ r)) (hg₀ : g z₀ = 0)
    (hre : ∀ w ∈ ball z₀ r, (g w).re ≤ A) {z : ℂ} (hz : ‖z - z₀‖ < r) :
    ‖deriv g z‖ ≤ 4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * A := by
  set d := ‖z - z₀‖
  have hd : 0 ≤ d := norm_nonneg _
  have hr : 0 < r := hd.trans_lt hz
  have hA : 0 ≤ A := by simpa [hg₀] using hre z₀ (mem_ball_self hr)
  -- Borel–Carathéodory for every real-part bound `K > A`.
  have hBC (K : ℝ) (hK : A < K) (w : ℂ) (hw : w ∈ ball z₀ r) :
      ‖g w‖ ≤ 2 * K * ‖w - z₀‖ / (r - ‖w - z₀‖) := by
    have hball (u : ℂ) (hu : u ∈ ball (0 : ℂ) r) : z₀ + u ∈ ball z₀ r := by
      simpa [dist_eq_norm] using hu
    have := Complex.borelCaratheodory_zero (f := fun u ↦ g (z₀ + u)) (M := K)
      (hA.trans_lt hK) (hg.comp (by fun_prop) fun u hu ↦ hball u hu)
      (fun u hu ↦ (hre _ (hball u hu)).trans hK.le) hr
      (by simpa [dist_eq_norm] using hw) (by simpa using hg₀)
    simpa using this
  -- The Cauchy estimate on the circle of radius `(r - d) / 2` about `z`.
  have hderiv (K : ℝ) (hK : A < K) :
      ‖deriv g z‖ ≤ 4 * (r + d) / (r - d) ^ 2 * K := by
    have hK0 : 0 < K := hA.trans_lt hK
    have hδ : 0 < (r - d) / 2 := by linarith
    have hsub : closedBall z ((r - d) / 2) ⊆ ball z₀ r := fun w hw ↦ by
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball, dist_eq_norm]
      linarith [norm_sub_le_norm_sub_add_norm_sub w z z₀]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (DifferentiableOn.diffContOnCl (by rw [closure_ball z hδ.ne']; exact hg.mono hsub))
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
  -- Let `K` decrease to `A`.
  have hc : 0 < 4 * (r + d) / (r - d) ^ 2 := by
    have : 0 < r - d := by linarith
    positivity
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  have := hderiv (a / (4 * (r + d) / (r - d) ^ 2)) (by rwa [lt_div_iff₀' hc])
  rwa [mul_div_cancel₀ _ hc.ne'] at this

end DerivBound
