/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.MeanValue
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Consequences of the Borel–Carathéodory theorem

Mathlib's Borel–Carathéodory theorem bounds a holomorphic function on a disc by an upper bound on
its real part. This file draws consequences of it for entire functions and for logarithmic
derivatives, and proves the derivative form of the inequality.

For an entire `H`, an upper bound `Complex.exp(H(z)) = O(Complex.exp(‖z‖^p))` with `p ≥ 0` forces
`H(z) = O(‖z‖^p)`. An upper bound on the real part therefore controls the entire complex
function at the same power. This supplies the growth transfer needed to identify the
exponential factor in Hadamard's theorem.

The derivative form of the theorem bounds every derivative of `f` by the same one-sided
information: if `f` is holomorphic on `ball c R` with `re f ≤ M` there, then for `k ≥ 1` and
`‖z - c‖ ≤ r < R`,
`‖f^{(k)}(z)‖ ≤ 2 k! R (M - re (f c)) / (R - r) ^ (k + 1)`.
At `z = c` this is Carathéodory's coefficient inequality `‖a_k‖ R ^ k ≤ 2 (M - re a₀)` for the
Taylor coefficients `a_k = f^{(k)}(c) / k!`. Such bounds turn an upper bound on `re log F` into
bounds on the logarithmic derivative `F' / F` and its derivatives, as in Landau's local
logarithmic-derivative lemma.

For a nonvanishing holomorphic function on an open disc, a relative norm bound by `M`
also bounds its logarithmic derivative by the same coefficient times `log M`. Boundary and
exterior values are unrestricted.

## Main results

* `Differentiable.isBigO_of_cexp_isBigO`: polynomial growth of an entire logarithm.
* `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_re_le`: the derivative bound on a closed
  disc from a real-part bound on its boundary circle.
* `Complex.norm_iteratedDeriv_le_borelCaratheodory`: the derivative form of the
  Borel–Carathéodory inequality on an open disc.
* `Complex.norm_iteratedDeriv_mul_pow_le_of_forall_mem_ball_re_le`: Carathéodory's coefficient
  inequality.
* `Complex.norm_deriv_le_of_forall_mem_ball_re_le`: the first-derivative bound for a function
  vanishing at the centre, in the form used for logarithmic derivatives.
* `Complex.norm_logDeriv_le_of_forall_mem_ball_norm_le_mul`: the logarithmic-derivative estimate
  from a relative norm bound.

## Implementation notes

Write `f^{(k)}(z)` as the circle average of `K f` with the Cauchy kernel
`K w = (w - c) / (w - z) ^ (k + 1)` on `sphere c ρ`. Since `f = 2 re f - conj f`, and the average
of `K` against the conjugate of any holomorphic function vanishes for `k ≥ 1` (on the circle,
`conj K` is holomorphic on the closed disc and vanishes at `c`), the average of `K f` equals
`-2` times the average of `K (M - re f)`. As `M - re f ≥ 0`, its norm is at most
`sup ‖K‖ ≤ ρ / (ρ - ‖z - c‖) ^ (k + 1)` times the average of `M - re f`, which is
`M - re (f c)` by the mean value property.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 6, §6.1.
* A. Kontorovich, T. Tao et al., *The Prime Number Theorem and more* (PNT+), blueprint,
  Theorem 5.3.2, for the weaker bound `16 M R ^ 2 / (R - r) ^ 3` at `k = 1`, `f c = 0`.
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

open Metric Real ComplexConjugate

namespace Complex

variable {f : ℂ → ℂ} {c z : ℂ} {ρ : ℝ} {k : ℕ}

/-- The Cauchy kernel `(w - c) / (w - z) ^ (k + 1)` of a point `z` of `ball c ρ` is continuous on
the circle `sphere c ρ`. -/
private theorem continuousOn_div_sub_pow_sphere (hz : z ∈ ball c ρ) :
    ContinuousOn (fun w ↦ (w - c) / (w - z) ^ (k + 1)) (sphere c |ρ|) := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.mp hz)
  have h₁ : ContinuousOn (fun w : ℂ ↦ w - c) (sphere c ρ) := by fun_prop
  have h₂ : ContinuousOn (fun w : ℂ ↦ (w - z) ^ (k + 1)) (sphere c ρ) := by fun_prop
  rw [abs_of_pos hρ]
  refine h₁.div h₂ fun w hw ↦ pow_ne_zero _ (sub_ne_zero.2 fun hwz ↦ ?_)
  rw [mem_sphere, hwz] at hw
  exact (mem_ball.mp hz).ne hw

/-- The circle average of the Cauchy kernel `(w - c) / (w - z) ^ (k + 1)` against the conjugate of a
holomorphic function vanishes once `k ≥ 1`: on the circle, the conjugate kernel is holomorphic on
the closed disc and vanishes at `c`. -/
private theorem circleAverage_div_sub_pow_mul_conj_eq_zero {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (ball c ρ)) (hk : 1 ≤ k) (hz : z ∈ ball c ρ) :
    circleAverage (fun w ↦ (w - c) / (w - z) ^ (k + 1) * conj (g w)) c ρ = 0 := by
  have hzc : ‖z - c‖ < ρ := by simpa [dist_eq_norm] using hz
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt hzc
  -- On the circle, `conj (w - c) = ρ ^ 2 / (w - c)`, so the conjugate of the kernel is the
  -- rational function `A` below, holomorphic on a neighbourhood of the closed disc.
  have hconjK (w : ℂ) (hw : w ∈ sphere c ρ) : conj ((w - c) / (w - z) ^ (k + 1)) =
      (ρ : ℂ) ^ 2 * (w - c) ^ k / ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) ^ (k + 1) := by
    have hwc : ‖w - c‖ = ρ := by simpa [dist_eq_norm] using hw
    have hu : w - c ≠ 0 := norm_ne_zero_iff.mp (hwc.trans_ne hρ.ne')
    have hconj : conj (w - c) = (ρ : ℂ) ^ 2 / (w - c) := by
      rw [eq_div_iff hu, mul_comm, mul_conj, normSq_eq_norm_sq, hwc]; push_cast; ring
    have hsub : conj (w - z) = ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) / (w - c) := by
      rw [show w - z = (w - c) - (z - c) by ring, map_sub, hconj]
      field_simp
    rw [map_div₀, map_pow, hconj, hsub, div_pow, pow_succ (w - c)]
    field_simp
  set A : ℂ → ℂ := fun w ↦
    (ρ : ℂ) ^ 2 * (w - c) ^ k / ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) ^ (k + 1)
  have hden (w : ℂ) (hw : w ∈ closedBall c ρ) :
      ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) ^ (k + 1) ≠ 0 := by
    refine pow_ne_zero _ fun h0 ↦ ?_
    have hwc : ‖w - c‖ ≤ ρ := by simpa [dist_eq_norm] using hw
    have : ‖(w - c) * conj (z - c)‖ = ρ ^ 2 := by
      rw [← sub_eq_zero.mp h0]
      simp [sq, abs_of_pos hρ]
    rw [norm_mul, norm_conj] at this
    nlinarith [norm_nonneg (z - c), norm_nonneg (w - c)]
  have hA : DifferentiableOn ℂ A (closure (ball c ρ)) := by
    have h₁ : DifferentiableOn ℂ (fun w : ℂ ↦ (ρ : ℂ) ^ 2 * (w - c) ^ k) (closedBall c ρ) := by
      fun_prop
    have h₂ : DifferentiableOn ℂ (fun w : ℂ ↦ ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) ^ (k + 1))
        (closedBall c ρ) := by
      fun_prop
    rw [closure_ball c hρ.ne']
    exact h₁.div h₂ hden
  have hh : DiffContOnCl ℂ (fun w ↦ A w • g w) (ball c |ρ|) := by
    rw [abs_of_pos hρ]
    exact hA.diffContOnCl.smul hg
  calc circleAverage (fun w ↦ (w - c) / (w - z) ^ (k + 1) * conj (g w)) c ρ
      = circleAverage (conjCLE.toContinuousLinearMap ∘ fun w ↦ A w • g w) c ρ := by
        refine circleAverage_congr_sphere fun w hw ↦ ?_
        rw [abs_of_pos hρ] at hw
        simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply,
          smul_eq_mul, map_mul, A]
        rw [← hconjK w hw, conj_conj]
    _ = 0 := by
        rw [ContinuousLinearMap.circleAverage_comp_comm _
          (hh.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable',
          hh.circleAverage]
        simp [A, zero_pow (Nat.one_le_iff_ne_zero.mp hk)]

/-- Against the Cauchy kernel `(w - c) / (w - z) ^ (k + 1)` with `k ≥ 1`, a holomorphic `f` has
the same circle average as `-2 (M - re f)`, for every real `M`: write `f = 2 re f - conj f`. -/
private theorem circleAverage_div_sub_pow_mul_eq_neg_two_mul (hf : DiffContOnCl ℂ f (ball c ρ))
    (hk : 1 ≤ k) (hz : z ∈ ball c ρ) (M : ℝ) :
    circleAverage (fun w ↦ (w - c) / (w - z) ^ (k + 1) * f w) c ρ =
      -2 * circleAverage (fun w ↦ (w - c) / (w - z) ^ (k + 1) * ((M - (f w).re : ℝ) : ℂ)) c ρ := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.mp hz)
  have hKs := continuousOn_div_sub_pow_sphere (k := k) hz
  have hfs : ContinuousOn f (sphere c |ρ|) := by
    rw [abs_of_pos hρ]
    exact hf.continuousOn_ball.mono sphere_subset_closedBall
  set K : ℂ → ℂ := fun w ↦ (w - c) / (w - z) ^ (k + 1)
  set G : ℂ → ℂ := fun w ↦ K w * ((M - (f w).re : ℝ) : ℂ)
  have hdecomp : (fun w ↦ K w * f w) =
      fun w ↦ (-2 : ℂ) • G w - K w * conj (f w - 2 * (M : ℂ)) := by
    ext w
    have := add_conj (f w)
    push_cast at this
    simp only [G, smul_eq_mul, map_sub, map_mul, map_ofNat, conj_ofReal, ofReal_sub]
    linear_combination K w * this
  have h₁ : CircleIntegrable (fun w ↦ (-2 : ℂ) • G w) c ρ :=
    ((hKs.mul (continuous_ofReal.comp_continuousOn (continuousOn_const.sub
      (continuous_re.comp_continuousOn hfs)))).const_smul (-2 : ℂ)).circleIntegrable'
  have h₂ : CircleIntegrable (fun w ↦ K w * conj (f w - 2 * (M : ℂ))) c ρ :=
    (hKs.mul (continuous_conj.comp_continuousOn (hfs.sub continuousOn_const))).circleIntegrable'
  have h₃ : DiffContOnCl ℂ (fun w ↦ f w - 2 * (M : ℂ)) (ball c ρ) := hf.sub diffContOnCl_const
  rw [hdecomp, circleAverage_fun_sub h₁ h₂, circleAverage_fun_smul, smul_eq_mul,
    circleAverage_div_sub_pow_mul_conj_eq_zero h₃ hk hz, sub_zero]

/-- Cauchy's integral formula for `f^{(k)}(z)` as a circle average: the kernel is
`(w - c) / (w - z) ^ (k + 1)`, since `dw = i (w - c) dθ` on `sphere c ρ`. -/
private theorem iteratedDeriv_eq_factorial_mul_circleAverage (hf : DiffContOnCl ℂ f (ball c ρ))
    (hz : z ∈ ball c ρ) :
    iteratedDeriv k f z =
      k.factorial * circleAverage (fun w ↦ (w - c) / (w - z) ^ (k + 1) * f w) c ρ := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.mp hz)
  rw [circleAverage_eq_circleIntegral hρ.ne',
    circleIntegral.integral_congr hρ.le (g := fun w ↦ (1 / (w - z) ^ (k + 1)) • f w) ?_,
    hf.circleIntegral_one_div_sub_pow_smul k hz]
  · have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [smul_eq_mul]
    field_simp
  · intro w hw
    have hu : w - c ≠ 0 := sub_ne_zero.2 (ne_of_mem_sphere hw hρ.ne')
    simp only [smul_eq_mul]
    field_simp

/-- **Derivative form of the Borel–Carathéodory inequality on a closed disc.** Let `f` be
holomorphic on `ball c ρ` and continuous on its closure, with `re (f w) ≤ M` on `sphere c ρ`. For
`k ≥ 1` and `z ∈ ball c ρ`,
`‖f^{(k)}(z)‖ ≤ 2 k! ρ (M - re (f c)) / (ρ - ‖z - c‖) ^ (k + 1)`. -/
theorem norm_iteratedDeriv_le_of_forall_mem_sphere_re_le {M : ℝ}
    (hf : DiffContOnCl ℂ f (ball c ρ)) (hM : ∀ w ∈ sphere c ρ, (f w).re ≤ M) (hk : 1 ≤ k)
    (hz : z ∈ ball c ρ) :
    ‖iteratedDeriv k f z‖ ≤ 2 * k.factorial * ρ * (M - (f c).re) / (ρ - ‖z - c‖) ^ (k + 1) := by
  have hzc : ‖z - c‖ < ρ := by simpa [dist_eq_norm] using hz
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt hzc
  have hfs : ContinuousOn f (sphere c |ρ|) := by
    rw [abs_of_pos hρ]
    exact hf.continuousOn_ball.mono sphere_subset_closedBall
  have hKs := continuousOn_div_sub_pow_sphere (k := k) hz
  set K : ℂ → ℂ := fun w ↦ (w - c) / (w - z) ^ (k + 1)
  set B : ℝ := ρ / (ρ - ‖z - c‖) ^ (k + 1)
  -- On the circle, `‖w - z‖ ≥ ρ - ‖z - c‖ > 0`, so `‖K w‖ ≤ B`.
  have hKB (w : ℂ) (hw : w ∈ sphere c ρ) : ‖K w‖ ≤ B := by
    have hwc : ‖w - c‖ = ρ := by simpa [dist_eq_norm] using hw
    simp only [K, B, norm_div, norm_pow, hwc]
    have : 0 < ρ - ‖z - c‖ := sub_pos.2 hzc
    gcongr
    linarith [norm_sub_le_norm_sub_add_norm_sub w z c]
  -- The mean value property for `M - f` gives the average of `M - re f`.
  have hmean : circleAverage (fun w ↦ M - (f w).re) c ρ = M - (f c).re := by
    have hMf : DiffContOnCl ℂ (fun w ↦ (M : ℂ) - f w) (ball c |ρ|) := by
      rw [abs_of_pos hρ]
      exact diffContOnCl_const.sub hf
    have := reCLM.circleAverage_comp_comm
      (continuousOn_const.sub hfs).circleIntegrable' (f := fun w ↦ (M : ℂ) - f w) (c := c)
    rw [hMf.circleAverage] at this
    simpa [Function.comp_def] using this
  -- Since `M - re f ≥ 0` on the circle, the average against `K` is at most `B` times its mean.
  have hGle :
      ‖circleAverage (fun w ↦ K w * ((M - (f w).re : ℝ) : ℂ)) c ρ‖ ≤ B * (M - (f c).re) := by
    refine norm_circleAverage_le_circleAverage_norm.trans ?_
    rw [← hmean, ← smul_eq_mul, ← circleAverage_fun_smul]
    refine circleAverage_mono ?_ ?_ fun w hw ↦ ?_
    · exact (hKs.mul (continuous_ofReal.comp_continuousOn (continuousOn_const.sub
        (continuous_re.comp_continuousOn hfs)))).norm.circleIntegrable'
    · exact (by fun_prop :
        ContinuousOn (fun w ↦ B • (M - (f w).re)) (sphere c |ρ|)).circleIntegrable'
    · rw [abs_of_pos hρ] at hw
      have hMw : 0 ≤ M - (f w).re := sub_nonneg.2 (hM w hw)
      simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hMw, smul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hKB w hw) hMw
  rw [iteratedDeriv_eq_factorial_mul_circleAverage hf hz,
    circleAverage_div_sub_pow_mul_eq_neg_two_mul hf hk hz M, norm_mul, norm_mul, norm_natCast,
    norm_neg, norm_ofNat]
  calc (k.factorial : ℝ) * (2 * ‖circleAverage (fun w ↦ K w * ((M - (f w).re : ℝ) : ℂ)) c ρ‖)
      ≤ k.factorial * (2 * (B * (M - (f c).re))) := by gcongr
    _ = 2 * k.factorial * ρ * (M - (f c).re) / (ρ - ‖z - c‖) ^ (k + 1) := by
      simp only [B]
      ring

/-- **Derivative form of the Borel–Carathéodory inequality.** Let `f` be holomorphic on
`ball c R` with `re (f w) ≤ M` there. For `k ≥ 1`, `r < R` and `‖z - c‖ ≤ r`,
`‖f^{(k)}(z)‖ ≤ 2 k! R (M - re (f c)) / (R - r) ^ (k + 1)`.

The bound is sharp: for `M > 0`, the function `w ↦ -2 M (w - c) / (R - (w - c))` has real part
below `M` on `ball c R`, vanishes at `c`, and attains the bound at `z = c + r` for every `k`. -/
theorem norm_iteratedDeriv_le_borelCaratheodory {R M r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hM : ∀ w ∈ ball c R, (f w).re ≤ M) (hk : 1 ≤ k)
    (hrR : r < R) (hz : ‖z - c‖ ≤ r) :
    ‖iteratedDeriv k f z‖ ≤ 2 * k.factorial * R * (M - (f c).re) / (R - r) ^ (k + 1) := by
  have hR : 0 < R := (norm_nonneg _).trans_lt (hz.trans_lt hrR)
  have hA : 0 ≤ M - (f c).re := sub_nonneg.2 (hM c (mem_ball_self hR))
  -- The bound on every circle of radius `ρ ∈ (r, R)`, then `ρ → R`.
  have hbound (ρ : ℝ) (hρ : ρ ∈ Set.Ioo r R) :
      ‖iteratedDeriv k f z‖ ≤ 2 * k.factorial * ρ * (M - (f c).re) / (ρ - r) ^ (k + 1) := by
    have hzρ : z ∈ ball c ρ := mem_ball_iff_norm.2 (hz.trans_lt hρ.1)
    refine (norm_iteratedDeriv_le_of_forall_mem_sphere_re_le
      (hf.diffContOnCl_ball (closedBall_subset_ball hρ.2))
      (fun w hw ↦ hM w (closedBall_subset_ball hρ.2 (sphere_subset_closedBall hw))) hk
      hzρ).trans ?_
    have hρr : 0 < ρ - r := sub_pos.2 hρ.1
    have hnum : 0 ≤ 2 * (k.factorial : ℝ) * ρ * (M - (f c).re) := by
      have : 0 ≤ ρ := ((norm_nonneg _).trans hz).trans hρ.1.le
      positivity
    exact div_le_div_of_nonneg_left hnum (pow_pos hρr _)
      (pow_le_pow_left₀ hρr.le (by linarith) _)
  have hlim : Tendsto (fun ρ ↦ 2 * k.factorial * ρ * (M - (f c).re) / (ρ - r) ^ (k + 1))
      (𝓝[<] R) (𝓝 (2 * k.factorial * R * (M - (f c).re) / (R - r) ^ (k + 1))) := by
    have h₁ : ContinuousAt (fun ρ : ℝ ↦ 2 * (k.factorial : ℝ) * ρ * (M - (f c).re)) R := by
      fun_prop
    have h₂ : ContinuousAt (fun ρ : ℝ ↦ (ρ - r) ^ (k + 1)) R := by fun_prop
    exact (h₁.div h₂ (pow_ne_zero _ (sub_pos.2 hrR).ne')).tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsLT hrR) hbound)

/-- **Carathéodory's coefficient inequality.** Let `f` be holomorphic on `ball c R`, `0 < R`, with
`re (f w) ≤ M` there. For `k ≥ 1`, the Taylor coefficient `a_k = f^{(k)}(c) / k!` satisfies
`‖a_k‖ R ^ k ≤ 2 (M - re (f c))`. -/
theorem norm_iteratedDeriv_mul_pow_le_of_forall_mem_ball_re_le {R M : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hM : ∀ w ∈ ball c R, (f w).re ≤ M) (hk : 1 ≤ k)
    (hR : 0 < R) :
    ‖iteratedDeriv k f c‖ * R ^ k ≤ 2 * k.factorial * (M - (f c).re) := by
  have h := norm_iteratedDeriv_le_borelCaratheodory (z := c) hf hM hk hR (by simp)
  rw [sub_zero, pow_succ] at h
  calc ‖iteratedDeriv k f c‖ * R ^ k
      ≤ 2 * k.factorial * R * (M - (f c).re) / (R ^ k * R) * R ^ k := by gcongr
    _ = 2 * k.factorial * (M - (f c).re) := by
      field_simp

end Complex

/-- **Derivative bound from a one-sided real-part bound.** Let `g` be holomorphic on
`ball z₀ r` with `g z₀ = 0` and `re (g w) ≤ A` there. Then at every `z` with
`‖z - z₀‖ < r`, `‖deriv g z‖ ≤ 4 (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * A`. This is a weakened
`k = 1` case of `Complex.norm_iteratedDeriv_le_borelCaratheodory`. -/
theorem Complex.norm_deriv_le_of_forall_mem_ball_re_le {g : ℂ → ℂ} {z₀ : ℂ} {r A : ℝ}
    (hg : DifferentiableOn ℂ g (ball z₀ r)) (hg₀ : g z₀ = 0)
    (hre : ∀ w ∈ ball z₀ r, (g w).re ≤ A) {z : ℂ} (hz : ‖z - z₀‖ < r) :
    ‖deriv g z‖ ≤ 4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * A := by
  have hA : 0 ≤ A := by
    simpa [hg₀] using hre z₀ (mem_ball_self ((norm_nonneg _).trans_lt hz))
  have h := Complex.norm_iteratedDeriv_le_borelCaratheodory hg hre le_rfl hz le_rfl
  rw [iteratedDeriv_one, hg₀, zero_re, sub_zero, Nat.factorial_one, Nat.cast_one] at h
  refine h.trans ?_
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg (z - z₀)]) (by positivity)

/-- A nonvanishing holomorphic function on an open disc with relative norm bound `M` has
logarithmic derivative bounded by `4 (r + ‖z-z₀‖) / (r - ‖z-z₀‖)² log M` inside the disc.
No condition on its boundary or exterior values is required. -/
theorem Complex.norm_logDeriv_le_of_forall_mem_ball_norm_le_mul {B : ℂ → ℂ} {z₀ z : ℂ} {r M : ℝ}
    (hB : DifferentiableOn ℂ B (ball z₀ r))
    (hB0 : ∀ w ∈ ball z₀ r, B w ≠ 0)
    (hM : ∀ w ∈ ball z₀ r, ‖B w‖ ≤ M * ‖B z₀‖)
    (hz : ‖z - z₀‖ < r) :
    ‖logDeriv B z‖ ≤ 4 * (r + ‖z - z₀‖) / (r - ‖z - z₀‖) ^ 2 * Real.log M := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hz
  have hzb : z ∈ ball z₀ r := by rwa [mem_ball, dist_eq_norm]
  have hBz₀ : B z₀ ≠ 0 := hB0 z₀ (mem_ball_self hr)
  have hMpos : 0 < M := by
    have hc := hM z₀ (mem_ball_self hr)
    have hn := norm_pos_iff.mpr hBz₀
    nlinarith
  obtain ⟨L, hLd, hL⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp (U := ball z₀ r)
    ((convex_ball z₀ r).isSimplyConnected ⟨z₀, mem_ball_self hr⟩) isOpen_ball
    (hB.div_const (B z₀))
    (fun ⟨w, hw, h0⟩ ↦ div_ne_zero (hB0 w hw) hBz₀ h0)
  let H : ℂ → ℂ := fun w ↦ L w - L z₀
  have hre (w : ℂ) (hw : w ∈ ball z₀ r) : (H w).re ≤ Real.log M := by
    have hexp : exp (H w) = B w / B z₀ := by
      have h₁ := hL hw
      have h₂ := hL (mem_ball_self hr)
      simp only [Function.comp_apply, div_self hBz₀] at h₁ h₂
      simp [H, Complex.exp_sub, h₁, h₂]
    rw [Real.le_log_iff_exp_le hMpos, ← Complex.norm_exp, hexp, norm_div,
      div_le_iff₀ (norm_pos_iff.2 hBz₀)]
    exact hM w hw
  have hlogB : deriv H z = logDeriv B z := by
    simp only [H, deriv_sub_const]
    rw [TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball hLd hL hzb]
    simp only [div_eq_mul_inv]
    exact logDeriv_mul_const z _ (inv_ne_zero hBz₀)
  rw [← hlogB]
  exact Complex.norm_deriv_le_of_forall_mem_ball_re_le (hLd.sub_const _)
    (sub_self _) hre hz

end DerivBound
