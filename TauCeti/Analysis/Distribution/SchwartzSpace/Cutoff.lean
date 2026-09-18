/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Cutting off a Schwartz function

Let `χ : E → ℝ` be a smooth compactly supported function that equals `1` near the origin. For a
Schwartz function `f`, the truncations `x ↦ χ (R⁻¹ • x) • f x` are smooth and compactly supported,
and they converge to `f` in the Schwartz topology as `R → ∞`. Consequently the smooth compactly
supported functions are dense in `𝓢(E, F)` when `E` is finite-dimensional.

This is how a statement proved for smooth compactly supported test functions is passed to Schwartz
test functions: any quantity controlled by finitely many Schwartz seminorms (for instance a
weighted sup norm of the Fourier transform) is approximated by its values on the truncations.

The estimate is explicit. Suppose `χ = 1` on the ball of radius `r` and `R ≥ 1`. The difference
`f - χ (R⁻¹ • ·) • f` is `(1 - χ (R⁻¹ • ·)) • f`, which vanishes on the ball of radius `r R`.
Expand its `n`-th derivative by the Leibniz rule. The term in which no derivative falls on the
cutoff is supported where `‖x‖ ≥ r R`, so trading one power of `‖x‖` against `(r R)⁻¹` bounds it by
the `(k + 1, n)` seminorm of `f` divided by `r R`. Every other term carries a derivative of
`χ (R⁻¹ • ·)` of order `i ≥ 1`, which is `R⁻ⁱ` times a derivative of `χ` and hence `O(R⁻¹)`.
Altogether the `(k, n)` seminorm of the difference is `O(R⁻¹)`.

## Main results

* `SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le`: the explicit bound
  `seminorm k n (f - χ (R⁻¹ • ·) • f) ≤ K / R` for `R ≥ 1`.
* `SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`: the truncations converge to `f` in
  `𝓢(E, F)`.
* `SchwartzMap.hasCompactSupport_smulLeftCLM_comp_inv_smul`: the truncations are compactly
  supported.
* `SchwartzMap.dense_setOf_hasCompactSupport`: compactly supported functions are dense in
  `𝓢(E, F)` for finite-dimensional `E`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Section 7.1.
-/

public section

open Filter Metric Set
open scoped ContDiff Topology SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace SchwartzMap

variable {χ : E → ℝ}

/-- The truncation `χ (R⁻¹ • ·) • f` of a Schwartz function by a cutoff of temperate growth,
evaluated pointwise. -/
theorem smulLeftCLM_comp_inv_smul_apply (hχ : χ.HasTemperateGrowth) (R : ℝ) (f : 𝓢(E, F))
    (x : E) : smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f x = χ (R⁻¹ • x) • f x :=
  smulLeftCLM_apply_apply (hχ.comp (R⁻¹ • ContinuousLinearMap.id ℝ E).hasTemperateGrowth) f x

/-- A truncation of a Schwartz function by a compactly supported cutoff is compactly supported. -/
theorem hasCompactSupport_smulLeftCLM_comp_inv_smul (hχ : ContDiff ℝ ∞ χ)
    (hsupp : HasCompactSupport χ) {R : ℝ} (hR : R ≠ 0) (f : 𝓢(E, F)) :
    HasCompactSupport (smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) := by
  rw [funext (smulLeftCLM_comp_inv_smul_apply (hsupp.hasTemperateGrowth hχ) R f)]
  exact (hsupp.comp_smul (inv_ne_zero hR)).smul_right

/-- For `i ≠ 0` and `R ≥ 1`, the `i`-th derivative of `1 - χ (R⁻¹ • ·)` is at most `B / R`, where
`B` bounds the `i`-th derivative of `χ`. -/
private lemma norm_iteratedFDeriv_one_sub_comp_inv_smul_le (hχ : ContDiff ℝ ∞ χ) {i : ℕ}
    (hi : i ≠ 0) {B : ℝ} (hB : ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ ≤ B / R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hcomp : ContDiff ℝ i fun y ↦ χ (R⁻¹ • y) :=
    (hχ.comp (contDiff_const_smul _)).of_le (mod_cast le_top)
  rw [fun_iteratedFDeriv_sub_apply contDiffAt_const hcomp.contDiffAt,
    iteratedFDeriv_const_of_ne hi, Pi.zero_apply, zero_sub, norm_neg,
    iteratedFDeriv_comp_const_smul _ (hχ.of_le (mod_cast le_top)), norm_smul, norm_pow,
    norm_inv, Real.norm_of_nonneg hR0.le]
  have hRi : (R ^ i)⁻¹ ≤ R⁻¹ := by
    rw [← inv_pow]
    exact pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hR) hi
  calc (R⁻¹) ^ i * ‖iteratedFDeriv ℝ i χ (R⁻¹ • x)‖ ≤ R⁻¹ * B := by
        rw [inv_pow]
        exact mul_le_mul hRi (hB _) (norm_nonneg _) (by positivity)
    _ = B / R := by rw [inv_mul_eq_div]

/-- Where `‖x‖ ≥ ρ > 0`, one power of `‖x‖` can be traded for `ρ⁻¹` against the next seminorm. -/
private lemma pow_mul_norm_iteratedFDeriv_le_div (f : 𝓢(E, F)) (k j : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : E} (hx : ρ ≤ ‖x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℝ (k + 1) j f / ρ := by
  rw [le_div_iff₀ hρ]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ * ρ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j f x‖ := by ring
    _ ≤ SchwartzMap.seminorm ℝ (k + 1) j f := le_seminorm ℝ (k + 1) j f x

/-- One Leibniz term of `D^n ((1 - χ (R⁻¹ • ·)) • f)` at a point with `‖x‖ ≥ r R` is `O(R⁻¹)`:
if no derivative falls on the cutoff, the factor `‖x‖ ^ k` is traded for `(r R)⁻¹`, and otherwise
the derivative of the cutoff contributes the factor `R⁻¹`. -/
private lemma norm_iteratedFDeriv_one_sub_mul_le (hχ : ContDiff ℝ ∞ χ) {B : ℕ → ℝ}
    (hB : ∀ i x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B i) {r : ℝ} (hr : 0 < r) (f : 𝓢(E, F))
    (k n i : ℕ) {R : ℝ} (hR : 1 ≤ R) {x : E} (hx : r * R ≤ ‖x‖) :
    ‖iteratedFDeriv ℝ i (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ *
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) ≤
      (1 + B i) * (SchwartzMap.seminorm ℝ k (n - i) f +
        SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) / R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hB0 : ∀ i, 0 ≤ B i := fun i ↦ (norm_nonneg _).trans (hB i 0)
  have hrR : 0 < r * R := mul_pos hr hR0
  rcases eq_or_ne i 0 with rfl | hi
  · -- No derivative falls on the cutoff: use `‖x‖ ≥ r R`.
    have hh0 : ‖iteratedFDeriv ℝ 0 (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ ≤ 1 + B 0 := by
      rw [norm_iteratedFDeriv_zero]
      refine (norm_sub_le _ _).trans ?_
      have := hB 0 (R⁻¹ • x)
      rw [norm_iteratedFDeriv_zero] at this
      simpa using this
    have hf0 := pow_mul_norm_iteratedFDeriv_le_div f k (n - 0) hrR hx
    have hS : 0 ≤ SchwartzMap.seminorm ℝ k (n - 0) f := apply_nonneg _ _
    calc _ ≤ (1 + B 0) * (SchwartzMap.seminorm ℝ (k + 1) (n - 0) f / (r * R)) :=
          mul_le_mul hh0 hf0 (by positivity) (by linarith [hB0 0])
      _ = (1 + B 0) * (SchwartzMap.seminorm ℝ (k + 1) (n - 0) f / r) / R := by
          field_simp
      _ ≤ _ := by
          gcongr
          · linarith [hB0 0]
          · exact le_add_of_nonneg_left hS
  · -- A derivative falls on the cutoff: it contributes a factor `R⁻¹`.
    have hhi := norm_iteratedFDeriv_one_sub_comp_inv_smul_le hχ hi (hB i) hR x
    have hfi : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤
        SchwartzMap.seminorm ℝ k (n - i) f := le_seminorm ℝ k (n - i) f x
    have hS : 0 ≤ SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r :=
      div_nonneg (apply_nonneg _ _) hr.le
    calc _ ≤ B i / R * SchwartzMap.seminorm ℝ k (n - i) f :=
          mul_le_mul hhi hfi (by positivity) (by have := hB0 i; positivity)
      _ ≤ (1 + B i) / R * (SchwartzMap.seminorm ℝ k (n - i) f +
            SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) := by
          gcongr
          · exact div_nonneg (by linarith [hB0 i]) hR0.le
          · linarith
          · exact le_add_of_nonneg_right hS
      _ = _ := by ring

/-- **The truncation estimate.** Let `χ` be smooth with `‖D^i χ‖ ≤ B i` for every `i`, and equal
to `1` on the ball of radius `r > 0`. For `R ≥ 1` the `(k, n)` seminorm of `f - χ (R⁻¹ • ·) • f`
is at most `K / R`, where `K` depends on `χ`, `f`, `k` and `n` but not on `R`. -/
theorem seminorm_sub_smulLeftCLM_comp_inv_smul_le (hχ : ContDiff ℝ ∞ χ)
    {B : ℕ → ℝ} (hB : ∀ i x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B i)
    {r : ℝ} (hr : 0 < r) (hχ1 : ∀ y, ‖y‖ < r → χ y = 1) (f : 𝓢(E, F)) (k n : ℕ) {R : ℝ}
    (hR : 1 ≤ R) :
    SchwartzMap.seminorm ℝ k n (f - smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
        (SchwartzMap.seminorm ℝ k (n - i) f + SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r)) /
        R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hB0 : ∀ i, 0 ≤ B i := fun i ↦ (norm_nonneg _).trans (hB i 0)
  set h : E → ℝ := fun y ↦ 1 - χ (R⁻¹ • y) with hh
  have hhsmooth : ContDiff ℝ ∞ h := contDiff_const.sub (hχ.comp (contDiff_const_smul _))
  have hcoe : ⇑(f - smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) = fun x ↦ h x • f x := by
    ext x
    have hχt : χ.HasTemperateGrowth := ⟨hχ, fun i ↦ ⟨0, B i, fun x ↦ by simpa using hB i x⟩⟩
    simp only [sub_apply, smulLeftCLM_comp_inv_smul_apply hχt R f x, hh, sub_smul, one_smul]
  have hK : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
      (SchwartzMap.seminorm ℝ k (n - i) f + SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (by linarith [hB0 i])) (add_nonneg (apply_nonneg _ _) (div_nonneg (apply_nonneg _ _) hr.le))
  refine seminorm_le_bound ℝ k n _ (div_nonneg hK hR0.le) fun x ↦ ?_
  rw [hcoe]
  rcases lt_or_ge ‖x‖ (r * R) with hx | hx
  · -- Near the origin the truncation agrees with `f`, so the difference is locally zero.
    have hzero : (fun y ↦ h y • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
      rw [mem_ball_zero_iff] at hy
      have hy' : ‖R⁻¹ • y‖ < r := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hR0.le, inv_mul_lt_iff₀ hR0]
        linarith
      simp [hh, hχ1 _ hy']
    rw [(hzero.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply,
      norm_zero, mul_zero]
    exact div_nonneg hK hR0.le
  · -- Away from the origin, expand by the Leibniz rule and bound each term by `O(R⁻¹)`.
    refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hhsmooth (f.smooth ⊤) x
      (mod_cast le_top)) (by positivity)).trans ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i h x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        = (n.choose i : ℝ) *
            (‖iteratedFDeriv ℝ i h x‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖)) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + B i) * (SchwartzMap.seminorm ℝ k (n - i) f +
            SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) / R) :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_one_sub_mul_le hχ hB hr f k n i hR hx)
            (Nat.cast_nonneg _)
      _ = _ := by ring

/-- **Truncations converge in the Schwartz topology.** If `χ` is smooth, compactly supported and
equal to `1` near the origin, then `χ (R⁻¹ • ·) • f → f` in `𝓢(E, F)` as `R → ∞`. -/
theorem tendsto_smulLeftCLM_comp_inv_smul_atTop (hχ : ContDiff ℝ ∞ χ)
    (hsupp : HasCompactSupport χ) (hχ1 : χ =ᶠ[𝓝 0] 1) (f : 𝓢(E, F)) :
    Tendsto (fun R : ℝ ↦ smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) atTop (𝓝 f) := by
  choose B hB using fun i ↦ (hχ.continuous_iteratedFDeriv (m := i) (mod_cast le_top))
    |>.bounded_above_of_compact_support (hsupp.iteratedFDeriv i)
  obtain ⟨r, hr, hχr⟩ := Metric.eventually_nhds_iff.1 hχ1
  have hχ1' : ∀ y, ‖y‖ < r → χ y = 1 := fun y hy ↦ hχr (by rwa [dist_zero_right])
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  set K := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
    (SchwartzMap.seminorm ℝ k (n - i) f + SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r)
  filter_upwards [eventually_ge_atTop 1, eventually_gt_atTop (K / ε)] with R hR hKR
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rw [schwartzSeminormFamily_apply, ← map_neg_eq_map, neg_sub]
  refine (seminorm_sub_smulLeftCLM_comp_inv_smul_le hχ hB hr hχ1' f k n hR).trans_lt ?_
  rw [div_lt_iff₀ hR0]
  rwa [div_lt_iff₀ hε, mul_comm] at hKR

/-- **Compactly supported functions are dense in Schwartz space.** -/
theorem dense_setOf_hasCompactSupport [FiniteDimensional ℝ E] :
    Dense {f : 𝓢(E, F) | HasCompactSupport f} := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  intro f
  refine mem_closure_of_tendsto
    (tendsto_smulLeftCLM_comp_inv_smul_atTop b.contDiff b.hasCompactSupport b.eventuallyEq_one f)
    ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact hasCompactSupport_smulLeftCLM_comp_inv_smul b.contDiff b.hasCompactSupport hR.ne' f

end SchwartzMap
