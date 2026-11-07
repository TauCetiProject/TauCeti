/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Interpolation inequalities for derivatives

This file proves the supremum-norm interpolation inequalities that control an intermediate
derivative by a small multiple of a higher one plus a large multiple of the function. They are
used to absorb lower-order terms in Schauder estimates, elliptic and parabolic.

The basic estimate is a first-order Taylor bound: if `g` has derivative `g'` and `g'` is
`α`-Hölder with constant `H` on a segment from `x` to `x + w`, then
`‖g (x + w) - g x - g' x w‖ ≤ H ‖w‖^(1 + α)`. Hence

`‖g' x w‖ ≤ ‖g (x + w)‖ + ‖g x‖ + H ‖w‖^(1 + α)`.

Choosing `‖w‖ = ε` in every direction gives, on the whole space,

`‖D^(k+1) f‖_∞ ≤ 2 ε⁻¹ ‖D^k f‖_∞ + ε^α [D^(k+1) f]_α`

for every `ε > 0`. For `α = 1` this is the Landau-type inequality
`‖D^(k+1) f‖_∞ ≤ 2 ε⁻¹ ‖D^k f‖_∞ + ε ‖D^(k+2) f‖_∞`. Combining the two and absorbing the
supremum of `D^(k+2) f`, which must be finite a priori, gives

`‖D^(k+2) f‖_∞ ≤ 32 ε⁻² ‖D^k f‖_∞ + 2 ε^α [D^(k+2) f]_α`.

All constants are absolute: they depend neither on the dimension nor on `α`.

Interior estimates need local bounds, which use the second derivative. If `g''` is `α`-Hölder with
constant `H` on `s`, the second-order Taylor remainder of `g` along a segment in `s` is at most
`H ‖w‖^(2 + α)`. In the symmetric difference `g (x + w) - g (x - w)` the second-order terms cancel,
so at the centre `x` of a closed ball of radius `ε` in `s`, with `‖g‖ ≤ M` there,

`‖g' x‖ ≤ M / ε + H ε^(1 + α)`,

and at the centre of a closed ball of radius `2 ε` in `s`, `‖g'' x‖ ≤ 2 M / ε² + 3 H ε^α`. Only
the values of `g` and the Hölder constant of `g''` on `s` enter. For a function which is `C²` on
an open set containing `s`, with `D²u` `α`-Hölder on `s`, these are bounds on `‖Du‖` and `‖D²u‖`.

On a closed interval `[a, b]` the same argument applies to one-sided derivatives within
`[a, b]`, for steps `h` with `2 h ≤ b - a`, since from each point of `[a, b]` a step of length `h`
in one of the two directions stays in the interval. With temporal Hölder exponent `α / 2` and
`h = ε²`, this is the estimate for time derivatives on a slab used in parabolic Hölder spaces.

For a function `u (x, t)` of space and time, the same Taylor bound at the spatial scale
`h = √|t - s|`, applied to the difference `u (·, t) - u (·, s)`, gives

`‖D_x u (x, t) - D_x u (x, s)‖ ≤ (C₂ + Cₜ) |t - s|^((1 + α) / 2)`,

where `C₂` is the `α / 2`-Hölder constant in time of `D_x² u` and `Cₜ` is the `α`-Hölder constant
in space of `∂ₜ u`. The increment of the difference over a spatial step of length `h` is
controlled by the mean value inequality in time and the spatial Hölder bound on `∂ₜ u`, and its
linear approximation error by the difference of the Hessians.

## Main declarations

* `HolderOnWith.norm_image_sub_sub_le_of_hasFDerivWithinAt`: the first-order Taylor bound for a
  Hölder derivative.
* `HolderOnWith.norm_sub_fderiv_le_of_mem_ball`: the Taylor remainder on a ball for the
  derivative of a differentiable function.
* `HolderOnWith.norm_apply_le_of_hasFDerivWithinAt`: the resulting bound on a directional
  derivative.
* `HolderOnWith.norm_le_of_hasFDerivWithinAt_ball`: the local interpolation inequality on a
  ball, also applicable to differences of two functions.
* `HolderOnWith.norm_fderiv_sub_fderiv_le_of_norm_sub_le_ball`: comparison of two derivatives
  from uniform function error and possibly different Hölder constants.
* `HolderWith.norm_le_of_hasFDerivAt`, `HolderWith.norm_fderiv_le_of_norm_le` and
  `HolderWith.norm_iteratedFDeriv_succ_le_of_norm_le`: the interpolation inequality on the whole
  space.
* `ContDiff.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_le`: the Landau-type inequality.
* `HolderWith.norm_iteratedFDeriv_add_two_le_of_norm_le` and
  `HolderWith.norm_iteratedFDeriv_succ_le_of_norm_le_of_bddAbove`: the absorbed bounds on the two
  derivatives above `D^k f`, and
  `HolderWith.norm_iteratedFDeriv_succ_le_and_norm_iteratedFDeriv_add_two_le`: both bounds with
  one constant, for scales `ε ≤ 1`.
* `HolderOnWith.norm_image_sub_sub_sub_le_of_hasFDerivWithinAt`: the second-order Taylor bound
  for a Hölder second derivative.
* `HolderOnWith.norm_le_of_hasFDerivWithinAt_of_closedBall_subset` and
  `HolderOnWith.norm_le_of_hasFDerivWithinAt_of_closedBall_two_mul_subset`: the local
  interpolation inequalities for the first and second derivatives on a ball.
* `HolderOnWith.norm_fderiv_le_of_contDiffOn` and
  `HolderOnWith.norm_iteratedFDeriv_two_le_of_contDiffOn`: the same for a `C²` function.
* `HolderOnWith.norm_le_of_hasDerivWithinAt_Icc`: the interpolation inequality for derivatives
  within a closed interval.
* `TauCeti.holderOnWith_Icc_of_hasFDerivAt_of_hasDerivWithinAt`: the temporal
  `(1 + α) / 2`-Hölder continuity of the spatial derivative.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.8 (interpolation inequalities).
* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Chapter 0.
* O. A. Ladyzhenskaya, V. A. Solonnikov, N. N. Ural'tseva, *Linear and Quasi-linear Equations of
  Parabolic Type*, Chapter II (parabolic Hölder spaces).
-/

public section

open Set
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace HolderOnWith

/-- **First-order Taylor bound for a Hölder derivative.** If `g` has derivative `g'` within `s`
and `g'` is `α`-Hölder with constant `H` on `s`, then for a segment from `x` to `x + w` contained
in `s`, the error of the linear approximation is at most `H ‖w‖^(1 + α)`. -/
theorem norm_image_sub_sub_le_of_hasFDerivWithinAt {s : Set E} {g : E → F}
    {g' : E → E →L[ℝ] F} {H α : ℝ≥0} (hH : HolderOnWith H α g' s)
    (hg : ∀ y ∈ s, HasFDerivWithinAt g (g' y) s y) {x w : E}
    (hxw : segment ℝ x (x + w) ⊆ s) :
    ‖g (x + w) - g x - g' x w‖ ≤ H * ‖w‖ ^ (1 + (α : ℝ)) := by
  have hx : x ∈ segment ℝ x (x + w) := left_mem_segment ℝ x (x + w)
  -- On the segment, `g'` stays within `H ‖w‖^α` of `g' x`, so the mean value inequality for a
  -- derivative minus a fixed linear map bounds the linear remainder from `x` to `x + w`.
  have hbound : ∀ y ∈ segment ℝ x (x + w), ‖g' y - g' x‖ ≤ H * ‖w‖ ^ (α : ℝ) := by
    intro y hy
    have hyx : dist y x ≤ ‖w‖ := by
      simpa [dist_comm] using segment_subset_closedBall_left x (x + w) hy
    rw [← dist_eq_norm]
    exact (hH.dist_le (hxw hy) (hxw hx)).trans (by gcongr)
  have hmvt := (convex_segment x (x + w)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun y hy => (hg y (hxw hy)).mono hxw) hbound hx (right_mem_segment ℝ x (x + w))
  rw [Real.rpow_add' (norm_nonneg w) (by positivity), Real.rpow_one, mul_comm (‖w‖)]
  simpa only [add_sub_cancel_left, mul_assoc] using hmvt

/-- **Taylor remainder on a ball.** A differentiable function whose derivative is `(H, α)`-Hölder
on a ball satisfies `‖g y - g x - Dg(x)(y - x)‖ ≤ H ‖y - x‖^α ‖y - x‖` at its centre `x`.
Neither finite dimensionality, completeness nor a positive exponent is required. -/
theorem norm_sub_fderiv_le_of_mem_ball {g : E → F} {H α : ℝ≥0} {x y : E} {r : ℝ}
    (hH : HolderOnWith H α (fderiv ℝ g) (Metric.ball x r))
    (hg : DifferentiableOn ℝ g (Metric.ball x r)) (hy : y ∈ Metric.ball x r) :
    ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ H * ‖y - x‖ ^ (α : ℝ) * ‖y - x‖ := by
  have hrpos := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hy)
  have hseg : segment ℝ x (x + (y - x)) ⊆ Metric.ball x r := by
    rw [add_sub_cancel]
    exact (convex_ball x r).segment_subset (Metric.mem_ball_self hrpos) hy
  have hTaylor := hH.norm_image_sub_sub_le_of_hasFDerivWithinAt
    (fun z hz => ((hg z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasFDerivAt
      |>.hasFDerivWithinAt) hseg
  rw [add_sub_cancel, add_comm 1, Real.rpow_add' (norm_nonneg _) (by positivity),
    Real.rpow_one] at hTaylor
  simpa only [mul_assoc] using hTaylor

/-- **Interpolation along a segment.** If `g` has derivative `g'` within `s` and `g'` is
`α`-Hölder with constant `H` on `s`, then for a segment from `x` to `x + w` contained in `s`,
the derivative in the direction `w` is bounded by the values of `g` at the endpoints and the
Hölder constant. -/
theorem norm_apply_le_of_hasFDerivWithinAt {s : Set E} {g : E → F} {g' : E → E →L[ℝ] F}
    {H α : ℝ≥0} (hH : HolderOnWith H α g' s) (hg : ∀ y ∈ s, HasFDerivWithinAt g (g' y) s y)
    {x w : E} (hxw : segment ℝ x (x + w) ⊆ s) :
    ‖g' x w‖ ≤ ‖g (x + w)‖ + ‖g x‖ + H * ‖w‖ ^ (1 + (α : ℝ)) := by
  have hT := hH.norm_image_sub_sub_le_of_hasFDerivWithinAt hg hxw
  calc ‖g' x w‖ = ‖(g (x + w) - g x) - (g (x + w) - g x - g' x w)‖ := by abel_nf
    _ ≤ ‖g (x + w) - g x‖ + ‖g (x + w) - g x - g' x w‖ := norm_sub_le _ _
    _ ≤ ‖g (x + w)‖ + ‖g x‖ + H * ‖w‖ ^ (1 + (α : ℝ)) := by
      linarith [norm_sub_le (g (x + w)) (g x)]

/-- **Local interpolation inequality.** On a ball of radius `ε`, a function bounded by `M`
whose derivative is `(H, α)`-Hölder has derivative norm at the centre at most
`4 M / ε + H ε^α`. Applying the estimate to a difference compares derivatives using only
uniform function errors and Hölder derivative bounds. -/
theorem norm_le_of_hasFDerivWithinAt_ball {g : E → F} {g' : E → E →L[ℝ] F}
    {H α : ℝ≥0} {x : E} {ε M : ℝ} (hH : HolderOnWith H α g' (Metric.ball x ε))
    (hg : ∀ y ∈ Metric.ball x ε, HasFDerivWithinAt g (g' y) (Metric.ball x ε) y)
    (hM : ∀ y ∈ Metric.ball x ε, ‖g y‖ ≤ M) (hε : 0 < ε) :
    ‖g' x‖ ≤ 4 * M / ε + H * ε ^ (α : ℝ) := by
  have hx : x ∈ Metric.ball x ε := Metric.mem_ball_self hε
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  refine ContinuousLinearMap.opNorm_le_of_shell (𝕜 := ℝ) (c := (2 : ℝ)) hε
    (by positivity) (by norm_num) fun w hwlo hwhi => ?_
  rw [Real.norm_two] at hwlo
  have hxw : x + w ∈ Metric.ball x ε := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hwhi
  have hseg := (convex_ball x ε).segment_subset hx hxw
  have hT := hH.norm_apply_le_of_hasFDerivWithinAt hg hseg
  rw [Real.rpow_add' (norm_nonneg w) (by positivity), Real.rpow_one] at hT
  have hpow : ‖w‖ ^ (α : ℝ) ≤ ε ^ (α : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg w) hwhi.le α.coe_nonneg
  have hrem : H * (‖w‖ * ‖w‖ ^ (α : ℝ)) ≤ H * ε ^ (α : ℝ) * ‖w‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hpow
      (mul_nonneg H.coe_nonneg (norm_nonneg w))]
  have herr : 2 * M ≤ (4 * M / ε) * ‖w‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith
  nlinarith [hM (x + w) hxw, hM x hx]

/-- **Derivative comparison on a ball.** If two differentiable functions differ by at most `M`
on a ball of radius `ε`, and their derivatives have Hölder constants `H` and `K` with a common
exponent `α`, their derivatives at the centre differ by at most `4 M / ε + (H + K) ε^α`.
Neither completeness nor a positive exponent is required. -/
theorem norm_fderiv_sub_fderiv_le_of_norm_sub_le_ball {g f : E → F} {H K α : ℝ≥0}
    {x : E} {ε M : ℝ} (hH : HolderOnWith H α (fderiv ℝ g) (Metric.ball x ε))
    (hK : HolderOnWith K α (fderiv ℝ f) (Metric.ball x ε))
    (hg : DifferentiableOn ℝ g (Metric.ball x ε))
    (hf : DifferentiableOn ℝ f (Metric.ball x ε))
    (hM : ∀ y ∈ Metric.ball x ε, ‖g y - f y‖ ≤ M) (hε : 0 < ε) :
    ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ 4 * M / ε + (H + K) * ε ^ (α : ℝ) :=
  (hH.sub hK).norm_le_of_hasFDerivWithinAt_ball
    (fun y hy => (((hg y hy).differentiableAt (Metric.isOpen_ball.mem_nhds hy)).hasFDerivAt.sub
      ((hf y hy).differentiableAt (Metric.isOpen_ball.mem_nhds hy)).hasFDerivAt).hasFDerivWithinAt)
    hM hε

/-- **Interpolation inequality on an interval.** Let `f` have derivative `f'` within `[a, b]`,
with `f'` `β`-Hölder with constant `H` on `[a, b]` and `‖f‖ ≤ M` there. Then for every step
`h > 0` with `2 h ≤ b - a`, the derivative satisfies `‖f' t‖ ≤ 2 M / h + H h^β` on `[a, b]`.
With `β = α / 2` and `h = ε²` this reads `‖f'‖ ≤ 2 ε⁻² M + ε^α H`. -/
theorem norm_le_of_hasDerivWithinAt_Icc {f f' : ℝ → F} {a b : ℝ} {H β : ℝ≥0}
    (hH : HolderOnWith H β f' (Icc a b))
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t) {M : ℝ}
    (hM : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) {h : ℝ} (hh : 0 < h) (hab : 2 * h ≤ b - a) {t : ℝ}
    (ht : t ∈ Icc a b) :
    ‖f' t‖ ≤ 2 * M / h + H * h ^ (β : ℝ) := by
  -- From `t`, a step of length `h` to the right or to the left stays in `[a, b]`.
  obtain ⟨w, hw, hseg⟩ : ∃ w : ℝ, |w| = h ∧ segment ℝ t (t + w) ⊆ Icc a b := by
    rcases le_or_gt (t + h) b with hb | hb
    · refine ⟨h, abs_of_pos hh, ?_⟩
      rw [segment_eq_Icc (by linarith)]
      exact Icc_subset_Icc ht.1 hb
    · refine ⟨-h, by simp [abs_of_pos hh], ?_⟩
      rw [segment_symm, segment_eq_Icc (by linarith)]
      exact Icc_subset_Icc (by linarith) ht.2
  have hH' : HolderOnWith H β (fun s => ContinuousLinearMap.toSpanSingleton ℝ (f' s))
      (Icc a b) := fun x hx y hy => by
    simpa only [← ContinuousLinearMap.toSpanSingletonLIE_apply,
      LinearIsometryEquiv.edist_map] using hH x hx y hy
  have hD := hH'.norm_apply_le_of_hasFDerivWithinAt (fun s hs => (hf s hs).hasFDerivWithinAt)
    hseg
  have hwmem : t + w ∈ Icc a b := hseg (right_mem_segment ℝ t (t + w))
  simp only [ContinuousLinearMap.toSpanSingleton_apply, norm_smul, Real.norm_eq_abs, hw] at hD
  rw [Real.rpow_add' hh.le (by positivity), Real.rpow_one] at hD
  rw [div_add' _ _ _ hh.ne', le_div_iff₀ hh]
  nlinarith [hM t ht, hM (t + w) hwmem]

/-- **Second-order Taylor bound for a Hölder second derivative.** If `g` has derivative `g'`
within `s`, `g'` has derivative `g''` within `s`, and `g''` is `α`-Hölder with constant `H` on
`s`, then for a segment from `x` to `x + w` contained in `s`, the error of the second-order Taylor
polynomial is at most `H ‖w‖^(2 + α)`. -/
theorem norm_image_sub_sub_sub_le_of_hasFDerivWithinAt {s : Set E} {g : E → F}
    {g' : E → E →L[ℝ] F} {g'' : E → E →L[ℝ] E →L[ℝ] F} {H α : ℝ≥0}
    (hH : HolderOnWith H α g'' s) (hg : ∀ y ∈ s, HasFDerivWithinAt g (g' y) s y)
    (hg' : ∀ y ∈ s, HasFDerivWithinAt g' (g'' y) s y) {x w : E}
    (hxw : segment ℝ x (x + w) ⊆ s) :
    ‖g (x + w) - g x - g' x w - (2 : ℝ)⁻¹ • g'' x w w‖ ≤ H * ‖w‖ ^ (2 + (α : ℝ)) := by
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • w ∈ segment ℝ x (x + w) := fun τ hτ => by
    rw [segment_eq_image']
    exact ⟨τ, hτ, by simp⟩
  -- The remainder `ψ τ = g (x + τ w) - τ g' x w - τ² / 2 g'' x w w` has derivative
  -- `(g' (x + τ w) - g' x - g'' x (τ w)) w`, which the first-order bound for `g'` controls.
  set ψ : ℝ → F := fun τ => g (x + τ • w) - τ • g' x w - (τ ^ 2 / 2) • g'' x w w
  have hderiv : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt ψ
      (g' (x + τ • w) w - g' x w - τ • g'' x w w) (Icc 0 1) τ := by
    intro τ hτ
    have hline : HasDerivWithinAt (fun σ : ℝ => x + σ • w) w (Icc 0 1) τ := by
      simpa using (((hasDerivAt_id τ).smul_const w).const_add x).hasDerivWithinAt
    have hgτ := HasFDerivWithinAt.comp_hasDerivWithinAt τ (hg _ (hxw (hmem τ hτ))) hline
      fun σ hσ => hxw (hmem σ hσ)
    have hlin := ((hasDerivAt_id τ).smul_const (g' x w)).hasDerivWithinAt (s := Icc 0 1)
    have hquad := (((hasDerivAt_pow 2 τ).div_const 2).smul_const (g'' x w w)).hasDerivWithinAt
      (s := Icc 0 1)
    convert (hgτ.sub hlin).sub hquad using 1
    · funext σ
      simp [ψ]
    · have h2 : ((2 : ℕ) : ℝ) * τ ^ (2 - 1) / 2 = τ := by norm_num
      rw [h2, one_smul]
  have hbound : ∀ τ ∈ Ico (0 : ℝ) 1,
      ‖g' (x + τ • w) w - g' x w - τ • g'' x w w‖ ≤ H * ‖w‖ ^ (2 + (α : ℝ)) := by
    intro τ hτ
    have hseg : segment ℝ x (x + τ • w) ⊆ s := ((convex_segment x (x + w)).segment_subset
      (left_mem_segment ℝ x (x + w)) (hmem τ (Ico_subset_Icc_self hτ))).trans hxw
    have hT := hH.norm_image_sub_sub_le_of_hasFDerivWithinAt hg' hseg
    have hτw : ‖τ • w‖ ≤ ‖w‖ := by
      rw [norm_smul, Real.norm_of_nonneg hτ.1]
      exact mul_le_of_le_one_left (norm_nonneg w) hτ.2.le
    have heq : g' (x + τ • w) w - g' x w - τ • g'' x w w =
        (g' (x + τ • w) - g' x - g'' x (τ • w)) w := by
      simp
    rw [heq, Real.rpow_add' (norm_nonneg w) (by positivity), Real.rpow_two, ← mul_assoc]
    refine (ContinuousLinearMap.le_opNorm _ w).trans ?_
    calc ‖g' (x + τ • w) - g' x - g'' x (τ • w)‖ * ‖w‖
        ≤ H * ‖τ • w‖ ^ (1 + (α : ℝ)) * ‖w‖ := by gcongr
      _ ≤ H * ‖w‖ ^ (1 + (α : ℝ)) * ‖w‖ := by gcongr
      _ = H * ‖w‖ ^ (2 : ℝ) * ‖w‖ ^ (α : ℝ) := by
        rw [Real.rpow_add' (norm_nonneg w) (by positivity), Real.rpow_one, Real.rpow_two]
        ring
      _ = H * ‖w‖ ^ 2 * ‖w‖ ^ (α : ℝ) := by rw [Real.rpow_two]
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (right_mem_Icc.2 zero_le_one)
  have hψ : ψ 1 - ψ 0 = g (x + w) - g x - g' x w - (2 : ℝ)⁻¹ • g'' x w w := by
    simp only [ψ, one_smul, zero_smul, add_zero]
    module
  rw [← hψ]
  simpa using hmv

/-- **Interpolation of the first derivative on a ball.** If `g` has derivative `g'` within `s`,
`g'` has derivative `g''` within `s`, `g''` is `α`-Hölder with constant `H` on `s` and `‖g‖ ≤ M`
on `s`, then `‖g' x‖ ≤ M / ε + H ε^(1 + α)` at every centre `x` of a closed ball of radius
`ε > 0` contained in `s`. The symmetric difference `g (x + w) - g (x - w)` approximates `2 g' x w`
up to `2 H ‖w‖^(2 + α)`, since the second-order terms cancel. -/
theorem norm_le_of_hasFDerivWithinAt_of_closedBall_subset {s : Set E} {g : E → F}
    {g' : E → E →L[ℝ] F} {g'' : E → E →L[ℝ] E →L[ℝ] F} {H α : ℝ≥0}
    (hH : HolderOnWith H α g'' s) (hg : ∀ y ∈ s, HasFDerivWithinAt g (g' y) s y)
    (hg' : ∀ y ∈ s, HasFDerivWithinAt g' (g'' y) s y) {M : ℝ} (hM : ∀ y ∈ s, ‖g y‖ ≤ M)
    {x : E} {ε : ℝ} (hε : 0 < ε) (hxs : Metric.closedBall x ε ⊆ s) :
    ‖g' x‖ ≤ M / ε + H * ε ^ (1 + (α : ℝ)) := by
  have hx : x ∈ s := hxs (Metric.mem_closedBall_self hε.le)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv => ?_
  -- Test `g' x` in the direction `w = ε v` and in the opposite direction.
  set w := ε • v
  have hw : ‖w‖ = ε := by rw [norm_smul, hv, mul_one, Real.norm_of_nonneg hε.le]
  have hseg : ∀ u : E, ‖u‖ = ε → segment ℝ x (x + u) ⊆ s := fun u hu =>
    ((convex_closedBall x ε).segment_subset (Metric.mem_closedBall_self hε.le)
      (by simp [hu])).trans hxs
  have hp := hH.norm_image_sub_sub_sub_le_of_hasFDerivWithinAt hg hg' (hseg w hw)
  have hm := hH.norm_image_sub_sub_sub_le_of_hasFDerivWithinAt hg hg' (hseg (-w) (by simp [hw]))
  rw [hw] at hp
  rw [norm_neg, hw] at hm
  have hdiff : (2 : ℝ) • g' x w = (g (x + w) - g (x + -w)) -
      ((g (x + w) - g x - g' x w - (2 : ℝ)⁻¹ • g'' x w w) -
        (g (x + -w) - g x - g' x (-w) - (2 : ℝ)⁻¹ • g'' x (-w) (-w))) := by
    simp only [map_neg, neg_apply, neg_neg]
    module
  have hMp := hM _ (hseg w hw (right_mem_segment ℝ _ _))
  have hMm := hM _ (hseg (-w) (by simp [hw]) (right_mem_segment ℝ _ _))
  have h2 : 2 * ‖g' x w‖ ≤ 2 * M + 2 * (H * ε ^ (2 + (α : ℝ))) := by
    have := congrArg norm hdiff
    rw [norm_smul, Real.norm_two] at this
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    have h₁ := norm_sub_le (g (x + w)) (g (x + -w))
    have h₂ := norm_sub_le (g (x + w) - g x - g' x w - (2 : ℝ)⁻¹ • g'' x w w)
      (g (x + -w) - g x - g' x (-w) - (2 : ℝ)⁻¹ • g'' x (-w) (-w))
    linarith
  have hgw : ‖g' x w‖ = ε * ‖g' x v‖ := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
  rw [hgw] at h2
  rw [Real.rpow_add' hε.le (by positivity), Real.rpow_one, div_add' _ _ _ hε.ne', le_div_iff₀ hε]
  rw [Real.rpow_add' hε.le (by positivity), Real.rpow_two, sq] at h2
  have hre : (H : ℝ) * (ε * ε ^ (α : ℝ)) * ε = H * (ε * ε * ε ^ (α : ℝ)) := by ring
  linarith

/-- **Interpolation of the second derivative on a ball.** If `g` has derivative `g'` within `s`,
`g'` has derivative `g''` within `s`, `g''` is `α`-Hölder with constant `H` on `s` and `‖g‖ ≤ M`
on `s`, then `‖g'' x‖ ≤ 2 M / ε² + 3 H ε^α` at every centre `x` of a closed ball of radius
`2 ε > 0` contained in `s`. Only `g` and the Hölder constant of `g''` enter, so this is the local
form of the interpolation inequality used to absorb lower-order terms in interior estimates. -/
theorem norm_le_of_hasFDerivWithinAt_of_closedBall_two_mul_subset {s : Set E} {g : E → F}
    {g' : E → E →L[ℝ] F} {g'' : E → E →L[ℝ] E →L[ℝ] F} {H α : ℝ≥0}
    (hH : HolderOnWith H α g'' s) (hg : ∀ y ∈ s, HasFDerivWithinAt g (g' y) s y)
    (hg' : ∀ y ∈ s, HasFDerivWithinAt g' (g'' y) s y) {M : ℝ} (hM : ∀ y ∈ s, ‖g y‖ ≤ M)
    {x : E} {ε : ℝ} (hε : 0 < ε) (hxs : Metric.closedBall x (2 * ε) ⊆ s) :
    ‖g'' x‖ ≤ 2 * M / ε ^ 2 + 3 * H * ε ^ (α : ℝ) := by
  have hx : x ∈ s := hxs (Metric.mem_closedBall_self (by positivity))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  -- The first derivative is bounded at every point whose `ε`-ball lies in `s`.
  have h1 : ∀ y, dist y x ≤ ε → ‖g' y‖ ≤ M / ε + H * ε ^ (1 + (α : ℝ)) := fun y hy =>
    hH.norm_le_of_hasFDerivWithinAt_of_closedBall_subset hg hg' hM hε fun z hz =>
      hxs (by
        rw [Metric.mem_closedBall] at hz ⊢
        linarith [dist_triangle z y x])
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv => ?_
  set w := ε • v
  have hw : ‖w‖ = ε := by rw [norm_smul, hv, mul_one, Real.norm_of_nonneg hε.le]
  have hseg : segment ℝ x (x + w) ⊆ s :=
    ((convex_closedBall x (2 * ε)).segment_subset (Metric.mem_closedBall_self (by positivity))
      (by rw [Metric.mem_closedBall, dist_self_add_left, hw]; linarith)).trans hxs
  have hD := hH.norm_apply_le_of_hasFDerivWithinAt hg' hseg
  rw [hw, map_smul, norm_smul, Real.norm_of_nonneg hε.le] at hD
  have hxw := h1 (x + w) (by simp [hw])
  have hxx := h1 x (by simp [hε.le])
  rw [Real.rpow_add' hε.le (by positivity), Real.rpow_one] at hD hxw hxx
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  have hεα : 0 ≤ (H : ℝ) * ε ^ (α : ℝ) := by positivity
  have key : ε * ‖g'' x v‖ ≤ 2 * (M / ε) + 3 * (H * (ε * ε ^ (α : ℝ))) := by linarith
  have key' : ε * (ε * ‖g'' x v‖) ≤ ε * (2 * (M / ε) + 3 * (H * (ε * ε ^ (α : ℝ)))) :=
    mul_le_mul_of_nonneg_left key hε.le
  have hMε : ε * (M / ε) = M := mul_div_cancel₀ M hε.ne'
  nlinarith

/-- For `u` of class `C²` on an open set `U ⊇ s`, the first and second Fréchet derivatives are
derivatives within `s`. -/
private theorem hasFDerivWithinAt_fderiv_and_fderiv_fderiv {U s : Set E} {u : E → F}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hsU : s ⊆ U) :
    (∀ y ∈ s, HasFDerivWithinAt u (fderiv ℝ u y) s y) ∧
      (∀ y ∈ s, HasFDerivWithinAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) y) s y) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · exact ((hu.contDiffAt (hU.mem_nhds (hsU hy))).differentiableAt (by norm_num)).hasFDerivAt
      |>.hasFDerivWithinAt
  · exact (((hu.contDiffAt (hU.mem_nhds (hsU hy))).fderiv_right (m := 1)
      (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt

/-- **Interpolation of the gradient of a `C²` function on a ball.** Let `u` be `C²` on an open set
`U ⊇ s`, with `D²u` `α`-Hölder with constant `H` on `s` and `‖u‖ ≤ M` on `s`. Then
`‖Du(x)‖ ≤ M / ε + H ε^(1 + α)` at every centre `x` of a closed ball of radius `ε > 0` in `s`. -/
theorem norm_fderiv_le_of_contDiffOn {U s : Set E} {u : E → F} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hsU : s ⊆ U) {H α : ℝ≥0}
    (hH : HolderOnWith H α (iteratedFDeriv ℝ 2 u) s) {M : ℝ} (hM : ∀ y ∈ s, ‖u y‖ ≤ M)
    {x : E} {ε : ℝ} (hε : 0 < ε) (hxs : Metric.closedBall x ε ⊆ s) :
    ‖fderiv ℝ u x‖ ≤ M / ε + H * ε ^ (1 + (α : ℝ)) := by
  obtain ⟨hd1, hd2⟩ := hasFDerivWithinAt_fderiv_and_fderiv_fderiv hU hu hsU
  have hH' := (TauCeti.holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two u).2 hH
  exact hH'.norm_le_of_hasFDerivWithinAt_of_closedBall_subset hd1 hd2 hM hε hxs

/-- **Interpolation of the Hessian of a `C²` function on a ball.** Let `u` be `C²` on an open set
`U ⊇ s`, with `D²u` `α`-Hölder with constant `H` on `s` and `‖u‖ ≤ M` on `s`. Then
`‖D²u(x)‖ ≤ 2 M / ε² + 3 H ε^α` at every centre `x` of a closed ball of radius `2 ε > 0` in
`s`. -/
theorem norm_iteratedFDeriv_two_le_of_contDiffOn {U s : Set E} {u : E → F} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hsU : s ⊆ U) {H α : ℝ≥0}
    (hH : HolderOnWith H α (iteratedFDeriv ℝ 2 u) s) {M : ℝ} (hM : ∀ y ∈ s, ‖u y‖ ≤ M)
    {x : E} {ε : ℝ} (hε : 0 < ε) (hxs : Metric.closedBall x (2 * ε) ⊆ s) :
    ‖iteratedFDeriv ℝ 2 u x‖ ≤ 2 * M / ε ^ 2 + 3 * H * ε ^ (α : ℝ) := by
  obtain ⟨hd1, hd2⟩ := hasFDerivWithinAt_fderiv_and_fderiv_fderiv hU hu hsU
  have hH' := (TauCeti.holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two u).2 hH
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  exact hH'.norm_le_of_hasFDerivWithinAt_of_closedBall_two_mul_subset hd1 hd2 hM hε hxs

end HolderOnWith

namespace HolderWith

/-- **Interpolation inequality.** If `g` has derivative `g'` everywhere, `‖g‖ ≤ M`, and `g'` is
globally `α`-Hölder with constant `H`, then `‖g' x‖ ≤ 2 M / ε + H ε^α` for every `ε > 0`. With
`α = 1` this is the Landau-type inequality `‖g' x‖ ≤ 2 M / ε + L ε` for a derivative that is
Lipschitz with constant `L`. -/
theorem norm_le_of_hasFDerivAt {g : E → F} {g' : E → E →L[ℝ] F} {H α : ℝ≥0}
    (hH : HolderWith H α g') (hg : ∀ y, HasFDerivAt g (g' y) y) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖g' x‖ ≤ 2 * M / ε + H * ε ^ (α : ℝ) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  -- Test the derivative in the direction `v` with a step of length `ε`.
  set c := ε / ‖v‖ with hc_def
  have hc : 0 < c := div_pos hε hv'
  have hcv : ‖c • v‖ = ε := by
    rw [norm_smul, Real.norm_of_nonneg hc.le, hc_def, div_mul_cancel₀ _ hv'.ne']
  have hD := (hH.holderOnWith univ).norm_apply_le_of_hasFDerivWithinAt
    (fun y _ => (hg y).hasFDerivWithinAt) (subset_univ _) (x := x) (w := c • v)
  rw [map_smul, norm_smul, Real.norm_of_nonneg hc.le, hcv,
    Real.rpow_add' hε.le (by positivity), Real.rpow_one] at hD
  have hrhs : (2 * M / ε + H * ε ^ (α : ℝ)) * ‖v‖ =
      (2 * M + H * (ε * ε ^ (α : ℝ))) / c := by
    rw [hc_def]
    field_simp
  rw [hrhs, le_div_iff₀ hc, mul_comm]
  linarith [hM (x + c • v), hM x]

/-- **Interpolation inequality.** If `g` is differentiable with `‖g‖ ≤ M` and its derivative is
globally `α`-Hölder with constant `H`, then `‖fderiv ℝ g x‖ ≤ 2 M / ε + H ε^α` for every
`ε > 0`. -/
theorem norm_fderiv_le_of_norm_le {g : E → F} {H α : ℝ≥0} (hH : HolderWith H α (fderiv ℝ g))
    (hg : Differentiable ℝ g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ g x‖ ≤ 2 * M / ε + H * ε ^ (α : ℝ) :=
  hH.norm_le_of_hasFDerivAt (fun y => (hg y).hasFDerivAt) hM hε x

/-- **Interpolation inequality for iterated derivatives.** If `‖D^k f‖ ≤ M` and `D^(k+1) f` is
globally `α`-Hölder with constant `H`, then `‖D^(k+1) f x‖ ≤ 2 M / ε + H ε^α` for every
`ε > 0`. -/
theorem norm_iteratedFDeriv_succ_le_of_norm_le {f : E → F} {k : ℕ} {H α : ℝ≥0}
    (hH : HolderWith H α (iteratedFDeriv ℝ (k + 1) f))
    (hf : Differentiable ℝ (iteratedFDeriv ℝ k f)) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M) {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ 2 * M / ε + H * ε ^ (α : ℝ) := by
  have hH' : HolderWith H α (fderiv ℝ (iteratedFDeriv ℝ k f)) := fun y z => by
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      LinearIsometryEquiv.edist_map] using hH y z
  rw [← norm_fderiv_iteratedFDeriv]
  exact hH'.norm_fderiv_le_of_norm_le hf hM hε x

end HolderWith

namespace ContDiff

/-- **Landau-type interpolation inequality.** If `f` is `C^(k+2)` with `‖D^k f‖ ≤ M₀` and
`‖D^(k+2) f‖ ≤ M₂`, then `‖D^(k+1) f x‖ ≤ 2 M₀ / ε + M₂ ε` for every `ε > 0`. -/
theorem norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_le {f : E → F} {k : ℕ}
    (hf : ContDiff ℝ (k + 2) f) {M₀ M₂ : ℝ} (hM₀ : ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M₀)
    (hM₂ : ∀ y, ‖iteratedFDeriv ℝ (k + 2) f y‖ ≤ M₂) {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ 2 * M₀ / ε + M₂ * ε := by
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ x)
  have hlip : LipschitzWith M₂.toNNReal (iteratedFDeriv ℝ (k + 1) f) := by
    refine lipschitzWith_of_nnnorm_fderiv_le
      (hf.differentiable_iteratedFDeriv (by norm_cast; omega)) fun y => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, norm_fderiv_iteratedFDeriv, Real.coe_toNNReal _ hM₂0]
    exact hM₂ y
  have h := (holderWith_one.2 hlip).norm_iteratedFDeriv_succ_le_of_norm_le
    (hf.differentiable_iteratedFDeriv (by norm_cast; omega)) hM₀ hε x
  simpa [Real.coe_toNNReal _ hM₂0] using h

end ContDiff

namespace HolderWith

/-- The supremum of `‖D^(k+2) f‖` satisfies the absorbed interpolation bound. -/
private theorem iSup_norm_iteratedFDeriv_add_two_le {f : E → F} {k : ℕ} {H α : ℝ≥0}
    (hH : HolderWith H α (iteratedFDeriv ℝ (k + 2) f)) (hf : ContDiff ℝ (k + 2) f) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M)
    (hbdd : BddAbove (range fun y => ‖iteratedFDeriv ℝ (k + 2) f y‖)) {ε : ℝ} (hε : 0 < ε) :
    ⨆ y, ‖iteratedFDeriv ℝ (k + 2) f y‖ ≤ 32 * M / ε ^ 2 + 2 * H * ε ^ (α : ℝ) := by
  set S := ⨆ y, ‖iteratedFDeriv ℝ (k + 2) f y‖
  have hS : ∀ y, ‖iteratedFDeriv ℝ (k + 2) f y‖ ≤ S := fun y => le_ciSup hbdd y
  -- The Landau inequality at scale `ε / 4` bounds `D^(k+1) f` in terms of `M` and `S`.
  have h₁ : ∀ y, ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ 2 * M / (ε / 4) + S * (ε / 4) :=
    hf.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_le hM hS (by positivity)
  -- The Hölder interpolation at scale `ε` then bounds `D^(k+2) f` by `S / 2` plus the rest.
  have h₂ : ∀ y, ‖iteratedFDeriv ℝ (k + 2) f y‖ ≤
      2 * (2 * M / (ε / 4) + S * (ε / 4)) / ε + H * ε ^ (α : ℝ) :=
    hH.norm_iteratedFDeriv_succ_le_of_norm_le
      (hf.differentiable_iteratedFDeriv (by norm_cast; omega)) h₁ hε
  have heq : 2 * (2 * M / (ε / 4) + S * (ε / 4)) / ε + H * ε ^ (α : ℝ) =
      16 * M / ε ^ 2 + S / 2 + H * ε ^ (α : ℝ) := by
    field_simp
    ring
  have hle : S ≤ 16 * M / ε ^ 2 + S / 2 + H * ε ^ (α : ℝ) :=
    ciSup_le fun y => (h₂ y).trans_eq heq
  have h32 : 32 * M / ε ^ 2 = 2 * (16 * M / ε ^ 2) := by ring
  rw [h32]
  linarith

/-- **Absorbed interpolation inequality for the top derivative.** If `f` is `C^(k+2)` with
`‖D^k f‖ ≤ M`, `D^(k+2) f` is bounded and globally `α`-Hölder with constant `H`, then
`‖D^(k+2) f x‖ ≤ 32 M / ε² + 2 H ε^α` for every `ε > 0`. -/
theorem norm_iteratedFDeriv_add_two_le_of_norm_le {f : E → F} {k : ℕ} {H α : ℝ≥0}
    (hH : HolderWith H α (iteratedFDeriv ℝ (k + 2) f)) (hf : ContDiff ℝ (k + 2) f) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M)
    (hbdd : BddAbove (range fun y => ‖iteratedFDeriv ℝ (k + 2) f y‖)) {ε : ℝ} (hε : 0 < ε)
    (x : E) :
    ‖iteratedFDeriv ℝ (k + 2) f x‖ ≤ 32 * M / ε ^ 2 + 2 * H * ε ^ (α : ℝ) :=
  (le_ciSup hbdd x).trans (hH.iSup_norm_iteratedFDeriv_add_two_le hf hM hbdd hε)

/-- **Absorbed interpolation inequality for the intermediate derivative.** If `f` is `C^(k+2)`
with `‖D^k f‖ ≤ M`, `D^(k+2) f` is bounded and globally `α`-Hölder with constant `H`, then
`‖D^(k+1) f x‖ ≤ 34 M / ε + 2 H ε^(1 + α)` for every `ε > 0`. -/
theorem norm_iteratedFDeriv_succ_le_of_norm_le_of_bddAbove {f : E → F} {k : ℕ} {H α : ℝ≥0}
    (hH : HolderWith H α (iteratedFDeriv ℝ (k + 2) f)) (hf : ContDiff ℝ (k + 2) f) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M)
    (hbdd : BddAbove (range fun y => ‖iteratedFDeriv ℝ (k + 2) f y‖)) {ε : ℝ} (hε : 0 < ε)
    (x : E) :
    ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ 34 * M / ε + 2 * H * ε ^ (1 + (α : ℝ)) := by
  have hS := hH.iSup_norm_iteratedFDeriv_add_two_le hf hM hbdd hε
  have h := hf.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_le hM
    (fun y => le_ciSup hbdd y) hε x
  have heq : 2 * M / ε + (32 * M / ε ^ 2 + 2 * H * ε ^ (α : ℝ)) * ε =
      34 * M / ε + 2 * H * ε ^ (1 + (α : ℝ)) := by
    rw [Real.rpow_add' hε.le (by positivity), Real.rpow_one]
    field_simp
    ring
  calc ‖iteratedFDeriv ℝ (k + 1) f x‖
      ≤ 2 * M / ε + (⨆ y, ‖iteratedFDeriv ℝ (k + 2) f y‖) * ε := h
    _ ≤ 2 * M / ε + (32 * M / ε ^ 2 + 2 * H * ε ^ (α : ℝ)) * ε := by gcongr
    _ = 34 * M / ε + 2 * H * ε ^ (1 + (α : ℝ)) := heq

/-- **Absorbed interpolation inequalities with one constant.** If `f` is `C^(k+2)` with
`‖D^k f‖ ≤ M`, `D^(k+2) f` is bounded and globally `α`-Hölder with constant `H`, then for every
scale `0 < ε ≤ 1` both `‖D^(k+1) f x‖` and `‖D^(k+2) f x‖` are at most
`(34 / ε + 32 / ε²) M + 2 H ε^α`. -/
theorem norm_iteratedFDeriv_succ_le_and_norm_iteratedFDeriv_add_two_le {f : E → F} {k : ℕ}
    {H α : ℝ≥0} (hH : HolderWith H α (iteratedFDeriv ℝ (k + 2) f)) (hf : ContDiff ℝ (k + 2) f)
    {M : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M)
    (hbdd : BddAbove (range fun y => ‖iteratedFDeriv ℝ (k + 2) f y‖)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x : E) :
    ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ (34 / ε + 32 / ε ^ 2) * M + 2 * H * ε ^ (α : ℝ) ∧
      ‖iteratedFDeriv ℝ (k + 2) f x‖ ≤ (34 / ε + 32 / ε ^ 2) * M + 2 * H * ε ^ (α : ℝ) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h34 : 0 ≤ 34 * M / ε := by positivity
  have h32 : 0 ≤ 32 * M / ε ^ 2 := by positivity
  have hc : (34 / ε + 32 / ε ^ 2) * M = 34 * M / ε + 32 * M / ε ^ 2 := by ring
  have hεα : ε ^ (1 + (α : ℝ)) ≤ ε ^ (α : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have h1 := hH.norm_iteratedFDeriv_succ_le_of_norm_le_of_bddAbove hf hM hbdd hε x
  have h2 := hH.norm_iteratedFDeriv_add_two_le_of_norm_le hf hM hbdd hε x
  rw [hc]
  constructor
  · nlinarith [H.coe_nonneg]
  · linarith

end HolderWith

namespace TauCeti

/-- **Temporal Hölder continuity of the spatial derivative.** Let `u (x, t)` be twice
differentiable in `x ∈ E` and differentiable in `t ∈ [a, b]` within `[a, b]`, with spatial
derivatives `u'`, `u''` and time derivative `uₜ`. If the Hessian `u'' (x, ·)` is `α / 2`-Hölder in
time with constant `C₂` and the time derivative `uₜ (·, t)` is `α`-Hölder in space with constant
`Cₜ`, then the gradient `u' (x, ·)` is `(1 + α) / 2`-Hölder in time with constant `C₂ + Cₜ`.

This controls the temporal `(1 + α) / 2` seminorm of the spatial gradient, which appears in the
norm of the parabolic Hölder space `C^{2+α, 1+α/2}`, by the parabolic seminorms of the Hessian
and of the time derivative. -/
theorem holderOnWith_Icc_of_hasFDerivAt_of_hasDerivWithinAt {u : E → ℝ → F}
    {u' : E → ℝ → E →L[ℝ] F} {u'' : E → ℝ → E →L[ℝ] E →L[ℝ] F} {uₜ : E → ℝ → F}
    {a b : ℝ} {C₂ Cₜ α : ℝ≥0}
    (hu' : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (u · t) (u' y t) y)
    (hu'' : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (u' · t) (u'' y t) y)
    (huₜ : ∀ y, ∀ t ∈ Icc a b, HasDerivWithinAt (u y) (uₜ y t) (Icc a b) t)
    (hC₂ : ∀ y, HolderOnWith C₂ (α / 2) (u'' y) (Icc a b))
    (hCₜ : ∀ t ∈ Icc a b, HolderWith Cₜ α (uₜ · t)) (x : E) :
    HolderOnWith (C₂ + Cₜ) ((1 + α) / 2) (u' x) (Icc a b) := by
  refine HolderOnWith.of_dist_le fun t ht s hs => ?_
  rw [dist_eq_norm, Real.dist_eq]
  rcases eq_or_ne t s with rfl | hts
  · simp only [sub_self, norm_zero, abs_zero]
    positivity
  -- Work at the spatial scale `h = √|t - s|`.
  obtain ⟨h, h_def⟩ : ∃ h, h = √|t - s| := ⟨_, rfl⟩
  have hh : 0 < h := h_def ▸ Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.2 hts))
  have hsq : h ^ 2 = |t - s| := h_def ▸ Real.sq_sqrt (abs_nonneg _)
  have hrpow : ∀ r : ℝ, |t - s| ^ (r / 2) = h ^ r := fun r => by
    simpa only [h_def] using Real.rpow_div_two_eq_sqrt r (abs_nonneg (t - s))
  -- At the times `t` and `s` the Hessians differ by at most `K = C₂ h^α` everywhere in space, so
  -- the difference of the gradients is `K`-Lipschitz in space.
  obtain ⟨K, hKcoe⟩ : ∃ K : ℝ≥0, (K : ℝ) = C₂ * h ^ (α : ℝ) :=
    ⟨_, Real.coe_toNNReal _ (by positivity)⟩
  have hK : ∀ y, ‖u'' y t - u'' y s‖ ≤ K := fun y => by
    have := (hC₂ y).dist_le ht hs
    rwa [dist_eq_norm, Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat, hrpow, ← hKcoe] at this
  have hlip : HolderOnWith K 1 (fun y => u' y t - u' y s) univ :=
    HolderOnWith.of_dist_le fun y _ z _ => by
      rw [NNReal.coe_one, Real.rpow_one, dist_eq_norm, dist_eq_norm]
      exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y _ => ((hu'' t ht y).sub (hu'' s hs y)).hasFDerivWithinAt) (fun y _ => hK y)
        convex_univ (mem_univ z) (mem_univ y)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv => ?_
  -- Test the difference `u (·, t) - u (·, s)` on the step `w = h v` of length `h`. Its linear
  -- approximation error is at most `K h²` by the Taylor bound.
  set w := h • v with hw_def
  have hw : ‖w‖ = h := by rw [hw_def, norm_smul, hv, Real.norm_of_nonneg hh.le, mul_one]
  have hT := hlip.norm_image_sub_sub_le_of_hasFDerivWithinAt
    (fun y _ => ((hu' t ht y).sub (hu' s hs y)).hasFDerivWithinAt) (subset_univ _) (x := x)
    (w := w)
  simp only [Pi.sub_apply, NNReal.coe_one, show (1 : ℝ) + 1 = 2 by norm_num,
    Real.rpow_two] at hT
  -- Its increment from `x` to `x + w` is, by the mean value inequality in time, at most
  -- `Cₜ h^α |t - s|`.
  have hincr : ‖(u (x + w) t - u x t) - (u (x + w) s - u x s)‖ ≤
      Cₜ * ‖w‖ ^ (α : ℝ) * ‖t - s‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun τ hτ => (huₜ (x + w) τ hτ).sub (huₜ x τ hτ))
      (fun τ hτ => by simpa [dist_eq_norm] using (hCₜ τ hτ).dist_le (x + w) x)
      (convex_Icc a b) hs ht
  have key : h * ‖(u' x t - u' x s) v‖ ≤ (C₂ + Cₜ) * h ^ (α : ℝ) * h ^ 2 := by
    have hsplit : (u' x t - u' x s) w = ((u (x + w) t - u x t) - (u (x + w) s - u x s)) -
        ((u (x + w) t - u (x + w) s) - (u x t - u x s) - (u' x t - u' x s) w) := by abel
    have happ : (u' x t - u' x s) w = h • (u' x t - u' x s) v := by rw [hw_def, map_smul]
    have hle := norm_sub_le_of_le hincr hT
    rw [← hsplit, happ, norm_smul, Real.norm_of_nonneg hh.le, Real.norm_eq_abs, ← hsq, hw,
      hKcoe] at hle
    linarith
  -- Divide by `h`, using `h^(1 + α) = |t - s|^((1 + α) / 2)`.
  have hexp : (((1 + α) / 2 : ℝ≥0) : ℝ) = (1 + α) / 2 := by push_cast; ring
  rw [hexp, hrpow, Real.rpow_add hh, Real.rpow_one]
  refine le_of_mul_le_mul_left (key.trans_eq ?_) hh
  push_cast
  ring

end TauCeti
