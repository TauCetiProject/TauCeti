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

On a closed interval `[a, b]` the same argument applies to one-sided derivatives within
`[a, b]`, for steps `h` with `2 h ≤ b - a`, since from each point of `[a, b]` a step of length `h`
in one of the two directions stays in the interval. With temporal Hölder exponent `α / 2` and
`h = ε²`, this is the estimate for time derivatives on a slab used in parabolic Hölder spaces.

## Main declarations

* `HolderOnWith.norm_image_sub_sub_le_of_hasFDerivWithinAt`: the first-order Taylor bound for a
  Hölder derivative.
* `HolderOnWith.norm_apply_le_of_hasFDerivWithinAt`: the resulting bound on a directional
  derivative.
* `HolderWith.norm_fderiv_le_of_norm_le` and `HolderWith.norm_iteratedFDeriv_succ_le_of_norm_le`:
  the interpolation inequality on the whole space.
* `ContDiff.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_le`: the Landau-type inequality.
* `HolderWith.norm_iteratedFDeriv_add_two_le_of_norm_le` and
  `HolderWith.norm_iteratedFDeriv_succ_le_of_norm_le_of_bddAbove`: the absorbed bounds on the two
  derivatives above `D^k f`.
* `HolderOnWith.norm_le_of_hasDerivWithinAt_Icc`: the interpolation inequality for derivatives
  within a closed interval.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.8 (interpolation inequalities).
* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Chapter 0.
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

end HolderOnWith

namespace HolderWith

/-- **Interpolation inequality.** If `g` is differentiable with `‖g‖ ≤ M` and its derivative is
globally `α`-Hölder with constant `H`, then `‖fderiv ℝ g x‖ ≤ 2 M / ε + H ε^α` for every
`ε > 0`. -/
theorem norm_fderiv_le_of_norm_le {g : E → F} {H α : ℝ≥0} (hH : HolderWith H α (fderiv ℝ g))
    (hg : Differentiable ℝ g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ g x‖ ≤ 2 * M / ε + H * ε ^ (α : ℝ) := by
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
    (fun y _ => (hg y).hasFDerivAt.hasFDerivWithinAt) (subset_univ _) (x := x) (w := c • v)
  rw [map_smul, norm_smul, Real.norm_of_nonneg hc.le, hcv,
    Real.rpow_add' hε.le (by positivity), Real.rpow_one] at hD
  have hrhs : (2 * M / ε + H * ε ^ (α : ℝ)) * ‖v‖ =
      (2 * M + H * (ε * ε ^ (α : ℝ))) / c := by
    rw [hc_def]
    field_simp
  rw [hrhs, le_div_iff₀ hc, mul_comm]
  linarith [hM (x + c • v), hM x]

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

end HolderWith
