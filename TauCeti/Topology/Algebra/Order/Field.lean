/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import TauCeti.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.DenselyOrdered

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Ratios, reciprocals of vanishing powers, and one-sided bounds in ordered fields

Mathlib's `Mathlib/Topology/Algebra/Order/Field.lean` proves
`tendsto_bdd_div_atTop_nhds_zero`: a numerator confined to a fixed interval, divided by a
denominator that diverges to `atTop`, tends to `0`. This file records the companion statement
for a numerator that is *not* bounded but instead tracks the denominator: if `f` agrees with `g`
up to a two-sided additive bounded error and `g` diverges, then `f / g` tends to `1`.

It also records that the reciprocal of a positive power of `x - a` diverges to `atTop` as `x`
tends to `a` from the right, and likewise for `a - x` from the left. These are the one-sided
blow-ups of `tendsto_inv_nhdsGT_zero` along a vanishing power. Finally, it records the
one-sided bound `x ^ 2 < 1` for `x` sufficiently close to `1` from below.

Comparisons whose linear weights share a parameter tending to negative infinity lose those
weights in the limit. One-sided continuity carries the resulting inequalities to any right
endpoint. These are ordered-field facts; no differential inequality is assumed.

## Main results

* `TauCeti.tendsto_add_div_add_atTop`: ratios of translates converge to one.
* `TauCeti.le_of_eventually_mul_sub_le`: remove common diverging linear weights.
* `TauCeti.le_of_eventually_mul_sub_le_nhdsLT`,
  `TauCeti.le_of_eventually_le_add_div_nhdsLT`: one-sided endpoint comparisons.
* `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le` — if `g` tends to `atTop`
  along `l` and,
  eventually along `l`, `g - C₂ ≤ f ≤ g + C₁` for constants `C₁` and `C₂`, then `f / g` tends
  to `1`. No property of the denominator beyond divergence is used: the additive error washes
  out because `g` blows up.
* `TauCeti.tendsto_inv_pow_sub_nhdsGT`, `TauCeti.tendsto_inv_pow_sub_nhdsLT` — for `k ≠ 0`,
  `((x - a) ^ k)⁻¹` tends to `atTop` as `x` tends to `a` from the right, and `((a - x) ^ k)⁻¹`
  tends to `atTop` as `x` tends to `a` from the left.

* `TauCeti.eventually_sq_lt_one_nhdsLT_one` — eventually `x ^ 2 < 1` along `𝓝[<] 1`.

## Implementation notes

The two error bounds are taken as separate `∃ C, ∀ᶠ …` hypotheses rather than as a single
bound on `|f - g|`, because a caller that derives the two inequalities from different estimates
arrives holding them in that shape and would otherwise have to recombine them.

## References

Adapted from `tendsto_ratio_one_of_div_atTop_pm_bounded` in
`CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source states it
over `ℝ`; the statement here is over an arbitrary linearly ordered topological field.
-/

public section

namespace TauCeti

open Filter Topology

/-- A ratio whose denominator diverges and whose numerator tracks it up to a two-sided additive
bounded error tends to `1`. Contrast `tendsto_bdd_div_atTop_nhds_zero`, whose numerator is confined
to a fixed interval and whose ratio tends to `0`. -/
theorem tendsto_div_nhds_one_of_le_add_const_of_sub_const_le {𝕜 α : Type*} [Field 𝕜]
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    {l : Filter α} {g f : α → 𝕜}
    (hg : Tendsto g l atTop) (h_le : ∃ C : 𝕜, ∀ᶠ s in l, f s ≤ g s + C)
    (h_lower : ∃ C : 𝕜, ∀ᶠ s in l, g s - C ≤ f s) : Tendsto (fun s ↦ f s / g s) l (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hlower⟩ := h_lower
  -- the additive error washes out under division because the denominator blows up
  have h0 : Tendsto (fun s ↦ (f s - g s) / g s) l (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hg
  exact (add_zero (1 : 𝕜) ▸ h0.const_add 1).congr' <|
    (hg.eventually_gt_atTop 0).mono fun s h ↦ by grind

/-- The square is strictly less than one sufficiently close to one from below. -/
theorem eventually_sq_lt_one_nhdsLT_one {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] :
    ∀ᶠ x : 𝕜 in 𝓝[<] 1, x ^ 2 < 1 := by
  filter_upwards [Ioo_mem_nhdsLT (by simp : (-1 : 𝕜) < 1)] with x hx
  nlinarith [hx.1, hx.2]

section InvPow

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] {a : 𝕜}

/-- The reciprocal of `(x - a) ^ k`, for `k ≠ 0`, tends to `+∞` from the right of `a`. -/
theorem tendsto_inv_pow_sub_nhdsGT {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun x ↦ ((x - a) ^ k)⁻¹) (𝓝[>] a) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · exact (Continuous.tendsto' (f := fun x : 𝕜 ↦ (x - a) ^ k) (by fun_prop) a 0
      (by simp [zero_pow hk])).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_pos (sub_pos.2 hx) k

/-- The reciprocal of `(a - x) ^ k`, for `k ≠ 0`, tends to `+∞` from the left of `a`. -/
theorem tendsto_inv_pow_sub_nhdsLT {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun x ↦ ((a - x) ^ k)⁻¹) (𝓝[<] a) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · exact (Continuous.tendsto' (f := fun x : 𝕜 ↦ (a - x) ^ k) (by fun_prop) a 0
      (by simp [zero_pow hk])).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_pos (sub_pos.2 hx) k

end InvPow

/-- In an ordered field, the ratio `(t + x) / (t + y)` of two translates of `t` tends to `1` as
`t → ∞`. -/
theorem tendsto_add_div_add_atTop {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] (x y : 𝕜) :
    Tendsto (fun t : 𝕜 ↦ (t + x) / (t + y)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := x - y)).div_atTop
    (tendsto_atTop_add_const_right atTop y tendsto_id)
  refine (add_zero (1 : 𝕜) ▸ h.const_add 1).congr' ?_
  filter_upwards [eventually_gt_atTop (-y)] with t ht
  have : t + y ≠ 0 := by linarith
  simp only [id]
  field_simp
  ring


section Comparisons

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/-- A constant divided by `t - T` tends to zero as `T` tends to negative infinity. -/
theorem tendsto_div_sub_atBot (t R : 𝕜) :
    Tendsto (fun T : 𝕜 ↦ R / (t - T)) atBot (𝓝 0) := by
  apply Filter.Tendsto.const_div_atTop
  -- Eta-expand subtraction to expose the denominator as a function of `T`.
  change Tendsto (fun T : 𝕜 ↦ t - T) atBot atTop
  simpa only [sub_eq_add_neg] using
    (tendsto_atTop_add_const_left atBot t tendsto_neg_atBot_atTop)

/-- An eventual comparison with common diverging linear weights compares their coefficients. -/
theorem le_of_eventually_mul_sub_le {a b A B : 𝕜}
    (hfinite : ∀ᶠ T : 𝕜 in atBot, A * (a - T) ≤ B * (b - T)) : A ≤ B := by
  have hr : Tendsto (fun T : 𝕜 ↦ (a - T) / (b - T)) atBot (𝓝 1) := by
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
      (tendsto_add_div_add_atTop a b).comp tendsto_neg_atBot_atTop
  have hnorm : ∀ᶠ T : 𝕜 in atBot, A * ((a - T) / (b - T)) ≤ B := by
    filter_upwards [hfinite, eventually_lt_atBot b] with T hT hTb
    rw [← mul_div_assoc, div_le_iff₀ (sub_pos.mpr hTb)]
    exact hT
  exact le_of_tendsto (by simpa using hr.const_mul A) hnorm

/-- Continuous functions satisfy the limiting comparison at a right endpoint if their
linearly weighted comparisons hold eventually at negative infinity and near that endpoint. -/
theorem le_of_eventually_mul_sub_le_nhdsLT {f g : 𝕜 → 𝕜} {a b : 𝕜}
    (hg : ContinuousWithinAt g (Set.Iio b) b) (hf : ContinuousWithinAt f (Set.Iio b) b)
    (hfinite : ∀ᶠ t in 𝓝[<] b, ∀ᶠ T : 𝕜 in atBot,
      g t * (a - T) ≤ f t * (t - T)) : g b ≤ f b :=
  le_of_tendsto_of_tendsto hg hf (hfinite.mono fun _ ht ↦ le_of_eventually_mul_sub_le ht)

/-- A reciprocal correction vanishing at negative infinity does not change the comparison
at a right endpoint where both sides are continuous from the left. -/
theorem le_of_eventually_le_add_div_nhdsLT {f q r : 𝕜 → 𝕜} {b : 𝕜}
    (hf : ContinuousWithinAt f (Set.Iio b) b) (hq : ContinuousWithinAt q (Set.Iio b) b)
    (hfinite : ∀ᶠ t in 𝓝[<] b, ∀ᶠ T : 𝕜 in atBot, f t ≤ q t + r t / (t - T)) :
    f b ≤ q b :=
  le_of_tendsto_of_tendsto hf hq (hfinite.mono fun t ht ↦
    (tendsto_div_sub_atBot t (r t)).le_of_eventually_le_add ht)

end Comparisons

end TauCeti
