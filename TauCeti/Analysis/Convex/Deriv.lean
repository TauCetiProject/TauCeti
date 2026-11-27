/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Convex.Function.Basic

/-!
# Derivatives and convexity on intervals

For real convex functions on a set `I`, inequalities between slopes on adjacent intervals imply
inequalities between their right derivatives at interior points. If the slopes interlace in
both directions, the difference of the functions is constant on the interior of `I`. These
results support uniqueness up to an additive constant when derivatives agree only on a dense set.

A real function whose third derivative is positive on `(a, b)` and whose second derivative is
continuous on `[a, b]` and nonnegative at `a` is strictly convex on `[a, b]`, since its second
derivative increases from a nonnegative value.

A differentiable strictly convex function on `[l, u]`, positive at both ends and negative at some
interior point, has exactly two zeros in `(l, u)`, with negative derivative at the first and
positive derivative at the second.

## Main statements

* `ConvexOn.rightDeriv_le_rightDeriv_of_slope_le` compares right derivatives from
  adjacent-slope inequalities.
* `ConvexOn.sub_eq_sub_of_slope_le` proves constancy of the difference when the slopes
  interlace.
* `ConvexOn.add_rightDeriv_mul_sub_le`: the tangent line with the right derivative as slope lies
  below a convex function.
* `ConvexOn.exists_mul_sub_le_max_zero`: a supporting line with nonnegative slope and
  nonpositive intercept to the positive part of a convex function `Φ` on `[0, ∞)` with
  `Φ 0 ≤ 0`.
* `StrictConvexOn.exists_setOf_eq_zero_eq_pair`: the two zeros of a strictly convex function that
  is positive at the ends of an interval and negative inside.
* `TauCeti.strictConvexOn_Icc_of_deriv3_pos`: strict convexity on `[a, b]` from a positive third
  derivative and a nonnegative second derivative at `a`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §24
  (one-sided derivatives of convex functions).
-/

public section

open Filter Set
open scoped Topology

namespace ConvexOn

variable {φ ψ : ℝ → ℝ} {I : Set ℝ}

/-- If no slope of `φ` on an interval `[x, y]` exceeds a slope of `ψ` on an adjacent interval
`[y, z]` in `I`, then the right derivative of `φ` at an interior point `x` of `I` is at most that
of `ψ`. -/
theorem rightDeriv_le_rightDeriv_of_slope_le (hφ : ConvexOn ℝ I φ) (hψ : ConvexOn ℝ I ψ)
    {x : ℝ} (hx : x ∈ interior I)
    (h : ∀ y z, z ∈ I → x < y → y < z → slope φ x y ≤ slope ψ y z) :
    derivWithin φ (Ioi x) x ≤ derivWithin ψ (Ioi x) x := by
  have hφd := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  have hψd := hψ.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi] at hφd hψd
  -- The right derivative of `φ` at `x` is at most every slope of `ψ` starting at `x`.
  refine ge_of_tendsto hψd ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx),
    self_mem_nhdsWithin] with z hz (hxz : x < z)
  have hψx : ContinuousAt ψ x :=
    hψ.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hx)
  have hcont : Tendsto (fun y => slope ψ y z) (𝓝[>] x) (𝓝 (slope ψ x z)) := by
    simp only [slope_def_field]
    exact ((continuousAt_const.sub hψx).div (continuousAt_const.sub continuousAt_id)
      (sub_ne_zero.2 hxz.ne')).tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hφd hcont ?_
  filter_upwards [Ioo_mem_nhdsGT hxz] with y hy
  exact h y z hz hy.1 hy.2

/-- Two convex functions on a set `I` whose slopes on adjacent intervals in `I` interlace in both
directions differ by a constant on the interior of `I`. -/
theorem sub_eq_sub_of_slope_le (hφ : ConvexOn ℝ I φ) (hψ : ConvexOn ℝ I ψ)
    (h₁ : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope φ a b ≤ slope ψ b c)
    (h₂ : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope ψ a b ≤ slope φ b c)
    {s t : ℝ} (hs : s ∈ interior I) (ht : t ∈ interior I) : φ t - ψ t = φ s - ψ s := by
  wlog hst : s ≤ t generalizing s t
  · exact (this ht hs (le_of_not_ge hst)).symm
  have hsub : Icc s t ⊆ interior I := hφ.1.interior.ordConnected.out hs ht
  refine constant_of_has_deriv_right_zero
    ((hφ.continuousOn_interior.sub hψ.continuousOn_interior).mono hsub) (fun x hx => ?_) t
    ⟨hst, le_rfl⟩
  have hx := hsub (Ico_subset_Icc_self hx)
  have hd := (hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hx).sub
    (hψ.hasDerivWithinAt_rightDeriv_of_mem_interior hx)
  have hxI := interior_subset hx
  rw [le_antisymm (hφ.rightDeriv_le_rightDeriv_of_slope_le hψ hx (h₁ x · · hxI))
    (hψ.rightDeriv_le_rightDeriv_of_slope_le hφ hx (h₂ x · · hxI)), sub_self] at hd
  exact hasDerivWithinAt_Ioi_iff_Ici.1 hd

/-- **The tangent line of a convex function.** At an interior point `x` of `I`, the line through
`(x, φ x)` whose slope is the right derivative of `φ` at `x` lies below `φ` on all of `I`. -/
theorem add_rightDeriv_mul_sub_le (hφ : ConvexOn ℝ I φ) {x y : ℝ} (hx : x ∈ interior I)
    (hy : y ∈ I) : φ x + derivWithin φ (Ioi x) x * (y - x) ≤ φ y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hφ.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hxy)] at h
    linarith
  · simp
  · have hslope := hφ.slope_le_leftDeriv_of_mem_interior hy hx hyx
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hyx)] at hslope
    have hderiv := mul_le_mul_of_nonneg_right (hφ.leftDeriv_le_rightDeriv_of_mem_interior hx)
      (sub_pos.2 hyx).le
    linarith

/-- **A supporting line to the positive part.** If `Φ` is convex on `[0, ∞)` with `Φ 0 ≤ 0`, then
at every `c > 0` the positive part `max (Φ ·) 0` has a supporting line `s ↦ k * s - d` with slope
`k ≥ 0` and intercept `-d ≤ 0`: it lies below `max (Φ ·) 0` on `[0, ∞)` and touches it at `c`. -/
theorem exists_mul_sub_le_max_zero {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0)
    {c : ℝ} (hc : 0 < c) :
    ∃ k d : ℝ, 0 ≤ k ∧ 0 ≤ d ∧ (∀ s, 0 ≤ s → k * s ≤ max (Φ s) 0 + d) ∧
      max (Φ c) 0 + d = k * c := by
  set Ψ : ℝ → ℝ := fun s ↦ max (Φ s) 0
  have hΨ : ConvexOn ℝ (Ici 0) Ψ := hΦ.sup (convexOn_const 0 (convex_Ici 0))
  have hc' : c ∈ interior (Ici (0 : ℝ)) := by rwa [interior_Ici]
  set k := derivWithin Ψ (Ioi c) c
  have htan (s : ℝ) (hs : 0 ≤ s) : Ψ c + k * (s - c) ≤ Ψ s := hΨ.add_rightDeriv_mul_sub_le hc' hs
  -- The tangent line passes below the origin, where `Ψ` vanishes, so its slope is nonnegative.
  have hd : 0 ≤ k * c - Ψ c := by linarith [htan 0 le_rfl, show Ψ 0 = 0 from max_eq_right hΦ0]
  have hk : 0 ≤ k := nonneg_of_mul_nonneg_left (by linarith [le_max_right (Φ c) 0]) hc
  exact ⟨k, k * c - Ψ c, hk, hd, fun s hs ↦ by linarith [htan s hs], by ring⟩

end ConvexOn

/-- A strictly convex function, differentiable on `[l, u]`, positive at `l` and `u` and negative
at `x ∈ (l, u)`, has exactly two zeros `p < x < q` in `(l, u)`. It is negative between them, with
negative derivative at `p` and positive derivative at `q`. -/
theorem StrictConvexOn.exists_setOf_eq_zero_eq_pair {φ : ℝ → ℝ} {l u x : ℝ}
    (hφ : StrictConvexOn ℝ (Icc l u) φ) (hd : ∀ y ∈ Icc l u, DifferentiableAt ℝ φ y)
    (hl : 0 < φ l) (hu : 0 < φ u) (hx : x ∈ Ioo l u) (hφx : φ x < 0) :
    ∃ p ∈ Ioo l x, ∃ q ∈ Ioo x u, {y ∈ Ioo l u | φ y = 0} = {p, q} ∧ φ p = 0 ∧ φ q = 0 ∧
      (∀ y ∈ Ioo p q, φ y < 0) ∧ deriv φ p < 0 ∧ 0 < deriv φ q := by
  have hc : ContinuousOn φ (Icc l u) := fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt
  -- A zero on each side of `x`, by the intermediate value theorem.
  obtain ⟨p, hp, hp0⟩ := intermediate_value_Ioo' hx.1.le
    (hc.mono (Icc_subset_Icc_right hx.2.le)) ⟨hφx, hl⟩
  obtain ⟨q, hq, hq0⟩ := intermediate_value_Ioo hx.2.le
    (hc.mono (Icc_subset_Icc_left hx.1.le)) ⟨hφx, hu⟩
  have hpI : p ∈ Icc l u := ⟨hp.1.le, hp.2.le.trans hx.2.le⟩
  have hqI : q ∈ Icc l u := ⟨hx.1.le.trans hq.1.le, hq.2.le⟩
  have hpq : p < q := hp.2.trans hq.1
  refine ⟨p, hp, q, hq, ?_, hp0, hq0, fun y hy ↦ ?_, ?_, ?_⟩
  · ext y
    simp only [mem_sep_iff, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨hy, hy0⟩ ↦
      hφ.eq_or_eq_of_apply_eq hpI hqI (Ioo_subset_Icc_self hy) hpq hp0 hq0 hy0, ?_⟩
    rintro (rfl | rfl)
    exacts [⟨⟨hp.1, hp.2.trans hx.2⟩, hp0⟩, ⟨⟨hx.1.trans hq.1, hq.2⟩, hq0⟩]
  · -- By strict convexity `φ` lies below the chord from `p` to `q`, which is zero.
    have h := hφ.lt_on_openSegment hpI hqI hpq.ne (by rwa [openSegment_eq_Ioo hpq])
    rwa [hp0, hq0, max_self] at h
  · have h := hφ.lt_slope_of_hasDerivAt hpI hqI hpq (hd p hpI).hasDerivAt
    rwa [slope_def_field, hp0, hq0, sub_self, zero_div] at h
  · have h := hφ.slope_lt_of_hasDerivAt hpI hqI hpq (hd q hqI).hasDerivAt
    rwa [slope_def_field, hp0, hq0, sub_self, zero_div] at h

namespace TauCeti

/-- A function whose second derivative is continuous on `[a, b]` and nonnegative at `a`, and whose
third derivative is positive on `(a, b)`, is strictly convex on `[a, b]`. -/
theorem strictConvexOn_Icc_of_deriv3_pos {g : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn g (Icc a b))
    (h2 : 0 ≤ deriv^[2] g a) (hc2 : ContinuousOn (deriv^[2] g) (Icc a b))
    (h3 : ∀ x ∈ Ioo a b, 0 < deriv^[3] g x) : StrictConvexOn ℝ (Icc a b) g := by
  have hmono : StrictMonoOn (deriv^[2] g) (Icc a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hc2 fun y hy => ?_
    rw [interior_Icc] at hy
    rw [← Function.iterate_succ_apply' deriv]
    exact h3 y hy
  refine strictConvexOn_of_deriv2_pos (convex_Icc _ _) hc fun y hy => ?_
  rw [interior_Icc] at hy
  exact h2.trans_lt (hmono (left_mem_Icc.2 (hy.1.trans hy.2).le) (Ioo_subset_Icc_self hy) hy.1)

end TauCeti
