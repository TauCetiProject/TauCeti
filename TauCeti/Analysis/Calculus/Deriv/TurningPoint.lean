/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Instances.Sign
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Topology.Order.IntermediateValue

/-!
# Oscillation between two turning points

Let `x, p : ℝ → ℝ` describe a motion with one degree of freedom: the position `x` moves with
velocity `c p` for a constant `c > 0`, and the momentum `p` is continuous. While `p` keeps a sign,
the position is strictly monotone (`TauCeti.strictMonoOn_Icc_of_forall_hasDerivAt_mul`,
`TauCeti.strictAntiOn_Icc_of_forall_hasDerivAt_mul`). If `x` stays in `[a, b]` and the elapsed time
along every monotone stretch is the quadrature `∫ g` between the positions reached, for some
nonnegative `g` integrable on `[a, b]`, then every time interval on which `p` does not vanish lasts
at most `∫_a^b g` (`TauCeti.sub_le_integral_of_forall_hasDerivAt_mul`).

Suppose moreover that `x` stays in `[a, b]`, that `p` vanishes exactly when `x` is at a turning
point `a` or `b`, that `p` has a positive derivative whenever `x = a` and a negative one whenever
`x = b`, and that every time interval on which `p` does not vanish lasts at most `L`. Then the
motion oscillates between the turning points:

* from `a` the position rises to `b`, with `p > 0` meanwhile
  (`TauCeti.exists_gt_eq_and_forall_pos_of_forall_hasDerivAt_mul`);
* from `b` it falls to `a`, with `p < 0` meanwhile
  (`TauCeti.exists_gt_eq_and_forall_neg_of_forall_hasDerivAt_mul`);
* after any time `t`, it reaches `a` before the time `t + 1 + 2 L`
  (`TauCeti.exists_mem_Ioo_eq_of_forall_hasDerivAt_mul`).

This is the common core of the oscillation of the radius of a motion in a central potential well
and of the height of the spherical pendulum, where the bound `L` is the time quadrature between the
turning points.
-/

public section

open Filter Set MeasureTheory
open scoped Topology

namespace TauCeti

variable {x p : ℝ → ℝ} {c a b L : ℝ}

/-- While `p` is positive on `(s, t)`, a position `x` with velocity `c p`, `c > 0`, increases
strictly on `[s, t]`. -/
theorem strictMonoOn_Icc_of_forall_hasDerivAt_mul (hc : 0 < c) {s t : ℝ}
    (hx : ∀ u ∈ Icc s t, HasDerivAt x (c * p u) u) (hp : ∀ u ∈ Ioo s t, 0 < p u) :
    StrictMonoOn x (Icc s t) :=
  strictMonoOn_of_deriv_pos (convex_Icc s t)
    (fun u hu ↦ (hx u hu).continuousAt.continuousWithinAt) fun u hu ↦ by
      rw [interior_Icc] at hu
      rw [(hx u (Ioo_subset_Icc_self hu)).deriv]
      exact mul_pos hc (hp u hu)

/-- While `p` is negative on `(s, t)`, a position `x` with velocity `c p`, `c > 0`, decreases
strictly on `[s, t]`. -/
theorem strictAntiOn_Icc_of_forall_hasDerivAt_mul (hc : 0 < c) {s t : ℝ}
    (hx : ∀ u ∈ Icc s t, HasDerivAt x (c * p u) u) (hp : ∀ u ∈ Ioo s t, p u < 0) :
    StrictAntiOn x (Icc s t) :=
  strictAntiOn_of_deriv_neg (convex_Icc s t)
    (fun u hu ↦ (hx u hu).continuousAt.continuousWithinAt) fun u hu ↦ by
      rw [interior_Icc] at hu
      rw [(hx u (Ioo_subset_Icc_self hu)).deriv]
      exact mul_neg_of_pos_of_neg hc (hp u hu)

section Oscillation

variable (hc : 0 < c) (hx : ∀ t, HasDerivAt x (c * p t) t) (hp : Continuous p)
  (hmem : ∀ t, x t ∈ Icc a b) (hne : ∀ t, p t ≠ 0 ↔ x t ∈ Ioo a b)
  (ha : ∀ t, x t = a → ∃ d, 0 < d ∧ HasDerivAt p d t)
  (hb : ∀ t, x t = b → ∃ d, d < 0 ∧ HasDerivAt p d t)
  (hL : ∀ s t, s ≤ t → (∀ u ∈ Ioo s t, p u ≠ 0) → t - s ≤ L)

include hc hx hp hmem in
/-- **Passages are short.** Let `x` move with velocity `c p`, `c > 0`, with `p` continuous and `x`
in `[a, b]`, and let `g` be nonnegative and integrable on `[a, b]`. Suppose that the elapsed time
along a stretch where `p > 0` is `∫_{x(s)}^{x(t)} g`, and along a stretch where `p < 0` it is
`∫_{x(t)}^{x(s)} g`. Then every time interval on which `p` does not vanish lasts at most
`∫_a^b g`. -/
theorem sub_le_integral_of_forall_hasDerivAt_mul {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hg₀ : ∀ y ∈ Icc a b, 0 ≤ g y)
    (hrise : ∀ s t, s ≤ t → (∀ u ∈ Ioo s t, 0 < p u) → t - s = ∫ y in x s..x t, g y)
    (hfall : ∀ s t, s ≤ t → (∀ u ∈ Ioo s t, p u < 0) → t - s = ∫ y in x t..x s, g y)
    {s t : ℝ} (hst : s ≤ t) (hne : ∀ u ∈ Ioo s t, p u ≠ 0) : t - s ≤ ∫ y in a..b, g y := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a b)] g :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun y hy ↦ hg₀ y (Ioc_subset_Icc_self hy)
  rcases hst.eq_or_lt with rfl | hst'
  · rw [sub_self]
    exact intervalIntegral.integral_nonneg ((hmem s).1.trans (hmem s).2) hg₀
  -- `p` has a constant sign on `(s, t)`, that of its value at the midpoint.
  have hsign {u w : ℝ} (hu : u ∈ Ioo s t) (hw : w ∈ Ioo s t) :
      SignType.sign (p u) = SignType.sign (p w) :=
    isPreconnected_Ioo.sign_eq_of_continuousOn hp.continuousOn hne hu hw
  have hmid : (s + t) / 2 ∈ Ioo s t := ⟨by linarith, by linarith⟩
  rcases (hne _ hmid).lt_or_gt with hneg | hpos
  · have hp' (u : ℝ) (hu : u ∈ Ioo s t) : p u < 0 :=
      sign_eq_neg_one_iff.1 ((hsign hu hmid).trans (sign_eq_neg_one_iff.2 hneg))
    have hlt := strictAntiOn_Icc_of_forall_hasDerivAt_mul hc (fun u _ ↦ hx u) hp'
      ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst'
    rw [hfall s t hst hp']
    exact intervalIntegral.integral_mono_interval (hmem t).1 hlt.le (hmem s).2 hnn hg
  · have hp' (u : ℝ) (hu : u ∈ Ioo s t) : 0 < p u :=
      sign_eq_one_iff.1 ((hsign hu hmid).trans (sign_eq_one_iff.2 hpos))
    have hlt := strictMonoOn_Icc_of_forall_hasDerivAt_mul hc (fun u _ ↦ hx u) hp'
      ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst'
    rw [hrise s t hst hp']
    exact intervalIntegral.integral_mono_interval (hmem s).1 hlt.le (hmem t).2 hnn hg

include hL in
/-- The bound on the duration of passages is nonnegative. -/
private theorem nonneg_of_forall_sub_le : 0 ≤ L := by
  simpa using hL 0 0 le_rfl (by simp)

include hmem hne in
/-- Where `p` vanishes, the position is a turning point. -/
private theorem eq_or_eq_of_eq_zero {t : ℝ} (h : p t = 0) : x t = a ∨ x t = b := by
  have hnot := mt (hne t).2 (not_not.2 h)
  rcases (hmem t).1.eq_or_lt with h' | h'
  · exact Or.inl h'.symm
  · exact Or.inr (le_antisymm (hmem t).2 (not_lt.1 fun h'' ↦ hnot ⟨h', h''⟩))

include hne in
/-- If `p` vanishes exactly when `x` is outside `(a, b)`, then `p` vanishes whenever `x` is at one
of the turning points `a` or `b`. -/
theorem eq_zero_of_eq_or_eq_of_forall_ne_zero_iff {t : ℝ} (h : x t = a ∨ x t = b) : p t = 0 :=
  not_not.1 fun hpt ↦ by
    have := (hne t).1 hpt
    rcases h with h | h <;> rw [h] at this
    exacts [this.1.false, this.2.false]

include hp hL in
/-- **The next zero.** If `σ p` is positive just after `t₁`, then `p` vanishes at a later time `t₂`,
and `σ p` is positive in between. -/
private theorem exists_next_zero {σ t₁ : ℝ} (hσ : σ ≠ 0) (hpos : ∀ᶠ u in 𝓝[>] t₁, 0 < σ * p u) :
    ∃ t₂, t₁ < t₂ ∧ p t₂ = 0 ∧ ∀ u ∈ Ioo t₁ t₂, 0 < σ * p u := by
  have hL₀ := nonneg_of_forall_sub_le hL
  obtain ⟨t₂, ⟨h₁₂, -⟩, hf₂, hpos'⟩ := (continuous_const.mul hp).continuousOn
    |>.exists_mem_Ioo_eq_and_forall_gt (b := t₁ + 1 + L) hpos <| by
    -- Passages are short, so `σ p` does not stay positive.
    by_contra! hfpos
    have := hL t₁ (t₁ + 1 + L) (by linarith) fun w hw ↦ right_ne_zero_of_mul (hfpos w hw).ne'
    linarith
  exact ⟨t₂, h₁₂, (mul_eq_zero.1 hf₂).resolve_left hσ, hpos'⟩

include hc hx hp hmem hne ha hL in
/-- **From the lower turning point to the upper one.** Let `x` move with velocity `c p`, `c > 0`,
with `p` continuous, `x` in `[a, b]`, `p` vanishing exactly when `x ∈ {a, b}`, `p` with positive
derivative whenever `x = a`, and passages with `p ≠ 0` lasting at most `L`. If `x t₁ = a`, then `x`
reaches `b` at a later time `t₂`, with `p` positive in between. -/
theorem exists_gt_eq_and_forall_pos_of_forall_hasDerivAt_mul {t₁ : ℝ} (h₁ : x t₁ = a) :
    ∃ t₂, t₁ < t₂ ∧ x t₂ = b ∧ ∀ u ∈ Ioo t₁ t₂, 0 < p u := by
  obtain ⟨d, hd, hpd⟩ := ha t₁ h₁
  have hp₁ := eq_zero_of_eq_or_eq_of_forall_ne_zero_iff hne (Or.inl h₁)
  obtain ⟨t₂, h₁₂, hp₂, hpos⟩ := exists_next_zero hp hL one_ne_zero (by
    simpa [hp₁] using hpd.hasDerivWithinAt.eventually_nhdsGT_lt_of_pos hd)
  simp only [one_mul] at hpos
  refine ⟨t₂, h₁₂, (eq_or_eq_of_eq_zero hmem hne hp₂).resolve_left fun h₂ ↦ ?_, hpos⟩
  have := strictMonoOn_Icc_of_forall_hasDerivAt_mul hc (fun u _ ↦ hx u) hpos ⟨le_rfl, h₁₂.le⟩
    ⟨h₁₂.le, le_rfl⟩ h₁₂
  simp only [h₁, h₂, lt_self_iff_false] at this

include hc hx hp hmem hne hb hL in
/-- **From the upper turning point to the lower one.** Under the hypotheses of
`TauCeti.exists_gt_eq_and_forall_pos_of_forall_hasDerivAt_mul`, with `p` having negative derivative
whenever `x = b` instead, if `x t₂ = b`, then `x` reaches `a` at a later time `t₃`, with `p`
negative in between. -/
theorem exists_gt_eq_and_forall_neg_of_forall_hasDerivAt_mul {t₂ : ℝ} (h₂ : x t₂ = b) :
    ∃ t₃, t₂ < t₃ ∧ x t₃ = a ∧ ∀ u ∈ Ioo t₂ t₃, p u < 0 := by
  obtain ⟨d, hd, hpd⟩ := hb t₂ h₂
  have hp₂ := eq_zero_of_eq_or_eq_of_forall_ne_zero_iff hne (Or.inr h₂)
  obtain ⟨t₃, h₂₃, hp₃, hneg⟩ := exists_next_zero hp hL (neg_ne_zero.2 one_ne_zero) (by
    simpa [hp₂] using hpd.neg.hasDerivWithinAt.eventually_nhdsGT_lt_of_pos (neg_pos.2 hd))
  simp only [neg_one_mul, neg_pos] at hneg
  refine ⟨t₃, h₂₃, (eq_or_eq_of_eq_zero hmem hne hp₃).resolve_right fun h₃ ↦ ?_, hneg⟩
  have := strictAntiOn_Icc_of_forall_hasDerivAt_mul hc (fun u _ ↦ hx u) hneg ⟨le_rfl, h₂₃.le⟩
    ⟨h₂₃.le, le_rfl⟩ h₂₃
  simp only [h₂, h₃, lt_self_iff_false] at this

include hc hx hp hmem hne hb hL in
/-- **The motion reaches the lower turning point.** Under the hypotheses of
`TauCeti.exists_gt_eq_and_forall_neg_of_forall_hasDerivAt_mul`, after any time `t` the position `x`
reaches `a` before the time `t + 1 + 2 L`. -/
theorem exists_mem_Ioo_eq_of_forall_hasDerivAt_mul (t : ℝ) :
    ∃ s ∈ Ioo t (t + 1 + 2 * L), x s = a := by
  have hL₀ := nonneg_of_forall_sub_le hL
  -- Passages are short, so `p` vanishes at some time, at a turning point.
  obtain ⟨u, hu, hpu⟩ : ∃ u ∈ Ioo t (t + 1 + L), p u = 0 := by
    by_contra! hpne
    have := hL t (t + 1 + L) (by linarith) hpne
    linarith
  rcases eq_or_eq_of_eq_zero hmem hne hpu with hu' | hu'
  · exact ⟨u, ⟨hu.1, by linarith [hu.2]⟩, hu'⟩
  · obtain ⟨s, hus, hs, hneg⟩ :=
      exists_gt_eq_and_forall_neg_of_forall_hasDerivAt_mul hc hx hp hmem hne hb hL hu'
    have := hL u s hus.le fun w hw ↦ (hneg w hw).ne
    exact ⟨s, ⟨hu.1.trans hus, by linarith [hu.2]⟩, hs⟩

end Oscillation

end TauCeti
