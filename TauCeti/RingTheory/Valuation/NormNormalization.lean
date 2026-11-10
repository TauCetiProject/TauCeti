/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Comparing norm-compatible additive valuations

Two real additive valuations recovering the same norm with specified bases greater
than one differ by the ratio of the logarithms of those bases. The comparison includes
zero, whose value remains infinity. In particular, fixing the base determines the
additive valuation uniquely; no choice of scale is installed as a global instance.
Under norm recovery, the sphere `‖x‖ = b ^ σ` is the level set `v x = -σ`
(`AddValuation.norm_eq_rpow_iff`).
-/

public section

namespace AddValuation

variable {K : Type*} [NormedDivisionRing K]

/-- Changing the base in norm recovery scales a real additive valuation by the ratio
of the logarithms. At zero the comparison maps infinity to infinity. -/
theorem eq_map_of_norm_eq_rpow (v w : AddValuation K (WithTop ℝ))
    {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b')
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
    (hw : ∀ x ≠ 0, ‖x‖ = b' ^ (-(w x).untop₀)) (x : K) :
    w x = WithTop.map (fun t => (Real.log b / Real.log b') * t) (v x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hlog := congrArg Real.log ((hv x hx).symm.trans (hw x hx))
  rw [Real.log_rpow (zero_lt_one.trans hb), Real.log_rpow (zero_lt_one.trans hb')] at hlog
  rw [← WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hx),
    ← WithTop.coe_untop₀_of_ne_top (w.ne_top_iff.mpr hx),
    WithTop.map_coe, WithTop.coe_eq_coe]
  rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt (Real.log_pos hb'))]
  nlinarith

/-- For a fixed base greater than one, norm recovery uniquely specifies the real
additive valuation. -/
theorem eq_of_norm_eq_rpow (v w : AddValuation K (WithTop ℝ))
    {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
    (hw : ∀ x ≠ 0, ‖x‖ = b ^ (-(w x).untop₀)) : w = v := by
  ext x
  have h := v.eq_map_of_norm_eq_rpow w hb hb hv hw x
  have hid : (fun t : ℝ => (Real.log b / Real.log b) * t) = id := by
    ext t
    simp [ne_of_gt (Real.log_pos hb)]
  rw [hid, WithTop.map_id] at h
  exact h

/-- Under norm recovery with base `b > 1`, the points of norm `b ^ σ` are exactly those of
valuation `-σ`. Zero lies on neither side. -/
theorem norm_eq_rpow_iff (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {x : K} {σ : ℝ} :
    ‖x‖ = b ^ σ ↔ v x = ((-σ : ℝ) : WithTop ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [norm_zero, map_zero]
    exact iff_of_false (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ).ne WithTop.top_ne_coe
  rw [hv x hx, Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne',
    ← WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hx), WithTop.coe_eq_coe,
    WithTop.untop₀_coe, neg_eq_iff_eq_neg]

end AddValuation
