/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The piecewise linear ramp

`TauCeti.ramp s δ x = max 0 (min 1 ((x - s) / δ))` is the continuous piecewise linear function
that vanishes left of `s`, equals `1` right of `s + δ`, and is linear in between. It is the
projection of `(x - s) / δ` onto `[0, 1]`. Ramps approximate the indicator of `[s, ∞)`, and
differences of ramps approximate indicators of intervals; this is how they serve as one-sided
approximations and as test functions.

## Main declarations

* `TauCeti.ramp`: the ramp from `0` at `s` to `1` at `s + δ`.
* `TauCeti.lipschitzWith_ramp`: for `δ > 0` the ramp is `δ⁻¹`-Lipschitz.
* `TauCeti.hasDerivAt_ramp`: away from its two corners the ramp has derivative `δ⁻¹` on
  `(s, s + δ)` and `0` elsewhere.
-/

public section

open Set

namespace TauCeti

/-- The continuous piecewise linear ramp, `0` left of `s` and `1` right of `s + δ`: the projection
of `(x - s) / δ` onto `[0, 1]`. -/
noncomputable def ramp (s δ x : ℝ) : ℝ := max 0 (min 1 ((x - s) / δ))

theorem continuous_ramp (s δ : ℝ) : Continuous (ramp s δ) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const δ))

theorem ramp_nonneg (s δ x : ℝ) : 0 ≤ ramp s δ x := le_max_left _ _

theorem ramp_le_one (s δ x : ℝ) : ramp s δ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ramp_eq_zero {s δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ s) : ramp s δ x = 0 :=
  max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))

theorem ramp_eq_one {s δ x : ℝ} (hδ : 0 < δ) (hx : s + δ ≤ x) : ramp s δ x = 1 := by
  rw [ramp, min_eq_left ((le_div_iff₀ hδ).2 (by linarith)), max_eq_right zero_le_one]

/-- Moving the start of the ramp to the right lowers it. -/
theorem antitone_ramp {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : Antitone fun s ↦ ramp s δ x :=
  fun _ _ h ↦ max_le_max le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right (by linarith) hδ))

/-- For `δ > 0` the ramp is Lipschitz with constant `δ⁻¹`. -/
theorem lipschitzWith_ramp {s δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal δ⁻¹) (ramp s δ) := by
  have hlin : LipschitzWith (Real.toNNReal δ⁻¹) fun x : ℝ ↦ (x - s) / δ :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hδ.le), ← sub_div,
        sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ, div_eq_inv_mul]
  have h := (LipschitzWith.subtype_val _).comp ((LipschitzWith.projIcc zero_le_one).comp hlin)
  rwa [one_mul, one_mul] at h

/-- Away from its two corners the ramp has derivative `δ⁻¹` on `(s, s + δ)` and `0` elsewhere. -/
theorem hasDerivAt_ramp {s δ x : ℝ} (hδ : 0 < δ) (hs : x ≠ s) (hsδ : x ≠ s + δ) :
    HasDerivAt (ramp s δ) ((Ioo s (s + δ)).indicator (fun _ ↦ δ⁻¹) x) x := by
  rcases lt_or_gt_of_ne hs with hxs | hxs
  · have hx : x ∉ Ioo s (s + δ) := fun h ↦ (lt_asymm hxs h.1).elim
    rw [indicator_of_notMem hx]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hxs] with y hy using ramp_eq_zero hδ (le_of_lt hy)
  rcases lt_or_gt_of_ne hsδ with hxsδ | hxsδ
  · have hx : x ∈ Ioo s (s + δ) := ⟨hxs, hxsδ⟩
    rw [indicator_of_mem hx]
    have hlin : HasDerivAt (fun y ↦ (y - s) / δ) δ⁻¹ x := by
      simpa [one_div] using ((hasDerivAt_id x).sub_const s).div_const δ
    refine hlin.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hxs hxsδ] with y hy
    rw [ramp, min_eq_right ((div_le_iff₀ hδ).2 (by linarith [hy.2])),
      max_eq_right (div_nonneg (by linarith [hy.1]) hδ.le)]
  · have hx : x ∉ Ioo s (s + δ) := fun h ↦ (lt_asymm hxsδ h.2).elim
    rw [indicator_of_notMem hx]
    refine (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hxsδ] with y hy using ramp_eq_one hδ (le_of_lt hy)

end TauCeti
