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

`TauCeti.ramp s δ x = max 0 (min 1 ((x - s) / δ))` is the projection of `(x - s) / δ` onto
`[0, 1]`. For `δ > 0` it is the continuous piecewise linear function that vanishes left of `s`,
equals `1` right of `s + δ`, and is linear in between. Ramps approximate the indicator of
`[s, ∞)`, and differences of ramps approximate indicators of intervals; this is how they serve as
one-sided approximations and as test functions.

## Main declarations

* `TauCeti.ramp`: the projection of `(x - s) / δ` onto `[0, 1]`; for `δ > 0`, the ramp from `0`
  at `s` to `1` at `s + δ`.
* `TauCeti.ramp_eq_div`: for `δ > 0` the ramp equals `(x - s) / δ` on `[s, s + δ]`.
* `TauCeti.lipschitzWith_ramp`: for `δ > 0` the ramp is `δ⁻¹`-Lipschitz.
* `TauCeti.hasDerivAt_ramp`: for `δ > 0`, away from its two corners the ramp has derivative `δ⁻¹`
  on `(s, s + δ)` and `0` elsewhere.
* `TauCeti.ramp_sub_ramp_mem_Icc`, `TauCeti.ramp_sub_ramp_eq_zero_of_notMem`: for `δ > 0` and
  `s ≤ t`, the difference `ramp s δ - ramp t δ` takes values in `[0, 1]` and vanishes off
  `(s, t + δ)`.
-/

public section

open Set

namespace TauCeti

/-- The projection of `(x - s) / δ` onto `[0, 1]`. For `δ > 0` this is the continuous piecewise
linear ramp, `0` left of `s` and `1` right of `s + δ`. -/
noncomputable def ramp (s δ x : ℝ) : ℝ := max 0 (min 1 ((x - s) / δ))

theorem ramp_def (s δ x : ℝ) : ramp s δ x = max 0 (min 1 ((x - s) / δ)) := (rfl)

/-- The ramp is the projection of `(x - s) / δ` onto `[0, 1]`. -/
theorem ramp_eq_projIcc (s δ x : ℝ) :
    ramp s δ x = (projIcc 0 1 zero_le_one ((x - s) / δ) : ℝ) := by
  rw [ramp_def, coe_projIcc]

theorem continuous_ramp (s δ : ℝ) : Continuous (ramp s δ) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const δ))

theorem ramp_nonneg (s δ x : ℝ) : 0 ≤ ramp s δ x := le_max_left _ _

theorem ramp_le_one (s δ x : ℝ) : ramp s δ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ramp_eq_zero {s δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ s) : ramp s δ x = 0 :=
  max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))

theorem ramp_eq_one {s δ x : ℝ} (hδ : 0 < δ) (hx : s + δ ≤ x) : ramp s δ x = 1 := by
  rw [ramp_def, min_eq_left ((le_div_iff₀ hδ).2 (by linarith)), max_eq_right zero_le_one]

/-- For `δ > 0` the ramp is linear on `[s, s + δ]`. -/
theorem ramp_eq_div {s δ x : ℝ} (hδ : 0 < δ) (hx : x ∈ Icc s (s + δ)) :
    ramp s δ x = (x - s) / δ := by
  rw [ramp_def, min_eq_right ((div_le_iff₀ hδ).2 (by linarith [hx.2])),
    max_eq_right (div_nonneg (by linarith [hx.1]) hδ.le)]

/-- Moving the start of the ramp to the right lowers it. -/
theorem ramp_left_antitone {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : Antitone fun s ↦ ramp s δ x :=
  fun _ _ h ↦ max_le_max le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right (by linarith) hδ))

/-- For `δ > 0` and `s ≤ t`, the difference of the ramps starting at `s` and at `t` takes values
in `[0, 1]`. -/
theorem ramp_sub_ramp_mem_Icc {s t δ : ℝ} (hδ : 0 < δ) (h : s ≤ t) (x : ℝ) :
    ramp s δ x - ramp t δ x ∈ Icc 0 1 :=
  ⟨sub_nonneg.2 (ramp_left_antitone hδ.le x h),
    by linarith [ramp_le_one s δ x, ramp_nonneg t δ x]⟩

/-- For `δ > 0` and `s ≤ t`, the difference of the ramps starting at `s` and at `t` vanishes
off `(s, t + δ)`. -/
theorem ramp_sub_ramp_eq_zero_of_notMem {s t δ x : ℝ} (hδ : 0 < δ) (h : s ≤ t)
    (hx : x ∉ Ioo s (t + δ)) : ramp s δ x - ramp t δ x = 0 := by
  rw [sub_eq_zero]
  rcases le_or_gt x s with hxs | hxs
  · rw [ramp_eq_zero hδ hxs, ramp_eq_zero hδ (hxs.trans h)]
  · have htx : t + δ ≤ x := not_lt.1 fun h' ↦ hx ⟨hxs, h'⟩
    rw [ramp_eq_one hδ (by linarith), ramp_eq_one hδ htx]

/-- For `δ > 0` the ramp is Lipschitz with constant `δ⁻¹`. -/
theorem lipschitzWith_ramp {s δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal δ⁻¹) (ramp s δ) := by
  have hlin : LipschitzWith (Real.toNNReal δ⁻¹) fun x : ℝ ↦ (x - s) / δ :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hδ.le), ← sub_div,
        sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ, div_eq_inv_mul]
  rw [funext (ramp_def s δ)]
  exact (hlin.const_min 1).const_max 0

/-- For `δ > 0`, away from its two corners the ramp has derivative `δ⁻¹` on `(s, s + δ)` and `0`
elsewhere. -/
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
    exact ramp_eq_div hδ (Ioo_subset_Icc_self hy)
  · have hx : x ∉ Ioo s (s + δ) := fun h ↦ (lt_asymm hxsδ h.2).elim
    rw [indicator_of_notMem hx]
    refine (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hxsδ] with y hy using ramp_eq_one hδ (le_of_lt hy)

end TauCeti
