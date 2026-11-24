/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

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
* `TauCeti.ramp_eq_zero_iff`, `TauCeti.ramp_eq_one_iff`: for `δ > 0` the ramp vanishes exactly on
  `(-∞, s]` and equals `1` exactly on `[s + δ, ∞)`.
* `TauCeti.monotone_ramp`, `TauCeti.ramp_left_antitone`: for `δ ≥ 0` the ramp is monotone in `x`
  and antitone in its start `s`.
* `TauCeti.lipschitzWith_ramp`: the ramp is `|δ|⁻¹`-Lipschitz.
* `TauCeti.hasDerivAt_ramp`: for `δ > 0`, away from its two corners the ramp has derivative `δ⁻¹`
  on `(s, s + δ)` and `0` elsewhere.
* `TauCeti.deriv_ramp_ae_eq`, `TauCeti.memLp_deriv_ramp`: for `δ > 0` the derivative of the ramp
  is almost everywhere `δ⁻¹` times the indicator of `(s, s + δ)`, so it lies in every `Lᵖ`.
* `TauCeti.ramp_sub_ramp_mem_Icc`, `TauCeti.ramp_sub_ramp_eq_zero_of_notMem`: for `δ ≥ 0` and
  `s ≤ t`, the difference `ramp s δ - ramp t δ` takes values in `[0, 1]`, and for `δ > 0` it
  vanishes off `(s, t + δ)`.
* `TauCeti.deriv_ramp_sub_ramp_ae_eq`, `TauCeti.memLp_deriv_ramp_sub_ramp`: for `δ₁, δ₂ > 0` the
  derivative of `ramp s δ₁ - ramp t δ₂` is almost everywhere the difference of the two normalized
  indicators, so it lies in every `Lᵖ`.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- The projection of `(x - s) / δ` onto `[0, 1]`. For `δ > 0` this is the continuous piecewise
linear ramp, `0` left of `s` and `1` right of `s + δ`. -/
noncomputable def ramp (s δ x : ℝ) : ℝ := max 0 (min 1 ((x - s) / δ))

theorem ramp_def (s δ x : ℝ) : ramp s δ x = max 0 (min 1 ((x - s) / δ)) := (rfl)

/-- The ramp is the projection of `(x - s) / δ` onto `[0, 1]`. -/
theorem ramp_eq_projIcc (s δ x : ℝ) :
    ramp s δ x = (projIcc 0 1 zero_le_one ((x - s) / δ) : ℝ) := by
  rw [ramp_def, coe_projIcc]

@[fun_prop]
theorem continuous_ramp (s δ : ℝ) : Continuous (ramp s δ) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const δ))

theorem ramp_nonneg (s δ x : ℝ) : 0 ≤ ramp s δ x := le_max_left _ _

theorem ramp_le_one (s δ x : ℝ) : ramp s δ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ramp_eq_zero {s δ x : ℝ} (hδ : 0 ≤ δ) (hx : x ≤ s) : ramp s δ x = 0 :=
  max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ))

theorem ramp_eq_one {s δ x : ℝ} (hδ : 0 < δ) (hx : s + δ ≤ x) : ramp s δ x = 1 := by
  rw [ramp_def, min_eq_left ((le_div_iff₀ hδ).2 (by linarith)), max_eq_right zero_le_one]

/-- For `δ > 0` the ramp is linear on `[s, s + δ]`. -/
theorem ramp_eq_div {s δ x : ℝ} (hδ : 0 < δ) (hx : x ∈ Icc s (s + δ)) :
    ramp s δ x = (x - s) / δ := by
  rw [ramp_def, min_eq_right ((div_le_iff₀ hδ).2 (by linarith [hx.2])),
    max_eq_right (div_nonneg (by linarith [hx.1]) hδ.le)]

@[simp]
theorem ramp_self (s δ : ℝ) : ramp s δ s = 0 := by
  simp [ramp_def]

/-- A ramp of width zero vanishes identically. -/
@[simp]
theorem ramp_zero_width (s x : ℝ) : ramp s 0 x = 0 := by
  simp [ramp_def]

@[simp]
theorem ramp_self_add {s δ : ℝ} (hδ : δ ≠ 0) : ramp s δ (s + δ) = 1 := by
  simp [ramp_def, hδ]

/-- For `δ > 0` the ramp vanishes exactly on `(-∞, s]`. -/
theorem ramp_eq_zero_iff {s δ x : ℝ} (hδ : 0 < δ) : ramp s δ x = 0 ↔ x ≤ s := by
  refine ⟨fun h ↦ not_lt.1 fun hx ↦ ?_, ramp_eq_zero hδ.le⟩
  have hpos : 0 < min 1 ((x - s) / δ) := lt_min one_pos (div_pos (sub_pos.2 hx) hδ)
  rw [ramp_def, max_eq_right hpos.le] at h
  exact hpos.ne' h

/-- For `δ > 0` the ramp equals `1` exactly on `[s + δ, ∞)`. -/
theorem ramp_eq_one_iff {s δ x : ℝ} (hδ : 0 < δ) : ramp s δ x = 1 ↔ s + δ ≤ x := by
  refine ⟨fun h ↦ not_lt.1 fun hx ↦ ?_, ramp_eq_one hδ⟩
  rcases le_or_gt x s with hxs | hxs
  · rw [ramp_eq_zero hδ.le hxs] at h
    exact zero_ne_one h
  · rw [ramp_eq_div hδ ⟨hxs.le, hx.le⟩, div_eq_one_iff_eq hδ.ne'] at h
    linarith

/-- For `δ ≥ 0` the ramp is monotone. -/
theorem monotone_ramp (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : Monotone (ramp s δ) :=
  fun _ _ h ↦ max_le_max le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right (by linarith) hδ))

/-- For `δ ≥ 0`, moving the start of the ramp to the right lowers it. -/
theorem ramp_left_antitone {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : Antitone fun s ↦ ramp s δ x :=
  fun _ _ h ↦ max_le_max le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right (by linarith) hδ))

/-- For `δ ≥ 0` and `s ≤ t`, the difference of the ramps starting at `s` and at `t` takes values
in `[0, 1]`. -/
theorem ramp_sub_ramp_mem_Icc {s t δ : ℝ} (hδ : 0 ≤ δ) (h : s ≤ t) (x : ℝ) :
    ramp s δ x - ramp t δ x ∈ Icc 0 1 :=
  ⟨sub_nonneg.2 (ramp_left_antitone hδ x h),
    by linarith [ramp_le_one s δ x, ramp_nonneg t δ x]⟩

/-- For `δ > 0` and `s ≤ t`, the difference of the ramps starting at `s` and at `t` vanishes
off `(s, t + δ)`. -/
theorem ramp_sub_ramp_eq_zero_of_notMem {s t δ x : ℝ} (hδ : 0 < δ) (h : s ≤ t)
    (hx : x ∉ Ioo s (t + δ)) : ramp s δ x - ramp t δ x = 0 := by
  rw [sub_eq_zero]
  rcases le_or_gt x s with hxs | hxs
  · rw [ramp_eq_zero hδ.le hxs, ramp_eq_zero hδ.le (hxs.trans h)]
  · have htx : t + δ ≤ x := not_lt.1 fun h' ↦ hx ⟨hxs, h'⟩
    rw [ramp_eq_one hδ (by linarith), ramp_eq_one hδ htx]

/-- The ramp is Lipschitz with constant `|δ|⁻¹`. For `δ = 0` both sides vanish: the ramp is
identically zero and `0⁻¹ = 0`. -/
theorem lipschitzWith_ramp (s δ : ℝ) : LipschitzWith ‖δ‖₊⁻¹ (ramp s δ) := by
  have hlin : LipschitzWith ‖δ‖₊⁻¹ fun x : ℝ ↦ (x - s) / δ :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_inv, coe_nnNorm, Real.norm_eq_abs, ← sub_div,
        sub_sub_sub_cancel_right, abs_div, div_eq_inv_mul]
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
    filter_upwards [Iio_mem_nhds hxs] with y hy using ramp_eq_zero hδ.le (le_of_lt hy)
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

/-- For `δ > 0` the ramp has derivative `δ⁻¹` on `(s, s + δ)` and `0` elsewhere, at almost every
point. -/
theorem ae_hasDerivAt_ramp {s δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x, HasDerivAt (ramp s δ) ((Ioo s (s + δ)).indicator (fun _ ↦ δ⁻¹) x) x := by
  filter_upwards [Measure.ae_ne volume s, Measure.ae_ne volume (s + δ)] with x h₁ h₂
  exact hasDerivAt_ramp hδ h₁ h₂

/-- For `δ > 0` the derivative of the ramp is almost everywhere `δ⁻¹` times the indicator of
`(s, s + δ)`. -/
theorem deriv_ramp_ae_eq {s δ : ℝ} (hδ : 0 < δ) :
    deriv (ramp s δ) =ᵐ[volume] (Ioo s (s + δ)).indicator (fun _ ↦ δ⁻¹) :=
  (ae_hasDerivAt_ramp hδ).mono fun _ hx ↦ hx.deriv

/-- For `δ > 0` the derivative of the ramp lies in every `Lᵖ`. -/
theorem memLp_deriv_ramp {s δ : ℝ} (hδ : 0 < δ) (p : ENNReal) :
    MemLp (deriv (ramp s δ)) p :=
  (memLp_indicator_const p measurableSet_Ioo.nullMeasurableSet δ⁻¹
    (Or.inr measure_Ioo_lt_top.ne)).ae_eq (deriv_ramp_ae_eq hδ).symm

/-- For `δ₁, δ₂ > 0` the derivative of `ramp s δ₁ - ramp t δ₂` is almost everywhere the
difference of the normalized indicators of `(s, s + δ₁)` and `(t, t + δ₂)`. -/
theorem deriv_ramp_sub_ramp_ae_eq {s t δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    deriv (ramp s δ₁ - ramp t δ₂) =ᵐ[volume] fun y ↦
      (Ioo s (s + δ₁)).indicator (fun _ ↦ δ₁⁻¹) y -
        (Ioo t (t + δ₂)).indicator (fun _ ↦ δ₂⁻¹) y := by
  filter_upwards [ae_hasDerivAt_ramp (s := s) hδ₁, ae_hasDerivAt_ramp (s := t) hδ₂] with y h₁ h₂
  exact (h₁.sub h₂).deriv

/-- For `δ₁, δ₂ > 0` the derivative of `ramp s δ₁ - ramp t δ₂` lies in every `Lᵖ`. -/
theorem memLp_deriv_ramp_sub_ramp {s t δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (p : ENNReal) :
    MemLp (deriv (ramp s δ₁ - ramp t δ₂)) p :=
  ((memLp_deriv_ramp (s := s) hδ₁ p).sub (memLp_deriv_ramp (s := t) hδ₂ p)).ae_eq (by
    filter_upwards [deriv_ramp_sub_ramp_ae_eq (s := s) (t := t) hδ₁ hδ₂,
      deriv_ramp_ae_eq (s := s) hδ₁, deriv_ramp_ae_eq (s := t) hδ₂] with y h h₁ h₂
    rw [h, Pi.sub_apply, h₁, h₂])

end TauCeti
