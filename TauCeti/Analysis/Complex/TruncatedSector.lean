/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.Rectangle

/-!
# Closed and open truncated sectors in the complex plane

For a centre `z₀ : ℂ`, radial bounds `r, R : ℝ` and angular bounds `θ₁, θ₂ : ℝ`, the polar map
`(ρ, θ) ↦ circleMap z₀ ρ θ = z₀ + ρ exp (θ I)` sends the closed parameter rectangle
`[r, R] × [θ₁, θ₂]` to the closed truncated sector `Complex.closedTruncatedSector z₀ r R θ₁ θ₂`
and the open parameter rectangle `(r, R) × (θ₁, θ₂)` to the open truncated sector
`Complex.openTruncatedSector z₀ r R θ₁ θ₂`. When `r = 0` the inner arc collapses to the vertex `z₀`
and these sets reduce to full sectors of radius `R`.

Defining truncated sectors as polar images rather than through `Complex.arg` avoids any restriction
to the principal branch `(-π, π]`: sectors crossing the negative real axis behave the same way as
sectors inside the slit plane. When the angular interval does lie in `(-π, π]` (respectively
`[-π, π]` in the open case), membership reduces to simultaneous bounds on `‖z - z₀‖` and
`Complex.arg (z - z₀)`.

For `0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π` the polar parametrization does not wrap around `z₀`, so the
topological interior of the closed truncated sector is the open truncated sector and its frontier
is the union of the two radial segments at `θ₁`, `θ₂` and the two circular arcs at radii `r`, `R`.

## Main definitions

* `Complex.closedTruncatedSector z₀ r R θ₁ θ₂`: the polar image of `Icc r R ×ˢ Icc θ₁ θ₂` around
  `z₀`.
* `Complex.openTruncatedSector z₀ r R θ₁ θ₂`: the polar image of `Ioo r R ×ˢ Ioo θ₁ θ₂` around
  `z₀`.

## Main results

* `Complex.openTruncatedSector_eq_norm_arg`, `Complex.closedTruncatedSector_eq_norm_arg`:
  characterizations by bounds on `‖z - z₀‖` and `arg (z - z₀)` on the principal branch.
* `Complex.image_add_exp_rectangle_eq_closedTruncatedSector`: for `0 < r ≤ R` and `θ₁ ≤ θ₂`,
  `s ↦ z₀ + exp s` maps `Rectangle (log r + θ₁ * I) (log R + θ₂ * I)` onto the closed truncated
  sector.
* `Complex.isCompact_closedTruncatedSector`, `Complex.isClosed_closedTruncatedSector`,
  `Complex.isPreconnected_closedTruncatedSector`, `Complex.isOpen_openTruncatedSector`:
  compactness, closedness, connectedness and openness.
* `Complex.closure_openTruncatedSector`, `Complex.interior_closedTruncatedSector`,
  `Complex.frontier_closedTruncatedSector`: closure, interior and frontier for `0 ≤ r ≤ R` and
  `0 ≤ θ₂ - θ₁ < 2π`.
-/

public section

open Set Metric Real

namespace Complex

/-- The closed truncated sector around `z₀` with radii in `[r, R]` and angles in `[θ₁, θ₂]`,
defined as the image of `Icc r R ×ˢ Icc θ₁ θ₂` under `(ρ, θ) ↦ circleMap z₀ ρ θ`. When `r = 0`
this is a closed full sector of radius `R`. -/
noncomputable def closedTruncatedSector (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) : Set ℂ :=
  Function.uncurry (circleMap z₀) '' (Icc r R ×ˢ Icc θ₁ θ₂)

/-- The open truncated sector around `z₀` with radii in `(r, R)` and angles in `(θ₁, θ₂)`,
defined as the image of `Ioo r R ×ˢ Ioo θ₁ θ₂` under `(ρ, θ) ↦ circleMap z₀ ρ θ`. When `r = 0`
this is an open full sector of radius `R`. -/
noncomputable def openTruncatedSector (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) : Set ℂ :=
  Function.uncurry (circleMap z₀) '' (Ioo r R ×ˢ Ioo θ₁ θ₂)

/-- `Complex.closedTruncatedSector` unfolded to its polar-image definition. -/
theorem closedTruncatedSector_def (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    closedTruncatedSector z₀ r R θ₁ θ₂ =
      Function.uncurry (circleMap z₀) '' (Icc r R ×ˢ Icc θ₁ θ₂) := (rfl)

/-- `Complex.openTruncatedSector` unfolded to its polar-image definition. -/
theorem openTruncatedSector_def (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    openTruncatedSector z₀ r R θ₁ θ₂ =
      Function.uncurry (circleMap z₀) '' (Ioo r R ×ˢ Ioo θ₁ θ₂) := (rfl)

variable {z₀ z : ℂ} {r R θ₁ θ₂ : ℝ}

/-- Membership in `closedTruncatedSector` in terms of a polar witness `(ρ, θ)`. -/
theorem mem_closedTruncatedSector :
    z ∈ closedTruncatedSector z₀ r R θ₁ θ₂ ↔
      ∃ ρ ∈ Icc r R, ∃ θ ∈ Icc θ₁ θ₂, circleMap z₀ ρ θ = z := by
  simp only [closedTruncatedSector, mem_image, Prod.exists, mem_prod, Function.uncurry_apply_pair]
  exact ⟨fun ⟨a, b, ⟨ha, hb⟩, h⟩ ↦ ⟨a, ha, b, hb, h⟩,
    fun ⟨a, ha, b, hb, h⟩ ↦ ⟨a, b, ⟨ha, hb⟩, h⟩⟩

/-- Membership in `openTruncatedSector` in terms of a polar witness `(ρ, θ)`. -/
theorem mem_openTruncatedSector :
    z ∈ openTruncatedSector z₀ r R θ₁ θ₂ ↔
      ∃ ρ ∈ Ioo r R, ∃ θ ∈ Ioo θ₁ θ₂, circleMap z₀ ρ θ = z := by
  simp only [openTruncatedSector, mem_image, Prod.exists, mem_prod, Function.uncurry_apply_pair]
  exact ⟨fun ⟨a, b, ⟨ha, hb⟩, h⟩ ↦ ⟨a, ha, b, hb, h⟩,
    fun ⟨a, ha, b, hb, h⟩ ↦ ⟨a, b, ⟨ha, hb⟩, h⟩⟩

/-- A polar point `circleMap z₀ ρ θ` with `ρ ∈ [r, R]` and `θ ∈ [θ₁, θ₂]` belongs to the closed
truncated sector. -/
theorem circleMap_mem_closedTruncatedSector {ρ θ : ℝ} (hρ : ρ ∈ Icc r R) (hθ : θ ∈ Icc θ₁ θ₂) :
    circleMap z₀ ρ θ ∈ closedTruncatedSector z₀ r R θ₁ θ₂ :=
  mem_closedTruncatedSector.2 ⟨ρ, hρ, θ, hθ, rfl⟩

/-- A polar point `circleMap z₀ ρ θ` with `ρ ∈ (r, R)` and `θ ∈ (θ₁, θ₂)` belongs to the open
truncated sector. -/
theorem circleMap_mem_openTruncatedSector {ρ θ : ℝ} (hρ : ρ ∈ Ioo r R) (hθ : θ ∈ Ioo θ₁ θ₂) :
    circleMap z₀ ρ θ ∈ openTruncatedSector z₀ r R θ₁ θ₂ :=
  mem_openTruncatedSector.2 ⟨ρ, hρ, θ, hθ, rfl⟩

/-- The open truncated sector is contained in the closed truncated sector. -/
theorem openTruncatedSector_subset_closedTruncatedSector (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    openTruncatedSector z₀ r R θ₁ θ₂ ⊆ closedTruncatedSector z₀ r R θ₁ θ₂ :=
  image_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-- Enlarging the radial and angular intervals enlarges the closed truncated sector. -/
theorem closedTruncatedSector_mono {r' R' θ₁' θ₂' : ℝ} (hr : r' ≤ r) (hR : R ≤ R')
    (hθ₁ : θ₁' ≤ θ₁) (hθ₂ : θ₂ ≤ θ₂') :
    closedTruncatedSector z₀ r R θ₁ θ₂ ⊆ closedTruncatedSector z₀ r' R' θ₁' θ₂' :=
  image_mono (prod_mono (Icc_subset_Icc hr hR) (Icc_subset_Icc hθ₁ hθ₂))

/-- Enlarging the radial and angular intervals enlarges the open truncated sector. -/
theorem openTruncatedSector_mono {r' R' θ₁' θ₂' : ℝ} (hr : r' ≤ r) (hR : R ≤ R')
    (hθ₁ : θ₁' ≤ θ₁) (hθ₂ : θ₂ ≤ θ₂') :
    openTruncatedSector z₀ r R θ₁ θ₂ ⊆ openTruncatedSector z₀ r' R' θ₁' θ₂' :=
  image_mono (prod_mono (Ioo_subset_Ioo hr hR) (Ioo_subset_Ioo hθ₁ hθ₂))

/-- The closed truncated sector is nonempty if and only if `r ≤ R` and `θ₁ ≤ θ₂`. -/
@[simp]
theorem closedTruncatedSector_nonempty :
    (closedTruncatedSector z₀ r R θ₁ θ₂).Nonempty ↔ r ≤ R ∧ θ₁ ≤ θ₂ := by
  rw [closedTruncatedSector, image_nonempty, prod_nonempty_iff, nonempty_Icc, nonempty_Icc]

/-- The open truncated sector is nonempty if and only if `r < R` and `θ₁ < θ₂`. -/
@[simp]
theorem openTruncatedSector_nonempty :
    (openTruncatedSector z₀ r R θ₁ θ₂).Nonempty ↔ r < R ∧ θ₁ < θ₂ := by
  rw [openTruncatedSector, image_nonempty, prod_nonempty_iff, nonempty_Ioo, nonempty_Ioo]

/-! ### Polar uniqueness, norm bounds, and `Complex.arg` characterizations -/

/-- Polar coordinates around `z₀` determine a positive radius and an angle within `2π`: if
`0 < ρ₁`, `0 ≤ ρ₂`, `|φ₁ - φ₂| < 2π` and `circleMap z₀ ρ₁ φ₁ = circleMap z₀ ρ₂ φ₂`, then
`ρ₁ = ρ₂` and `φ₁ = φ₂`. -/
theorem eq_and_eq_of_circleMap_eq {ρ₁ ρ₂ φ₁ φ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hφ : |φ₁ - φ₂| < 2 * Real.pi) (h : circleMap z₀ ρ₁ φ₁ = circleMap z₀ ρ₂ φ₂) :
    ρ₁ = ρ₂ ∧ φ₁ = φ₂ := by
  have hnorm : ‖circleMap z₀ ρ₁ φ₁ - z₀‖ = ‖circleMap z₀ ρ₂ φ₂ - z₀‖ := by rw [h]
  rw [circleMap_sub_center, circleMap_sub_center, norm_circleMap_zero, norm_circleMap_zero,
    abs_of_pos hρ₁, abs_of_nonneg hρ₂] at hnorm
  subst hnorm
  exact ⟨rfl, eq_of_circleMap_eq hρ₁.ne' hφ h⟩

/-- Every point of `closedTruncatedSector z₀ r R θ₁ θ₂` with `0 ≤ r` has distance to `z₀` in
`[r, R]`. -/
theorem norm_sub_mem_Icc_of_mem_closedTruncatedSector (hr : 0 ≤ r)
    (hz : z ∈ closedTruncatedSector z₀ r R θ₁ θ₂) : ‖z - z₀‖ ∈ Icc r R := by
  obtain ⟨ρ, hρ, θ, -, rfl⟩ := mem_closedTruncatedSector.1 hz
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg (hr.trans hρ.1)]
  exact hρ

/-- Every point of `openTruncatedSector z₀ r R θ₁ θ₂` with `0 ≤ r` has distance to `z₀` in
`(r, R)`. -/
theorem norm_sub_mem_Ioo_of_mem_openTruncatedSector (hr : 0 ≤ r)
    (hz : z ∈ openTruncatedSector z₀ r R θ₁ θ₂) : ‖z - z₀‖ ∈ Ioo r R := by
  obtain ⟨ρ, hρ, θ, -, rfl⟩ := mem_openTruncatedSector.1 hz
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos (hr.trans_lt hρ.1)]
  exact hρ

/-- For `0 < ρ` and `θ ∈ (-π, π]`, the principal argument of `circleMap z₀ ρ θ - z₀` is `θ`. -/
theorem arg_circleMap_sub {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    arg (circleMap z₀ ρ θ - z₀) = θ := by
  rw [circleMap_sub_center, circleMap_zero, arg_real_mul _ hρ, arg_exp_mul_I,
    (toIocMod_eq_self Real.two_pi_pos).2 ⟨hθ.1, by linarith [hθ.2]⟩]

/-- When `0 ≤ r` and `[θ₁, θ₂] ⊆ [-π, π]`, the open truncated sector is cut out by strict bounds
on `‖z - z₀‖` and `arg (z - z₀)`. Even at the endpoints `θ₁ = -π` or `θ₂ = π` no branch-cut defect
arises because strict inequalities confine `θ` to `(-π, π)`. -/
theorem openTruncatedSector_eq_norm_arg (hr : 0 ≤ r) (hθ₁ : -Real.pi ≤ θ₁) (hθ₂ : θ₂ ≤ Real.pi) :
    openTruncatedSector z₀ r R θ₁ θ₂ =
      {z : ℂ | r < ‖z - z₀‖ ∧ ‖z - z₀‖ < R ∧ θ₁ < arg (z - z₀) ∧ arg (z - z₀) < θ₂} := by
  ext w
  rw [mem_openTruncatedSector, mem_ofPred]
  constructor
  · rintro ⟨ρ, hρ, θ, hθ, rfl⟩
    have hρ₀ : 0 < ρ := hr.trans_lt hρ.1
    rw [arg_circleMap_sub hρ₀ ⟨hθ₁.trans_lt hθ.1, (hθ.2.trans_le hθ₂).le⟩, circleMap_sub_center,
      norm_circleMap_zero, abs_of_pos hρ₀]
    exact ⟨hρ.1, hρ.2, hθ.1, hθ.2⟩
  · rintro ⟨hrw, hwR, h1, h2⟩
    refine ⟨‖w - z₀‖, ⟨hrw, hwR⟩, arg (w - z₀), ⟨h1, h2⟩, ?_⟩
    simp only [circleMap, norm_mul_exp_arg_mul_I, add_sub_cancel]

/-- Origin-centred specialization of `Complex.openTruncatedSector_eq_norm_arg`. -/
theorem openTruncatedSector_zero_eq_norm_arg (hr : 0 ≤ r) (hθ₁ : -Real.pi ≤ θ₁)
    (hθ₂ : θ₂ ≤ Real.pi) :
    openTruncatedSector 0 r R θ₁ θ₂ =
      {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R ∧ θ₁ < arg z ∧ arg z < θ₂} := by
  simpa using openTruncatedSector_eq_norm_arg (z₀ := 0) hr hθ₁ hθ₂

/-- When `0 < r` and `[θ₁, θ₂] ⊆ (-π, π]`, the closed truncated sector is cut out by nonstrict
bounds on `‖z - z₀‖` and `arg (z - z₀)`. Both `0 < r` and `-π < θ₁` are needed: `arg 0 = 0` and
`arg (-ρ) = π` for `0 < ρ`. -/
theorem closedTruncatedSector_eq_norm_arg (hr : 0 < r) (hθ₁ : -Real.pi < θ₁)
    (hθ₂ : θ₂ ≤ Real.pi) :
    closedTruncatedSector z₀ r R θ₁ θ₂ =
      {z : ℂ | r ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ R ∧ θ₁ ≤ arg (z - z₀) ∧ arg (z - z₀) ≤ θ₂} := by
  ext w
  rw [mem_closedTruncatedSector, mem_ofPred]
  constructor
  · rintro ⟨ρ, hρ, θ, hθ, rfl⟩
    have hρ₀ : 0 < ρ := hr.trans_le hρ.1
    rw [arg_circleMap_sub hρ₀ ⟨hθ₁.trans_le hθ.1, hθ.2.trans hθ₂⟩, circleMap_sub_center,
      norm_circleMap_zero, abs_of_pos hρ₀]
    exact ⟨hρ.1, hρ.2, hθ.1, hθ.2⟩
  · rintro ⟨hrw, hwR, h1, h2⟩
    refine ⟨‖w - z₀‖, ⟨hrw, hwR⟩, arg (w - z₀), ⟨h1, h2⟩, ?_⟩
    simp only [circleMap, norm_mul_exp_arg_mul_I, add_sub_cancel]

/-- Origin-centred specialization of `Complex.closedTruncatedSector_eq_norm_arg`. -/
theorem closedTruncatedSector_zero_eq_norm_arg (hr : 0 < r) (hθ₁ : -Real.pi < θ₁)
    (hθ₂ : θ₂ ≤ Real.pi) :
    closedTruncatedSector 0 r R θ₁ θ₂ =
      {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R ∧ θ₁ ≤ arg z ∧ arg z ≤ θ₂} := by
  simpa using closedTruncatedSector_eq_norm_arg (z₀ := 0) hr hθ₁ hθ₂

/-- An origin-centred closed truncated sector with `0 < r` and `[θ₁, θ₂] ⊆ (-π, π)` lies in the
slit plane. -/
theorem closedTruncatedSector_zero_subset_slitPlane (hr : 0 < r) (hθ₁ : -Real.pi < θ₁)
    (hθ₂ : θ₂ < Real.pi) :
    closedTruncatedSector 0 r R θ₁ θ₂ ⊆ slitPlane := by
  rw [closedTruncatedSector_zero_eq_norm_arg hr hθ₁ hθ₂.le]
  rintro z ⟨hrz, -, -, hz₂⟩
  exact mem_slitPlane_iff_arg.2 ⟨(hz₂.trans_lt hθ₂).ne, norm_pos_iff.1 (hr.trans_le hrz)⟩

/-- For `0 < r ≤ R` and `θ₁ ≤ θ₂`, the translated exponential `s ↦ z₀ + exp s` maps the closed
rectangle `Rectangle (log r + θ₁ * I) (log R + θ₂ * I)` onto the closed truncated sector
`closedTruncatedSector z₀ r R θ₁ θ₂`. -/
theorem image_add_exp_rectangle_eq_closedTruncatedSector (hr : 0 < r) (hrR : r ≤ R)
    (hθ : θ₁ ≤ θ₂) :
    (fun s : ℂ ↦ z₀ + exp s) ''
        Rectangle ((Real.log r : ℂ) + θ₁ * I) ((Real.log R : ℂ) + θ₂ * I) =
      closedTruncatedSector z₀ r R θ₁ θ₂ := by
  have hlog : Real.log r ≤ Real.log R := Real.log_le_log hr hrR
  ext z
  rw [mem_image, mem_closedTruncatedSector]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [mem_rectangle_iff (by simpa using hlog) (by simpa using hθ)] at hs
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hs
    refine ⟨Real.exp s.re, ⟨?_, ?_⟩, s.im, hs.2, ?_⟩
    · simpa [Real.exp_log hr] using Real.exp_le_exp.2 hs.1.1
    · simpa [Real.exp_log (hr.trans_le hrR)] using Real.exp_le_exp.2 hs.1.2
    · rw [← re_add_im s, exp_add]
      simp [circleMap, ofReal_exp]
  · rintro ⟨ρ, hρ, θ, hθ', rfl⟩
    have hρ₀ : 0 < ρ := hr.trans_le hρ.1
    refine ⟨(Real.log ρ : ℂ) + θ * I, ?_, ?_⟩
    · rw [mem_rectangle_iff (by simpa using hlog) (by simpa using hθ)]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add]
      exact ⟨⟨Real.log_le_log hr hρ.1, Real.log_le_log hρ₀ hρ.2⟩, hθ'⟩
    · rw [exp_add, ← ofReal_exp, Real.exp_log hρ₀]
      rfl

/-! ### Topological properties: compactness, openness, closure, interior, and frontier -/

private theorem continuous_uncurry_circleMap (z₀ : ℂ) :
    Continuous (Function.uncurry (circleMap z₀)) := by
  unfold Function.uncurry circleMap
  fun_prop

/-- The closed truncated sector is compact. -/
theorem isCompact_closedTruncatedSector (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    IsCompact (closedTruncatedSector z₀ r R θ₁ θ₂) :=
  (isCompact_Icc.prod isCompact_Icc).image (continuous_uncurry_circleMap z₀)

/-- The closed truncated sector is closed. -/
theorem isClosed_closedTruncatedSector (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    IsClosed (closedTruncatedSector z₀ r R θ₁ θ₂) :=
  (isCompact_closedTruncatedSector z₀ r R θ₁ θ₂).isClosed

/-- The closed truncated sector is preconnected. -/
theorem isPreconnected_closedTruncatedSector (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    IsPreconnected (closedTruncatedSector z₀ r R θ₁ θ₂) :=
  (isPreconnected_Icc.prod isPreconnected_Icc).image _
    (continuous_uncurry_circleMap z₀).continuousOn

/-- The open truncated sector is preconnected. -/
theorem isPreconnected_openTruncatedSector (z₀ : ℂ) (r R θ₁ θ₂ : ℝ) :
    IsPreconnected (openTruncatedSector z₀ r R θ₁ θ₂) :=
  (isPreconnected_Ioo.prod isPreconnected_Ioo).image _
    (continuous_uncurry_circleMap z₀).continuousOn

/-- For `0 ≤ r`, the open truncated sector is an open set in `ℂ`. Neither `r < R` nor
`θ₂ - θ₁ < 2π` is required: every point of `Ioo r R` is strictly positive, so the open truncated
sector is the image under the open map `s ↦ z₀ + exp s` of an open set in `ℂ`. -/
theorem isOpen_openTruncatedSector (hr : 0 ≤ r) :
    IsOpen (openTruncatedSector z₀ r R θ₁ θ₂) := by
  have heq : openTruncatedSector z₀ r R θ₁ θ₂ =
      (fun s : ℂ ↦ z₀ + exp s) '' {s : ℂ | Real.exp s.re ∈ Ioo r R ∧ s.im ∈ Ioo θ₁ θ₂} := by
    ext z
    rw [mem_openTruncatedSector, mem_image]
    constructor
    · rintro ⟨ρ, hρ, θ, hθ, rfl⟩
      have hρ₀ : 0 < ρ := hr.trans_lt hρ.1
      refine ⟨(Real.log ρ : ℂ) + θ * I, ?_, ?_⟩
      · simpa [Real.exp_log hρ₀] using ⟨hρ, hθ⟩
      · rw [exp_add, ← ofReal_exp, Real.exp_log hρ₀]
        rfl
    · rintro ⟨s, ⟨hre, him⟩, rfl⟩
      refine ⟨Real.exp s.re, hre, s.im, him, ?_⟩
      rw [← re_add_im s, exp_add]
      simp [circleMap, ofReal_exp]
  rw [heq]
  exact ((isOpenMap_add_left z₀).comp isOpenMap_exp) _
    ((isOpen_Ioo.preimage (Real.continuous_exp.comp continuous_re)).inter
      (isOpen_Ioo.preimage continuous_im))

/-- When `r < R` and `θ₁ < θ₂`, the closure of the open truncated sector is the closed truncated
sector. -/
theorem closure_openTruncatedSector (hrR : r < R) (hθ : θ₁ < θ₂) :
    closure (openTruncatedSector z₀ r R θ₁ θ₂) = closedTruncatedSector z₀ r R θ₁ θ₂ := by
  have hcl : closure (Ioo r R ×ˢ Ioo θ₁ θ₂) = Icc r R ×ˢ Icc θ₁ θ₂ := by
    rw [closure_prod_eq, closure_Ioo hrR.ne, closure_Ioo hθ.ne]
  rw [openTruncatedSector_def, closedTruncatedSector_def, ← hcl]
  exact (image_closure_of_isCompact
    (hcl ▸ (isCompact_Icc.prod isCompact_Icc))
    (continuous_uncurry_circleMap z₀).continuousOn).symm

/-- A point on the parameter-boundary image of a non-wrapping truncated sector cannot lie in the
open truncated sector. -/
private theorem disjoint_openTruncatedSector_boundary (hr : 0 ≤ r)
    (hspan : θ₂ - θ₁ < 2 * Real.pi) :
    Disjoint (openTruncatedSector z₀ r R θ₁ θ₂)
      (Function.uncurry (circleMap z₀) '' (Icc r R ×ˢ {θ₁, θ₂} ∪ {r, R} ×ˢ Icc θ₁ θ₂)) := by
  refine disjoint_left.2 ?_
  rintro _ ⟨⟨ρ₀, φ₀⟩, ⟨hρ₀, hφ₀⟩, rfl⟩ ⟨⟨ρ₁, φ₁⟩, hb, heq⟩
  simp only [Function.uncurry_apply_pair] at heq
  have hρ₀_pos : 0 < ρ₀ := hr.trans_lt hρ₀.1
  rcases hb with ⟨hρ₁, hφ₁⟩ | ⟨hρ₁, -⟩
  · have ⟨_, hφeq⟩ := eq_and_eq_of_circleMap_eq hρ₀_pos (hr.trans hρ₁.1)
      (by rcases hφ₁ with rfl | rfl <;>
        exact abs_lt.2 ⟨by linarith [hφ₀.1, hφ₀.2], by linarith [hφ₀.1, hφ₀.2]⟩) heq.symm
    rcases hφ₁ with rfl | rfl
    · exact hφ₀.1.ne' hφeq
    · exact hφ₀.2.ne hφeq
  · have hnorm : ρ₁ = ρ₀ := by
      have h : ‖circleMap z₀ ρ₁ φ₁ - z₀‖ = ‖circleMap z₀ ρ₀ φ₀ - z₀‖ := by rw [heq]
      have hρ₁_nonneg : 0 ≤ ρ₁ := by
        rcases hρ₁ with rfl | rfl
        · exact hr
        · exact hr.trans (hρ₀.1.trans hρ₀.2).le
      simpa [circleMap_sub_center, abs_of_pos hρ₀_pos, abs_of_nonneg hρ₁_nonneg] using h
    rcases hρ₁ with rfl | rfl
    · exact hρ₀.1.ne hnorm
    · exact hρ₀.2.ne' hnorm

/-- No point on the parameter-boundary image of a non-wrapping truncated sector lies in the
topological interior of the closed truncated sector: small radial or angular perturbations escape
the sector. -/
private theorem notMem_interior_closedTruncatedSector_of_boundary (hr : 0 ≤ r) (hrR : r ≤ R)
    (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * Real.pi) {ρ₁ φ₁ : ℝ}
    (hb : (ρ₁, φ₁) ∈ Icc r R ×ˢ ({θ₁, θ₂} : Set ℝ) ∪ ({r, R} : Set ℝ) ×ˢ Icc θ₁ θ₂) :
    circleMap z₀ ρ₁ φ₁ ∉ interior (closedTruncatedSector z₀ r R θ₁ θ₂) := by
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hρ₁_mem : ρ₁ ∈ Icc r R := by
    rcases hb with ⟨h, -⟩ | ⟨rfl | rfl, -⟩
    · exact h
    · exact ⟨le_rfl, hrR⟩
    · exact ⟨hrR, le_rfl⟩
  -- Case 1: outer arc `ρ₁ = R` — step radially outward by `ε / 2`.
  by_cases hR : ρ₁ = R
  · subst ρ₁
    have hmem : circleMap z₀ (R + ε / 2) φ₁ ∈ closedTruncatedSector z₀ r R θ₁ θ₂ := by
      refine hball (mem_ball.2 ?_)
      have hd : circleMap z₀ (R + ε / 2) φ₁ - circleMap z₀ R φ₁ =
          ((ε / 2 : ℝ) : ℂ) * exp (φ₁ * I) := by
        simp [circleMap]; ring
      rw [dist_eq_norm, hd, norm_mul, norm_real, norm_exp_ofReal_mul_I, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith
    have hnorm := (norm_sub_mem_Icc_of_mem_closedTruncatedSector hr hmem).2
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos (by linarith [hr.trans hrR])] at hnorm
    linarith
  -- Case 2: inner arc `ρ₁ = r` with `0 < r` — step radially inward by `min (ε / 2) (r / 2)`.
  by_cases hr_eq : ρ₁ = r ∧ 0 < r
  · obtain ⟨hρr, hr_pos⟩ := hr_eq
    subst ρ₁
    set δ := min (ε / 2) (r / 2)
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have hmem : circleMap z₀ (r - δ) φ₁ ∈ closedTruncatedSector z₀ r R θ₁ θ₂ := by
      refine hball (mem_ball.2 ?_)
      have hd : circleMap z₀ (r - δ) φ₁ - circleMap z₀ r φ₁ = -((δ : ℝ) : ℂ) * exp (φ₁ * I) := by
        simp [circleMap]; ring
      rw [dist_eq_norm, hd, norm_mul, norm_neg, norm_real, norm_exp_ofReal_mul_I, mul_one,
        Real.norm_of_nonneg hδ.le]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hnorm := (norm_sub_mem_Icc_of_mem_closedTruncatedSector hr hmem).1
    rw [circleMap_sub_center, norm_circleMap_zero,
      abs_of_nonneg (by linarith [min_le_right (ε / 2) (r / 2)])] at hnorm
    linarith
  -- Case 3: vertex `ρ₁ = 0` — step in the opposite direction `(θ₁ + θ₂) / 2 + π`.
  by_cases h0 : ρ₁ = 0
  · subst ρ₁
    set ψ := (θ₁ + θ₂) / 2 + Real.pi with hψ
    have hmem : circleMap z₀ (ε / 2) ψ ∈ closedTruncatedSector z₀ r R θ₁ θ₂ := by
      refine hball (mem_ball.2 ?_)
      rw [circleMap_zero_radius, Function.const_apply, dist_eq_norm, circleMap_sub_center,
        norm_circleMap_zero, abs_of_pos (by positivity)]
      linarith
    obtain ⟨ρ₂, hρ₂, φ₂, hφ₂, heq⟩ := mem_closedTruncatedSector.1 hmem
    have ⟨_, hφeq⟩ := eq_and_eq_of_circleMap_eq (by positivity : 0 < ε / 2) (hr.trans hρ₂.1)
      (abs_lt.2 ⟨by linarith [hψ, hφ₂.1, hφ₂.2, Real.pi_pos],
        by linarith [hψ, hφ₂.1, hφ₂.2]⟩) heq.symm
    linarith [hψ, hφ₂.2, hφeq]
  -- Case 4: `0 < ρ₁ < R` and `ρ₁ ≠ r`, so `(ρ₁, φ₁)` lies on one of the two rays `φ₁ ∈ {θ₁, θ₂}`.
  have hρ₁_pos : 0 < ρ₁ := lt_of_le_of_ne (hr.trans hρ₁_mem.1) (Ne.symm h0)
  have hφ_ray : φ₁ = θ₁ ∨ φ₁ = θ₂ := by
    rcases hb with ⟨-, hφ⟩ | ⟨hρ | hρ, -⟩
    · exact hφ
    · exact (hr_eq ⟨hρ, hρ ▸ hρ₁_pos⟩).elim
    · exact (hR hρ).elim
  set η := (2 * Real.pi - (θ₂ - θ₁)) / 2 with hη_def
  have hη : 0 < η := by positivity
  rcases hφ_ray with hφ₁ | hφ₁
  · -- Perturb below `θ₁`.
    subst φ₁
    have hcont : Continuous fun t : ℝ ↦ circleMap z₀ ρ₁ (θ₁ - t) := by unfold circleMap; fun_prop
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        circleMap z₀ ρ₁ (θ₁ - t) ∈ ball (circleMap z₀ ρ₁ θ₁) ε :=
      nhdsWithin_le_nhds
        ((hcont.continuousAt (x := 0)).preimage_mem_nhds (by simpa using ball_mem_nhds _ hε))
    obtain ⟨t, ht_ball, ht_Ioo⟩ := (hev.and (Ioo_mem_nhdsGT hη)).exists
    obtain ⟨ρ₂, hρ₂, φ₂, hφ₂, heq⟩ := mem_closedTruncatedSector.1 (hball ht_ball)
    have ⟨_, hφeq⟩ := eq_and_eq_of_circleMap_eq hρ₁_pos (hr.trans hρ₂.1)
      (abs_lt.2 ⟨by linarith [hη_def, hφ₂.1, hφ₂.2, ht_Ioo.1, ht_Ioo.2],
        by linarith [hη_def, hφ₂.1, hφ₂.2, ht_Ioo.1, ht_Ioo.2]⟩) heq.symm
    linarith [hφ₂.1, ht_Ioo.1]
  · -- Perturb above `θ₂`.
    subst φ₁
    have hcont : Continuous fun t : ℝ ↦ circleMap z₀ ρ₁ (θ₂ + t) := by unfold circleMap; fun_prop
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        circleMap z₀ ρ₁ (θ₂ + t) ∈ ball (circleMap z₀ ρ₁ θ₂) ε :=
      nhdsWithin_le_nhds
        ((hcont.continuousAt (x := 0)).preimage_mem_nhds (by simpa using ball_mem_nhds _ hε))
    obtain ⟨t, ht_ball, ht_Ioo⟩ := (hev.and (Ioo_mem_nhdsGT hη)).exists
    obtain ⟨ρ₂, hρ₂, φ₂, hφ₂, heq⟩ := mem_closedTruncatedSector.1 (hball ht_ball)
    have ⟨_, hφeq⟩ := eq_and_eq_of_circleMap_eq hρ₁_pos (hr.trans hρ₂.1)
      (abs_lt.2 ⟨by linarith [hη_def, hφ₂.1, hφ₂.2, ht_Ioo.1, ht_Ioo.2],
        by linarith [hη_def, hφ₂.1, hφ₂.2, ht_Ioo.1, ht_Ioo.2]⟩) heq.symm
    linarith [hφ₂.2, ht_Ioo.1]

private theorem closedTruncatedSector_eq_open_union_boundary (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂) :
    closedTruncatedSector z₀ r R θ₁ θ₂ =
      openTruncatedSector z₀ r R θ₁ θ₂ ∪
        Function.uncurry (circleMap z₀) '' (Icc r R ×ˢ {θ₁, θ₂} ∪ {r, R} ×ˢ Icc θ₁ θ₂) := by
  rw [closedTruncatedSector_def, openTruncatedSector_def, ← image_union]
  congr 1
  ext ⟨ρ, φ⟩
  simp only [mem_prod, mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact Or.inr (Or.inr ⟨Or.inl rfl, h3, h4⟩)
    rcases eq_or_lt_of_le h2 with rfl | h2'
    · exact Or.inr (Or.inr ⟨Or.inr rfl, h3, h4⟩)
    rcases eq_or_lt_of_le h3 with rfl | h3'
    · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, Or.inl rfl⟩)
    rcases eq_or_lt_of_le h4 with rfl | h4'
    · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, Or.inr rfl⟩)
    exact Or.inl ⟨⟨h1', h2'⟩, ⟨h3', h4'⟩⟩
  · rintro (⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ | ⟨hρ, rfl | rfl⟩ | ⟨rfl | rfl, hφ⟩)
    · exact ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩
    · exact ⟨hρ, le_rfl, hθ⟩
    · exact ⟨hρ, hθ, le_rfl⟩
    · exact ⟨⟨le_rfl, hrR⟩, hφ⟩
    · exact ⟨⟨hrR, le_rfl⟩, hφ⟩

/-- For `0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π`, the interior of the closed truncated sector is the open
truncated sector. This covers both genuinely truncated sectors (`0 < r`) and full sectors (`r = 0`),
as well as degenerate arcs or segments (`r = R` or `θ₁ = θ₂`, where both sides are empty). -/
theorem interior_closedTruncatedSector (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂)
    (hspan : θ₂ - θ₁ < 2 * Real.pi) :
    interior (closedTruncatedSector z₀ r R θ₁ θ₂) = openTruncatedSector z₀ r R θ₁ θ₂ := by
  refine Subset.antisymm ?_
    ((isOpen_openTruncatedSector hr).subset_interior_iff.2
      (openTruncatedSector_subset_closedTruncatedSector z₀ r R θ₁ θ₂))
  intro z hz
  rcases (closedTruncatedSector_eq_open_union_boundary hrR hθ ▸ interior_subset hz) with
    hzO | ⟨⟨ρ₁, φ₁⟩, hb, rfl⟩
  · exact hzO
  · exact (notMem_interior_closedTruncatedSector_of_boundary hr hrR hθ hspan hb hz).elim

/-- For `0 ≤ r ≤ R` and `0 ≤ θ₂ - θ₁ < 2π`, the frontier of the closed truncated sector is the
union of its two radial segments at `θ₁`, `θ₂` and its two circular arcs at radii `r`, `R`. -/
theorem frontier_closedTruncatedSector (hr : 0 ≤ r) (hrR : r ≤ R) (hθ : θ₁ ≤ θ₂)
    (hspan : θ₂ - θ₁ < 2 * Real.pi) :
    frontier (closedTruncatedSector z₀ r R θ₁ θ₂) =
      Function.uncurry (circleMap z₀) '' (Icc r R ×ˢ {θ₁, θ₂} ∪ {r, R} ×ˢ Icc θ₁ θ₂) := by
  rw [frontier, (isClosed_closedTruncatedSector z₀ r R θ₁ θ₂).closure_eq,
    interior_closedTruncatedSector hr hrR hθ hspan,
    closedTruncatedSector_eq_open_union_boundary hrR hθ, union_sdiff_left]
  exact (disjoint_openTruncatedSector_boundary hr hspan).symm.sdiff_eq_left

/-- A point of the closed truncated sector that is not on its frontier lies in the open truncated
sector. -/
theorem mem_openTruncatedSector_of_mem_closedTruncatedSector (hr : 0 ≤ r) (hrR : r ≤ R)
    (hθ : θ₁ ≤ θ₂) (hspan : θ₂ - θ₁ < 2 * Real.pi)
    {s : ℂ} (hs : s ∈ closedTruncatedSector z₀ r R θ₁ θ₂)
    (hfr : s ∉ frontier (closedTruncatedSector z₀ r R θ₁ θ₂)) :
    s ∈ openTruncatedSector z₀ r R θ₁ θ₂ := by
  rw [← interior_closedTruncatedSector hr hrR hθ hspan, ← self_sdiff_frontier]
  exact ⟨hs, hfr⟩

end Complex
