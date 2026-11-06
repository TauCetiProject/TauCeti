/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Radial normalization of positively homogeneous maps

Let `L : E → F` be a continuous, positively homogeneous map (`L (c • v) = c • L v` for `c ≥ 0`)
out of a finite-dimensional real normed space, vanishing only at the origin; injective positively
homogeneous maps are the main example. Such a map is the cone on its restriction
to the unit sphere, but that restriction need not land in the unit sphere of `F`: along each ray
`L` stretches norms by a factor `‖L u‖ > 0` depending on the direction `u`. This file removes that
stretching by a homeomorphism of the source. The radial rescaling `v ↦ (‖L v‖ / ‖v‖) • v` moves
every point along its own ray, commutes with nonnegative scalars and turns `‖v‖` into `‖L v‖`, and
it is a homeomorphism of `E` (`Continuous.exists_homeomorph_norm_eq`). Composed with its inverse,
`L` becomes positively homogeneous and norm-preserving, that is, the cone `w ↦ ‖w‖ • γ (‖w‖⁻¹ • w)`
over a map `γ` from the unit sphere of `E` to the unit sphere of `F`, the *link* of `L`.

Mathlib's `gaugeRescaleHomeomorph` rescales rays in the same way by the ratio of the gauges of two
convex bodies. It does not apply here: `‖L v‖` is the gauge of `{v | ‖L v‖ ≤ 1}`, which need not be
convex when `L` is only piecewise linear.

Continuity of the inverse at the origin is where finite dimension enters: on the compact unit
sphere `‖L u‖` is bounded below by a positive constant, so `‖L v‖` is at least a positive multiple
of `‖v‖` (`Continuous.exists_pos_mul_norm_le`).

The positively homogeneous injective maps of interest are the conical germs of piecewise-linear
embeddings (`TauCeti.IsPLWithinAt.exists_eventually_eq_add_homogeneous`): after the normalization
here, such a germ is the cone over its link, and questions such as local flatness at a point are
questions about that cone.

## Main results

* `Continuous.exists_pos_mul_norm_le`: such a map stretches norms by at least a positive factor.
* `Continuous.exists_homeomorph_norm_eq`: such a map `L` admits a homeomorphism `σ` of the source
  which commutes with nonnegative scalars, maps every vector into its own ray, and satisfies
  `‖σ v‖ = ‖L v‖`.
-/

public section

open Set Filter Topology Metric

namespace Continuous

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {L : E → F}

/-- A continuous positively homogeneous map out of a finite-dimensional real normed space,
vanishing only at the origin, stretches norms by at least a fixed positive factor: the minimum
of `‖L u‖` over the compact unit sphere. -/
theorem exists_pos_mul_norm_le (hL : Continuous L) (hne : ∀ v, v ≠ 0 → L v ≠ 0)
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ v, L (c • v) = c • L v) :
    ∃ m > 0, ∀ v, m * ‖v‖ ≤ ‖L v‖ := by
  have hL0 : L 0 = 0 := by simpa using hhom 0 le_rfl 0
  rcases (sphere (0 : E) 1).eq_empty_or_nonempty with hS | hS
  · -- The unit sphere is empty only for the zero space.
    refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by simp [norm_smul, hv]
      simp [hS] at this
    simp [hv]
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hS
    (continuous_norm.comp hL).continuousOn
  have hpos : 0 < ‖L u₀‖ :=
    norm_pos_iff.2 (hne u₀ (ne_zero_of_mem_sphere one_ne_zero ⟨u₀, hu₀⟩))
  refine ⟨‖L u₀‖, hpos, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [hL0]
  have hu : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by simp [norm_smul, hv]
  have hLv : ‖L v‖ = ‖v‖ * ‖L (‖v‖⁻¹ • v)‖ := by
    rw [hhom _ (inv_nonneg.2 (norm_nonneg v)), norm_smul, norm_inv, norm_norm,
      mul_inv_cancel_left₀ (norm_ne_zero_iff.2 hv)]
  rw [hLv, mul_comm]
  exact mul_le_mul_of_nonneg_left (hmin hu) (norm_nonneg v)

omit [FiniteDimensional ℝ E] in
/-- The ratio `‖L v‖ / ‖v‖` is constant along open rays. -/
private theorem norm_map_div_norm_smul (hhom : ∀ c : ℝ, 0 ≤ c → ∀ v, L (c • v) = c • L v)
    {a : ℝ} (ha : 0 < a) (v : E) : ‖L (a • v)‖ / ‖a • v‖ = ‖L v‖ / ‖v‖ := by
  rw [hhom a ha.le, norm_smul, norm_smul, Real.norm_of_nonneg ha.le, mul_div_mul_left _ _ ha.ne']

omit [FiniteDimensional ℝ E] in
/-- The radial rescaling `σ v = (‖L v‖ / ‖v‖) • v` and `τ w = (‖w‖ / ‖L w‖) • w` are inverse to
each other. -/
private theorem radial_leftInverse_rightInverse (hne : ∀ v, v ≠ 0 → L v ≠ 0)
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ v, L (c • v) = c • L v) {σ τ : E → E}
    (hσ : ∀ v, σ v = (‖L v‖ / ‖v‖) • v) (hτ : ∀ w, τ w = (‖w‖ / ‖L w‖) • w) :
    Function.LeftInverse τ σ ∧ Function.RightInverse τ σ := by
  have hpos {v : E} (hv : v ≠ 0) : 0 < ‖L v‖ := norm_pos_iff.2 (hne v hv)
  have hray {a : ℝ} (ha : 0 < a) (v : E) : ‖a • v‖ / ‖L (a • v)‖ = ‖v‖ / ‖L v‖ := by
    rw [← inv_div, norm_map_div_norm_smul hhom ha, inv_div]
  constructor
  · intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp [hσ, hτ]
    rw [hτ, hσ]
    have h : ‖v‖ / ‖L v‖ * (‖L v‖ / ‖v‖) = 1 := by
      field_simp [norm_ne_zero_iff.2 hv, (hpos hv).ne']
    rw [hray (div_pos (hpos hv) (norm_pos_iff.2 hv)), smul_smul, h, one_smul]
  · intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp [hσ, hτ]
    rw [hσ, hτ]
    have h : ‖L w‖ / ‖w‖ * (‖w‖ / ‖L w‖) = 1 := by
      field_simp [norm_ne_zero_iff.2 hw, (hpos hw).ne']
    rw [norm_map_div_norm_smul hhom (div_pos (norm_pos_iff.2 hw) (hpos hw)), smul_smul, h,
      one_smul]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- The radial rescaling `σ v = (‖L v‖ / ‖v‖) • v` turns `‖v‖` into `‖L v‖`. -/
private theorem norm_radial (hL0 : L 0 = 0) {σ : E → E}
    (hσ : ∀ v, σ v = (‖L v‖ / ‖v‖) • v) (v : E) : ‖σ v‖ = ‖L v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [hσ, hL0]
  rw [hσ, norm_smul, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv)]

omit [FiniteDimensional ℝ E] in
/-- The radial rescaling `σ v = (‖L v‖ / ‖v‖) • v` commutes with nonnegative scalars. -/
private theorem radial_smul (hhom : ∀ c : ℝ, 0 ≤ c → ∀ v, L (c • v) = c • L v) {σ : E → E}
    (hσ : ∀ v, σ v = (‖L v‖ / ‖v‖) • v) (c : ℝ) (hc : 0 ≤ c) (v : E) :
    σ (c • v) = c • σ v := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [hσ]
  rw [hσ, hσ, norm_map_div_norm_smul hhom hc, smul_comm]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- Continuity of the radial rescaling `σ v = (‖L v‖ / ‖v‖) • v`. Away from the origin it is that
of the formula; at the origin, `‖σ v‖ = ‖L v‖` tends to zero. -/
private theorem continuous_radial (hL : Continuous L) (hL0 : L 0 = 0) {σ : E → E}
    (hσ : ∀ v, σ v = (‖L v‖ / ‖v‖) • v) : Continuous σ := by
  refine continuous_iff_continuousAt.2 fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : σ 0 = 0 := by simp [hσ]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_radial hL0 hσ]
    simpa [hL0] using hL.norm.tendsto 0
  · rw [show σ = fun v => (‖L v‖ / ‖v‖) • v from funext hσ]
    exact (hL.norm.continuousAt.div continuous_norm.continuousAt
      (norm_ne_zero_iff.2 hv)).smul continuousAt_id

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- Continuity of `τ w = (‖w‖ / ‖L w‖) • w`, given a positive lower bound `‖L w‖ ≥ m * ‖w‖`.
At the origin, `‖τ w‖ ≤ m⁻¹ * ‖w‖` tends to zero. -/
private theorem continuous_radial_inv (hL : Continuous L) (hne : ∀ v, v ≠ 0 → L v ≠ 0) {m : ℝ}
    (hm : 0 < m) (hmL : ∀ w, m * ‖w‖ ≤ ‖L w‖) {τ : E → E}
    (hτ : ∀ w, τ w = (‖w‖ / ‖L w‖) • w) : Continuous τ := by
  have hpos {v : E} (hv : v ≠ 0) : 0 < ‖L v‖ := norm_pos_iff.2 (hne v hv)
  have hτle (w : E) : ‖τ w‖ ≤ m⁻¹ * ‖w‖ := by
    rcases eq_or_ne w 0 with rfl | hw
    · simp [hτ]
    rw [hτ, norm_smul, Real.norm_of_nonneg (div_pos (norm_pos_iff.2 hw) (hpos hw)).le,
      div_mul_eq_mul_div, div_le_iff₀ (hpos hw)]
    calc ‖w‖ * ‖w‖ = m⁻¹ * ‖w‖ * (m * ‖w‖) := by field_simp
      _ ≤ m⁻¹ * ‖w‖ * ‖L w‖ := by gcongr; exact hmL w
  refine continuous_iff_continuousAt.2 fun w => ?_
  rcases eq_or_ne w 0 with rfl | hw
  · have h0 : τ 0 = 0 := by simp [hτ]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hτle
      (by simpa using (tendsto_norm_zero (E := E)).const_mul m⁻¹)
  · rw [show τ = fun w => (‖w‖ / ‖L w‖) • w from funext hτ]
    exact (continuous_norm.continuousAt.div hL.norm.continuousAt (hpos hw).ne').smul
      continuousAt_id

/-- **Radial normalization.** Let `L : E → F` be continuous and positively homogeneous, vanishing
only at the origin, with `E` a finite-dimensional real normed space. Then some homeomorphism `σ`
of `E` commutes with nonnegative scalars, moves every vector `v` along its ray (`σ v = a • v` with
`a > 0`), and satisfies `‖σ v‖ = ‖L v‖`. Consequently `L ∘ σ.symm` is positively homogeneous and
preserves norms: it is the cone over a map from the unit sphere of `E` to the unit sphere of `F`. -/
theorem exists_homeomorph_norm_eq (hL : Continuous L) (hne : ∀ v, v ≠ 0 → L v ≠ 0)
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ v, L (c • v) = c • L v) :
    ∃ σ : E ≃ₜ E, (∀ c : ℝ, 0 ≤ c → ∀ v, σ (c • v) = c • σ v) ∧
      (∀ v, ∃ a : ℝ, 0 < a ∧ σ v = a • v) ∧ ∀ v, ‖σ v‖ = ‖L v‖ := by
  have hL0 : L 0 = 0 := by simpa using hhom 0 le_rfl 0
  obtain ⟨m, hm, hmL⟩ := hL.exists_pos_mul_norm_le hne hhom
  -- The rescaling `σ` and its inverse `τ` multiply each vector by a factor constant on its ray.
  let σ : E → E := fun v => (‖L v‖ / ‖v‖) • v
  let τ : E → E := fun w => (‖w‖ / ‖L w‖) • w
  have hσ : ∀ v, σ v = (‖L v‖ / ‖v‖) • v := fun _ => rfl
  have hτ : ∀ w, τ w = (‖w‖ / ‖L w‖) • w := fun _ => rfl
  obtain ⟨hτσ, hστ⟩ := radial_leftInverse_rightInverse hne hhom hσ hτ
  refine ⟨⟨⟨σ, τ, hτσ, hστ⟩, continuous_radial hL hL0 hσ,
    continuous_radial_inv hL hne hm hmL hτ⟩, radial_smul hhom hσ, fun v => ?_,
    norm_radial hL0 hσ⟩
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨1, one_pos, by simp [σ]⟩
  · exact ⟨_, div_pos (norm_pos_iff.2 (hne v hv)) (norm_pos_iff.2 hv), rfl⟩


end Continuous
