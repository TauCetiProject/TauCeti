/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Inner-product half-spaces

A translation orthogonal to the normal vector preserves a strict half-space. The ball of radius
`r` about a unit vector `x` lies in the half-space `{z | 1 - r ≤ ⟪x, z⟫}`. The projection
`z - (⟪z, ν⟫ / ‖ν‖²) ν` lands in the boundary hyperplane `{z | ⟪z, ν⟫ = 0}`. Relative to an
orthonormal basis `(eᵢ)`, a bilinear form splits into a part along `ν` and a part along the
projected basis vectors `eᵢ - (⟪eᵢ, ν⟫ / ‖ν‖²) ν`.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

/-- Every translation parallel to the boundary of the half-space `{x | c < ⟪x, ν⟫}` maps it into
itself. -/
theorem mapsTo_add_smul_of_halfSpace {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : Set E} {ν τ : E} {c : ℝ}
    (hΩ : ∀ x, x ∈ s ↔ c < ⟪x, ν⟫_ℝ) (hτ : ⟪τ, ν⟫_ℝ = 0) (t : ℝ) :
    Set.MapsTo (· + t • τ) s s := fun x hx => by
  have hx' := (hΩ x).1 hx
  exact (hΩ _).2 (by simpa [inner_add_left, real_inner_smul_left, hτ] using hx')

/-- The inner product of a unit vector `x` with `z` is at least `1 - ‖z - x‖`. -/
theorem one_sub_norm_sub_le_inner {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : ‖x‖ = 1) (z : E) : 1 - ‖z - x‖ ≤ ⟪x, z⟫_ℝ := by
  have h := real_inner_le_norm x (x - z)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hx, norm_sub_rev] at h
  linarith

/-- The projection `z - (⟪z, ν⟫ / ‖ν‖²) ν` onto the hyperplane orthogonal to `ν` is orthogonal
to `ν`. It is the explicit form of `z - (ℝ ∙ ν).starProjection z`, by
`Submodule.starProjection_singleton`. -/
theorem real_inner_sub_div_norm_sq_smul_self_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (z ν : E) : ⟪z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν, ν⟫_ℝ = 0 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ (pow_pos (norm_pos_iff.2 hν) 2).ne', sub_self]


/-- Splitting a bilinear form along `ν` and the hyperplane orthogonal to it: for an orthonormal
basis `(eᵢ)`,
`B(g, w) = ⟪g, ν⟫ ∑ⱼ B(ν', eⱼ) ⟪w, eⱼ⟫ + ∑ᵢ ∑ⱼ ⟪g, P eᵢ⟫ B(eᵢ, eⱼ) ⟪w, eⱼ⟫`, where
`ν' = ν / ‖ν‖²` and `P z = z - (⟪z, ν⟫ / ‖ν‖²) ν`. -/
theorem bilin_eq_inner_mul_sum_add_sum_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (ν g w : E) :
    B g w = ⟪g, ν⟫_ℝ * ∑ j, B ((‖ν‖ ^ 2)⁻¹ • ν) (b j) * ⟪w, b j⟫_ℝ +
      ∑ i, ∑ j, ⟪g, b i - (⟪b i, ν⟫_ℝ / ‖ν‖ ^ 2) • ν⟫_ℝ * (B (b i) (b j) * ⟪w, b j⟫_ℝ) := by
  have hw : ∀ p, B p w = ∑ j, B p (b j) * ⟪w, b j⟫_ℝ := fun p => by
    conv_lhs => rw [← b.sum_repr' w]
    simp only [map_sum, map_smul, smul_eq_mul, real_inner_comm, mul_comm]
  have hν : ∑ i, (⟪b i, ν⟫_ℝ / ‖ν‖ ^ 2 * ⟪g, ν⟫_ℝ) • b i = (⟪g, ν⟫_ℝ / ‖ν‖ ^ 2) • ν := by
    have h := congrArg (fun z => (⟪g, ν⟫_ℝ / ‖ν‖ ^ 2) • z) (b.sum_repr' ν)
    simp only [Finset.smul_sum, smul_smul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by congr 1; ring
  have hg : ⟪g, ν⟫_ℝ • (‖ν‖ ^ 2)⁻¹ • ν +
      ∑ i, ⟪g, b i - (⟪b i, ν⟫_ℝ / ‖ν‖ ^ 2) • ν⟫_ℝ • b i = g := by
    have hsum : ∑ i, ⟪g, b i⟫_ℝ • b i = g := by
      simpa only [real_inner_comm] using b.sum_repr' g
    simp only [inner_sub_right, real_inner_smul_right, sub_smul, Finset.sum_sub_distrib, hν]
    rw [hsum, smul_smul, div_eq_mul_inv]
    abel
  conv_lhs => rw [← hg]
  simp [hw, Finset.mul_sum, mul_assoc]

/-- **The normal part of a bilinear form.** For an orthonormal basis `(eᵢ)`, subtracting the
tangential parts `∑ⱼ B(ν', eⱼ) ⟪g, P eⱼ⟫` from `∑ⱼ B(ν', eⱼ) ⟪g, eⱼ⟫` leaves `B(ν', ν') ⟪g, ν⟫`,
where `ν' = ν / ‖ν‖²` and `P z = z - (⟪z, ν⟫ / ‖ν‖²) ν`. -/
theorem sum_smul_inner_sub_sum_smul_inner_proj {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) (ν g : E) :
    (∑ j, B ((‖ν‖ ^ 2)⁻¹ • ν) (b j) • ⟪g, b j⟫_ℝ) -
      ∑ j, B ((‖ν‖ ^ 2)⁻¹ • ν) (b j) • ⟪g, b j - (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2) • ν⟫_ℝ =
      B ((‖ν‖ ^ 2)⁻¹ • ν) ((‖ν‖ ^ 2)⁻¹ • ν) * ⟪g, ν⟫_ℝ := by
  set ν' : E := (‖ν‖ ^ 2)⁻¹ • ν
  have hν'sum : ∑ j, (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2) • b j = ν' := by
    simp only [ν', div_eq_inv_mul, ← smul_smul, ← Finset.smul_sum, b.sum_repr']
  have hν' : ∑ j, B ν' (b j) * (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2) = B ν' ν' := by
    calc ∑ j, B ν' (b j) * (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2)
        = B ν' (∑ j, (⟪b j, ν⟫_ℝ / ‖ν‖ ^ 2) • b j) := by
          simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
      _ = B ν' ν' := by rw [hν'sum]
  simp only [inner_sub_right, real_inner_smul_right, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [← hν', Finset.sum_mul]
  simp only [sub_sub_cancel]
  exact Finset.sum_congr rfl fun j _ => by ring

end TauCeti
