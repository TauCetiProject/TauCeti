/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Basic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.UnitInterval

/-!
# Circles on a sphere tangent to a direction

Let `p` and `u` be orthonormal vectors of a real inner product space `V`. For each unit vector `q`
orthogonal to `u` there is exactly one circle on the unit sphere `S_V` through `p` and `q` that is
tangent to `u` at `p`: the section of `S_V` by the affine plane through `p` spanned by `u` and
`q - p`. Run from `p` in the direction of `u`, proportionally to arc length, it reaches `q` at half
time:

`θ ↦ ((1 + cos θ) / 2) • p + ((1 - cos θ) / 2) • q + (‖q - p‖ / 2 * sin θ) • u`
(`TauCeti.tangentCircle`), a constant loop at `p` when `q = p`.

Every point of `S_V` other than `p` lies on exactly one of these circles, at an angle determined
up to `2π`: the component along `u` and the component orthogonal to `u` recover first `q`, on the
ray from `p`, and then the cosine and sine of the angle
(`TauCeti.eq_of_tangentCircle_eq`, `TauCeti.exists_tangentCircle_eq`).

These are the circles of the family `φ_{V,u}` of Barraud–Damian–Humilière–Oancea, Example 6.20;
the family itself, as a generalized loop of `S_V`, is in
`TauCeti.AlgebraicTopology.Sphere.TangentCircle`.

## Main declarations

* `TauCeti.tangentCircle p u q θ`: the circle through `p` tangent to `u` and through `q`.
* `TauCeti.norm_tangentCircle`: it runs on the unit sphere.
* `TauCeti.eq_of_tangentCircle_eq`: the circles are disjoint off `p`.
* `TauCeti.exists_tangentCircle_eq`: the circles sweep the sphere.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Example 6.20.
-/

public section

noncomputable section

open Real
open scoped RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The circle through `p` and `q` tangent to `u` at `p`, at the angle `θ`:
`((1 + cos θ) / 2) • p + ((1 - cos θ) / 2) • q + (‖q - p‖ / 2 * sin θ) • u`. When `p`, `q` are unit
vectors orthogonal to the unit vector `u`, it runs on the unit sphere
(`TauCeti.norm_tangentCircle`), from `p` at `θ = 0` to `q` at `θ = π`, proportionally to arc
length, and back to `p` at `θ = 2π`. -/
def tangentCircle (p u q : V) (θ : ℝ) : V :=
  ((1 + cos θ) / 2) • p + ((1 - cos θ) / 2) • q + (‖q - p‖ / 2 * sin θ) • u

/-- The defining formula of `TauCeti.tangentCircle`. -/
theorem tangentCircle_def (p u q : V) (θ : ℝ) :
    tangentCircle p u q θ =
      ((1 + cos θ) / 2) • p + ((1 - cos θ) / 2) • q + (‖q - p‖ / 2 * sin θ) • u :=
  (rfl)

@[simp]
theorem tangentCircle_zero (p u q : V) : tangentCircle p u q 0 = p := by
  simp [tangentCircle]

@[simp]
theorem tangentCircle_pi (p u q : V) : tangentCircle p u q π = q := by
  simp [tangentCircle]

@[simp]
theorem tangentCircle_self (p u : V) (θ : ℝ) : tangentCircle p u p θ = p := by
  rw [tangentCircle, sub_self, norm_zero]
  module

theorem tangentCircle_add_two_pi (p u q : V) (θ : ℝ) :
    tangentCircle p u q (θ + 2 * π) = tangentCircle p u q θ := by
  simp [tangentCircle]

theorem continuous_tangentCircle (p u : V) :
    Continuous fun x : V × ℝ ↦ tangentCircle p u x.1 x.2 := by
  unfold tangentCircle
  fun_prop

variable {p u q : V}

/-- The component of the circle along `u`. -/
theorem inner_tangentCircle (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hqu : ⟪q, u⟫ = 0) (θ : ℝ) :
    ⟪tangentCircle p u q θ, u⟫ = ‖q - p‖ / 2 * sin θ := by
  simp [tangentCircle, inner_add_left, real_inner_smul_left, hpu, hqu, hu]

/-- The component of the circle orthogonal to `u` lies on the segment from `p` to `q`. -/
theorem tangentCircle_sub_inner_smul (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hqu : ⟪q, u⟫ = 0)
    (θ : ℝ) :
    tangentCircle p u q θ - ⟪tangentCircle p u q θ, u⟫ • u = p + ((1 - cos θ) / 2) • (q - p) := by
  rw [inner_tangentCircle hu hpu hqu, tangentCircle]
  module

/-- The circle lies on the unit sphere. -/
theorem norm_tangentCircle (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hq : ‖q‖ = 1)
    (hqu : ⟪q, u⟫ = 0) (θ : ℝ) : ‖tangentCircle p u q θ‖ = 1 := by
  have hpq : ‖q - p‖ ^ 2 = 2 - 2 * ⟪p, q⟫ := by
    rw [norm_sub_sq_real, hp, hq, real_inner_comm]
    ring
  have h : ‖tangentCircle p u q θ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [tangentCircle, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hpu, hqu, real_inner_comm p u, real_inner_comm q u,
      real_inner_comm p q]
    simp only [real_inner_self_eq_norm_sq, hp, hq, hu]
    linear_combination (1 / 4 * sin θ ^ 2) * hpq + (1 / 2 - ⟪p, q⟫ / 2) * sin_sq_add_cos_sq θ
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- The circle passes through `p` only at the angles `2πk`, unless it is the constant loop
`q = p`. -/
theorem tangentCircle_eq_self_iff (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hqu : ⟪q, u⟫ = 0)
    (θ : ℝ) : tangentCircle p u q θ = p ↔ q = p ∨ cos θ = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h' := tangentCircle_sub_inner_smul hu hpu hqu θ
    rw [h, hpu, zero_smul, sub_zero, left_eq_add, smul_eq_zero, div_eq_zero_iff, sub_eq_zero,
      sub_eq_zero] at h'
    rcases h' with (h' | h') | h'
    · exact Or.inr h'.symm
    · norm_num at h'
    · exact Or.inl h'
  · rintro (rfl | h)
    · exact tangentCircle_self _ _ θ
    · have hs : sin θ = 0 := by nlinarith [sin_sq_add_cos_sq θ]
      simp [tangentCircle, h, hs]

/-- **The circles are disjoint off `p`.** Two points of these circles that agree and differ from
`p` lie on the same circle, at angles with the same cosine and sine. -/
theorem eq_of_tangentCircle_eq (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hq : ‖q‖ = 1)
    (hqu : ⟪q, u⟫ = 0) {q' : V} (hq' : ‖q'‖ = 1) (hq'u : ⟪q', u⟫ = 0) {θ θ' : ℝ}
    (h : tangentCircle p u q θ = tangentCircle p u q' θ') (hne : tangentCircle p u q θ ≠ p) :
    q = q' ∧ cos θ = cos θ' ∧ sin θ = sin θ' := by
  have h₁ := tangentCircle_sub_inner_smul hu hpu hqu θ
  have h₂ := tangentCircle_sub_inner_smul hu hpu hq'u θ'
  rw [← h, h₁, add_right_inj] at h₂
  set w := ((1 - cos θ) / 2) • (q - p) with hw
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, add_zero] at h₁
    -- A unit vector whose component orthogonal to `u` is `p` has inner product `‖p‖ ^ 2` with `p`.
    have hyp := congrArg (⟪·, p⟫) h₁
    simp only [inner_sub_left, real_inner_smul_left, real_inner_comm p u, hpu, mul_zero,
      sub_zero] at hyp
    exact hne (eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
      (by rw [norm_tangentCircle hp hu hpu hq hqu θ, hp]) (by simpa using hyp))
  have hb : (1 - cos θ) / 2 ≠ 0 := fun h0 ↦ hw0 (by rw [hw, h0, zero_smul])
  have hb' : (1 - cos θ') / 2 ≠ 0 := fun h0 ↦ hw0 (by rw [h₂, h0, zero_smul])
  have hqw : q = p + ((1 - cos θ) / 2)⁻¹ • w := by
    rw [hw, smul_smul, inv_mul_cancel₀ hb, one_smul, add_sub_cancel]
  have hq'w : q' = p + ((1 - cos θ') / 2)⁻¹ • w := by
    rw [h₂, smul_smul, inv_mul_cancel₀ hb', one_smul, add_sub_cancel]
  -- The line through `p` along `w` meets the unit sphere at one nonzero parameter.
  have hline (c : ℝ) (hc : c ≠ 0) (hc' : ‖p + c • w‖ = 1) :=
    ((EuclideanGeometry.dist_smul_vadd_eq_dist p 0 hw0 c).1 (by
      rw [vadd_eq_add, dist_zero_right, dist_zero_right, add_comm, hc', hp])).resolve_left hc
  have hab := (hline _ (inv_ne_zero hb) (hqw ▸ hq)).trans
    (hline _ (inv_ne_zero hb') (hq'w ▸ hq')).symm
  have hc : cos θ = cos θ' := by
    have := inv_injective hab
    linarith
  have hqq' : q = q' := by rw [hqw, hq'w, hab]
  refine ⟨hqq', hc, ?_⟩
  have hs := congrArg (⟪·, u⟫) h
  simp only [inner_tangentCircle hu hpu hqu, ← hqq'] at hs
  have hqp0 : q - p ≠ 0 := fun h0 ↦ hw0 (by rw [hw, h0, smul_zero])
  have hqp : ‖q - p‖ / 2 ≠ 0 := div_ne_zero (norm_ne_zero_iff.2 hqp0) two_ne_zero
  exact mul_left_cancel₀ hqp hs

/-- **The circles sweep the sphere.** Every point `y` of the unit sphere lies on the circle through
`p` tangent to `u` and through some unit vector `q` orthogonal to `u`. -/
theorem exists_tangentCircle_eq (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) {y : V}
    (hy : ‖y‖ = 1) : ∃ q, ‖q‖ = 1 ∧ ⟪q, u⟫ = 0 ∧ ∃ θ, tangentCircle p u q θ = y := by
  by_cases hyp : y = p
  · exact ⟨p, hp, hpu, 0, by rw [tangentCircle_zero, hyp]⟩
  set s := ⟪y, u⟫ with hs
  set d := y - s • u - p with hd
  have hdu : ⟪d, u⟫ = 0 := by
    simp [hd, inner_sub_left, real_inner_smul_left, hu, hpu, ← hs]
  have hd0 : d ≠ 0 := by
    intro h0
    -- A unit vector whose component orthogonal to `u` is `p` has inner product `‖p‖ ^ 2` with `p`.
    have hyp' := congrArg (⟪·, p⟫) h0
    simp only [hd, inner_sub_left, real_inner_smul_left, real_inner_comm p u, hpu, mul_zero,
      sub_zero, inner_zero_left, sub_eq_zero] at hyp'
    exact hyp (eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) (by rw [hy, hp]) (by simpa using hyp'))
  have hyd : y = p + d + s • u := by rw [hd]; abel
  set D := ‖d‖ ^ 2 with hD
  have hDpos : 0 < D := by positivity
  -- The unit length of `y` determines the component of `d` along `p`.
  have hpd : -2 * ⟪p, d⟫ = D + s ^ 2 := by
    have h : ‖y‖ ^ 2 = 1 := by rw [hy, one_pow]
    rw [hyd, norm_add_sq_real, norm_add_sq_real, inner_add_left, real_inner_smul_right,
      real_inner_smul_right, hpu, hdu, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu, hp] at h
    linarith
  set l := (D + s ^ 2) / D with hl
  have hlD : l * D = D + s ^ 2 := div_mul_cancel₀ _ hDpos.ne'
  have hl1 : 1 ≤ l := by rw [hl, le_div_iff₀ hDpos]; nlinarith
  have hl0 : 0 < l := by linarith
  set q := p + l • d with hq
  have hqn : ‖q‖ = 1 := by
    have : ‖q‖ ^ 2 = 1 := by
      rw [hq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs, hp, ← hD]
      nlinarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
  have hqu : ⟪q, u⟫ = 0 := by
    rw [hq, inner_add_left, real_inner_smul_left, hpu, hdu, mul_zero, add_zero]
  have hqp : ‖q - p‖ = l * ‖d‖ := by
    rw [hq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
  obtain ⟨t, hc, hsn⟩ := exists_cos_sin_two_pi_mul_eq (a := 1 - 2 / l) (b := 2 * s / (l * ‖d‖))
    (by
      field_simp
      rw [← hD]
      nlinarith)
  refine ⟨q, hqn, hqu, 2 * π * t, ?_⟩
  have hb : (1 - cos (2 * π * t)) / 2 * l = 1 := by rw [hc]; field_simp; ring
  have hsc : ‖q - p‖ / 2 * sin (2 * π * t) = s := by rw [hsn, hqp]; field_simp
  calc tangentCircle p u q (2 * π * t)
      = p + ((1 - cos (2 * π * t)) / 2 * l) • d + (‖q - p‖ / 2 * sin (2 * π * t)) • u := by
        rw [tangentCircle, hq, mul_smul]; module
    _ = y := by rw [hb, hsc, one_smul, hyd]

end TauCeti
