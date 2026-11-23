/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Inner-product half-spaces

A translation orthogonal to the normal vector preserves a strict half-space, and the open and
closed half-spaces are convex (`TauCeti.convex_of_halfSpace`, `TauCeti.convex_setOf_le_inner`).
The ball of radius `r` about a unit vector `x` lies in the half-space `{z | 1 - r ≤ ⟪x, z⟫}`, and
more generally a closed ball `closedBall w r` lies in `{y | ⟪y, ν⟫ < c}` whenever
`⟪w, ν⟫ + r * ‖ν‖ < c` (`TauCeti.closedBall_subset_setOf_inner_lt`) and in `{y | c < ⟪y, ν⟫}`
whenever `c + r * ‖ν‖ < ⟪w, ν⟫` (`TauCeti.closedBall_subset_setOf_lt_inner`); an open ball
`ball w r` lies in `{y | c < ⟪y, ν⟫}` already when `c + r * ‖ν‖ ≤ ⟪w, ν⟫`
(`TauCeti.ball_subset_setOf_lt_inner`).
For `x` in the closed half-space `{z | c ≤ ⟪z, ν⟫}`, the open ball of radius `ρ` about
`x + (ρ / ‖ν‖) ν` lies in the open half-space `{z | c < ⟪z, ν⟫}`
(`TauCeti.ball_add_smul_subset_setOf_lt_inner`).
The projection `z - (⟪z, ν⟫ / ‖ν‖²) ν` lands in the boundary hyperplane `{z | ⟪z, ν⟫ = 0}` and
does not increase norms, and neither does the projection `(⟪z, ν⟫ / ‖ν‖²) ν` onto the line
`ℝ ∙ ν`. The foot `x - ((⟪x, ν⟫ - c) / ‖ν‖²) ν` of the perpendicular from `x` lies on the
hyperplane `{y | ⟪y, ν⟫ = c}`, at distance `|⟪x, ν⟫ - c| / ‖ν‖` from `x`, and every point of that
hyperplane lies at distance at least `(⟪x, ν⟫ - c) / ‖ν‖` from `x`. Relative to an
orthonormal basis `(eᵢ)`, a bilinear form splits into a part along `ν` and a part along the
projected basis vectors `eᵢ - (⟪eᵢ, ν⟫ / ‖ν‖²) ν`. In rigid coordinates
`e : F ≃ᵃⁱ ℝ × E`, the normal coordinate `(e x).fst` is `⟪x, ν⟫` plus a constant, so the region
where it is positive is a half-space.
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

/-- The half-space `{x | c < ⟪x, ν⟫}` is convex. -/
theorem convex_of_halfSpace {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set E} {ν : E} {c : ℝ} (hΩ : ∀ x, x ∈ s ↔ c < ⟪x, ν⟫_ℝ) : Convex ℝ s := by
  have h : s = {x | c < innerSL ℝ ν x} := Set.ext fun x => by simp [hΩ x, real_inner_comm]
  rw [h]
  exact convex_halfSpace_gt (innerSL ℝ ν).toLinearMap.isLinear c

/-- The closed half-space `{x | c ≤ ⟪x, ν⟫}` is convex. -/
theorem convex_setOf_le_inner {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν : E) (c : ℝ) : Convex ℝ {x : E | c ≤ ⟪x, ν⟫_ℝ} :=
  convex_halfSpace_ge ⟨fun x y => inner_add_left x y ν, fun a x => real_inner_smul_left x ν a⟩ c

/-- The inner product of a unit vector `x` with `z` is at least `1 - ‖z - x‖`. -/
theorem one_sub_norm_sub_le_inner {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : ‖x‖ = 1) (z : E) : 1 - ‖z - x‖ ≤ ⟪x, z⟫_ℝ := by
  have h := real_inner_le_norm x (x - z)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hx, norm_sub_rev] at h
  linarith

/-- A closed ball `Metric.closedBall w r` lies in the open half-space `{y | ⟪y, ν⟫ < c}` whenever
`⟪w, ν⟫ + r * ‖ν‖ < c`. -/
theorem closedBall_subset_setOf_inner_lt {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {w ν : E} {r c : ℝ} (h : ⟪w, ν⟫_ℝ + r * ‖ν‖ < c) :
    Metric.closedBall w r ⊆ {y | ⟪y, ν⟫_ℝ < c} := by
  intro y hy
  have hyw : ‖y - w‖ ≤ r := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
  have hcs : ⟪y - w, ν⟫_ℝ ≤ r * ‖ν‖ :=
    (real_inner_le_norm (y - w) ν).trans (mul_le_mul_of_nonneg_right hyw (norm_nonneg ν))
  have hsplit : ⟪y, ν⟫_ℝ = ⟪w, ν⟫_ℝ + ⟪y - w, ν⟫_ℝ := by
    rw [← inner_add_left, add_sub_cancel]
  exact Set.mem_ofPred.2 (by linarith)

/-- A closed ball `Metric.closedBall w r` lies in the open half-space `{y | c < ⟪y, ν⟫}` whenever
`c + r * ‖ν‖ < ⟪w, ν⟫`. -/
theorem closedBall_subset_setOf_lt_inner {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {w ν : E} {r c : ℝ} (h : c + r * ‖ν‖ < ⟪w, ν⟫_ℝ) :
    Metric.closedBall w r ⊆ {y | c < ⟪y, ν⟫_ℝ} := by
  have h' : ⟪w, -ν⟫_ℝ + r * ‖-ν‖ < -c := by
    rw [inner_neg_right, norm_neg]
    linarith
  intro y hy
  have hy' := closedBall_subset_setOf_inner_lt h' hy
  rw [Set.mem_ofPred_eq, inner_neg_right, neg_lt_neg_iff] at hy'
  exact hy'

/-- An open ball `Metric.ball w r` lies in the open half-space `{y | c < ⟪y, ν⟫}` whenever
`ν ≠ 0` and `c + r * ‖ν‖ ≤ ⟪w, ν⟫`. -/
theorem ball_subset_setOf_lt_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w ν : E} {r c : ℝ} (hν : ν ≠ 0) (h : c + r * ‖ν‖ ≤ ⟪w, ν⟫_ℝ) :
    Metric.ball w r ⊆ {y | c < ⟪y, ν⟫_ℝ} := by
  intro y hy
  have hyw : ‖w - y‖ < r := by rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hy
  have hcs : ⟪w - y, ν⟫_ℝ < r * ‖ν‖ :=
    (real_inner_le_norm (w - y) ν).trans_lt
      (mul_lt_mul_of_pos_right hyw (norm_pos_iff.2 hν))
  rw [inner_sub_left] at hcs
  exact Set.mem_ofPred.2 (by linarith)

/-- For a point `x` of the closed half-space `{z | c ≤ ⟪z, ν⟫}`, `ν ≠ 0`, the open ball of radius
`ρ` about `x + (ρ / ‖ν‖) ν` lies in the open half-space `{z | c < ⟪z, ν⟫}`. -/
theorem ball_add_smul_subset_setOf_lt_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ν x : E} {c ρ : ℝ} (hν : ν ≠ 0) (hx : c ≤ ⟪x, ν⟫_ℝ) :
    Metric.ball (x + (ρ / ‖ν‖) • ν) ρ ⊆ {z | c < ⟪z, ν⟫_ℝ} :=
  ball_subset_setOf_lt_inner hν (by
    have h : ρ / ‖ν‖ * ‖ν‖ ^ 2 = ρ * ‖ν‖ := by
      rw [pow_two, ← mul_assoc, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hν)]
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, h]
    linarith)

/-- The projection `z - (⟪z, ν⟫ / ‖ν‖²) ν` onto the hyperplane orthogonal to `ν` is orthogonal
to `ν`. It is the explicit form of `z - (ℝ ∙ ν).starProjection z`, by
`Submodule.starProjection_singleton`. -/
theorem real_inner_sub_div_norm_sq_smul_self_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (z ν : E) : ⟪z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν, ν⟫_ℝ = 0 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ (pow_pos (norm_pos_iff.2 hν) 2).ne', sub_self]

/-- The projection `z - (⟪z, ν⟫ / ‖ν‖²) ν` onto the hyperplane orthogonal to `ν` does not increase
norms. -/
theorem norm_sub_div_norm_sq_smul_self_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (z ν : E) : ‖z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ≤ ‖z‖ := by
  have h := Submodule.starProjection_singleton ℝ (v := ν) z
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [real_inner_comm, ← h, ← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_starProjection_apply_le _ z

/-- The projection `(⟪z, ν⟫ / ‖ν‖²) ν` of `z` onto the line spanned by `ν` does not increase
norms. It is the explicit form of `(ℝ ∙ ν).starProjection z`, by
`Submodule.starProjection_singleton`. -/
theorem norm_inner_div_norm_sq_smul_self_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (z ν : E) : ‖(⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ≤ ‖z‖ := by
  have h := Submodule.starProjection_singleton ℝ (v := ν) z
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [real_inner_comm, ← h]
  exact Submodule.norm_starProjection_apply_le _ z

/-- The vector `(t / ‖ν‖²) ν` has norm `|t| / ‖ν‖`. -/
theorem norm_div_norm_sq_smul_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ℝ) (ν : E) : ‖(t / ‖ν‖ ^ 2) • ν‖ = |t| / ‖ν‖ := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < ‖ν‖ ^ 2)]
  field_simp

/-- The foot `x - ((⟪x, ν⟫ - c) / ‖ν‖²) ν` of the perpendicular from `x` to the hyperplane
`{y | ⟪y, ν⟫ = c}` lies on that hyperplane. -/
theorem real_inner_sub_div_norm_sq_smul_self_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ν : E} (hν : ν ≠ 0) (x : E) (c : ℝ) :
    ⟪x - ((⟪x, ν⟫_ℝ - c) / ‖ν‖ ^ 2) • ν, ν⟫_ℝ = c := by
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ (pow_pos (norm_pos_iff.2 hν) 2).ne', sub_sub_cancel]

/-- Every point `w` of the hyperplane `{y | ⟪y, ν⟫ = c}` lies at distance at least
`(⟪x, ν⟫ - c) / ‖ν‖` from `x`. -/
theorem div_norm_le_dist_of_inner_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x w ν : E} {c : ℝ} (hw : ⟪w, ν⟫_ℝ = c) : (⟪x, ν⟫_ℝ - c) / ‖ν‖ ≤ dist x w := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  rw [div_le_iff₀ (norm_pos_iff.2 hν), dist_eq_norm, ← hw, ← inner_sub_left]
  exact real_inner_le_norm _ _

end TauCeti

namespace OrthonormalBasis

open scoped InnerProductSpace

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

end OrthonormalBasis

namespace AffineIsometryEquiv

open scoped InnerProductSpace

/-- **The normal coordinate of rigid coordinates is affine.** For an affine isometry equivalence
`e : F ≃ᵃⁱ ℝ × E`, the first coordinate `(e x).fst` is `⟪x, ν⟫ + (e 0).fst`, where `ν` is the
preimage of the unit normal `(1, 0)` under the linear part of `e`. -/
theorem fst_apply_eq_inner_add {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (x : F) :
    (e x).fst = ⟪x, e.linearIsometryEquiv.symm (WithLp.toLp 2 (1, 0))⟫_ℝ + (e 0).fst := by
  have hx : e.linearIsometryEquiv x = e x - e 0 := by
    simpa only [vsub_eq_sub, sub_zero] using e.map_vsub x 0
  rw [← e.linearIsometryEquiv.inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    WithLp.prod_inner_apply, hx]
  simp

end AffineIsometryEquiv
