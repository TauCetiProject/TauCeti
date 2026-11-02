/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Parameter
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Norms of the Tate coordinates and the reduction strata

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`. Modulo `q`, the
Tate equation `y² + xy = x³ + a₄(q) x + a₆(q)` is the nodal cubic `y² + xy = x³`, whose singular
point is the origin and whose nonsingular points are parametrised by
`u ↦ (u / (1 - u)², u² / (1 - u)³)` for `u ≠ 0, 1`. This file shows that the Tate coordinates
`X(u)` and `Y(u)` are this parametrisation up to an error of norm at most
`max (‖q‖ ‖u‖) (‖q‖ / ‖u‖)` throughout the annulus `‖q‖ < ‖u‖ < ‖q‖⁻¹`; on the unit circle the
error has norm at most `‖q‖`.

Consequently the representative `u` of a class in `Kˣ ⧸ q^ℤ` in the fundamental annulus
`‖q‖ < ‖u‖ ≤ 1` determines the reduction behaviour of its Tate coordinates:

* if `‖1 - u‖ < 1` and `u ≠ 1`, then `‖X(u)‖ = ‖1 - u‖⁻² > 1`, so `X(u)` has a pole modulo the
  maximal ideal and the corresponding point lies in the kernel of reduction;
* if `‖u‖ = ‖1 - u‖ = 1`, then `X(u)` and `Y(u)` are integral and `‖X(u) + Y(u)‖ = 1`, so the
  point reduces to a nonsingular point of the nodal cubic;
* if `‖u‖ < 1`, then `‖X(u)‖ < 1` and `‖Y(u)‖ < 1`, so the point reduces to the node.

For a nonidentity class this gives the characterisations
`one_lt_norm_tateQuotientCoordinates_fst_iff` and
`norm_tateQuotientCoordinates_fst_lt_one_and_snd_lt_one_iff`; the middle stratum is the
complement of the other two. The statements are in terms of norms, so neither a discrete value
group nor any restriction on the characteristic is needed.

## Main results

* `TauCeti.norm_tateUniformizationX_sub_le`, `TauCeti.norm_tateUniformizationY_sub_le`: the
  Tate coordinates are the nodal parametrisation up to `max (‖q‖ ‖u‖) (‖q‖ / ‖u‖)`.
* `TauCeti.norm_tateUniformizationX_of_norm_one_sub_lt_one`: `‖X(u)‖ = ‖1 - u‖⁻²` near `u = 1`.
* `TauCeti.norm_tateUniformizationX_add_tateUniformizationY`: `‖X(u) + Y(u)‖ = 1` when
  `‖u‖ = ‖1 - u‖ = 1`.
* `TauCeti.norm_tateUniformizationX_le_max`, `TauCeti.norm_tateUniformizationY_le_max`: both
  coordinates are small on the strict annulus `‖q‖ < ‖u‖ < 1`.
* `TauCeti.one_lt_norm_tateQuotientCoordinates_fst_iff`: a nonidentity class has first coordinate
  of norm above one exactly when it has a representative in `1 + 𝔪`.
* `TauCeti.norm_tateQuotientCoordinates_fst_lt_one_and_snd_lt_one_iff`: a nonidentity class has
  both coordinates in the maximal ideal exactly when it has a representative in the strict
  annulus.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3–V.4.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K]

/-- The hypotheses `‖q‖ < ‖u‖ < ‖q‖⁻¹` of the annulus estimates, unpacked: both one-sided series
are evaluated inside the open unit disc, `‖q‖ < 1`, and `‖q‖` is at most the error bound. -/
private theorem annulus_bounds {q u : Kˣ} (hqu : ‖(q : K)‖ < ‖(u : K)‖)
    (huq : ‖(u : K)‖ < ‖(q : K)‖⁻¹) :
    ‖(q : K) * u‖ < 1 ∧ ‖(q : K) * (u : K)⁻¹‖ < 1 ∧ ‖(q : K)‖ < 1 ∧
      ‖(q : K)‖ ≤ max (‖(q : K)‖ * ‖(u : K)‖) (‖(q : K)‖ / ‖(u : K)‖) := by
  have hu0 : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hq0 : 0 < ‖(q : K)‖ := norm_pos_iff.mpr q.ne_zero
  have h₁ : ‖(q : K)‖ * ‖(u : K)‖ < 1 := by
    simpa [hq0.ne'] using mul_lt_mul_of_pos_left huq hq0
  have h₂ : ‖(q : K)‖ / ‖(u : K)‖ < 1 := (div_lt_one hu0).mpr hqu
  refine ⟨by rwa [norm_mul], by rwa [norm_mul, norm_inv, ← div_eq_mul_inv], ?_⟩
  rcases le_total ‖(u : K)‖ 1 with hu | hu
  · exact ⟨hqu.trans_le hu, le_max_of_le_right (le_div_self hq0.le hu0 hu)⟩
  · have h := le_mul_of_one_le_right hq0.le hu
    exact ⟨h.trans_lt h₁, le_max_of_le_left h⟩

variable [CompleteSpace K] [IsUltrametricDist K]

/-- **The first Tate coordinate is the nodal parametrisation up to a small error.** On the
annulus `‖q‖ < ‖u‖ < ‖q‖⁻¹`, `X(u)` differs from `u / (1 - u)²` by at most
`max (‖q‖ ‖u‖) (‖q‖ / ‖u‖)`. At `u = 1` the central term `u / (1 - u)²` is the totalised value
zero. -/
theorem norm_tateUniformizationX_sub_le (q u : Kˣ) (hqu : ‖(q : K)‖ < ‖(u : K)‖)
    (huq : ‖(u : K)‖ < ‖(q : K)‖⁻¹) :
    ‖tateUniformizationX q u - u / (1 - u) ^ 2‖ ≤
      max (‖(q : K)‖ * ‖(u : K)‖) (‖(q : K)‖ / ‖(u : K)‖) := by
  obtain ⟨h₁, h₂, hq, hqB⟩ := annulus_bounds hqu huq
  have hf (w : K) (hw : ‖w‖ < 1) : ‖w / (1 - w) ^ 2‖ ≤ ‖w‖ :=
    (norm_div_one_sub_pow w hw 2).le
  have e (a S₁ S₂ s : K) : a + S₁ + S₂ - 2 * s - a = S₁ + S₂ - (s + s) := by ring
  rw [tateUniformizationX_eq_tsum_nat q hq u, e]
  refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
  · refine (norm_tsum_le_norm_mul (fun w ↦ w / (1 - w) ^ 2) hf hq.le h₁).trans ?_
    rw [norm_mul]
    exact le_max_left _ _
  · refine (norm_tsum_le_norm_mul (fun w ↦ w / (1 - w) ^ 2) hf hq.le h₂).trans ?_
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    exact le_max_right _ _
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [max_self]
    exact (norm_divisorSumAt_le 1 hq).trans hqB

/-- **The second Tate coordinate is the nodal parametrisation up to a small error.** On the
annulus `‖q‖ < ‖u‖ < ‖q‖⁻¹`, `Y(u)` differs from `u² / (1 - u)³` by at most
`max (‖q‖ ‖u‖) (‖q‖ / ‖u‖)`. -/
theorem norm_tateUniformizationY_sub_le (q u : Kˣ) (hqu : ‖(q : K)‖ < ‖(u : K)‖)
    (huq : ‖(u : K)‖ < ‖(q : K)‖⁻¹) :
    ‖tateUniformizationY q u - (u : K) ^ 2 / (1 - u) ^ 3‖ ≤
      max (‖(q : K)‖ * ‖(u : K)‖) (‖(q : K)‖ / ‖(u : K)‖) := by
  obtain ⟨h₁, h₂, hq, hqB⟩ := annulus_bounds hqu huq
  have hf (w : K) (hw : ‖w‖ < 1) : ‖w ^ 2 / (1 - w) ^ 3‖ ≤ ‖w‖ := by
    rw [norm_div_one_sub_pow _ hw, norm_pow]
    exact pow_le_of_le_one (norm_nonneg _) hw.le two_ne_zero
  have hf' (w : K) (hw : ‖w‖ < 1) : ‖-w / (1 - w) ^ 3‖ ≤ ‖w‖ := by
    rw [norm_div_one_sub_pow _ hw, norm_neg]
  have e (a T₁ T₂ s : K) : a + T₁ + T₂ + s - a = T₁ + T₂ + s := by ring
  rw [tateUniformizationY_eq_tsum_nat q hq u, e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
  · refine (norm_tsum_le_norm_mul (fun w ↦ w ^ 2 / (1 - w) ^ 3) hf hq.le h₁).trans ?_
    rw [norm_mul]
    exact le_max_left _ _
  · refine (norm_tsum_le_norm_mul (fun w ↦ -w / (1 - w) ^ 3) hf' hq.le h₂).trans ?_
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    exact le_max_right _ _
  · exact (norm_divisorSumAt_le 1 hq).trans hqB

/-- On the unit circle the first Tate coordinate is `u / (1 - u)²` up to an error of norm at
most `‖q‖`. -/
theorem norm_tateUniformizationX_sub_le_of_norm_eq_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) : ‖tateUniformizationX q u - u / (1 - u) ^ 2‖ ≤ ‖(q : K)‖ := by
  have huq : ‖(u : K)‖ < ‖(q : K)‖⁻¹ := by
    rw [hu]
    exact (one_lt_inv₀ (norm_pos_iff.mpr q.ne_zero)).mpr hq
  simpa [hu] using norm_tateUniformizationX_sub_le q u (by rwa [hu]) huq

/-- On the unit circle the second Tate coordinate is `u² / (1 - u)³` up to an error of norm at
most `‖q‖`. -/
theorem norm_tateUniformizationY_sub_le_of_norm_eq_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) :
    ‖tateUniformizationY q u - (u : K) ^ 2 / (1 - u) ^ 3‖ ≤ ‖(q : K)‖ := by
  have huq : ‖(u : K)‖ < ‖(q : K)‖⁻¹ := by
    rw [hu]
    exact (one_lt_inv₀ (norm_pos_iff.mpr q.ne_zero)).mpr hq
  simpa [hu] using norm_tateUniformizationY_sub_le q u (by rwa [hu]) huq

/-- **Points near the identity: the kernel of reduction.** If `‖1 - u‖ < 1` and `u ≠ 1`, then
`‖X(u)‖ = ‖1 - u‖⁻²`, which exceeds one. -/
theorem norm_tateUniformizationX_of_norm_one_sub_lt_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : (u : K) ≠ 1) (h : ‖1 - (u : K)‖ < 1) :
    ‖tateUniformizationX q u‖ = (‖1 - (u : K)‖ ^ 2)⁻¹ := by
  have hnorm : ‖(u : K)‖ = 1 := by simpa using norm_one_sub_of_norm_lt_one h
  have hd : 0 < ‖1 - (u : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu.symm)
  have hmain : ‖(u : K) / (1 - u) ^ 2‖ = (‖1 - (u : K)‖ ^ 2)⁻¹ := by
    rw [norm_div, norm_pow, hnorm, one_div]
  rw [← hmain]
  refine (IsUltrametricDist.norm_eq_of_norm_sub_lt_left ?_).symm
  rw [norm_sub_rev]
  calc ‖tateUniformizationX q u - u / (1 - u) ^ 2‖
      ≤ ‖(q : K)‖ := norm_tateUniformizationX_sub_le_of_norm_eq_one q u hq hnorm
    _ < 1 := hq
    _ ≤ (‖1 - (u : K)‖ ^ 2)⁻¹ :=
      (one_le_inv₀ (by positivity)).mpr (pow_le_one₀ hd.le h.le)
    _ = _ := hmain.symm

/-- **Points with nonsingular reduction: the first coordinate is integral.** -/
theorem norm_tateUniformizationX_le_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) (h : ‖1 - (u : K)‖ = 1) : ‖tateUniformizationX q u‖ ≤ 1 :=
  IsUltrametricDist.norm_le_of_norm_sub_le (by rw [norm_div, norm_pow, hu, h, one_pow, div_one])
    ((norm_tateUniformizationX_sub_le_of_norm_eq_one q u hq hu).trans hq.le)

/-- **Points with nonsingular reduction: the second coordinate is integral.** -/
theorem norm_tateUniformizationY_le_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) (h : ‖1 - (u : K)‖ = 1) : ‖tateUniformizationY q u‖ ≤ 1 :=
  IsUltrametricDist.norm_le_of_norm_sub_le
    (by rw [norm_div, norm_pow, norm_pow, hu, h, one_pow, one_pow, div_one])
    ((norm_tateUniformizationY_sub_le_of_norm_eq_one q u hq hu).trans hq.le)

/-- **Points with nonsingular reduction avoid the node.** If `‖u‖ = ‖1 - u‖ = 1`, then
`‖X(u) + Y(u)‖ = 1`, so the coordinates do not both lie in the maximal ideal. -/
theorem norm_tateUniformizationX_add_tateUniformizationY (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) (h : ‖1 - (u : K)‖ = 1) :
    ‖tateUniformizationX q u + tateUniformizationY q u‖ = 1 := by
  have h0 : (1 - (u : K)) ≠ 0 := norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero)
  have hsum : (u : K) / (1 - u) ^ 2 + (u : K) ^ 2 / (1 - u) ^ 3 = u / (1 - u) ^ 3 := by
    field_simp
    ring
  have hmain : ‖(u : K) / (1 - u) ^ 3‖ = 1 := by rw [norm_div, norm_pow, hu, h, one_pow, div_one]
  rw [← hmain]
  refine (IsUltrametricDist.norm_eq_of_norm_sub_lt_left ?_).symm
  rw [norm_sub_rev, hmain, ← hsum, add_sub_add_comm]
  exact ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    (norm_tateUniformizationX_sub_le_of_norm_eq_one q u hq hu)
    (norm_tateUniformizationY_sub_le_of_norm_eq_one q u hq hu))).trans_lt hq

/-- **Points reducing to the node: the first coordinate.** On the strict annulus
`‖q‖ < ‖u‖ < 1`, `‖X(u)‖ ≤ max ‖u‖ (‖q‖ / ‖u‖) < 1`. -/
theorem norm_tateUniformizationX_le_max (q u : Kˣ) (hqu : ‖(q : K)‖ < ‖(u : K)‖)
    (hu : ‖(u : K)‖ < 1) :
    ‖tateUniformizationX q u‖ ≤ max ‖(u : K)‖ (‖(q : K)‖ / ‖(u : K)‖) := by
  have hq : ‖(q : K)‖ < 1 := hqu.trans hu
  have huq : ‖(u : K)‖ < ‖(q : K)‖⁻¹ :=
    hu.trans ((one_lt_inv₀ (norm_pos_iff.mpr q.ne_zero)).mpr hq)
  refine IsUltrametricDist.norm_le_of_norm_sub_le
    (le_max_of_le_left (norm_div_one_sub_pow _ hu 2).le)
    ((norm_tateUniformizationX_sub_le q u hqu huq).trans (max_le_max_right _ ?_))
  exact mul_le_of_le_one_left (norm_nonneg _) hq.le

/-- **Points reducing to the node: the second coordinate.** On the strict annulus
`‖q‖ < ‖u‖ < 1`, `‖Y(u)‖ ≤ max ‖u‖ (‖q‖ / ‖u‖) < 1`. -/
theorem norm_tateUniformizationY_le_max (q u : Kˣ) (hqu : ‖(q : K)‖ < ‖(u : K)‖)
    (hu : ‖(u : K)‖ < 1) :
    ‖tateUniformizationY q u‖ ≤ max ‖(u : K)‖ (‖(q : K)‖ / ‖(u : K)‖) := by
  have hq : ‖(q : K)‖ < 1 := hqu.trans hu
  have huq : ‖(u : K)‖ < ‖(q : K)‖⁻¹ :=
    hu.trans ((one_lt_inv₀ (norm_pos_iff.mpr q.ne_zero)).mpr hq)
  refine IsUltrametricDist.norm_le_of_norm_sub_le (le_max_of_le_left ?_)
    ((norm_tateUniformizationY_sub_le q u hqu huq).trans (max_le_max_right _ ?_))
  · rw [norm_div_one_sub_pow _ hu, norm_pow]
    exact pow_le_of_le_one (norm_nonneg _) hu.le two_ne_zero
  · exact mul_le_of_le_one_left (norm_nonneg _) hq.le

/-- **The kernel-of-reduction stratum.** The first Tate coordinate of a nonidentity class in
`Kˣ ⧸ q^ℤ` has norm above one exactly when the class has a representative in `1 + 𝔪`. -/
theorem one_lt_norm_tateQuotientCoordinates_fst_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {x : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1) :
    1 < ‖(tateQuotientCoordinates q x).1‖ ↔
      ∃ u : Kˣ, (u : Kˣ ⧸ Subgroup.zpowers q) = x ∧ ‖1 - (u : K)‖ < 1 := by
  constructor
  · intro h
    obtain ⟨r, rfl, hr₁, hr₂⟩ := exists_mk_eq_and_norm_mem_Ioc q hq x
    rw [tateQuotientCoordinates_mk] at h
    refine ⟨r, rfl, lt_of_not_ge fun hge ↦ h.not_ge ?_⟩
    rcases hr₂.lt_or_eq with hlt | heq
    · exact (norm_tateUniformizationX_le_max q r hr₁ hlt).trans
        (max_le hlt.le ((div_le_one (norm_pos_iff.mpr r.ne_zero)).mpr hr₁.le))
    · have h1 : ‖1 - (r : K)‖ = 1 :=
        le_antisymm (by simpa [heq] using IsUltrametricDist.norm_sub_le_max (1 : K) r) hge
      exact norm_tateUniformizationX_le_one q r hq heq h1
  · rintro ⟨u, rfl, hu⟩
    have hu1 : (u : K) ≠ 1 := fun h ↦ hx (by rw [Units.val_eq_one.mp h, QuotientGroup.mk_one])
    rw [tateQuotientCoordinates_mk,
      norm_tateUniformizationX_of_norm_one_sub_lt_one q u hq hu1 hu]
    have hd : 0 < ‖1 - (u : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu1.symm)
    exact (one_lt_inv₀ (by positivity)).mpr (pow_lt_one₀ hd.le hu two_ne_zero)

/-- **The node stratum.** Both Tate coordinates of a nonidentity class in `Kˣ ⧸ q^ℤ` lie in the
maximal ideal exactly when the class has a representative in the strict annulus
`‖q‖ < ‖u‖ < 1`. -/
theorem norm_tateQuotientCoordinates_fst_lt_one_and_snd_lt_one_iff (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {x : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1) :
    ‖(tateQuotientCoordinates q x).1‖ < 1 ∧ ‖(tateQuotientCoordinates q x).2‖ < 1 ↔
      ∃ u : Kˣ, (u : Kˣ ⧸ Subgroup.zpowers q) = x ∧ ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ < 1 := by
  constructor
  · rintro ⟨hX, hY⟩
    obtain ⟨r, rfl, hr₁, hr₂⟩ := exists_mk_eq_and_norm_mem_Ioc q hq x
    refine ⟨r, rfl, hr₁, hr₂.lt_of_ne fun heq ↦ ?_⟩
    have hbound : ‖1 - (r : K)‖ ≤ 1 := by
      simpa [heq] using IsUltrametricDist.norm_sub_le_max (1 : K) r
    rcases hbound.lt_or_eq with hlt | h1
    · exact hX.not_gt ((one_lt_norm_tateQuotientCoordinates_fst_iff q hq hx).mpr ⟨r, rfl, hlt⟩)
    · rw [tateQuotientCoordinates_mk] at hX hY
      have := norm_tateUniformizationX_add_tateUniformizationY q r hq heq h1
      exact this.not_lt ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hX hY))
  · rintro ⟨u, rfl, hu₁, hu₂⟩
    have hB : max ‖(u : K)‖ (‖(q : K)‖ / ‖(u : K)‖) < 1 :=
      max_lt hu₂ ((div_lt_one (norm_pos_iff.mpr u.ne_zero)).mpr hu₁)
    rw [tateQuotientCoordinates_mk]
    exact ⟨(norm_tateUniformizationX_le_max q u hu₁ hu₂).trans_lt hB,
      (norm_tateUniformizationY_le_max q u hu₁ hu₂).trans_lt hB⟩

end TauCeti
