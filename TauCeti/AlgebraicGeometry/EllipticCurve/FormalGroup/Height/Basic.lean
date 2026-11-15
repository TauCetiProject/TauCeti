/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
public import TauCeti.RingTheory.FormalGroup.Height.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange

/-!
# The height-one locus of the formal group of a Weierstrass curve

Let `Ê` be the formal group of a Weierstrass curve `W` over a commutative ring `R`, with invariant
differential `P(T) dT`, the expansion of `dx / (2y + a₁x + a₃)` at the point at infinity. For a
prime `p`, the coefficient of `Tᵖ` in the multiplication-by-`p` series `[p]_Ê(T)` is congruent
modulo `p` to the coefficient of `Tᵖ⁻¹` in `P`. For a formal group law over a ring without
`p`-torsion this is `FormalGroup.natCast_dvd_coeff_nsmulSeries_sub_coeff_invariantDifferential`.
The universal Weierstrass curve lives over the domain `ℤ[a₁, a₂, a₃, a₄, a₆]`, and every
Weierstrass curve is a specialization of it, so the congruence holds for every `W` and every `R`.
When `p = 0` in `R` it is an equality.

Over a field of characteristic `p`, `Ê` has height one exactly when the coefficient of `Tᵖ` in
`[p]_Ê` is nonzero, hence exactly when the coefficient of `Tᵖ⁻¹` in `P` is nonzero. The first
coefficients of `P` are `1`, `a₁` and `a₁² + a₂`. In characteristic `2` the criterion is therefore
`a₁ ≠ 0`, and in characteristic `3` it is `a₁² + a₂ ≠ 0`, that is `b₂ ≠ 0`. For an elliptic curve
these are the conditions `j ≠ 0`, which characterize ordinary curves in these characteristics.
So in characteristic `2` and `3` the formal group of an elliptic curve has height one exactly when
the curve is ordinary, and height at least two exactly when it is supersingular.

## Main results

* `WeierstrassCurve.natCast_dvd_coeff_nsmulSeries_formalGroup_sub_coeff_invariantDifferential`:
  the coefficient of `Tᵖ` in `[p]_Ê` is congruent modulo `p` to the coefficient of `Tᵖ⁻¹` in the
  invariant differential, over every commutative ring.
* `WeierstrassCurve.coeff_nsmulSeries_formalGroup_eq_coeff_invariantDifferential`: the two
  coefficients agree in characteristic `p`.
* `WeierstrassCurve.height_formalGroup_eq_one_iff`: over a field of characteristic `p`, `Ê` has
  height one exactly when the coefficient of `Tᵖ⁻¹` in the invariant differential is nonzero.
* `WeierstrassCurve.height_formalGroup_eq_one_iff_a₁_ne_zero_of_char_two` and
  `WeierstrassCurve.height_formalGroup_eq_one_iff_b₂_ne_zero_of_char_three`: the explicit
  criteria in characteristic `2` and `3`.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one_of_char_two`,
  `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one_of_char_three`,
  `WeierstrassCurve.isSupersingular_iff_one_lt_height_formalGroup_of_char_two` and
  `WeierstrassCurve.isSupersingular_iff_one_lt_height_formalGroup_of_char_three`: in
  characteristic `2` and `3`, an elliptic curve is ordinary exactly when its formal group has
  height one, and supersingular exactly when the height exceeds one.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, IV.7, V.3 and
  Appendix A.
-/

public section

namespace WeierstrassCurve

section Ring

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {p : ℕ}

/-- **The coefficient of `Tᵖ` in `[p]_Ê` modulo `p`**: for the formal group `Ê` of a Weierstrass
curve over any commutative ring and a prime `p`, the coefficient of `Tᵖ` in `[p]_Ê(T)` is congruent
modulo `p` to the coefficient of `Tᵖ⁻¹` in the invariant differential of `Ê`. -/
theorem natCast_dvd_coeff_nsmulSeries_formalGroup_sub_coeff_invariantDifferential
    (hp : p.Prime) :
    (p : R) ∣ PowerSeries.coeff p ((formalGroup W).nsmulSeries p) -
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential := by
  -- the congruence holds for the universal curve, over the domain `ℤ[a₁, a₂, a₃, a₄, a₆]`
  have h := FormalGroup.natCast_dvd_coeff_nsmulSeries_sub_coeff_invariantDifferential
    (formalGroup Universal.curve) hp
    (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero))
  -- and specializes to `W`
  have := map_dvd W.specialize h
  rw [map_natCast, map_sub, ← PowerSeries.coeff_map, ← PowerSeries.coeff_map,
    FormalGroup.map_nsmulSeries, FormalGroup.map_invariantDifferential, ← map_formalGroup] at this
  simpa only [map_specialize] using this

/-- In characteristic `p`, the coefficient of `Tᵖ` in `[p]_Ê(T)` is the coefficient of `Tᵖ⁻¹` in
the invariant differential of `Ê`. -/
theorem coeff_nsmulSeries_formalGroup_eq_coeff_invariantDifferential [CharP R p] (hp : p.Prime) :
    PowerSeries.coeff p ((formalGroup W).nsmulSeries p) =
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential := by
  have h := W.natCast_dvd_coeff_nsmulSeries_formalGroup_sub_coeff_invariantDifferential hp
  rwa [CharP.cast_eq_zero R p, zero_dvd_iff, sub_eq_zero] at h

end Ring

section Field

variable {K : Type*} [Field K] (W : WeierstrassCurve K) {p : ℕ}

/-- **The height-one criterion for `Ê`**: over a field of characteristic `p`, the formal group of
a Weierstrass curve has height one exactly when the coefficient of `Tᵖ⁻¹` in its invariant
differential is nonzero. -/
theorem height_formalGroup_eq_one_iff [hp : Fact p.Prime] [CharP K p] :
    (formalGroup W).height p = 1 ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rw [FormalGroup.height_eq_one_iff,
    W.coeff_nsmulSeries_formalGroup_eq_coeff_invariantDifferential hp.out]

/-- In characteristic `2`, the formal group of a Weierstrass curve has height one exactly when
`a₁ ≠ 0`. -/
theorem height_formalGroup_eq_one_iff_a₁_ne_zero_of_char_two [CharP K 2] :
    (formalGroup W).height 2 = 1 ↔ W.a₁ ≠ 0 := by
  rw [height_formalGroup_eq_one_iff, coeff_one_invariantDifferential_formalGroup]

/-- In characteristic `3`, the formal group of a Weierstrass curve has height one exactly when
`b₂ ≠ 0`. -/
theorem height_formalGroup_eq_one_iff_b₂_ne_zero_of_char_three [CharP K 3] :
    (formalGroup W).height 3 = 1 ↔ W.b₂ ≠ 0 := by
  -- `b₂ = a₁² + 4a₂` is the quadratic coefficient `a₁² + a₂` of the invariant differential
  have h : W.b₂ = W.a₁ ^ 2 + W.a₂ := by
    rw [b₂]
    linear_combination W.a₂ * CharP.cast_eq_zero K 3
  rw [height_formalGroup_eq_one_iff, coeff_two_invariantDifferential_formalGroup, h]

variable [W.IsElliptic]

/-- **In characteristic `2` an elliptic curve is ordinary exactly when its formal group has height
one.** -/
theorem isOrdinary_iff_height_formalGroup_eq_one_of_char_two [CharP K 2] :
    W.IsOrdinary 2 ↔ (formalGroup W).height 2 = 1 := by
  rw [isOrdinary_iff_j_ne_zero_of_char_two, height_formalGroup_eq_one_iff_a₁_ne_zero_of_char_two,
    Ne, j_eq_zero_iff_of_char_two]

/-- **In characteristic `3` an elliptic curve is ordinary exactly when its formal group has height
one.** -/
theorem isOrdinary_iff_height_formalGroup_eq_one_of_char_three [CharP K 3] :
    W.IsOrdinary 3 ↔ (formalGroup W).height 3 = 1 := by
  rw [isOrdinary_iff_j_ne_zero_of_char_three,
    height_formalGroup_eq_one_iff_b₂_ne_zero_of_char_three, Ne, j_eq_zero_iff_of_char_three]

/-- **In characteristic `2` an elliptic curve is supersingular exactly when its formal group has
height greater than one.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup_of_char_two [CharP K 2] :
    W.IsSupersingular 2 ↔ 1 < (formalGroup W).height 2 := by
  rw [← not_isOrdinary, isOrdinary_iff_height_formalGroup_eq_one_of_char_two,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **In characteristic `3` an elliptic curve is supersingular exactly when its formal group has
height greater than one.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup_of_char_three [CharP K 3] :
    W.IsSupersingular 3 ↔ 1 < (formalGroup W).height 3 := by
  rw [← not_isOrdinary, isOrdinary_iff_height_formalGroup_eq_one_of_char_three,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

end Field

end WeierstrassCurve
