/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
import Mathlib.Algebra.CharP.Two
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Height two for supersingular elliptic curves in characteristic two

An elliptic Weierstrass curve in characteristic two has formal-group height one or two.
Its height is two exactly when `a₁ = 0`, equivalently when it is supersingular. The ellipticity
hypothesis matters: the formal group of a singular cubic can have infinite height.

Over any commutative ring of characteristic two, when `a₁ = 0`, the doubling series begins
`[2](T) = a₃ T⁴ + ⋯`. Indeed, the inverse parameter is `T / (1 - a₃ w(T))` with
`w(T) = T³ + ⋯`. Comparing addition at the pairs `(T, T)` and `(ι(T), T)` gives the asserted
leading term, using `PowerSeries.coeff_subst_update_add_X_pow_mul`. For an elliptic curve,
`a₁ = 0` forces `a₃ ≠ 0`, so this term gives height exactly two.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, IV.7 and V.3.
-/

public section

namespace WeierstrassCurve

section Ring

variable {R : Type*} [CommRing R] [CharP R 2] (W : WeierstrassCurve R)

/-- If `a₁ = 0` in characteristic two, the doubling series has no terms below degree four,
and its coefficient in degree four is `a₃`. No smoothness or field hypothesis is needed. -/
theorem coeff_nsmulSeries_two_formalGroup_of_char_two (h₁ : W.a₁ = 0) {n : ℕ} (hn : n ≤ 4) :
    PowerSeries.coeff n ((formalGroup W).nsmulSeries 2) = if n = 4 then W.a₃ else 0 := by
  let d := PowerSeries.invOfUnit W.formalInverseDenom 1
  let r := -(PowerSeries.C W.a₃ * W.formalU * d)
  have hfactor : W.formalInverse + PowerSeries.X ^ 4 * r = PowerSeries.X := by
    have hd := W.mul_invOfUnit_formalInverseDenom
    rw [formalInverseDenom_def, h₁, map_zero, zero_mul, sub_zero] at hd
    dsimp [r, d]
    simp only [formalInverse_def, formalInverseDenom_def, h₁, map_zero, zero_mul,
      sub_zero, formalW_eq_X_pow_mul_formalU] at hd ⊢
    have h2 : (2 : PowerSeries R) = 0 := by
      simpa only [map_ofNat, map_zero, Nat.cast_ofNat] using
        congrArg PowerSeries.C (CharP.cast_eq_zero R 2)
    linear_combination (norm := ring_nf) -PowerSeries.X * hd
    simp [h2]
  have h := (formalGroup W).coeff_nsmulSeries_succ_of_eq_addInvX_add_X_pow_mul
    (n := 1) (s := r) (by rw [FormalGroup.nsmulSeries_one, formalGroup_addInvX, hfactor])
    (by decide : (4 : ℕ) ≠ 0) hn
  simpa [r, d, CharTwo.neg_eq] using h

end Ring

section Field

variable {K : Type*} [Field K] [CharP K 2] (W : WeierstrassCurve K) [W.IsElliptic]

/-- In characteristic two, an elliptic curve has formal-group height two exactly when `a₁ = 0`.
-/
theorem height_formalGroup_eq_two_iff_a₁_eq_zero_of_char_two :
    (formalGroup W).height 2 = 2 ↔ W.a₁ = 0 := by
  constructor
  · intro h
    by_contra h₁
    have h' := (W.height_formalGroup_eq_one_iff_a₁_ne_zero_of_char_two).mpr h₁
    rw [h] at h'
    exact (by decide : (2 : ℕ∞) ≠ 1) h'
  · intro h₁
    have h₃ := (W.a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero_of_two_eq_zero
      (W.isUnit_Δ.ne_zero) (CharP.cast_eq_zero K 2)).resolve_left (not_not.mpr h₁)
    apply (formalGroup W).height_eq_natCast_iff.mpr
    norm_num only [Nat.reducePow]
    rw [← Nat.cast_ofNat (R := ℕ∞), PowerSeries.order_eq_nat]
    constructor
    · simpa only [W.coeff_nsmulSeries_two_formalGroup_of_char_two h₁ le_rfl, ite_true]
        using h₃
    · intro i hi
      simpa [ne_of_lt hi] using
        W.coeff_nsmulSeries_two_formalGroup_of_char_two h₁ hi.le

/-- In characteristic two, an elliptic curve has formal-group height one or two. -/
theorem height_formalGroup_eq_one_or_eq_two_of_char_two :
    (formalGroup W).height 2 = 1 ∨ (formalGroup W).height 2 = 2 := by
  by_cases h₁ : W.a₁ = 0
  · exact Or.inr (W.height_formalGroup_eq_two_iff_a₁_eq_zero_of_char_two.mpr h₁)
  · exact Or.inl (W.height_formalGroup_eq_one_iff_a₁_ne_zero_of_char_two.mpr h₁)

/-- In characteristic two, an elliptic curve is supersingular exactly when its formal group has
height two. -/
theorem isSupersingular_iff_height_formalGroup_eq_two_of_char_two :
    W.IsSupersingular 2 ↔ (formalGroup W).height 2 = 2 := by
  rw [isSupersingular_iff_j_eq_zero_of_char_two, j_eq_zero_iff_of_char_two,
    height_formalGroup_eq_two_iff_a₁_eq_zero_of_char_two]

end Field

end WeierstrassCurve
