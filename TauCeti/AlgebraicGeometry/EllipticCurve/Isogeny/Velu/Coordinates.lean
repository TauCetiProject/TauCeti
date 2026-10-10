/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.FixedField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Place

/-!
# Vélu's quotient coordinates

For a finite subgroup `Φ` of rational points of an elliptic curve, Vélu's functions are

`X_Φ = x + ∑_{Q ∈ Φ, Q ≠ O} (x ∘ τ_Q - x(Q))`,
`Y_Φ = y + ∑_{Q ∈ Φ, Q ≠ O} (y ∘ τ_Q - y(Q))`.

They are functions in the original function field, invariant under every translation in `Φ`.
Their poles are exactly the places in the `Φ`-orbit of infinity, with orders two and three,
respectively. At infinity only the identity translation contributes a pole. In particular these
functions are nonconstant, even when the characteristic divides the order of `Φ`. They are the
candidate coordinates for an explicit Weierstrass presentation of the translation fixed field;
the equation relating them is not established here.

The sums below include the identity. The coordinate accessors are zero there, and translation
by the identity fixes `x` and `y`, so this is precisely the displayed normalization, not an
average divided by `#Φ`.

## References

* J. Vélu, *Isogénies entre courbes elliptiques*, C. R. Acad. Sci. Paris Sér. A 273 (1971),
  238–241.
* S. Galbraith, *Mathematics of Public Key Cryptography*, §25.1.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate WithZero

namespace TauCeti

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
  (Φ : AddSubgroup (W⁄F).toAffine.Point) [Finite Φ]

attribute [local instance] Fintype.ofFinite

/-- Vélu's normalized `x`-coordinate for the quotient by `Φ`. -/
noncomputable def _root_.WeierstrassCurve.Affine.veluX : W.FunctionField :=
  ∑ Q : Φ, (translation W Q (genericX W) -
    algebraMap F W.FunctionField (Point.xCoord (Q : (W⁄F).toAffine.Point)))

/-- Vélu's normalized `y`-coordinate for the quotient by `Φ`. -/
noncomputable def _root_.WeierstrassCurve.Affine.veluY : W.FunctionField :=
  ∑ Q : Φ, (translation W Q (genericY W) -
    algebraMap F W.FunctionField (Point.yCoord (Q : (W⁄F).toAffine.Point)))

/-- The normalized `x`-coordinate as a sum of translated functions minus a constant. -/
theorem _root_.WeierstrassCurve.Affine.veluX_def :
    veluX W Φ = (∑ Q : Φ, translation W Q (genericX W)) -
      algebraMap F W.FunctionField (∑ Q : Φ, Point.xCoord (Q : (W⁄F).toAffine.Point)) := by
  simp only [veluX, Finset.sum_sub_distrib, map_sum]

/-- The normalized `y`-coordinate as a sum of translated functions minus a constant. -/
theorem _root_.WeierstrassCurve.Affine.veluY_def :
    veluY W Φ = (∑ Q : Φ, translation W Q (genericY W)) -
      algebraMap F W.FunctionField (∑ Q : Φ, Point.yCoord (Q : (W⁄F).toAffine.Point)) := by
  simp only [veluY, Finset.sum_sub_distrib, map_sum]

/-- Every translation by a point of `Φ` fixes Vélu's `x`-coordinate. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.translation_veluX (P : Φ) :
    translation W P (veluX W Φ) = veluX W Φ := by
  rw [veluX_def, map_sub, translation_sum, AlgEquiv.commutes]

/-- Every translation by a point of `Φ` fixes Vélu's `y`-coordinate. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.translation_veluY (P : Φ) :
    translation W P (veluY W Φ) = veluY W Φ := by
  rw [veluY_def, map_sub, translation_sum, AlgEquiv.commutes]

/-- Vélu's `x`-coordinate belongs to the translation fixed field. -/
theorem _root_.WeierstrassCurve.Affine.veluX_mem_translationFixedField :
    veluX W Φ ∈ translationFixedField W Φ := by
  rw [mem_translationFixedField_iff]
  exact fun P hP ↦ translation_veluX W Φ ⟨P, hP⟩

/-- Vélu's `y`-coordinate belongs to the translation fixed field. -/
theorem _root_.WeierstrassCurve.Affine.veluY_mem_translationFixedField :
    veluY W Φ ∈ translationFixedField W Φ := by
  rw [mem_translationFixedField_iff]
  exact fun P hP ↦ translation_veluY W Φ ⟨P, hP⟩

private theorem valuation_normalized_sum (r : W.CoordinateRing) (c : F)
    (hr : 1 < W.infinityPlace (algebraMap W.CoordinateRing W.FunctionField r)) :
    W.infinityPlace ((∑ Q : Φ,
      translation W Q (algebraMap W.CoordinateRing W.FunctionField r)) -
        algebraMap F W.FunctionField c) =
      W.infinityPlace (algebraMap W.CoordinateRing W.FunctionField r) := by
  classical
  have hsum : W.infinityPlace (∑ Q : Φ,
      translation W Q (algebraMap W.CoordinateRing W.FunctionField r)) =
      W.infinityPlace (algebraMap W.CoordinateRing W.FunctionField r) := by
    have hzero : translation W (0 : Φ) (algebraMap W.CoordinateRing W.FunctionField r) =
        algebraMap W.CoordinateRing W.FunctionField r := by simp
    have h := W.infinityPlace.map_sum_eq_of_lt (f := fun Q : Φ ↦
      translation W Q (algebraMap W.CoordinateRing W.FunctionField r))
      (Finset.mem_univ (0 : Φ)) (fun Q hQ ↦ ?_)
    · simpa only [hzero] using h
    · rw [hzero]
      have hQ0 : Q ≠ 0 := by simpa using (Finset.mem_sdiff.mp hQ).2
      exact (valuation_translation_le_one W (by
        intro h; exact hQ0 (Subtype.ext h)) r).trans_lt hr
  rw [Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt
    (Valuation.IsTrivialOn.valuation_algebraMap_le_one W.infinityPlace c) (hsum ▸ hr)), hsum]

/-- Vélu's `x`-coordinate has the same double pole at infinity as `x`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.infinityPlace_veluX :
    W.infinityPlace (veluX W Φ) = WithZero.exp (2 : ℤ) := by
  rw [veluX_def, genericX_def, valuation_normalized_sum]
  · exact infinityPlace.X W
  · simpa only [← genericX_def, genericX_eq_algebraMap] using W.one_lt_infinityPlace_X

/-- Vélu's `y`-coordinate has the same triple pole at infinity as `y`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.infinityPlace_veluY :
    W.infinityPlace (veluY W Φ) = WithZero.exp (3 : ℤ) := by
  rw [veluY_def, genericY_def, valuation_normalized_sum]
  · exact infinityPlace.mk_Y W
  · rw [infinityPlace.mk_Y W, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

/-- Vélu's `x`-coordinate is nonzero, including when the characteristic divides `#Φ`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.veluX_ne_zero : veluX W Φ ≠ 0 := by
  intro h
  have hv := infinityPlace_veluX W Φ
  rw [h, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-- Vélu's `y`-coordinate is nonzero, including when the characteristic divides `#Φ`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.veluY_ne_zero : veluY W Φ ≠ 0 := by
  intro h
  have hv := infinityPlace_veluY W Φ
  rw [h, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-- The order of Vélu's `x`-coordinate at infinity is `-2`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.ord_infinity_veluX :
    (Place.infinity W).ord (veluX W Φ) = -2 := by
  rw [(Place.infinity W).ord_eq_iff_valuation_eq_exp_neg (veluX_ne_zero W Φ)]
  simp

/-- The order of Vélu's `y`-coordinate at infinity is `-3`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.ord_infinity_veluY :
    (Place.infinity W).ord (veluY W Φ) = -3 := by
  rw [(Place.infinity W).ord_eq_iff_valuation_eq_exp_neg (veluY_ne_zero W Φ)]
  simp

/-- Vélu's `x`-coordinate is transcendental over the ground field. -/
theorem _root_.WeierstrassCurve.Affine.transcendental_veluX :
    Transcendental F (veluX W Φ) :=
  (Place.infinity W).transcendental_of_ord_ne_zero (by simp)

/-- Vélu's `y`-coordinate is transcendental over the ground field. -/
theorem _root_.WeierstrassCurve.Affine.transcendental_veluY :
    Transcendental F (veluY W Φ) :=
  (Place.infinity W).transcendental_of_ord_ne_zero (by simp)

/-- Every place in the subgroup orbit is a double pole of Vélu's `x`-coordinate. -/
theorem _root_.WeierstrassCurve.Affine.ord_translation_infinity_veluX (Q : Φ) :
    (translation W Q • Place.infinity W).ord (veluX W Φ) = -2 := by
  rw [Place.ord_smul, ← AlgEquiv.aut_inv, ← translation_neg]
  simpa only [AddSubgroup.coe_neg] using
    congrArg (Place.infinity W).ord (translation_veluX W Φ (-Q)) |>.trans
      (ord_infinity_veluX W Φ)

/-- Every place in the subgroup orbit is a triple pole of Vélu's `y`-coordinate. -/
theorem _root_.WeierstrassCurve.Affine.ord_translation_infinity_veluY (Q : Φ) :
    (translation W Q • Place.infinity W).ord (veluY W Φ) = -3 := by
  rw [Place.ord_smul, ← AlgEquiv.aut_inv, ← translation_neg]
  simpa only [AddSubgroup.coe_neg] using
    congrArg (Place.infinity W).ord (translation_veluY W Φ (-Q)) |>.trans
      (ord_infinity_veluY W Φ)

private theorem valuation_normalized_sum_le_one (r : W.CoordinateRing) (c : F)
    (P : Place F W.FunctionField)
    (hP : ∀ Q : Φ, P ≠ translation W Q • Place.infinity W) :
    P.valuation ((∑ Q : Φ,
      translation W Q (algebraMap W.CoordinateRing W.FunctionField r)) -
        algebraMap F W.FunctionField c) ≤ 1 := by
  apply P.valuation.map_sub_le _ (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _)
  apply P.valuation.map_sum_le
  intro Q _
  have hQ : (translation W Q)⁻¹ • P ≠ Place.infinity W :=
    fun h ↦ hP Q (inv_smul_eq_iff.mp h)
  simpa only [Place.valuation_smul, AlgEquiv.aut_inv, AlgEquiv.symm_symm] using
    Place.valuation_algebraMap_le_one_of_ne_infinity hQ r

/-- Vélu's `x`-coordinate is regular away from the subgroup orbit. -/
theorem _root_.WeierstrassCurve.Affine.valuation_veluX_le_one
    (P : Place F W.FunctionField)
    (hP : ∀ Q : Φ, P ≠ translation W Q • Place.infinity W) :
    P.valuation (veluX W Φ) ≤ 1 := by
  rw [veluX_def, genericX_def]
  exact valuation_normalized_sum_le_one W Φ _ _ P hP

/-- Vélu's `y`-coordinate is regular away from the subgroup orbit. -/
theorem _root_.WeierstrassCurve.Affine.valuation_veluY_le_one
    (P : Place F W.FunctionField)
    (hP : ∀ Q : Φ, P ≠ translation W Q • Place.infinity W) :
    P.valuation (veluY W Φ) ≤ 1 := by
  rw [veluY_def, genericY_def]
  exact valuation_normalized_sum_le_one W Φ _ _ P hP

/-- The poles of Vélu's `x`-coordinate are exactly the places in the subgroup orbit. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.one_lt_valuation_veluX_iff
    (P : Place F W.FunctionField) :
    1 < P.valuation (veluX W Φ) ↔ ∃ Q : Φ, P = translation W Q • Place.infinity W := by
  classical
  refine ⟨fun h ↦ by
    by_contra hn
    exact h.not_ge (valuation_veluX_le_one W Φ P (by simpa using hn)), ?_⟩
  rintro ⟨Q, rfl⟩
  rw [Place.valuation_eq_exp_neg_ord _ (veluX_ne_zero W Φ),
    ord_translation_infinity_veluX, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/-- The poles of Vélu's `y`-coordinate are exactly the places in the subgroup orbit. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.one_lt_valuation_veluY_iff
    (P : Place F W.FunctionField) :
    1 < P.valuation (veluY W Φ) ↔ ∃ Q : Φ, P = translation W Q • Place.infinity W := by
  classical
  refine ⟨fun h ↦ by
    by_contra hn
    exact h.not_ge (valuation_veluY_le_one W Φ P (by simpa using hn)), ?_⟩
  rintro ⟨Q, rfl⟩
  rw [Place.valuation_eq_exp_neg_ord _ (veluY_ne_zero W Φ),
    ord_translation_infinity_veluY, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

end TauCeti

end
