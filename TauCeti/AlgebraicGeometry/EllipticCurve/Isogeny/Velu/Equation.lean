/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Lift
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.FixedField
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
import Mathlib.RingTheory.Valuation.IsTrivialOn
import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
import TauCeti.RingTheory.Valuation.PowSubPow

/-!
# The Weierstrass equation of Vélu's coordinates

For a finite subgroup `Φ` of rational points of an elliptic curve `W` over `F`, Vélu's functions
`X = veluX W Φ` and `Y = veluY W Φ` generate the field fixed by the translations in `Φ`. This file
shows that they satisfy the affine equation of a Weierstrass curve over `F`,

`Y² + A₁XY + A₃Y = X³ + A₂X² + A₄X + A₆`,

and that exactly one Weierstrass curve over `F` has this property. This curve `veluCurve W Φ` is
the quotient curve `W / Φ`: its function field, embedded in `F(W)` by sending its generic point to
`(X, Y)`, is the translation fixed field. This works in every characteristic, including when the
characteristic divides `#Φ`.

The coefficients `A₁` and `A₂` agree with those of `W`. This follows by comparing the terms
of pole orders five and four, using that `X - x` and `Y - y` vanish at infinity.
The isogeny `W → veluCurve W Φ` and nonsingularity of `veluCurve W Φ` are in
`Isogeny/Velu/Isogeny.lean`.

## Main definitions

* `WeierstrassCurve.Affine.veluCurve`: the Weierstrass curve over `F` whose equation Vélu's
  coordinates satisfy.

## Main results

* `WeierstrassCurve.Affine.equation_veluX_veluY`: Vélu's coordinates satisfy the equation of
  `veluCurve W Φ`.
* `WeierstrassCurve.Affine.veluCurve_a₁` and `WeierstrassCurve.Affine.veluCurve_a₂`: the first
  two coefficients are unchanged.
* `WeierstrassCurve.Affine.eq_veluCurve_of_equation` and
  `WeierstrassCurve.Affine.equation_veluX_veluY_iff`: no other Weierstrass curve over `F` has
  this property.
* `WeierstrassCurve.Affine.fieldRange_functionFieldLift_veluCurve`: the function field of
  `veluCurve W Φ` is the translation fixed field.

## Implementation notes

No expansion of the translated coordinates at infinity is needed. The functions `X` and `Y` have
poles only in the orbit of infinity under `Φ`, so `Y` is integral over `F[X]`, and since the fixed
field has degree two over `F(X)` its minimal polynomial is `T² + p(X) T + q(X)` with
`p, q ∈ F[X]`. At infinity `X` and `Y` have poles of orders two and three, so `p(X) Y` has a pole
of odd order and `q(X)` one of even order; comparing with the pole of order six of `Y²` gives
`deg q = 3` and `deg p ≤ 1`. Since `X - x` and `Y - y` are regular at infinity, `Y² - X³` has a
pole of order less than six, which forces the leading coefficient of `q` to be `-1`. Uniqueness
holds because `1, X, Y, X², XY` have distinct pole orders at infinity.

## References

* J. Vélu, *Isogénies entre courbes elliptiques*, C. R. Acad. Sci. Paris Sér. A 273 (1971),
  238–241.
* S. Galbraith, *Mathematics of Public Key Cryptography*, §25.1.
-/

public section

open scoped IntermediateField Polynomial WithZero

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
  (Φ : AddSubgroup (W⁄F).toAffine.Point) [Finite Φ]

attribute [local instance] Fintype.ofFinite

/-- Vélu's `y`-coordinate is integral over the polynomial ring in Vélu's `x`-coordinate: its
poles lie among those of `x`. -/
private theorem isIntegral_veluY :
    IsIntegral (Algebra.adjoin F {veluX W Φ}) (veluY W Φ) := by
  rw [← mem_integralClosure_iff, mem_integralClosure_adjoin_iff W.isFunctionField]
  intro P hP
  rw [Place.mem_integers_iff] at hP ⊢
  refine valuation_veluY_le_one W Φ P fun Q hQ ↦ ?_
  have := (one_lt_valuation_veluX_iff W Φ P).mpr ⟨Q, hQ⟩
  exact (hP.trans_lt this).false

/-- **The quadratic relation**: Vélu's `y`-coordinate satisfies `Y² + p(X) Y + q(X) = 0` for
polynomials `p` and `q` over `F`. -/
private theorem exists_sq_add_mul_add_eq_zero :
    ∃ p q : F[X], veluY W Φ ^ 2 + Polynomial.aeval (veluX W Φ) p * veluY W Φ +
      Polynomial.aeval (veluX W Φ) q = 0 := by
  open IntermediateField.algebraAdjoinAdjoin in
  set X := veluX W Φ
  set Y := veluY W Φ
  let R := Algebra.adjoin F {X}
  have hX := transcendental_veluX W Φ
  have : IsIntegrallyClosed R :=
    IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental F X hX).toRingEquiv
  have hint := isIntegral_veluY W Φ
  -- The minimal polynomial over `F(X)` comes from `F[X]` and has degree `[F(X, Y) : F(X)] = 2`.
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' F⟮X⟯ hint
  have hdeg : (minpoly F⟮X⟯ Y).natDegree = 2 := by
    have hle : F⟮X⟯ ≤ F⟮X, Y⟯ := IntermediateField.adjoin.mono _ _ _
      (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    have h2 := relfinrank_adjoin_veluX_translationFixedField W Φ
    rw [← adjoin_veluX_veluY_eq_translationFixedField W Φ,
      IntermediateField.relfinrank_eq_finrank_of_le hle,
      IntermediateField.extendScalars_adjoin hle] at h2
    have hXY : (F⟮X⟯)⟮X, Y⟯ = (F⟮X⟯)⟮Y⟯ := by
      refine le_antisymm ?_ (IntermediateField.adjoin.mono _ _ _ (Set.subset_insert _ _))
      rw [IntermediateField.adjoin_le_iff]
      rintro z (rfl | rfl)
      · simpa using IntermediateField.algebraMap_mem (F⟮X⟯)⟮Y⟯
          (IntermediateField.AdjoinSimple.gen F X)
      · exact IntermediateField.mem_adjoin_simple_self _ _
    rw [← IntermediateField.adjoin.finrank (hint.tower_top), ← h2, hXY]
  have hmonic := minpoly.monic hint
  have hdegR : (minpoly R Y).natDegree = 2 := by
    rw [← hdeg, hmap, Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective R F⟮X⟯)]
  obtain ⟨p, hp⟩ := Algebra.adjoin_mem_exists_aeval F X ((minpoly R Y).coeff 1).property
  obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval F X ((minpoly R Y).coeff 0).property
  refine ⟨p, q, ?_⟩
  have h := minpoly.aeval R Y
  rw [Polynomial.aeval_eq_sum_range, hdegR] at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  rw [← hdegR, hmonic.coeff_natDegree, hdegR] at h
  rw [hp, hq]
  simpa [Algebra.smul_def, add_comm, add_left_comm, add_assoc] using h

/-- The value at infinity of a nonzero polynomial in Vélu's `x`-coordinate: a pole of order
twice its degree. -/
private theorem infinityPlace_aeval_veluX {p : F[X]} (hp : p ≠ 0) :
    W.infinityPlace (Polynomial.aeval (veluX W Φ) p) = WithZero.exp (2 * p.natDegree : ℤ) := by
  rw [Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
      (v := W.infinityPlace) _ ?_ hp, infinityPlace_veluX, ← WithZero.exp_nsmul, nsmul_eq_mul,
    mul_comm]
  rw [infinityPlace_veluX, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/-- For `q ≠ 0` the summands of `p(X) Y + q(X)` have different values at infinity, their pole
orders having different parities. -/
private theorem infinityPlace_aeval_mul_add {p q : F[X]} (hq : q ≠ 0) :
    W.infinityPlace (Polynomial.aeval (veluX W Φ) p * veluY W Φ +
        Polynomial.aeval (veluX W Φ) q) =
      max (W.infinityPlace (Polynomial.aeval (veluX W Φ) p * veluY W Φ))
        (WithZero.exp (2 * q.natDegree : ℤ)) := by
  rw [← infinityPlace_aeval_veluX W Φ hq]
  refine Valuation.map_add_of_distinct_val _ ?_
  rw [infinityPlace_aeval_veluX W Φ hq]
  rcases eq_or_ne p 0 with rfl | hp
  · simpa using WithZero.exp_ne_zero.symm
  · rw [map_mul, infinityPlace_aeval_veluX W Φ hp, infinityPlace_veluY, ← WithZero.exp_add,
      Ne, WithZero.exp_inj]
    omega

/-- Replacing the original coordinates by Vélu's coordinates changes `y² - x³` by a
function with pole order strictly below four at infinity. -/
private theorem infinityPlace_veluY_sq_sub_veluX_pow_three_sub_lt :
    W.infinityPlace ((veluY W Φ ^ 2 - veluX W Φ ^ 3) -
        (genericY W ^ 2 - genericX W ^ 3)) < WithZero.exp 4 := by
  have hdecomp : (veluY W Φ ^ 2 - veluX W Φ ^ 3) - (genericY W ^ 2 - genericX W ^ 3) =
      (veluY W Φ ^ 2 - genericY W ^ 2) - (veluX W Φ ^ 3 - genericX W ^ 3) := by ring
  rw [hdecomp]
  refine W.infinityPlace.map_sub_lt ?_ ?_
  · refine (W.infinityPlace.map_pow_sub_pow_le
      (infinityPlace_veluY W Φ).le (infinityPlace_genericY W).le 2).trans_lt ?_
    simpa only [Nat.reduceSub, pow_one] using
      (mul_lt_of_lt_one_left WithZero.exp_pos (infinityPlace_veluY_sub_genericY_lt_one W Φ)).trans
        (WithZero.exp_lt_exp.mpr (by decide : (3 : ℤ) < 4))
  · refine (W.infinityPlace.map_pow_sub_pow_le
      (infinityPlace_veluX W Φ).le (infinityPlace_genericX W).le 3).trans_lt ?_
    have hpow : WithZero.exp (2 : ℤ) ^ (3 - 1) = WithZero.exp 4 := by
      norm_num [← WithZero.exp_nsmul]
    rw [hpow]
    exact mul_lt_of_lt_one_left WithZero.exp_pos (infinityPlace_veluX_sub_genericX_lt_one W Φ)

/-- `Y² - X³` has a pole of order at most five at infinity, since replacing the original
coordinates does not affect terms of pole order four or greater. -/
private theorem infinityPlace_veluY_sq_sub_veluX_pow_three_le :
    W.infinityPlace (veluY W Φ ^ 2 - veluX W Φ ^ 3) ≤ WithZero.exp 5 := by
  have heq := (equation_baseChange_iff _ _ _).mp (equation_genericX_genericY W)
  have hgeneric : genericY W ^ 2 - genericX W ^ 3 =
      algebraMap F _ W.a₂ * genericX W ^ 2 + algebraMap F _ W.a₄ * genericX W +
        algebraMap F _ W.a₆ - algebraMap F _ W.a₁ * (genericX W * genericY W) -
        algebraMap F _ W.a₃ * genericY W := by linear_combination heq
  have hc (a : F) (z : W.FunctionField) :
      W.infinityPlace (algebraMap F _ a * z) ≤ W.infinityPlace z := by
    rw [map_mul]
    exact mul_le_of_le_one_left' (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _)
  have hval : W.infinityPlace (genericY W ^ 2 - genericX W ^ 3) ≤ WithZero.exp 5 := by
    rw [hgeneric]
    repeat' first | apply W.infinityPlace.map_sub_le | apply W.infinityPlace.map_add_le
    · exact (hc _ _).trans (by norm_num [map_pow, infinityPlace_genericX, ← WithZero.exp_nsmul])
    · exact (hc _ _).trans (by simp [infinityPlace_genericX])
    · exact (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _).trans (by simp)
    · exact (hc _ _).trans (by simp [map_mul, infinityPlace_genericX, infinityPlace_genericY,
        ← WithZero.exp_add])
    · exact (hc _ _).trans (by simp [infinityPlace_genericY])
  simpa only [sub_add_cancel] using W.infinityPlace.map_add_le
    ((infinityPlace_veluY_sq_sub_veluX_pow_three_sub_lt W Φ).le.trans
      (WithZero.exp_le_exp.mpr (by norm_num))) hval

section Relation

variable {W Φ} {p q : F[X]}
  (h : veluY W Φ ^ 2 + Polynomial.aeval (veluX W Φ) p * veluY W Φ +
    Polynomial.aeval (veluX W Φ) q = 0)
include h

/-- In the quadratic relation `Y² + p(X) Y + q(X) = 0`, the polynomial `q` is nonzero: otherwise
`Y = -p(X)` would have a pole of even order at infinity. -/
private theorem ne_zero_of_sq_add_mul_add_eq_zero : q ≠ 0 := by
  set X := veluX W Φ
  set Y := veluY W Φ
  rintro rfl
  have hY0 : Y ≠ 0 := veluY_ne_zero W Φ
  have hYp : Y + Polynomial.aeval X p = 0 := by
    have h' : Y ^ 2 + Polynomial.aeval X p * Y = 0 := by simpa using h
    have : Y * (Y + Polynomial.aeval X p) = 0 := by linear_combination h'
    exact (mul_eq_zero.mp this).resolve_left hY0
  rcases eq_or_ne p 0 with rfl | hp
  · exact hY0 (by simpa using hYp)
  · have hv : W.infinityPlace Y = W.infinityPlace (Polynomial.aeval X p) := by
      rw [eq_neg_of_add_eq_zero_left hYp, Valuation.map_neg]
    rw [infinityPlace_veluY, infinityPlace_aeval_veluX W Φ hp, WithZero.exp_inj] at hv
    omega

/-- In the quadratic relation `Y² + p(X) Y + q(X) = 0`, comparing poles at infinity with the pole
of order six of `Y²` gives `deg q = 3` and a pole of order at most five for `p(X) Y`. -/
private theorem natDegree_eq_three_and_infinityPlace_le_of_sq_add_mul_add_eq_zero :
    q.natDegree = 3 ∧
      W.infinityPlace (Polynomial.aeval (veluX W Φ) p * veluY W Φ) ≤ WithZero.exp 5 := by
  set X := veluX W Φ
  set Y := veluY W Φ
  set v := W.infinityPlace
  have hq := ne_zero_of_sq_add_mul_add_eq_zero h
  have hrel : v (Polynomial.aeval X p * Y + Polynomial.aeval X q) = WithZero.exp 6 := by
    rw [show Polynomial.aeval X p * Y + Polynomial.aeval X q = -(Y ^ 2) by linear_combination h,
      Valuation.map_neg, map_pow, infinityPlace_veluY, ← WithZero.exp_nsmul]
    norm_num
  rw [infinityPlace_aeval_mul_add W Φ hq] at hrel
  rcases max_choice (v (Polynomial.aeval X p * Y)) (WithZero.exp (2 * q.natDegree : ℤ))
    with hm | hm
  · -- The pole of `p(X) Y` has odd order, so it cannot be the pole of order six.
    rw [hm] at hrel
    rcases eq_or_ne p 0 with rfl | hp
    · simp only [map_zero, zero_mul] at hrel
      exact (WithZero.exp_ne_zero hrel.symm).elim
    · rw [map_mul, infinityPlace_aeval_veluX W Φ hp, infinityPlace_veluY, ← WithZero.exp_add,
        WithZero.exp_inj] at hrel
      omega
  · have hle := hm ▸ le_max_left (v (Polynomial.aeval X p * Y))
      (WithZero.exp (2 * q.natDegree : ℤ))
    rw [hm, WithZero.exp_inj] at hrel
    refine ⟨by omega, ?_⟩
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    · rw [map_mul, infinityPlace_aeval_veluX W Φ hp, infinityPlace_veluY,
        ← WithZero.exp_add, WithZero.exp_le_exp] at hle ⊢
      omega

/-- In the quadratic relation `Y² + p(X) Y + q(X) = 0`, the polynomial `p` has degree at most
one. -/
private theorem natDegree_le_one_of_sq_add_mul_add_eq_zero : p.natDegree ≤ 1 := by
  have hle := (natDegree_eq_three_and_infinityPlace_le_of_sq_add_mul_add_eq_zero h).2
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [map_mul, infinityPlace_aeval_veluX W Φ hp, infinityPlace_veluY, ← WithZero.exp_add,
      WithZero.exp_le_exp] at hle
    omega

/-- In the quadratic relation `Y² + p(X) Y + q(X) = 0`, the leading coefficient of `q` is `-1`:
otherwise `Y² - X³` would have a pole of order six at infinity. -/
private theorem coeff_three_eq_neg_one_of_sq_add_mul_add_eq_zero : q.coeff 3 = -1 := by
  set X := veluX W Φ
  set Y := veluY W Φ
  obtain ⟨hqdeg, hpY⟩ := natDegree_eq_three_and_infinityPlace_le_of_sq_add_mul_add_eq_zero h
  by_contra hne
  set q' := q + Polynomial.X ^ 3
  have hq'3 : q'.coeff 3 ≠ 0 := by
    simp only [q', Polynomial.coeff_add, Polynomial.coeff_X_pow_self]
    exact fun h0 ↦ hne (eq_neg_of_add_eq_zero_left h0)
  have hq'0 : q' ≠ 0 := fun h0 ↦ hq'3 (by rw [h0, Polynomial.coeff_zero])
  have hq'deg : q'.natDegree = 3 :=
    le_antisymm ((Polynomial.natDegree_add_le _ _).trans (by simp [hqdeg]))
      (Polynomial.le_natDegree_of_ne_zero hq'3)
  have hv := infinityPlace_aeval_mul_add W Φ (p := p) hq'0
  rw [hq'deg, max_eq_right (hpY.trans (WithZero.exp_le_exp.mpr (by norm_num)))] at hv
  have hsub : Polynomial.aeval X p * Y + Polynomial.aeval X q' = -(Y ^ 2 - X ^ 3) := by
    simp only [q', map_add, map_pow, Polynomial.aeval_X]
    linear_combination h
  rw [hsub, Valuation.map_neg] at hv
  have := infinityPlace_veluY_sq_sub_veluX_pow_three_le W Φ
  rw [hv, WithZero.exp_le_exp] at this
  norm_num at this

end Relation

/-- **Vélu's coordinates satisfy a Weierstrass equation** over `F`: the quadratic relation
`Y² + p(X) Y + q(X) = 0`, with `deg p ≤ 1` and `q` of degree three with leading coefficient `-1`,
is such an equation. -/
private theorem exists_equation_veluX_veluY :
    ∃ W' : WeierstrassCurve F,
      (W'.baseChange W.FunctionField).toAffine.Equation (veluX W Φ) (veluY W Φ) := by
  obtain ⟨p, q, h⟩ := exists_sq_add_mul_add_eq_zero W Φ
  refine ⟨⟨p.coeff 1, -q.coeff 2, p.coeff 0, -q.coeff 1, -q.coeff 0⟩, ?_⟩
  rw [equation_baseChange_iff]
  have hp := Polynomial.aeval_eq_sum_range' (n := 2)
    (Nat.lt_succ_of_le (natDegree_le_one_of_sq_add_mul_add_eq_zero h)) (veluX W Φ)
  have hq := Polynomial.aeval_eq_sum_range' (n := 4)
    (by rw [(natDegree_eq_three_and_infinityPlace_le_of_sq_add_mul_add_eq_zero h).1]; norm_num)
    (veluX W Φ)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Algebra.smul_def, coeff_three_eq_neg_one_of_sq_add_mul_add_eq_zero h, map_neg,
    map_one] at hp hq
  simp only [map_neg]
  rw [hp, hq] at h
  linear_combination h

/-- **The quotient curve `W / Φ`**: the Weierstrass curve over `F` whose affine equation is
satisfied by Vélu's coordinates `veluX W Φ` and `veluY W Φ`. No other Weierstrass curve over `F`
has this property (`WeierstrassCurve.Affine.eq_veluCurve_of_equation`). -/
noncomputable def _root_.WeierstrassCurve.Affine.veluCurve : WeierstrassCurve F :=
  (exists_equation_veluX_veluY W Φ).choose

/-- **Vélu's coordinates satisfy the Weierstrass equation of the quotient curve**:
`Y² + A₁XY + A₃Y = X³ + A₂X² + A₄X + A₆`, with the coefficients `Aᵢ` of `veluCurve W Φ`. -/
theorem _root_.WeierstrassCurve.Affine.equation_veluX_veluY :
    ((veluCurve W Φ).baseChange W.FunctionField).toAffine.Equation (veluX W Φ) (veluY W Φ) :=
  (exists_equation_veluX_veluY W Φ).choose_spec

/-- The two highest pole terms in the difference of the Weierstrass equations cancel up to
terms of pole order strictly below four. -/
private theorem infinityPlace_veluCurve_coeff_difference_lt :
    W.infinityPlace
        (algebraMap F _ ((veluCurve W Φ).a₁ - W.a₁) * (veluX W Φ * veluY W Φ) -
          algebraMap F _ ((veluCurve W Φ).a₂ - W.a₂) * veluX W Φ ^ 2) < WithZero.exp 4 := by
  set v := W.infinityPlace
  set X := veluX W Φ
  set Y := veluY W Φ
  set x := genericX W
  set y := genericY W
  set V := veluCurve W Φ
  let C := algebraMap F W.FunctionField
  have hc (a : F) (z : W.FunctionField) : v (C a * z) ≤ v z := by
    rw [map_mul]
    exact mul_le_of_le_one_left' (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _)
  have hx := infinityPlace_veluX_sub_genericX_lt_one W Φ
  have hXY : v (X * Y - x * y) < WithZero.exp 4 := by
    have h : X * Y - x * y = (X - x) * Y + x * (Y - y) := by ring
    rw [h]
    refine v.map_add_lt ?_ ?_
    · rw [map_mul, infinityPlace_veluY]
      exact (mul_le_of_le_one_left' hx.le).trans_lt (by simp)
    · rw [map_mul, infinityPlace_genericX]
      exact (mul_le_of_le_one_right' (infinityPlace_veluY_sub_genericY_lt_one W Φ).le).trans_lt
        (by simp)
  have hX2 : v (X ^ 2 - x ^ 2) < WithZero.exp 4 := by
    refine (v.map_pow_sub_pow_le (infinityPlace_veluX W Φ).le
      (infinityPlace_genericX W).le 2).trans_lt ?_
    exact (mul_le_of_le_one_left' hx.le).trans_lt (by simp)
  have hW := (equation_baseChange_iff _ _ _).mp (equation_genericX_genericY W)
  have hV := (equation_baseChange_iff _ _ _).mp (equation_veluX_veluY W Φ)
  have h : C (V.a₁ - W.a₁) * (X * Y) - C (V.a₂ - W.a₂) * X ^ 2 =
      -((Y ^ 2 - X ^ 3) - (y ^ 2 - x ^ 3)) - C W.a₁ * (X * Y - x * y) +
        C W.a₂ * (X ^ 2 - x ^ 2) - C V.a₃ * Y + C W.a₃ * y +
        C V.a₄ * X - C W.a₄ * x + C (V.a₆ - W.a₆) := by grind
  rw [h]
  repeat' first | apply v.map_sub_lt | apply v.map_add_lt
  · simpa only [Valuation.map_neg] using infinityPlace_veluY_sq_sub_veluX_pow_three_sub_lt W Φ
  · exact (hc _ _).trans_lt hXY
  · exact (hc _ _).trans_lt hX2
  · exact (hc _ _).trans_lt (by simp [v, Y])
  · exact (hc _ _).trans_lt (by simp [v, y])
  · exact (hc _ _).trans_lt (by simp [v, X])
  · exact (hc _ _).trans_lt (by simp [v, x])
  · exact (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _).trans_lt (by simp)

/-- Vélu's quotient equation preserves the coefficient `a₁` (Vélu, 1971). -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.veluCurve_a₁ : (veluCurve W Φ).a₁ = W.a₁ := by
  by_contra hne
  have h₁ : W.infinityPlace
      (algebraMap F _ ((veluCurve W Φ).a₁ - W.a₁) * (veluX W Φ * veluY W Φ)) =
        WithZero.exp 5 := by
    -- A nonzero constant does not change the pole order of `XY`.
    rw [map_mul, Valuation.IsTrivialOn.eq_one (v := W.infinityPlace) _ (sub_ne_zero.mpr hne),
      one_mul, map_mul, infinityPlace_veluX, infinityPlace_veluY, ← WithZero.exp_add]
    norm_num
  have h₂ : W.infinityPlace
      (algebraMap F _ ((veluCurve W Φ).a₂ - W.a₂) * veluX W Φ ^ 2) ≤ WithZero.exp 4 := by
    rw [map_mul, map_pow, infinityPlace_veluX, ← WithZero.exp_nsmul]
    exact (mul_le_of_le_one_left'
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _)).trans (by norm_num)
  have h := infinityPlace_veluCurve_coeff_difference_lt W Φ
  rw [Valuation.map_sub_eq_of_lt_left _ (h₂.trans_lt (h₁ ▸
    WithZero.exp_lt_exp.mpr (by decide))), h₁, WithZero.exp_lt_exp] at h
  omega

/-- Vélu's quotient equation preserves the coefficient `a₂` (Vélu, 1971). -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.veluCurve_a₂ : (veluCurve W Φ).a₂ = W.a₂ := by
  by_contra hne
  have h := infinityPlace_veluCurve_coeff_difference_lt W Φ
  -- The first term vanishes, leaving a nonzero multiple of `X²` with a pole of order four.
  simp only [veluCurve_a₁, sub_self, map_zero, zero_mul, zero_sub, Valuation.map_neg] at h
  rw [map_mul, Valuation.IsTrivialOn.eq_one (v := W.infinityPlace) _ (sub_ne_zero.mpr hne)] at h
  norm_num only [one_mul, map_pow, infinityPlace_veluX, ← WithZero.exp_nsmul,
    WithZero.exp_lt_exp, nsmul_eq_mul] at h

/-- **The quotient curve is unique**: a Weierstrass curve over `F` whose affine equation is
satisfied by Vélu's coordinates is `veluCurve W Φ`. -/
theorem _root_.WeierstrassCurve.Affine.eq_veluCurve_of_equation {W' : WeierstrassCurve F}
    (h : (W'.baseChange W.FunctionField).toAffine.Equation (veluX W Φ) (veluY W Φ)) :
    W' = veluCurve W Φ := by
  have h₁ := (equation_baseChange_iff _ _ _).mp h
  have h₂ := (equation_baseChange_iff _ _ _).mp (equation_veluX_veluY W Φ)
  have hXo := ord_infinity_veluX W Φ
  have hYo := ord_infinity_veluY W Φ
  set V := veluCurve W Φ
  set X := veluX W Φ
  set Y := veluY W Φ
  set P := Place.infinity W
  have hX0 : X ≠ 0 := veluX_ne_zero W Φ
  have hY0 : Y ≠ 0 := veluY_ne_zero W Φ
  set b : Fin 5 → W.FunctionField := ![1, X, Y, X ^ 2, X * Y] with hb
  have hord : (fun i ↦ P.ord (b i)) = ![0, -2, -3, -4, -5] := by
    funext i
    fin_cases i <;> simp [hb, P, P.ord_mul hX0 hY0, P.ord_pow, P.ord_one, hXo, hYo]
  have hli : LinearIndependent F b :=
    P.linearIndependent_of_injective_ord (fun i ↦ by fin_cases i <;> simp [hb, hX0, hY0])
      (by rw [hord]; decide)
  have hc := Fintype.linearIndependent_iff.mp hli
    ![V.a₆ - W'.a₆, V.a₄ - W'.a₄, W'.a₃ - V.a₃, V.a₂ - W'.a₂, W'.a₁ - V.a₁] (by
      simp only [Fin.sum_univ_five, hb, Matrix.cons_val, Algebra.smul_def, map_sub]
      linear_combination h₁ - h₂)
  -- `1, X, Y, X², XY` have distinct pole orders at infinity, so all differences vanish.
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  simp only [Matrix.cons_val, sub_eq_zero] at h0 h1 h2 h3 h4
  exact WeierstrassCurve.ext h4 h3.symm h2 h1.symm h0.symm

/-- Vélu's coordinates satisfy the affine equation of a Weierstrass curve over `F` exactly when it
is the quotient curve `veluCurve W Φ`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.equation_veluX_veluY_iff {W' : WeierstrassCurve F} :
    (W'.baseChange W.FunctionField).toAffine.Equation (veluX W Φ) (veluY W Φ) ↔
      W' = veluCurve W Φ :=
  ⟨eq_veluCurve_of_equation W Φ, fun h ↦ h ▸ equation_veluX_veluY W Φ⟩

/-- **The function field of the quotient curve is the translation fixed field**: the embedding
of `F(W / Φ)` into `F(W)` sending the generic point to Vélu's coordinates has image the field
fixed by the translations in `Φ`. -/
theorem _root_.WeierstrassCurve.Affine.fieldRange_functionFieldLift_veluCurve :
    (functionFieldLift (equation_veluX_veluY W Φ) (transcendental_veluX W Φ)).fieldRange =
      translationFixedField W Φ := by
  rw [fieldRange_functionFieldLift, adjoin_veluX_veluY_eq_translationFixedField]

end TauCeti

end
