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

The coefficients `Aᵢ` are characterized here but not computed; Vélu's explicit formulas express
them through `W` and the coordinates of the points of `Φ`. The isogeny `W → veluCurve W Φ`, and
nonsingularity of `veluCurve W Φ`, are in `Isogeny/Velu/Isogeny.lean`.

## Main definitions

* `WeierstrassCurve.Affine.veluCurve`: the Weierstrass curve over `F` whose equation Vélu's
  coordinates satisfy.

## Main results

* `WeierstrassCurve.Affine.equation_veluX_veluY`: Vélu's coordinates satisfy the equation of
  `veluCurve W Φ`.
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
  obtain ⟨p, hp⟩ := Algebra.adjoin_mem_exists_aeval F X ((minpoly R Y).coeff 1).2
  obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval F X ((minpoly R Y).coeff 0).2
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

/-- Subtracting a coordinate-ring function from its `Φ`-normalized sum leaves a function regular
at infinity: only the identity translation contributes a pole there. -/
private theorem infinityPlace_normalized_sum_sub_le_one (r : W.CoordinateRing) (c : F) :
    W.infinityPlace ((∑ Q : Φ, translation W Q (algebraMap W.CoordinateRing W.FunctionField r)) -
      algebraMap F W.FunctionField c - algebraMap W.CoordinateRing W.FunctionField r) ≤ 1 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), AddSubgroup.coe_zero, translation_zero,
    AlgEquiv.one_apply, show ∀ a b s : W.FunctionField, a + s - b - a = s - b from
      fun _ _ _ ↦ by ring]
  refine W.infinityPlace.map_sub_le (W.infinityPlace.map_sum_le fun Q hQ ↦ ?_)
    (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _)
  exact valuation_translation_le_one W (fun h ↦ (Finset.mem_erase.mp hQ).1 (Subtype.ext h)) r

/-- `Y² - X³` has a pole of order at most five at infinity, since `X - x` and `Y - y` are regular
there and `y² - x³` has a pole of order at most five. -/
private theorem infinityPlace_veluY_sq_sub_veluX_pow_three_le :
    W.infinityPlace (veluY W Φ ^ 2 - veluX W Φ ^ 3) ≤ WithZero.exp 5 := by
  classical
  have hx : W.infinityPlace (genericX W) = WithZero.exp 2 := by
    rw [genericX_def]; exact infinityPlace.X W
  have hy : W.infinityPlace (genericY W) = WithZero.exp 3 := by
    rw [genericY_def]; exact infinityPlace.mk_Y W
  have hXx : W.infinityPlace (veluX W Φ - genericX W) ≤ 1 := by
    rw [veluX_def, genericX_def]
    exact infinityPlace_normalized_sum_sub_le_one W Φ _ _
  have hYy : W.infinityPlace (veluY W Φ - genericY W) ≤ 1 := by
    rw [veluY_def, genericY_def]
    exact infinityPlace_normalized_sum_sub_le_one W Φ _ _
  set v := W.infinityPlace
  set x := genericX W
  set y := genericY W
  have hX := infinityPlace_veluX W Φ
  have hY := infinityPlace_veluY W Φ
  have hc : ∀ a : F, v (algebraMap F W.FunctionField a) ≤ 1 :=
    Valuation.IsTrivialOn.valuation_algebraMap_le_one _
  have heq := (equation_baseChange_iff _ _ _).mp (equation_genericX_genericY W)
  have hexp : ∀ m n : ℤ, m ≤ n → WithZero.exp m ≤ WithZero.exp n := fun _ _ h ↦
    WithZero.exp_le_exp.mpr h
  have h1 : (1 : ℤᵐ⁰) ≤ WithZero.exp 5 := by
    rw [← WithZero.exp_zero]; exact hexp _ _ (by norm_num)
  -- `Y² - X³ = (Y - y)(Y + y) - (X - x)(X² + X x + x²) + (y² - x³)`, and every term is small.
  have hdecomp : veluY W Φ ^ 2 - veluX W Φ ^ 3 =
      (veluY W Φ - y) * (veluY W Φ + y) -
        (veluX W Φ - x) * (veluX W Φ ^ 2 + veluX W Φ * x + x ^ 2) +
        (algebraMap F _ W.a₂ * x ^ 2 + algebraMap F _ W.a₄ * x + algebraMap F _ W.a₆ -
          algebraMap F _ W.a₁ * x * y - algebraMap F _ W.a₃ * y) := by
    linear_combination heq
  rw [hdecomp]
  refine (v.map_add_le (v.map_sub_le ?_ ?_) ?_)
  · rw [map_mul]
    refine (mul_le_of_le_one_left' hYy).trans ((v.map_add_le ?_ ?_))
    · rw [hY]; exact hexp _ _ (by norm_num)
    · rw [hy]; exact hexp _ _ (by norm_num)
  · rw [map_mul]
    refine (mul_le_of_le_one_left' hXx).trans (v.map_add_le (v.map_add_le ?_ ?_) ?_)
    · rw [map_pow, hX, ← WithZero.exp_nsmul]; exact hexp _ _ (by norm_num)
    · rw [map_mul, hX, hx, ← WithZero.exp_add]; exact hexp _ _ (by norm_num)
    · rw [map_pow, hx, ← WithZero.exp_nsmul]; exact hexp _ _ (by norm_num)
  · refine v.map_sub_le (v.map_sub_le (v.map_add_le (v.map_add_le ?_ ?_) ?_) ?_) ?_
    · rw [map_mul, map_pow, hx, ← WithZero.exp_nsmul]
      exact (mul_le_of_le_one_left' (hc _)).trans (hexp _ _ (by norm_num))
    · rw [map_mul, hx]; exact (mul_le_of_le_one_left' (hc _)).trans (hexp _ _ (by norm_num))
    · exact (hc _).trans h1
    · rw [map_mul, map_mul, hx, hy, mul_assoc, ← WithZero.exp_add]
      exact (mul_le_of_le_one_left' (hc _)).trans (hexp _ _ (by norm_num))
    · rw [map_mul, hy]; exact (mul_le_of_le_one_left' (hc _)).trans (hexp _ _ (by norm_num))

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
