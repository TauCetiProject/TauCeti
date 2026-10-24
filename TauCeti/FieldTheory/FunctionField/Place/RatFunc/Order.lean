/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic

/-!
# Orders at the finite places of the rational function field

This file computes the order of a rational function at the finite place associated to an
irreducible polynomial. For `q : k[X]` irreducible and nonzero `f : k(X)`, the answer is the
exponent of `q` in the numerator of `f` minus its exponent in the denominator. This complements
`TauCeti.Place.ord_infty` and is the concrete finite-place calculation used by divisors on the
rational function field.

## Main results

* `TauCeti.Place.ord_adicOfIrreducible_algebraMap`: the order of a nonzero polynomial at `P_q`
  is its multiplicity of `q`.
* `TauCeti.Place.ord_adicOfIrreducible`: the order of a nonzero rational function at `P_q` is the
  difference of the multiplicities in its numerator and denominator.
* `TauCeti.Place.ord_adicOfIrreducible_pos_iff`,
  `TauCeti.Place.ord_adicOfIrreducible_neg_iff` and
  `TauCeti.Place.ord_adicOfIrreducible_eq_zero_iff`: the zeros, poles and units at `P_q` are
  detected by divisibility of the reduced numerator and denominator by `q`.
* `TauCeti.Place.ord_adicOfIrreducible_algebraMap_irreducible`: an irreducible polynomial has
  order one at the place it defines and order zero elsewhere, and
  `TauCeti.Place.ord_adicOfIrreducible_algebraMap_of_squarefree` extends this to squarefree
  polynomials;
  `TauCeti.Place.ord_adicOfIrreducible_X` and its two `simp` specializations spell this out
  for `X`, and `TauCeti.Place.ord_adicOfIrreducible_X_sub_C_self` and
  `TauCeti.Place.ord_adicOfIrreducible_X_sub_C_of_not_associated` for `X - a`.
* `TauCeti.Place.ord_X_eq_zero_of_ne` and `TauCeti.Place.ord_X_sub_C_eq_zero_of_ne`: `X` is a
  unit at every place other than `X = 0` and `∞`, and `X - a` at every place other than `X = a`
  and `∞`.
* `TauCeti.Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow`: the order of
  `c X ^ a (X - 1) ^ b` at a place of `k(X)`, with its values `a`, `b` and `-(a + b)` at `0`, `1`
  and `∞`.
* `TauCeti.Place.valuation_ofIrreducible_le_one_iff` and
  `TauCeti.Place.residue_adicOfIrreducible_eq_zero_iff`: regularity and vanishing in the residue
  field are detected by the denominator and numerator respectively.
* `RatFunc.pow_ne_X`: `X` is not a proper power in `k(X)`.
* `TauCeti.Place.forall_ord_adicOfIrreducible_nonneg_iff`: the functions regular at every finite
  place are the polynomials.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.2.1(a).
-/

public section

noncomputable section

open IsDedekindDomain Polynomial

namespace TauCeti.Place

variable {k : Type*} [Field k]

/-- The order at the finite place associated to `q` of a nonzero polynomial `r` is the
multiplicity of `q` in `r`. -/
theorem ord_adicOfIrreducible_algebraMap {q r : k[X]} (hq : Irreducible q) (hr : r ≠ 0) :
    (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) r) = multiplicity q r := by
  rw [adicOfIrreducible_def, ord_ofPrime_algebraMap _ _ _ hr,
    HeightOneSpectrum.ofIrreducible_asIdeal]
  exact_mod_cast multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_span_eq_emultiplicity

open scoped Classical in
/-- An irreducible polynomial has order one at the finite place defined by an associated
polynomial, and order zero at every other finite place. -/
theorem ord_adicOfIrreducible_algebraMap_irreducible {q p : k[X]} (hq : Irreducible q)
    (hp : Irreducible p) :
    (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) p) =
      if Associated q p then 1 else 0 := by
  rw [ord_adicOfIrreducible_algebraMap hq hp.ne_zero]
  split_ifs with h
  · rw [← multiplicity_eq_of_associated_left h,
      multiplicity_self (.of_not_isUnit hp.not_isUnit hp.ne_zero)]
    norm_num
  · rw [Nat.cast_eq_zero, multiplicity_eq_zero (.of_not_isUnit hq.not_isUnit hp.ne_zero)]
    exact fun hdiv ↦ h (hq.associated_of_dvd hp hdiv)

open scoped Classical in
/-- A squarefree polynomial has order one at the finite place of each of its irreducible factors,
and order zero at every other finite place. -/
theorem ord_adicOfIrreducible_algebraMap_of_squarefree {q r : k[X]} (hq : Irreducible q)
    (hr : Squarefree r) :
    (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) r) = if q ∣ r then 1 else 0 := by
  rw [ord_adicOfIrreducible_algebraMap hq hr.ne_zero]
  have hfin : FiniteMultiplicity q r := .of_not_isUnit hq.not_isUnit hr.ne_zero
  split_ifs with hdvd
  · -- `q ∣ r` but `q ^ 2 ∤ r`, so the multiplicity is exactly one
    have hlt : multiplicity q r < 2 := by
      rw [hfin.multiplicity_lt_iff_not_dvd, sq]
      exact fun h ↦ hq.not_isUnit (hr q h)
    have : 1 ≤ multiplicity q r := by
      rwa [← hfin.pow_dvd_iff_le_multiplicity, pow_one]
    omega
  · rw [multiplicity_eq_zero_of_not_dvd hdvd, Nat.cast_zero]

open scoped Classical in
/-- Among the finite places, `X` has order one at the place defined by a polynomial associated to
`X` and order zero at every other place. -/
theorem ord_adicOfIrreducible_X {q : k[X]} (hq : Irreducible q) :
    (adicOfIrreducible hq).ord (RatFunc.X : RatFunc k) =
      if Associated q X then 1 else 0 := by
  rw [← RatFunc.algebraMap_X, ord_adicOfIrreducible_algebraMap_irreducible hq irreducible_X]

/-- `X` has order one at its own finite place. -/
@[simp]
theorem ord_adicOfIrreducible_X_self :
    (adicOfIrreducible (irreducible_X (R := k))).ord (RatFunc.X : RatFunc k) = 1 := by
  classical
  rw [ord_adicOfIrreducible_X, ite_eq_left (Associated.refl _)]

/-- `X` is not a proper power in `k(X)`: it has order one at the place `X = 0`. -/
theorem _root_.RatFunc.pow_ne_X {n : ℕ} (hn : 1 < n) (c : RatFunc k) : c ^ n ≠ RatFunc.X := by
  intro h
  have h1 := congrArg (adicOfIrreducible (irreducible_X (R := k))).ord h
  rw [ord_pow, ord_adicOfIrreducible_X_self] at h1
  have := Int.eq_one_of_dvd_one (by positivity) ⟨_, h1.symm⟩
  omega

/-- `X` has order zero at every finite place other than its own. -/
@[simp]
theorem ord_adicOfIrreducible_X_of_not_associated {q : k[X]} (hq : Irreducible q)
    (h : ¬Associated q X) :
    (adicOfIrreducible hq).ord (RatFunc.X : RatFunc k) = 0 := by
  classical
  rw [ord_adicOfIrreducible_X, ite_eq_right h]

/-- `X - a` has order one at its own finite place. -/
@[simp]
theorem ord_adicOfIrreducible_X_sub_C_self (a : k) :
    (adicOfIrreducible (irreducible_X_sub_C a)).ord (RatFunc.X - RatFunc.C a) = 1 := by
  classical
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub,
    ord_adicOfIrreducible_algebraMap_irreducible _ (irreducible_X_sub_C a),
    ite_eq_left (Associated.refl _)]

/-- `X - a` has order zero at every finite place other than its own. -/
@[simp]
theorem ord_adicOfIrreducible_X_sub_C_of_not_associated {q : k[X]} (hq : Irreducible q) {a : k}
    (h : ¬Associated q (X - C a)) :
    (adicOfIrreducible hq).ord (RatFunc.X - RatFunc.C a) = 0 := by
  classical
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub,
    ord_adicOfIrreducible_algebraMap_irreducible hq (irreducible_X_sub_C a), ite_eq_right h]

/-- `X` has order zero at every place of `k(X)` other than `X = 0` and `∞`. -/
theorem ord_X_eq_zero_of_ne {P : Place k (RatFunc k)}
    (hP0 : P ≠ adicOfIrreducible (irreducible_X (R := k))) (hPinf : P ≠ infty k) :
    P.ord (RatFunc.X : RatFunc k) = 0 := by
  rcases eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨q, hq, rfl⟩
  · exact absurd rfl hPinf
  · exact ord_adicOfIrreducible_X_of_not_associated hq fun h ↦
      hP0 ((adicOfIrreducible_eq_adicOfIrreducible_iff hq irreducible_X).mpr h)

/-- `X - a` has order zero at every place of `k(X)` other than `X = a` and `∞`. -/
theorem ord_X_sub_C_eq_zero_of_ne (a : k) {P : Place k (RatFunc k)}
    (hPa : P ≠ adicOfIrreducible (irreducible_X_sub_C a)) (hPinf : P ≠ infty k) :
    P.ord (RatFunc.X - RatFunc.C a) = 0 := by
  rcases eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨q, hq, rfl⟩
  · exact absurd rfl hPinf
  · exact ord_adicOfIrreducible_X_sub_C_of_not_associated hq fun h ↦
      hPa ((adicOfIrreducible_eq_adicOfIrreducible_iff hq (irreducible_X_sub_C a)).mpr h)

/-- `X - a` is a nonzero element of `k(X)`. -/
theorem _root_.RatFunc.X_sub_C_ne_zero (a : k) : (RatFunc.X - RatFunc.C a : RatFunc k) ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub, Ne,
    map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]
  exact Polynomial.X_sub_C_ne_zero a

/-- `c X ^ a (X - 1) ^ b` is a nonzero element of `k(X)` for `c ≠ 0`. -/
theorem _root_.RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero {c : k} (hc : c ≠ 0)
    (a b : ℤ) : algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b ≠ 0 :=
  mul_ne_zero (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) (zpow_ne_zero a RatFunc.X_ne_zero))
    (zpow_ne_zero b (by simpa using RatFunc.X_sub_C_ne_zero (1 : k)))

/-- **The order of `c X ^ a (X - 1) ^ b`** at a place `P` of `k(X)` is
`a · ord_P X + b · ord_P (X - 1)`. -/
theorem ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow (P : Place k (RatFunc k)) {c : k}
    (hc : c ≠ 0) (a b : ℤ) :
    P.ord (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b) =
      a * P.ord RatFunc.X + b * P.ord (RatFunc.X - 1) := by
  have hc' : algebraMap k (RatFunc k) c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hXa : (RatFunc.X : RatFunc k) ^ a ≠ 0 := zpow_ne_zero a RatFunc.X_ne_zero
  have hX1 : (RatFunc.X - 1 : RatFunc k) ≠ 0 := by simpa using RatFunc.X_sub_C_ne_zero (1 : k)
  rw [P.ord_mul (mul_ne_zero hc' hXa) (zpow_ne_zero b hX1), P.ord_mul hc' hXa,
    ord_algebraMap, ord_zpow, ord_zpow, zero_add]

/-- The order of `c X ^ a (X - 1) ^ b` at the place `X = 0` is `a`. -/
theorem ord_adicOfIrreducible_X_algebraMap_mul_X_zpow_mul_X_sub_one_zpow {c : k} (hc : c ≠ 0)
    (a b : ℤ) :
    (adicOfIrreducible (irreducible_X (R := k))).ord
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b) = a := by
  have h : ¬Associated (X : k[X]) (X - C 1) := fun h ↦ by
    simpa using congrArg (eval 0) (eq_of_monic_of_associated monic_X (monic_X_sub_C 1) h)
  have h1 := ord_adicOfIrreducible_X_sub_C_of_not_associated (irreducible_X (R := k)) h
  rw [map_one RatFunc.C] at h1
  rw [ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow _ hc, ord_adicOfIrreducible_X_self, h1]
  ring

/-- The order of `c X ^ a (X - 1) ^ b` at the place `X = 1` is `b`. -/
theorem ord_adicOfIrreducible_X_sub_one_algebraMap_mul_X_zpow_mul_X_sub_one_zpow {c : k}
    (hc : c ≠ 0) (a b : ℤ) :
    (adicOfIrreducible (irreducible_X_sub_C (1 : k))).ord
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b) = b := by
  have h : ¬Associated (X - C 1 : k[X]) X := fun h ↦ by
    simpa using congrArg (eval 0) (eq_of_monic_of_associated (monic_X_sub_C 1) monic_X h)
  have h1 := ord_adicOfIrreducible_X_sub_C_self (1 : k)
  rw [map_one RatFunc.C] at h1
  rw [ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow _ hc,
    ord_adicOfIrreducible_X_of_not_associated _ h, h1]
  ring

/-- The order of `c X ^ a (X - 1) ^ b` at the place `X = ∞` is `-(a + b)`. -/
theorem ord_infty_algebraMap_mul_X_zpow_mul_X_sub_one_zpow {c : k} (hc : c ≠ 0) (a b : ℤ) :
    (infty k).ord (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b) =
      -(a + b) := by
  have h1 : (RatFunc.X - 1 : RatFunc k).intDegree = 1 := by
    rw [← RatFunc.algebraMap_X, ← map_one (algebraMap k[X] (RatFunc k)), ← map_sub, ← C_1,
      RatFunc.intDegree_polynomial, natDegree_X_sub_C, Nat.cast_one]
  rw [ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow _ hc, ord_infty, ord_infty, RatFunc.intDegree_X,
    h1]
  ring

/-- The order of a nonzero rational function at the finite place associated to `q` is the
multiplicity of `q` in its numerator minus its multiplicity in its denominator. -/
theorem ord_adicOfIrreducible {q : k[X]} (hq : Irreducible q) {f : RatFunc k} (hf : f ≠ 0) :
    (adicOfIrreducible hq).ord f =
      (multiplicity q f.num : ℤ) - multiplicity q f.denom := by
  calc
    (adicOfIrreducible hq).ord f =
        (adicOfIrreducible hq).ord
          (algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom) :=
      congrArg (adicOfIrreducible hq).ord (RatFunc.num_div_denom f).symm
    _ = (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) f.num) -
          (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) f.denom) :=
      (adicOfIrreducible hq).ord_div (RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf))
        (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
    _ = (multiplicity q f.num : ℤ) - multiplicity q f.denom := by
      rw [ord_adicOfIrreducible_algebraMap hq (RatFunc.num_ne_zero hf),
        ord_adicOfIrreducible_algebraMap hq (RatFunc.denom_ne_zero f)]

private theorem not_dvd_right_of_dvd_left {q a b : k[X]} (hq : Irreducible q)
    (hab : IsCoprime a b) (ha : q ∣ a) : ¬q ∣ b := by
  intro hb
  exact hq.not_isUnit (hab.isUnit_of_dvd' ha hb)

/-- A nonzero rational function has a zero at `P_q` exactly when `q` divides its reduced
numerator. -/
@[simp]
theorem ord_adicOfIrreducible_pos_iff {q : k[X]} (hq : Irreducible q) {f : RatFunc k}
    (hf : f ≠ 0) :
    0 < (adicOfIrreducible hq).ord f ↔ q ∣ f.num := by
  rw [ord_adicOfIrreducible hq hf]
  have hfin : FiniteMultiplicity q f.num :=
    .of_not_isUnit hq.not_isUnit (RatFunc.num_ne_zero hf)
  constructor
  · intro h
    apply (multiplicity_ne_zero hfin).mp
    omega
  · intro hnum
    have hnum' : multiplicity q f.num ≠ 0 := (multiplicity_ne_zero hfin).mpr hnum
    have hden : multiplicity q f.denom = 0 :=
      multiplicity_eq_zero_of_not_dvd
        (not_dvd_right_of_dvd_left hq f.isCoprime_num_denom hnum)
    omega

/-- A rational function has a pole at `P_q` exactly when `q` divides its reduced denominator.
This statement includes the zero rational function, whose reduced denominator is `1`. -/
@[simp]
theorem ord_adicOfIrreducible_neg_iff {q : k[X]} (hq : Irreducible q) {f : RatFunc k} :
    (adicOfIrreducible hq).ord f < 0 ↔ q ∣ f.denom := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [ord_zero, lt_self_iff_false, RatFunc.denom_zero, false_iff]
    exact hq.not_dvd_one
  · rw [ord_adicOfIrreducible hq hf]
    have hfin : FiniteMultiplicity q f.denom :=
      .of_not_isUnit hq.not_isUnit (RatFunc.denom_ne_zero f)
    constructor
    · intro h
      apply (multiplicity_ne_zero hfin).mp
      omega
    · intro hden
      have hnum : multiplicity q f.num = 0 :=
        multiplicity_eq_zero_of_not_dvd
          (not_dvd_right_of_dvd_left hq f.isCoprime_num_denom.symm hden)
      have hden' : multiplicity q f.denom ≠ 0 := (multiplicity_ne_zero hfin).mpr hden
      omega

/-- A nonzero rational function is a unit at `P_q` exactly when `q` divides neither its reduced
numerator nor its reduced denominator. -/
@[simp]
theorem ord_adicOfIrreducible_eq_zero_iff {q : k[X]} (hq : Irreducible q) {f : RatFunc k}
    (hf : f ≠ 0) :
    (adicOfIrreducible hq).ord f = 0 ↔ ¬q ∣ f.num ∧ ¬q ∣ f.denom := by
  simp only [← ord_adicOfIrreducible_pos_iff hq hf, ← ord_adicOfIrreducible_neg_iff hq]
  omega

/-! ### The valuation ring and residue field -/

/-- A rational function is regular at the finite place `P_q` exactly when `q` does not divide
its reduced denominator. This statement includes the zero rational function. -/
@[simp]
theorem valuation_ofIrreducible_le_one_iff {q : k[X]} (hq : Irreducible q)
    (f : RatFunc k) :
    (HeightOneSpectrum.ofIrreducible hq).valuation (RatFunc k) f ≤ 1 ↔
      ¬q ∣ f.denom := by
  rw [← valuation_adicOfIrreducible hq, ← (adicOfIrreducible hq).mem_integers_iff,
    (adicOfIrreducible hq).mem_integers_iff_ord_nonneg, ← not_lt,
    ord_adicOfIrreducible_neg_iff hq]

/-- **A rational function is a polynomial exactly when it has no pole at any finite place.**  The
finite places of `k(x)` are the places of the height-one primes of `k[X]`, so this is the
Dedekind-domain fact that `k[X]` is the intersection of its localizations at them
(`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`), read in place
vocabulary. -/
theorem forall_ord_adicOfIrreducible_nonneg_iff {f : RatFunc k} :
    (∀ (q : k[X]) (hq : Irreducible q), 0 ≤ (adicOfIrreducible hq).ord f) ↔
      ∃ p : k[X], algebraMap k[X] (RatFunc k) p = f := by
  constructor
  · intro h
    refine RingHom.mem_range.mp (HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := k[X]) (RatFunc k) f fun v ↦ ?_)
    obtain ⟨q, hq, -, rfl⟩ := v.exists_monic_irreducible_eq_ofIrreducible
    rw [valuation_ofIrreducible_le_one_iff hq, ← ord_adicOfIrreducible_neg_iff hq, not_lt]
    exact h q hq
  · rintro ⟨p, rfl⟩ q hq
    rw [adicOfIrreducible_def]
    exact ord_ofPrime_algebraMap_nonneg k (RatFunc k) _ p

/-- A function regular at `P_q` has zero residue exactly when `q` divides its reduced numerator. -/
theorem residue_adicOfIrreducible_eq_zero_iff {q : k[X]} (hq : Irreducible q)
    (f : (adicOfIrreducible hq).integers) :
    IsLocalRing.residue (adicOfIrreducible hq).integers f = 0 ↔
      q ∣ (f : RatFunc k).num := by
  rcases eq_or_ne (f : RatFunc k) 0 with hf | hf
  · have : f = 0 := Subtype.ext hf
    subst f
    simp [RatFunc.num_zero]
  · rw [(adicOfIrreducible hq).residue_eq_zero_iff_ord_pos hf,
      ord_adicOfIrreducible_pos_iff hq hf]

end TauCeti.Place
