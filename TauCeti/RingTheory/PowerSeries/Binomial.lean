/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.RingTheory.PowerSeries.Log

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Rescale
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Formal binomial powers of power series

Let `R` be a commutative binomial ring and `A` a commutative `R`-algebra. Mathlib defines the
binomial series `PowerSeries.binomialSeries A r` representing `(1 + X) ^ r` and proves the
addition law `binomialSeries A (r + s) = binomialSeries A r * binomialSeries A s`.

For any series `f : A⟦X⟧` with constant coefficient `1`, substituting `f - 1` into
`binomialSeries A r` defines the formal binomial power

`f.binomialPow r = (binomialSeries A r).subst (f - 1)`.

This file develops the differential and algebraic laws of `binomialSeries` and `binomialPow`.
In particular, formal exponentiation makes the multiplicative group
`{f : A⟦X⟧ | constantCoeff f = 1}` of principal units into an `R`-module, without any additive
torsion-freeness hypothesis on `A`:

* `PowerSeries.binomialPow_add`: `f ^ (r + s) = f ^ r * f ^ s`,
* `PowerSeries.binomialPow_binomialPow`: `(f ^ r) ^ s = f ^ (r * s)`,
* `PowerSeries.binomialPow_mul`: `(f * g) ^ r = f ^ r * g ^ r`.

The iterated-power and base-multiplicativity identities are proved over rings with unique division
by positive integers (`HasUniqueDiv`) from uniqueness of solutions to the logarithmic differential
equation `u * P' = w * P` (`PowerSeries.eq_of_mul_derivative_eq`), applied to the universal rings
`R` and `MvPolynomial (Bool × ℕ) R`, and then specialized to an arbitrary `R`-algebra `A` along
coefficient homomorphisms.

Over a `ℚ`-algebra `A`, `binomialPow` agrees with `exp (r • logOf f)`
(`PowerSeries.logOf_binomialPow`, `PowerSeries.subst_exp_smul_logOf`).

## Main definitions

* `PowerSeries.binomialPow`: the formal binomial power `(binomialSeries A r).subst (f - 1)` of a
  power series `f : A⟦X⟧` by an exponent `r : R`.
* `PowerSeries.binomialReversion`: for `f : A⟦X⟧` with `constantCoeff f = 1` and unit exponents
  `a b : Rˣ`, the unique formal power series `S` with `constantCoeff S = 1` solving
  `S.binomialPow (a : R) * f.subst (X * S.binomialPow (-(b : R))) = 1`.

## Main results

* `PowerSeries.eq_of_mul_derivative_eq`: over a ring with `HasUniqueDiv`, a series `P` solving
  `u * d⁄dX P = w * P` for `u` with unit constant coefficient is uniquely determined by
  `constantCoeff P`.
* `PowerSeries.derivative_binomialSeries` and
  `PowerSeries.one_add_X_mul_derivative_binomialSeries`: `d⁄dX (1 + X) ^ r = r • (1 + X) ^ (r - 1)`
  and `(1 + X) * d⁄dX (1 + X) ^ r = r • (1 + X) ^ r`.
* `PowerSeries.subst_binomialSeries_sub_one`: substituting `(1 + X) ^ r - 1` into `(1 + X) ^ s`
  yields `(1 + X) ^ (r * s)`.
* `PowerSeries.binomialPow_add`, `PowerSeries.binomialPow_binomialPow`,
  `PowerSeries.binomialPow_mul`: the `R`-module laws on principal units `1 + X A⟦X⟧`.
* `PowerSeries.derivative_binomialPow` and `PowerSeries.mul_derivative_binomialPow`: the chain rule
  for formal binomial powers.
* `PowerSeries.subst_binomialPow`, `PowerSeries.rescale_binomialPow`,
  `PowerSeries.map_binomialPow`, `PowerSeries.binomialPow_eq_iff`,
  `PowerSeries.trunc_binomialPow_eq_iff`: compatibility with substitution, rescaling, coefficient
  homomorphisms, unit-exponent cancellation, and finite truncation.
* `PowerSeries.binomialPow_binomialReversion_mul_subst`, `PowerSeries.eq_binomialReversion_iff`,
  `PowerSeries.subst_X_mul_binomialPow_binomialReversion_of_mul_deriv`, and
  `PowerSeries.X_pow_dvd_sub_binomialReversion`: existence, uniqueness, differential identity, and
  congruence modulo `X ^ m` for fractional-power formal reversion.
* `PowerSeries.logOf_binomialPow` and `PowerSeries.subst_exp_smul_logOf`: compatibility with
  `PowerSeries.logOf` and `PowerSeries.exp` over `ℚ`-algebras.

## References

* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]
* N. Bourbaki, *Algebra II*, Chapter IV, §4, Formal power series.
-/

public section

namespace PowerSeries

open Finset

/-! ## Uniqueness for logarithmic differential equations -/

section DifferentialUniqueness

variable {A : Type*} [CommRing A] [HasUniqueDiv A]

/-- Over a commutative ring with unique division by positive integers, a formal power series `P`
solving `u * d⁄dX P = w * P`, where `constantCoeff u` is a unit, is uniquely determined by its
constant coefficient. -/
theorem eq_of_mul_derivative_eq {u P Q w : A⟦X⟧} (hu : IsUnit (constantCoeff u))
    (hc : constantCoeff P = constantCoeff Q) (hP : u * d⁄dX P = w * P)
    (hQ : u * d⁄dX Q = w * Q) : P = Q := by
  suffices hD : P - Q = 0 from sub_eq_zero.mp hD
  set D := P - Q
  have hD₀ : constantCoeff D = 0 := sub_eq_zero.mpr hc
  have hdeq : u * d⁄dX D = w * D := by
    rw [map_sub, mul_sub, mul_sub, hP, hQ]
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simpa [coeff_zero_eq_constantCoeff_apply] using hD₀
    · -- Compare degree-`m` coefficients of `u * D' = w * D`; lower coefficients of `D` vanish.
      have hm := congrArg (coeff m) hdeq
      have hrhs : coeff m (w * D) = 0 := by
        rw [coeff_mul]
        refine sum_eq_zero fun p hp => ?_
        rw [mem_antidiagonal] at hp
        rw [ih p.2 (by omega), mul_zero]
      have hlhs : coeff m (u * d⁄dX D) = (m + 1) • (constantCoeff u * coeff (m + 1) D) := by
        rw [coeff_mul, sum_eq_single (0, m)]
        · simp only [coeff_zero_eq_constantCoeff_apply, coeff_derivative, nsmul_eq_mul]
          push_cast
          ring
        · intro p hp hne
          rw [mem_antidiagonal] at hp
          have hp0 : p.1 ≠ 0 ∨ p.2 ≠ m := not_and_or.mp (by simpa [Prod.ext_iff] using hne)
          rw [coeff_derivative, ih (p.2 + 1) (by omega), zero_mul, mul_zero]
        · simp
      rw [hlhs, hrhs] at hm
      exact hu.mul_right_eq_zero.mp
        (nsmul_right_injective m.succ_ne_zero (hm.trans (smul_zero _).symm))

end DifferentialUniqueness

/-! ## Further properties of `PowerSeries.binomialSeries` -/

section BinomialSeries

variable {R S A B : Type*} [CommRing R] [BinomialRing R] [CommRing A] [Algebra R A]

/-- At exponent `1`, the binomial series is `1 + X`. -/
@[simp]
theorem binomialSeries_one : binomialSeries A (1 : R) = 1 + X := by
  simpa using binomialSeries_nat (R := R) (A := A) 1

/-- At a numeral exponent, the binomial series is the ordinary power of `1 + X`. -/
@[simp]
theorem binomialSeries_ofNat (n : ℕ) [n.AtLeastTwo] :
    binomialSeries A (ofNat(n) : R) = (1 + X) ^ (ofNat(n) : ℕ) :=
  binomialSeries_nat n

/-- `binomialSeries A (-r)` is the left inverse of `binomialSeries A r`. -/
@[simp]
theorem binomialSeries_neg_mul (r : R) :
    binomialSeries A (-r) * binomialSeries A r = 1 := by
  rw [← binomialSeries_add, neg_add_cancel, binomialSeries_zero]

/-- `binomialSeries A (-r)` is the right inverse of `binomialSeries A r`. -/
@[simp]
theorem binomialSeries_mul_neg (r : R) :
    binomialSeries A r * binomialSeries A (-r) = 1 := by
  rw [← binomialSeries_add, add_neg_cancel, binomialSeries_zero]

/-- Every binomial series is a unit in `A⟦X⟧`. -/
theorem isUnit_binomialSeries (r : R) : IsUnit (binomialSeries A r) :=
  isUnit_iff_exists.mpr ⟨binomialSeries A (-r), binomialSeries_mul_neg r, binomialSeries_neg_mul r⟩

/-- At exponent `-1`, the binomial series is the formal inverse of `1 + X`. -/
theorem binomialSeries_neg_one :
    binomialSeries A (-1 : R) = invOfUnit (1 + X) 1 := by
  have h1 : constantCoeff (1 + X : A⟦X⟧) = (1 : Aˣ) := by simp
  calc
    binomialSeries A (-1 : R) =
        binomialSeries A (-1 : R) * ((1 + X) * invOfUnit (1 + X) 1) := by
      rw [mul_invOfUnit (1 + X) 1 h1, mul_one]
    _ = (binomialSeries A (-1 : R) * binomialSeries A (1 : R)) * invOfUnit (1 + X) 1 := by
      rw [binomialSeries_one, mul_assoc]
    _ = invOfUnit (1 + X) 1 := by rw [binomialSeries_neg_mul, one_mul]

/-- Mapping coefficients along `algebraMap R A` sends `binomialSeries R r` to
`binomialSeries A r`. -/
@[simp]
theorem map_algebraMap_binomialSeries (r : R) :
    (binomialSeries R r).map (algebraMap R A) = binomialSeries A r := by
  ext n
  simp [Algebra.smul_def]

/-- Mapping coefficients along an `R`-algebra homomorphism preserves `binomialSeries`. -/
@[simp]
theorem map_algHom_binomialSeries [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (r : R) :
    (binomialSeries A r).map (φ : A →+* B) = binomialSeries B r := by
  ext n
  simp

/-- Mapping coefficients along a ring homomorphism between binomial rings maps the exponent of
`binomialSeries`. -/
theorem map_binomialSeries [CommRing S] [BinomialRing S] (φ : R →+* S) (r : R) :
    (binomialSeries R r).map φ = binomialSeries S (φ r) := by
  ext n
  simp [Ring.map_choose]

/-- **Derivative of the binomial series**: `d⁄dX (1 + X) ^ r = r • (1 + X) ^ (r - 1)`. -/
theorem derivative_binomialSeries (r : R) :
    d⁄dX (binomialSeries A r) = r • binomialSeries A (r - 1) := by
  ext n
  rw [coeff_derivative, coeff_smul]
  simp only [binomialSeries_coeff, Algebra.smul_def, mul_one]
  have hchoose : (n + 1) • Ring.choose r (n + 1) = r * Ring.choose (r - 1) n := by
    simpa [Nat.choose_one_right] using
      Ring.choose_smul_choose r (n := n + 1) (k := 1) (by omega)
  rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hchoose
  simpa [mul_comm] using congrArg (algebraMap R A) hchoose

/-- **Logarithmic differential equation of the binomial series**:
`(1 + X) * d⁄dX (1 + X) ^ r = r • (1 + X) ^ r`. -/
theorem one_add_X_mul_derivative_binomialSeries (r : R) :
    (1 + X) * d⁄dX (binomialSeries A r) = r • binomialSeries A r := by
  rw [derivative_binomialSeries, mul_smul_comm, ← binomialSeries_one (R := R),
    ← binomialSeries_add, add_sub_cancel]

/-- Over a binomial ring `R`, substituting `(1 + X) ^ r - 1` into `(1 + X) ^ s` gives
`(1 + X) ^ (r * s)`. -/
private theorem subst_binomialSeries_sub_one_self (r s : R) :
    (binomialSeries R s).subst (binomialSeries R r - 1) = binomialSeries R (r * s) := by
  let := BinomialRing.toHasUniqueDiv (R := R)
  have hsub : HasSubst (binomialSeries R r - 1) := TauCeti.hasSubst_binomialSeries_sub_one r
  refine eq_of_mul_derivative_eq (u := 1 + X) (w := C (r * s)) (by simp) ?_ ?_ ?_
  · rw [constantCoeff_eq,
      constantCoeff_subst_of_constantCoeff_zero (by simp [← constantCoeff_eq])]
    simp
  · -- Differentiate the composite and recombine `(1 + X) ^ (s - 1)` with `(1 + X) ^ r`.
    have hsplit : (binomialSeries R s).subst (binomialSeries R r - 1) =
        (binomialSeries R (s - 1)).subst (binomialSeries R r - 1) * binomialSeries R r := by
      conv_lhs => rw [show s = (s - 1) + 1 by ring, binomialSeries_add, binomialSeries_one]
      rw [subst_mul hsub, subst_add hsub, subst_one, subst_X hsub, add_sub_cancel]
    have hderiv := one_add_X_mul_derivative_binomialSeries (A := R) r
    rw [derivative_subst hsub, map_sub, derivative_one, sub_zero, derivative_binomialSeries,
      subst_smul hsub]
    calc
      (1 + X) * (s • (binomialSeries R (s - 1)).subst (binomialSeries R r - 1) *
          d⁄dX (binomialSeries R r))
        = s • (binomialSeries R (s - 1)).subst (binomialSeries R r - 1) *
            ((1 + X) * d⁄dX (binomialSeries R r)) := by
          simp only [smul_eq_C_mul]
          ring
      _ = C (r * s) * (binomialSeries R s).subst (binomialSeries R r - 1) := by
          rw [hderiv, hsplit]
          simp only [smul_eq_C_mul, map_mul]
          ring
  · simpa only [smul_eq_C_mul] using one_add_X_mul_derivative_binomialSeries (A := R) (r * s)

/-- **Iterated binomial series**: substituting `(1 + X) ^ r - 1` into `(1 + X) ^ s` gives
`(1 + X) ^ (r * s)` over any commutative `R`-algebra `A`. -/
@[simp]
theorem subst_binomialSeries_sub_one (r s : R) :
    (binomialSeries A s).subst (binomialSeries A r - 1) = binomialSeries A (r * s) := by
  have hsub : HasSubst (binomialSeries R r - 1) := TauCeti.hasSubst_binomialSeries_sub_one r
  have h := congrArg (map (algebraMap R A)) (subst_binomialSeries_sub_one_self r s)
  rw [map_algebraMap_binomialSeries] at h
  refine Eq.trans ?_ h
  refine ((map_subst hsub (h := algebraMap R A) (binomialSeries R s)).trans ?_).symm
  rw [map_algebraMap_binomialSeries]
  congr 1
  exact ((map (algebraMap R A)).map_sub _ _).trans (by simp)

end BinomialSeries

/-! ## Formal binomial powers of principal units -/

section BinomialPow

variable {R S A B : Type*} [CommRing R] [BinomialRing R] [CommRing A] [Algebra R A]

/-- The **formal binomial power** `f ^ r` of a power series `f : A⟦X⟧` with constant coefficient
`1` by an exponent `r : R`, defined by substituting `f - 1` into `PowerSeries.binomialSeries A r`.
-/
noncomputable def binomialPow (f : A⟦X⟧) (r : R) : A⟦X⟧ :=
  (binomialSeries A r).subst (f - 1)

/-- The formal binomial power `f.binomialPow r` is `(binomialSeries A r).subst (f - 1)`. -/
theorem binomialPow_def (f : A⟦X⟧) (r : R) :
    f.binomialPow r = (binomialSeries A r).subst (f - 1) :=
  (rfl)

private theorem hasSubst_sub_one {f : A⟦X⟧} (hf : constantCoeff f = 1) : HasSubst (f - 1) :=
  .of_constantCoeff_zero' (by simp [hf])

/-- The formal binomial power of a series with constant coefficient `1` has constant coefficient
`1`. -/
@[simp]
theorem constantCoeff_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    constantCoeff (f.binomialPow r) = 1 := by
  rw [binomialPow_def, constantCoeff_eq,
    constantCoeff_subst_of_constantCoeff_zero (by simp [← constantCoeff_eq, hf])]
  simp

/-- For `constantCoeff f = 1`, `f.binomialPow r - 1` has zero constant coefficient and can be
substituted into any power series. -/
theorem hasSubst_binomialPow_sub_one {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    HasSubst (f.binomialPow r - 1) :=
  hasSubst_sub_one (constantCoeff_binomialPow hf r)

/-- Every formal binomial power of `1` is `1`. -/
@[simp]
theorem binomialPow_one_left (r : R) : (1 : A⟦X⟧).binomialPow r = 1 := by
  rw [binomialPow_def, sub_self, subst_zero_eq_C_constantCoeff, binomialSeries_constantCoeff,
    map_one, map_one]

/-- The formal binomial power of `1 + X` is `binomialSeries A r`. -/
@[simp]
theorem binomialPow_one_add_X (r : R) :
    (1 + X : A⟦X⟧).binomialPow r = binomialSeries A r := by
  rw [binomialPow_def, add_sub_cancel_left, X_subst]

/-- At exponent `0`, the formal binomial power of any series is `1`. -/
@[simp]
theorem binomialPow_zero (f : A⟦X⟧) :
    f.binomialPow (0 : R) = 1 := by
  rw [binomialPow_def, binomialSeries_zero, subst_one]

/-- At exponent `1`, the formal binomial power is the series itself. -/
@[simp]
theorem binomialPow_one {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f.binomialPow (1 : R) = f := by
  have hsub := hasSubst_sub_one hf
  rw [binomialPow_def, binomialSeries_one, subst_add hsub, subst_one, subst_X hsub, add_sub_cancel]

/-- At a natural number exponent, the formal binomial power is the ordinary power. -/
@[simp]
theorem binomialPow_natCast {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) :
    f.binomialPow (n : R) = f ^ n := by
  have hsub := hasSubst_sub_one hf
  rw [binomialPow_def, binomialSeries_nat, subst_pow hsub, subst_add hsub, subst_one, subst_X hsub,
    add_sub_cancel]

/-- At a numeral exponent, the formal binomial power is the ordinary power. -/
@[simp]
theorem binomialPow_ofNat {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) [n.AtLeastTwo] :
    f.binomialPow (ofNat(n) : R) = f ^ (ofNat(n) : ℕ) :=
  binomialPow_natCast hf n

/-- **Addition of exponents**: `f ^ (r + s) = f ^ r * f ^ s`. -/
theorem binomialPow_add {f : A⟦X⟧} (hf : constantCoeff f = 1) (r s : R) :
    f.binomialPow (r + s) = f.binomialPow r * f.binomialPow s := by
  rw [binomialPow_def, binomialSeries_add, subst_mul (hasSubst_sub_one hf), ← binomialPow_def,
    ← binomialPow_def]

/-- `f.binomialPow (-r)` is the left inverse of `f.binomialPow r`. -/
@[simp]
theorem binomialPow_neg_mul {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    f.binomialPow (-r) * f.binomialPow r = 1 := by
  rw [← binomialPow_add hf, neg_add_cancel, binomialPow_zero]

/-- `f.binomialPow (-r)` is the right inverse of `f.binomialPow r`. -/
@[simp]
theorem binomialPow_mul_neg {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    f.binomialPow r * f.binomialPow (-r) = 1 := by
  rw [← binomialPow_add hf, add_neg_cancel, binomialPow_zero]

/-- Every formal binomial power of a series with constant coefficient `1` is a unit. -/
theorem isUnit_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    IsUnit (f.binomialPow r) :=
  isUnit_iff_exists.mpr ⟨f.binomialPow (-r), binomialPow_mul_neg hf r, binomialPow_neg_mul hf r⟩

/-- At exponent `-1`, the formal binomial power is `invOfUnit f 1`. -/
theorem binomialPow_neg_one {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f.binomialPow (-1 : R) = invOfUnit f 1 := by
  have hf1 : constantCoeff f = (1 : Aˣ) := hf
  calc
    f.binomialPow (-1 : R) = f.binomialPow (-1 : R) * (f * invOfUnit f 1) := by
      rw [mul_invOfUnit f 1 hf1, mul_one]
    _ = (f.binomialPow (-1 : R) * f.binomialPow (1 : R)) * invOfUnit f 1 := by
      rw [binomialPow_one hf, mul_assoc]
    _ = invOfUnit f 1 := by rw [binomialPow_neg_mul hf, one_mul]

/-- At a negated natural number `-(n : R)`, the formal binomial power is `(invOfUnit f 1) ^ n`. -/
theorem binomialPow_neg_natCast {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) :
    f.binomialPow (-(n : R)) = invOfUnit f 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, neg_add, binomialPow_add hf, ih, binomialPow_neg_one hf, pow_succ]

/-- For a unit `u : A⟦X⟧ˣ` with constant coefficient `1`, the formal binomial power at an integer
cast `(z : R)` is `↑(u ^ z)`. -/
theorem binomialPow_intCast {u : A⟦X⟧ˣ} (hu : constantCoeff (u : A⟦X⟧) = 1) (z : ℤ) :
    (u : A⟦X⟧).binomialPow (z : R) = ↑(u ^ z) := by
  cases z with
  | ofNat n => simp [hu]
  | negSucc n =>
    have hinv : invOfUnit (u : A⟦X⟧) 1 = ↑u⁻¹ :=
      u.mul_right_inj.mp ((mul_invOfUnit (u : A⟦X⟧) 1 hu).trans u.mul_inv.symm)
    rw [Int.cast_negSucc, binomialPow_neg_natCast hu (n + 1), hinv, zpow_negSucc, ← inv_pow,
      Units.val_pow_eq_pow_val]

/-- **Iterated formal binomial powers**: `(f ^ r) ^ s = f ^ (r * s)`. -/
@[simp]
theorem binomialPow_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r s : R) :
    (f.binomialPow r).binomialPow s = f.binomialPow (r * s) := by
  have hsub := hasSubst_sub_one hf
  have hinner : f.binomialPow r - 1 = (binomialSeries A r - 1).subst (f - 1) := by
    rw [binomialPow_def, subst_sub hsub, subst_one]
  rw [binomialPow_def, hinner,
    ← subst_comp_subst_apply (TauCeti.hasSubst_binomialSeries_sub_one r) hsub,
    subst_binomialSeries_sub_one, ← binomialPow_def]

/-- Raising a formal binomial power `f.binomialPow r` to `n : ℕ` scales the exponent by `n`. -/
theorem pow_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) (n : ℕ) :
    f.binomialPow r ^ n = f.binomialPow (n • r) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, succ_nsmul, binomialPow_add hf]

/-- Taking the formal binomial power of `f ^ n` scales the exponent by `n`. -/
theorem binomialPow_pow {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) (r : R) :
    (f ^ n).binomialPow r = f.binomialPow (n • r) := by
  rw [← binomialPow_natCast (R := R) hf n, binomialPow_binomialPow hf, nsmul_eq_mul]

/-- The linear coefficient of `f.binomialPow r` is `r • coeff 1 f`. -/
theorem coeff_one_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    coeff 1 (f.binomialPow r) = r • coeff 1 f := by
  rw [binomialPow_def, coeff_one_subst (by simp [hf])]
  simp [Algebra.smul_def]

/-- **Chain rule for formal binomial powers**:
`d⁄dX (f.binomialPow r) = r • (f.binomialPow (r - 1) * d⁄dX f)`. -/
theorem derivative_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    d⁄dX (f.binomialPow r) = r • (f.binomialPow (r - 1) * d⁄dX f) := by
  have hsub := hasSubst_sub_one hf
  rw [binomialPow_def, derivative_subst hsub, map_sub, derivative_one, sub_zero,
    derivative_binomialSeries, subst_smul hsub, smul_mul_assoc, ← binomialPow_def]

/-- **Logarithmic derivative identity for formal binomial powers**:
`f * d⁄dX (f.binomialPow r) = r • (f.binomialPow r * d⁄dX f)`. -/
theorem mul_derivative_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    f * d⁄dX (f.binomialPow r) = r • (f.binomialPow r * d⁄dX f) := by
  rw [derivative_binomialPow hf, mul_smul_comm, ← mul_assoc]
  nth_rw 1 [← binomialPow_one (R := R) hf]
  rw [← binomialPow_add hf, add_sub_cancel]

/-- Substituting a series `g` of zero constant coefficient commutes with `binomialPow`. -/
theorem subst_binomialPow {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 0)
    (r : R) :
    (f.binomialPow r).subst g = binomialPow (f.subst g) r := by
  have hg' : HasSubst g := .of_constantCoeff_zero' hg
  rw [binomialPow_def, subst_comp_subst_apply (hasSubst_sub_one hf) hg',
    subst_sub hg', subst_one, ← binomialPow_def]

/-- Rescaling the variable commutes with `binomialPow`. -/
theorem rescale_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (a : A) (r : R) :
    rescale a (f.binomialPow r) = (rescale a f).binomialPow r := by
  rw [rescale_eq_subst, rescale_eq_subst, subst_binomialPow hf (by simp)]

/-- Mapping coefficients along an `R`-algebra homomorphism commutes with `binomialPow`. -/
theorem map_algHom_binomialPow [CommRing B] [Algebra R B] {f : A⟦X⟧} (hf : constantCoeff f = 1)
    (φ : A →ₐ[R] B) (r : R) :
    (f.binomialPow r).map (φ : A →+* B) = (f.map (φ : A →+* B)).binomialPow r := by
  rw [binomialPow_def, binomialPow_def]
  refine (map_subst (hasSubst_sub_one hf) (h := (φ : A →+* B)) (binomialSeries A r)).trans ?_
  rw [map_algHom_binomialSeries]
  congr 1
  exact ((map (φ : A →+* B)).map_sub _ _).trans (by simp)

/-- Mapping coefficients along `algebraMap R A` commutes with `binomialPow`. -/
@[simp]
theorem map_algebraMap_binomialPow {f : R⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    (f.binomialPow r).map (algebraMap R A) = (f.map (algebraMap R A)).binomialPow r := by
  rw [binomialPow_def, binomialPow_def]
  refine (map_subst (hasSubst_sub_one hf) (h := algebraMap R A) (binomialSeries R r)).trans ?_
  rw [map_algebraMap_binomialSeries]
  congr 1
  exact ((map (algebraMap R A)).map_sub _ _).trans (by simp)

/-- Mapping coefficients along a ring homomorphism between binomial rings maps both base and
exponent of `binomialPow`. -/
theorem map_binomialPow [CommRing S] [BinomialRing S] {f : R⟦X⟧} (hf : constantCoeff f = 1)
    (φ : R →+* S) (r : R) :
    (f.binomialPow r).map φ = (f.map φ).binomialPow (φ r) := by
  rw [binomialPow_def, binomialPow_def]
  refine (map_subst (hasSubst_sub_one hf) (h := φ) (binomialSeries R r)).trans ?_
  rw [map_binomialSeries]
  congr 1
  exact ((map φ).map_sub _ _).trans (by simp)

/-- Over a ring with `HasUniqueDiv`, `binomialPow` distributes over products of principal units. -/
private theorem binomialPow_mul_of_hasUniqueDiv [HasUniqueDiv A] {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (r : R) :
    (f * g).binomialPow r = f.binomialPow r * g.binomialPow r := by
  have hfg : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, one_mul]
  refine eq_of_mul_derivative_eq (u := f * g) (w := r • d⁄dX (f * g))
    (by simp [hfg]) ?_ ?_ ?_
  · rw [constantCoeff_binomialPow hfg, map_mul, constantCoeff_binomialPow hf,
      constantCoeff_binomialPow hg, one_mul]
  · rw [mul_derivative_binomialPow hfg, smul_mul_assoc, mul_comm (d⁄dX (f * g))]
  · have hdf := mul_derivative_binomialPow hf r
    have hdg := mul_derivative_binomialPow hg r
    have hcalc : (f * g) * d⁄dX (f.binomialPow r * g.binomialPow r) =
        f * f.binomialPow r * (g * d⁄dX (g.binomialPow r)) +
          g * g.binomialPow r * (f * d⁄dX (f.binomialPow r)) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [hcalc, hdg, hdf, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [Algebra.smul_def (R := R)]
    ring

/-- **Multiplicativity of formal binomial powers in the base**: `(f * g) ^ r = f ^ r * g ^ r` for
any principal units `f, g : A⟦X⟧`, without any torsion hypothesis on `A`. -/
theorem binomialPow_mul {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (r : R) :
    (f * g).binomialPow r = f.binomialPow r * g.binomialPow r := by
  let := BinomialRing.toHasUniqueDiv (R := R)
  have : HasUniqueDiv (MvPolynomial (Bool × ℕ) R) :=
    ⟨fun {n} hn a b hab => MvPolynomial.ext _ _ fun m =>
      nsmul_right_injective hn
        ((map_nsmul (MvPolynomial.coeffAddMonoidHom m) n a).symm.trans
          ((congrArg (MvPolynomial.coeffAddMonoidHom m) hab).trans
            (map_nsmul (MvPolynomial.coeffAddMonoidHom m) n b)))⟩
  -- Specialize the identity from two generic principal units over `MvPolynomial (Bool × ℕ) R`.
  let F : (MvPolynomial (Bool × ℕ) R)⟦X⟧ := 1 + X * mk fun n => MvPolynomial.X (false, n)
  let G : (MvPolynomial (Bool × ℕ) R)⟦X⟧ := 1 + X * mk fun n => MvPolynomial.X (true, n)
  let φ : MvPolynomial (Bool × ℕ) R →ₐ[R] A :=
    MvPolynomial.aeval fun p => if p.1 then coeff (p.2 + 1) g else coeff (p.2 + 1) f
  have hF0 : constantCoeff F = 1 := by simp [F]
  have hG0 : constantCoeff G = 1 := by simp [G]
  have hFG0 : constantCoeff (F * G) = 1 := by rw [map_mul, hF0, hG0, one_mul]
  have hF : F.map (φ : MvPolynomial (Bool × ℕ) R →+* A) = f := by
    ext (_ | n)
    · simp [F, hf]
    · simp [F, φ, coeff_succ_X_mul]
  have hG : G.map (φ : MvPolynomial (Bool × ℕ) R →+* A) = g := by
    ext (_ | n)
    · simp [G, hg]
    · simp [G, φ, coeff_succ_X_mul]
  have h := congrArg (map (φ : MvPolynomial (Bool × ℕ) R →+* A))
    (binomialPow_mul_of_hasUniqueDiv hF0 hG0 r)
  rwa [map_algHom_binomialPow hFG0 φ, (map _).map_mul, (map _).map_mul,
    map_algHom_binomialPow hF0 φ, map_algHom_binomialPow hG0 φ, hF, hG] at h

/-- For a unit exponent `u : Rˣ`, `f ↦ f.binomialPow (u : R)` is injective on principal units. -/
theorem binomialPow_eq_iff {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (u : Rˣ) :
    f.binomialPow (u : R) = g.binomialPow (u : R) ↔ f = g := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h' := congrArg (fun p : A⟦X⟧ => p.binomialPow (↑u⁻¹ : R)) h
  simpa [hf, hg] using h'

/-- For a unit exponent `u : Rˣ`, `f.binomialPow (u : R) = 1` if and only if `f = 1`. -/
@[simp]
theorem binomialPow_eq_one_iff {f : A⟦X⟧} (hf : constantCoeff f = 1) (u : Rˣ) :
    f.binomialPow (u : R) = 1 ↔ f = 1 := by
  simpa using binomialPow_eq_iff hf constantCoeff_one u

/-- Congruence modulo `X ^ m` is preserved by `binomialPow`. -/
theorem X_pow_dvd_binomialPow_sub_binomialPow {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    {m : ℕ} (hfg : X ^ m ∣ f - g) (r : R) :
    X ^ m ∣ f.binomialPow r - g.binomialPow r := by
  rw [binomialPow_def, binomialPow_def]
  exact X_pow_dvd_subst_sub_subst (by simp [hf])
    (by simpa only [sub_sub_sub_cancel_right] using hfg) (binomialSeries A r)

/-- For a unit exponent `u : Rˣ`, two principal units are congruent modulo `X ^ m` if and only if
their `u`-th binomial powers are congruent modulo `X ^ m`. -/
theorem X_pow_dvd_binomialPow_sub_binomialPow_iff {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (u : Rˣ) {m : ℕ} :
    X ^ m ∣ f.binomialPow (u : R) - g.binomialPow (u : R) ↔ X ^ m ∣ f - g := by
  refine ⟨fun h => ?_, fun h => X_pow_dvd_binomialPow_sub_binomialPow hf h (u : R)⟩
  have h' := X_pow_dvd_binomialPow_sub_binomialPow (constantCoeff_binomialPow hf _) h (↑u⁻¹ : R)
  simpa [hf, hg] using h'

/-- The `m`-truncation of `f.binomialPow r` depends only on `trunc m f`. -/
theorem trunc_binomialPow_eq_of_trunc_eq {f g : A⟦X⟧} (hf : constantCoeff f = 1) {m : ℕ}
    (hfg : trunc m f = trunc m g) (r : R) :
    trunc m (f.binomialPow r) = trunc m (g.binomialPow r) := by
  have hdvd : X ^ m ∣ f - g := by
    rw [X_pow_dvd_iff]
    intro n hn
    rw [map_sub, coeff_eq_of_trunc_eq hfg hn, sub_self]
  have hout := X_pow_dvd_binomialPow_sub_binomialPow hf hdvd r
  rw [trunc_eq_trunc_iff]
  intro n hn
  exact sub_eq_zero.mp (by simpa only [map_sub] using X_pow_dvd_iff.mp hout n hn)

/-- For a unit exponent `u : Rˣ`, two principal units have the same `m`-truncation of their
`u`-th binomial powers if and only if they have the same `m`-truncation. -/
theorem trunc_binomialPow_eq_iff {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (u : Rˣ) {m : ℕ} :
    trunc m (f.binomialPow (u : R)) = trunc m (g.binomialPow (u : R)) ↔
      trunc m f = trunc m g := by
  refine ⟨fun h => ?_, fun h => trunc_binomialPow_eq_of_trunc_eq hf h (u : R)⟩
  have h' := trunc_binomialPow_eq_of_trunc_eq (constantCoeff_binomialPow hf _) h (↑u⁻¹ : R)
  simpa [hf, hg] using h'

/-- Product-chain formula for `d⁄dX (X * f ^ (-r))`:
`d⁄dX (X * f.binomialPow (-r)) = f.binomialPow (-r - 1) * (f - r • (X * d⁄dX f))`. -/
theorem derivative_X_mul_binomialPow_neg {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    d⁄dX (X * f.binomialPow (-r)) = f.binomialPow (-r - 1) * (f - r • (X * d⁄dX f)) := by
  have hsplit : f.binomialPow (-r - 1) * f = f.binomialPow (-r) := by
    nth_rw 2 [← binomialPow_one (R := R) hf]
    rw [← binomialPow_add hf, sub_add_cancel]
  rw [Derivation.leibniz, derivative_X, derivative_binomialPow hf, smul_eq_mul, smul_eq_mul,
    mul_one, ← hsplit]
  simp only [Algebra.smul_def (R := R), map_neg]
  ring

end BinomialPow

/-! ## Fractional-power formal reversion -/

section BinomialReversion

variable {R A B : Type*} [CommRing R] [BinomialRing R] [CommRing A] [Algebra R A]

/-- Given `f : A⟦X⟧` with `constantCoeff f = 1` and unit exponents `a b : Rˣ`,
`f.binomialReversion a b` is the unique formal power series `S : A⟦X⟧` with `constantCoeff S = 1`
solving `S.binomialPow (a : R) * f.subst (X * S.binomialPow (-(b : R))) = 1`.

It is constructed from the compositional inverse `G` of
`X * f.binomialPow (-(b : R) * (↑a⁻¹ : R))` by extracting `G / X` and taking its `-(b⁻¹)`-th
formal binomial power. -/
noncomputable def binomialReversion (f : A⟦X⟧) (a b : Rˣ) : A⟦X⟧ :=
  let P : A⟦X⟧ := X * (1 + X * mk fun n => coeff (n + 1) f).binomialPow (-(b : R) * (↑a⁻¹ : R))
  let G : A⟦X⟧ := P.substInvOfIsUnit (by simp [P])
  (mk fun n => coeff (n + 1) G).binomialPow (-(↑b⁻¹ : R))

/-- Explicit formula for `f.binomialReversion a b`. -/
theorem binomialReversion_def (f : A⟦X⟧) (a b : Rˣ) :
    f.binomialReversion a b =
      let P : A⟦X⟧ :=
        X * (1 + X * mk fun n => coeff (n + 1) f).binomialPow (-(b : R) * (↑a⁻¹ : R))
      let G : A⟦X⟧ := P.substInvOfIsUnit (by simp [P])
      (mk fun n => coeff (n + 1) G).binomialPow (-(↑b⁻¹ : R)) :=
  (rfl)

/-- Every formal binomial reversion has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_binomialReversion (f : A⟦X⟧) (a b : Rˣ) :
    constantCoeff (f.binomialReversion a b) = 1 := by
  rw [binomialReversion_def]
  dsimp only
  set P : A⟦X⟧ := X * (1 + X * mk fun n => coeff (n + 1) f).binomialPow (-(b : R) * (↑a⁻¹ : R))
  have hP1 : IsUnit (P.coeff 1) := by simp [P]
  refine constantCoeff_binomialPow ?_ _
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, coeff_one_substInvOfIsUnit]
  have hspec : (hP1.unit : A) = 1 := by rw [IsUnit.unit_spec]; simp [P]
  have hinv := hP1.unit.mul_inv
  rwa [hspec, one_mul] at hinv

/-- With `S = f.binomialReversion a b` (`constantCoeff f = 1`), `X * S ^ (-b)` is the
compositional inverse of `X * f ^ (-b * a⁻¹)`. -/
theorem subst_X_mul_binomialPow_binomialReversion {f : A⟦X⟧} (hf : constantCoeff f = 1)
    (a b : Rˣ) :
    (X * f.binomialPow (-(b : R) * (↑a⁻¹ : R))).subst
      (X * (f.binomialReversion a b).binomialPow (-(b : R))) = X := by
  rw [binomialReversion_def]
  dsimp only
  set P : A⟦X⟧ := X * (1 + X * mk fun n => coeff (n + 1) f).binomialPow (-(b : R) * (↑a⁻¹ : R))
  have hP1 : IsUnit (P.coeff 1) := by simp [P]
  set G : A⟦X⟧ := P.substInvOfIsUnit hP1
  have hG0 : constantCoeff G = 0 := constantCoeff_substInvOfIsUnit P hP1
  have hGtilde0 : constantCoeff (mk fun n => coeff (n + 1) G) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, coeff_one_substInvOfIsUnit]
    have hspec : (hP1.unit : A) = 1 := by rw [IsUnit.unit_spec]; simp [P]
    have hinv := hP1.unit.mul_inv
    rwa [hspec, one_mul] at hinv
  have hSpow : ((mk fun n => coeff (n + 1) G).binomialPow (-(↑b⁻¹ : R))).binomialPow (-(b : R)) =
      mk fun n => coeff (n + 1) G := by
    rw [binomialPow_binomialPow hGtilde0, neg_mul_neg, Units.inv_mul, binomialPow_one hGtilde0]
  have hGeq : X * mk (fun n => coeff (n + 1) G) = G := by
    conv_rhs => rw [G.eq_X_mul_shift_add_const, hG0, map_zero, add_zero]
  have hfeq : (1 : A⟦X⟧) + X * mk (fun n => coeff (n + 1) f) = f := by
    conv_rhs => rw [f.eq_X_mul_shift_add_const, hf, map_one, add_comm]
  have hPeq : P = X * f.binomialPow (-(b : R) * (↑a⁻¹ : R)) := by simp only [P, hfeq]
  rw [hSpow, hGeq, ← hPeq]
  exact P.subst_substInvOfIsUnit_right (by simp [P]) hP1

/-- **Characteristic equation of `binomialReversion`**: for `constantCoeff f = 1` and `a b : Rˣ`,
`S = f.binomialReversion a b` satisfies
`S.binomialPow (a : R) * f.subst (X * S.binomialPow (-(b : R))) = 1`. -/
theorem binomialPow_binomialReversion_mul_subst {f : A⟦X⟧} (hf : constantCoeff f = 1)
    (a b : Rˣ) :
    (f.binomialReversion a b).binomialPow (a : R) *
      f.subst (X * (f.binomialReversion a b).binomialPow (-(b : R))) = 1 := by
  set S := f.binomialReversion a b
  have hS0 : constantCoeff S = 1 := constantCoeff_binomialReversion f a b
  set G : A⟦X⟧ := X * S.binomialPow (-(b : R))
  have hG0 : constantCoeff G = 0 := by simp [G]
  have hG : HasSubst G := .of_constantCoeff_zero' hG0
  have hsub := subst_X_mul_binomialPow_binomialReversion hf a b
  rw [subst_mul hG, subst_X hG, subst_binomialPow hf hG0] at hsub
  have hmul : S.binomialPow (-(b : R)) *
      binomialPow (f.subst G) (-(b : R) * (↑a⁻¹ : R)) = 1 := by
    refine X_mul_cancel ?_
    calc
      X * (S.binomialPow (-(b : R)) * binomialPow (f.subst G) (-(b : R) * (↑a⁻¹ : R))) =
          G * binomialPow (f.subst G) (-(b : R) * (↑a⁻¹ : R)) := by rw [← mul_assoc]
      _ = X := hsub
      _ = X * 1 := (mul_one X).symm
  have hSrew : S.binomialPow (-(b : R)) =
      (S.binomialPow (a : R)).binomialPow (-(b : R) * (↑a⁻¹ : R)) := by
    rw [binomialPow_binomialPow hS0, mul_comm (a : R), mul_assoc, Units.inv_mul, mul_one]
  have hfG0 : constantCoeff (f.subst G : A⟦X⟧) = 1 := by
    rw [constantCoeff_eq,
      constantCoeff_subst_of_constantCoeff_zero (by simp [← constantCoeff_eq, G]), hf, map_one]
  rw [hSrew, ← binomialPow_mul (constantCoeff_binomialPow hS0 _) hfG0] at hmul
  exact (binomialPow_eq_one_iff
    (by rw [map_mul, constantCoeff_binomialPow hS0, hfG0, one_mul]) (-b * a⁻¹)).mp
    (by simpa [Units.val_mul, Units.val_neg] using hmul)

/-- **Congruence modulo `X ^ m` for `binomialReversion`**: if `constantCoeff g = 1` and
`X ^ m ∣ g ^ a * f(X * g ^ (-b)) - 1`, then `X ^ m ∣ g - f.binomialReversion a b`. -/
theorem X_pow_dvd_sub_binomialReversion {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (a b : Rˣ) {m : ℕ}
    (hdvd : X ^ m ∣ g.binomialPow (a : R) * f.subst (X * g.binomialPow (-(b : R))) - 1) :
    X ^ m ∣ g - f.binomialReversion a b := by
  set P : A⟦X⟧ := X * f.binomialPow (-(b : R) * (↑a⁻¹ : R))
  have hP0 : P.constantCoeff = 0 := by simp [P]
  have hP1 : IsUnit (P.coeff 1) := by simp [P, hf]
  set H : A⟦X⟧ := X * g.binomialPow (-(b : R))
  have hH0 : constantCoeff H = 0 := by simp [H]
  have hH : HasSubst H := .of_constantCoeff_zero' hH0
  have hfH0 : constantCoeff (f.subst H : A⟦X⟧) = 1 := by
    rw [constantCoeff_eq,
      constantCoeff_subst_of_constantCoeff_zero (by simp [← constantCoeff_eq, H]), hf, map_one]
  have hpow := X_pow_dvd_binomialPow_sub_binomialPow
    (by rw [map_mul, constantCoeff_binomialPow hg, hfH0, one_mul]) hdvd (-(b : R) * (↑a⁻¹ : R))
  rw [binomialPow_one_left, binomialPow_mul (constantCoeff_binomialPow hg _) hfH0,
    binomialPow_binomialPow hg,
    show (a : R) * (-(b : R) * (↑a⁻¹ : R)) = -(b : R) by
      rw [mul_comm (a : R), mul_assoc, Units.inv_mul, mul_one],
    ← subst_binomialPow hf hH0] at hpow
  have hXP : X ^ (m + 1) ∣ P.subst H - X := by
    have hmul : X * (g.binomialPow (-(b : R)) *
        (f.binomialPow (-(b : R) * (↑a⁻¹ : R))).subst H - 1) = P.subst H - X := by
      rw [subst_mul hH, subst_X hH, mul_sub, mul_one, mul_assoc]
    rw [← hmul, pow_succ']
    exact mul_dvd_mul_left X hpow
  have hinv := X_pow_dvd_subst_sub_subst
    (by rw [constantCoeff_eq,
      constantCoeff_subst_eq_zero (by simp [← constantCoeff_eq, H]) P (by simp [P])])
    hXP (P.substInvOfIsUnit hP1)
  have hGeq : P.substInvOfIsUnit hP1 = X * (f.binomialReversion a b).binomialPow (-(b : R)) :=
    (P.eq_substInvOfIsUnit_of_subst_eq_X hP0 hP1 (.of_constantCoeff_zero' (by simp))
      (subst_X_mul_binomialPow_binomialReversion hf a b)).symm
  rw [← subst_comp_subst_apply (.of_constantCoeff_zero hP0) hH,
    P.subst_substInvOfIsUnit_left hP0 hP1, X_subst, subst_X hH, hGeq, ← mul_sub] at hinv
  refine (X_pow_dvd_binomialPow_sub_binomialPow_iff hg
    (constantCoeff_binomialReversion f a b) (-b)).mp ?_
  rw [X_pow_dvd_iff] at hinv ⊢
  intro n hn
  simpa only [Units.val_neg, coeff_succ_X_mul] using hinv (n + 1) (Nat.succ_lt_succ hn)

/-- **Uniqueness of `binomialReversion`**: `f.binomialReversion a b` is the unique series `g` with
`constantCoeff g = 1` solving `g.binomialPow (a : R) * f.subst (X * g.binomialPow (-(b : R))) = 1`.
-/
theorem eq_binomialReversion_iff {f g : A⟦X⟧} (hf : constantCoeff f = 1) (a b : Rˣ) :
    constantCoeff g = 1 ∧
      g.binomialPow (a : R) * f.subst (X * g.binomialPow (-(b : R))) = 1 ↔
      g = f.binomialReversion a b := by
  refine ⟨fun ⟨hg0, hg⟩ => ?_, fun h => h ▸ ⟨constantCoeff_binomialReversion f a b,
    binomialPow_binomialReversion_mul_subst hf a b⟩⟩
  refine sub_eq_zero.mp (ext fun n => ?_)
  have hdvd := X_pow_dvd_sub_binomialReversion hf hg0 a b (m := n + 1)
    (by rw [hg, sub_self]; exact dvd_zero _)
  simpa only [map_zero] using X_pow_dvd_iff.mp hdvd n (Nat.lt_succ_self n)

/-- Mapping coefficients along an `R`-algebra homomorphism commutes with `binomialReversion` on
principal units. -/
theorem map_algHom_binomialReversion [CommRing B] [Algebra R B] {f : A⟦X⟧}
    (hf : constantCoeff f = 1) (φ : A →ₐ[R] B) (a b : Rˣ) :
    (f.binomialReversion a b).map (φ : A →+* B) = (f.map (φ : A →+* B)).binomialReversion a b := by
  have hfφ : constantCoeff (f.map (φ : A →+* B)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff, hf, map_one]
  rw [← eq_binomialReversion_iff hfφ a b]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
      constantCoeff_binomialReversion, map_one]
  have hchar := congrArg (map (φ : A →+* B)) (binomialPow_binomialReversion_mul_subst hf a b)
  rw [(map _).map_mul, (map _).map_one,
    map_algHom_binomialPow (constantCoeff_binomialReversion f a b) φ] at hchar
  refine Eq.trans ?_ hchar
  congr 1
  have hG : HasSubst (X * (f.binomialReversion a b).binomialPow (-(b : R))) :=
    .of_constantCoeff_zero' (by simp)
  refine ((map_subst hG (h := (φ : A →+* B)) f).trans ?_).symm
  congr 1
  exact ((map (φ : A →+* B)).map_mul _ _).trans
    (by simp [map_algHom_binomialPow (constantCoeff_binomialReversion f a b) φ])

/-- Mapping coefficients along `algebraMap R A` commutes with `binomialReversion` on principal
units. -/
@[simp]
theorem map_algebraMap_binomialReversion {f : R⟦X⟧} (hf : constantCoeff f = 1) (a b : Rˣ) :
    (f.binomialReversion a b).map (algebraMap R A) =
      (f.map (algebraMap R A)).binomialReversion a b :=
  map_algHom_binomialReversion hf (Algebra.ofId R A) a b

/-- **Differential identity for `binomialReversion`**: if `f : A⟦X⟧` has constant coefficient `1`
and `M * (f - ((b : R) * (↑a⁻¹ : R)) • (X * d⁄dX f)) = 1`, then `S = f.binomialReversion a b`
satisfies `M.subst (X * S ^ (-b)) = S ^ (a - 1) * (S - b • (X * d⁄dX S))`. -/
theorem subst_X_mul_binomialPow_binomialReversion_of_mul_deriv {M f : A⟦X⟧}
    (hf : constantCoeff f = 1) (a b : Rˣ)
    (hode : M * (f - ((b : R) * (↑a⁻¹ : R)) • (X * d⁄dX f)) = 1) :
    M.subst (X * (f.binomialReversion a b).binomialPow (-(b : R))) =
      (f.binomialReversion a b).binomialPow ((a : R) - 1) *
        (f.binomialReversion a b - (b : R) • (X * d⁄dX (f.binomialReversion a b))) := by
  set r : R := (b : R) * (↑a⁻¹ : R)
  set S := f.binomialReversion a b
  have hS0 : constantCoeff S = 1 := constantCoeff_binomialReversion f a b
  set P : A⟦X⟧ := X * f.binomialPow (-r)
  set G : A⟦X⟧ := X * S.binomialPow (-(b : R))
  have hG0 : constantCoeff G = 0 := by simp [G]
  have hG : HasSubst G := .of_constantCoeff_zero' hG0
  have hMP : M * d⁄dX P = f.binomialPow (-r - 1) := by
    rw [show P = X * f.binomialPow (-r) from rfl, derivative_X_mul_binomialPow_neg hf r,
      mul_left_comm, hode, mul_one]
  have hchain : (d⁄dX P).subst G * d⁄dX G = 1 := by
    have hPG := congrArg (d⁄dX) (subst_X_mul_binomialPow_binomialReversion hf a b)
    rwa [show X * f.binomialPow (-(b : R) * (↑a⁻¹ : R)) = P by simp [P, r],
      derivative_subst hG, derivative_X] at hPG
  have hMG : M.subst G = binomialPow (f.subst G) (-r - 1) * d⁄dX G := by
    calc
      M.subst G = M.subst G * ((d⁄dX P).subst G * d⁄dX G) := by rw [hchain, mul_one]
      _ = (M * d⁄dX P).subst G * d⁄dX G := by rw [← mul_assoc, ← subst_mul hG]
      _ = binomialPow (f.subst G) (-r - 1) * d⁄dX G := by
        rw [hMP, subst_binomialPow hf hG0]
  have hfG : f.subst G = S.binomialPow (-(a : R)) := by
    have hchar := binomialPow_binomialReversion_mul_subst hf a b
    calc
      f.subst G = S.binomialPow (-(a : R)) * (S.binomialPow (a : R) * f.subst G) := by
        rw [← mul_assoc, binomialPow_neg_mul hS0, one_mul]
      _ = S.binomialPow (-(a : R)) := by rw [hchar, mul_one]
  have hexp : (-(a : R)) * (-r - 1) + (-(b : R) - 1) = (a : R) - 1 := by
    have har : (a : R) * r = (b : R) := by
      rw [mul_comm (a : R), show r = (b : R) * (↑a⁻¹ : R) from rfl, mul_assoc, Units.inv_mul,
        mul_one]
    linear_combination har
  rw [hMG, hfG, show G = X * S.binomialPow (-(b : R)) from rfl,
    derivative_X_mul_binomialPow_neg hS0 (b : R), binomialPow_binomialPow hS0, ← mul_assoc,
    ← binomialPow_add hS0, hexp]

end BinomialReversion

/-! ## Compatibility with formal logarithm and exponential over `ℚ`-algebras -/

section RatAlgebra

variable {R A : Type*} [CommRing R] [BinomialRing R] [CommRing A] [Algebra ℚ A] [Algebra R A]

/-- Over a `ℚ`-algebra, the formal logarithm of `binomialSeries A r` is `r • log A`. -/
@[simp]
theorem logOf_binomialSeries (r : R) :
    logOf (binomialSeries A r) = r • log A := by
  have : HasUniqueDiv A := .of_module_rat A
  refine derivative.ext ?_ (by simp [constantCoeff_logOf])
  have hunit : IsUnit (1 + X : A⟦X⟧) := isUnit_iff_constantCoeff.mpr (by simp)
  have hbunit : IsUnit (binomialSeries A r) := isUnit_binomialSeries r
  refine hunit.mul_left_cancel (hbunit.mul_right_cancel ?_)
  calc
    (1 + X) * d⁄dX (logOf (binomialSeries A r)) * binomialSeries A r =
        (1 + X) * (logDeriv (binomialSeries A r) * binomialSeries A r) := by
      rw [logDeriv_def, mul_assoc]
    _ = (1 + X) * d⁄dX (binomialSeries A r) := by
      rw [logDeriv_mul _ (binomialSeries_constantCoeff r)]
    _ = r • binomialSeries A r := one_add_X_mul_derivative_binomialSeries r
    _ = (1 + X) * d⁄dX (r • log A) * binomialSeries A r := by
      have hlog : (1 + X) * d⁄dX (log A) = (1 : A⟦X⟧) := by
        simpa only [mul_comm] using derivative_log_mul_one_add_X (A := A)
      rw [show r • log A = C (algebraMap R A r) * log A by
            rw [Algebra.smul_def (R := R), algebraMap_apply],
        Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul,
        mul_left_comm (1 + X), hlog, mul_one, ← algebraMap_apply, ← Algebra.smul_def (R := R)]

/-- Over a `ℚ`-algebra, the formal logarithm of `f.binomialPow r` is `r • logOf f`. -/
@[simp]
theorem logOf_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    logOf (f.binomialPow r) = r • logOf f := by
  have hsub : HasSubst (f - 1) := .of_constantCoeff_zero' (by simp [hf])
  have hinner : f.binomialPow r - 1 = (binomialSeries A r - 1).subst (f - 1) := by
    rw [binomialPow_def, subst_sub hsub, subst_one]
  rw [logOf_eq, hinner,
    ← subst_comp_subst_apply (TauCeti.hasSubst_binomialSeries_sub_one r) hsub,
    ← logOf_eq, logOf_binomialSeries, subst_smul hsub, ← logOf_eq]

/-- Over a `ℚ`-algebra, `exp (r • logOf f)` equals `f.binomialPow r`. -/
@[simp]
theorem subst_exp_smul_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    (exp A).subst (r • logOf f) = f.binomialPow r := by
  rw [← logOf_binomialPow hf r, subst_exp_logOf (constantCoeff_binomialPow hf r)]

end RatAlgebra

end PowerSeries

