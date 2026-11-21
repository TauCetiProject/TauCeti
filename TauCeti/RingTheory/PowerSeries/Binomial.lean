/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.RingTheory.PowerSeries.Log

import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Rescale
import TauCeti.RingTheory.PowerSeries.SubstInv
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Formal binomial powers and fractional-power reversion of power series

Let `R` be a commutative binomial ring and `A` a commutative `R`-algebra. Mathlib defines the
binomial series `PowerSeries.binomialSeries A r` representing `(1 + X) ^ r` and proves the
addition law `binomialSeries A (r + s) = binomialSeries A r * binomialSeries A s`.

For any series `f : A⟦X⟧` with constant coefficient `1`, substituting `f - 1` into
`binomialSeries A r` defines the formal binomial power `f.binomialPow r =
(binomialSeries A r).subst (f - 1)`. This file develops the differential and algebraic laws of
`binomialSeries` and `binomialPow`, making the multiplicative group `{f : A⟦X⟧ | constantCoeff f =
1}` of principal units into an `R`-module without any additive torsion-freeness hypothesis on `A`:

* `PowerSeries.binomialPow_add`: `f ^ (r + s) = f ^ r * f ^ s`,
* `PowerSeries.binomialPow_binomialPow`: `(f ^ r) ^ s = f ^ (r * s)`,
* `PowerSeries.binomialPow_mul`: `(f * g) ^ r = f ^ r * g ^ r`.

Building on `binomialPow`, `PowerSeries.binomialReversion` constructs fractional-power formal
reversion: for any principal unit `f : A⟦X⟧`, unit exponent `a : Rˣ`, and arbitrary exponent
`b : R`, it gives the unique principal unit `S : A⟦X⟧` solving `S ^ a * f(X * S ^ (-b)) = 1`,
together with modulo-`X ^ m` congruence lifting and a differential reversion identity. Over
`ℚ`-algebras, `binomialPow` agrees with `exp (r • logOf f)` (`PowerSeries.logOf_binomialPow`,
`PowerSeries.subst_exp_smul_logOf`, `PowerSeries.subst_exp_smul_log`).

## Main definitions

* `PowerSeries.binomialPow`: the formal binomial power `(binomialSeries A r).subst (f - 1)` of a
  power series `f : A⟦X⟧` by an exponent `r : R`.
* `PowerSeries.binomialReversion`: for `f : A⟦X⟧` with `constantCoeff f = 1`, unit exponent
  `a : Rˣ`, and exponent `b : R`, the unique formal power series `S` with `constantCoeff S = 1`
  solving `S.binomialPow (a : R) * f.subst (X * S.binomialPow (-b)) = 1`.

## Main results

* `PowerSeries.derivative_binomialSeries`, `PowerSeries.one_add_X_mul_derivative_binomialSeries`,
  `PowerSeries.subst_binomialSeries_sub_one`, and `PowerSeries.binomialSeries_algebraMap`:
  derivative, logarithmic ODE, composition law, and scalar-tower compatibility of `binomialSeries`.
* `PowerSeries.rescale_neg_one_invOneSubPow_zpow`: under `X ↦ -X`, the integer power
  `(1 - X) ^ (-k)` is the binomial series `binomialSeries R (-k)`, extending Mathlib's
  `PowerSeries.rescale_neg_one_invOneSubPow` from natural to integer exponents.
* `PowerSeries.binomialPow_add`, `PowerSeries.binomialPow_binomialPow`,
  `PowerSeries.binomialPow_mul`, `PowerSeries.derivative_binomialPow`,
  `PowerSeries.mul_derivative_binomialPow`: `R`-module laws and chain rules for `binomialPow`.
* `PowerSeries.subst_binomialPow`, `PowerSeries.rescale_binomialPow`,
  `PowerSeries.map_binomialPow`, `PowerSeries.binomialPow_algebraMap`,
  `PowerSeries.binomialPow_left_inj`, `PowerSeries.trunc_binomialPow_eq_trunc_binomialPow_iff`:
  compatibility with substitution, rescaling, coefficient maps, scalar towers, unit-exponent
  cancellation, and truncation.
* `PowerSeries.binomialPow_binomialReversion_mul_subst`, `PowerSeries.eq_binomialReversion_iff`,
  `PowerSeries.eq_map_algHom_binomialReversion_iff`,
  `PowerSeries.eq_map_algebraMap_binomialReversion_iff`,
  `PowerSeries.binomialReversion_one`, `PowerSeries.binomialReversion_zero`,
  `PowerSeries.coeff_one_binomialReversion`, `PowerSeries.rescale_binomialReversion`,
  `PowerSeries.map_binomialReversion`, `PowerSeries.binomialReversion_unitsMap_algebraMap`,
  `PowerSeries.subst_X_mul_binomialPow_binomialReversion_of_mul_derivative`, and
  `PowerSeries.X_pow_dvd_sub_binomialReversion`: existence, uniqueness, functoriality, differential
  identity, and congruence modulo `X ^ m` for fractional-power formal reversion.
* `PowerSeries.logOf_binomialSeries`, `PowerSeries.logOf_binomialPow`,
  `PowerSeries.subst_exp_smul_log`, and `PowerSeries.subst_exp_smul_logOf`: compatibility with
  `PowerSeries.logOf` and `PowerSeries.exp` over `ℚ`-algebras.

## References

* J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*, J. Pure Appl. Algebra
  **207** (2006), 165–185.
* N. Bourbaki, *Algebra II*, Chapter IV, §4, Formal power series.
-/

public section

namespace PowerSeries

open Finset

/-! ## Further properties of `PowerSeries.binomialSeries` -/

section BinomialSeries

variable {R S : Type*} [CommRing R] [BinomialRing R]

/-- Mapping coefficients along a ring homomorphism between binomial rings maps the exponent of
`binomialSeries`. -/
theorem map_binomialSeries [CommRing S] [BinomialRing S] (φ : R →+* S) (r : R) :
    (binomialSeries R r).map φ = binomialSeries S (φ r) := by
  ext n; simp [Ring.map_choose]

section Semiring

variable {A B : Type*} [Semiring A] [Algebra R A]

/-- Mapping coefficients along `algebraMap R A` sends `binomialSeries R r` to
`binomialSeries A r`. -/
@[simp]
theorem map_algebraMap_binomialSeries (r : R) :
    (binomialSeries R r).map (algebraMap R A) = binomialSeries A r := by
  ext n; simp [Algebra.smul_def]

/-- Mapping coefficients along an `R`-algebra homomorphism preserves `binomialSeries`. -/
@[simp]
theorem map_algHom_binomialSeries [Semiring B] [Algebra R B] (φ : A →ₐ[R] B) (r : R) :
    (binomialSeries A r).map (φ : A →+* B) = binomialSeries B r := by
  ext n; simp

/-- Along a scalar tower `R → S → A` of binomial rings, `binomialSeries A` is compatible with
mapping the exponent along `algebraMap R S`. -/
theorem binomialSeries_algebraMap [CommRing S] [BinomialRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] (r : R) :
    binomialSeries A (algebraMap R S r) = binomialSeries A r := by
  ext n; simp [← Ring.map_choose, algebraMap_smul]

end Semiring

section Ring

variable {A : Type*} [Ring A] [Algebra R A]

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
theorem binomialSeries_neg_one : binomialSeries A (-1 : R) = invOfUnit (1 + X) 1 := by
  have h1 : (1 + X) * invOfUnit (1 + X : A⟦X⟧) 1 = 1 := mul_invOfUnit (1 + X) 1 (by simp)
  have h2 : binomialSeries A (-1 : R) * (1 + X) = 1 := by
    simpa [binomialSeries_one] using binomialSeries_neg_mul (A := A) (1 : R)
  exact left_inv_eq_right_inv h2 h1

end Ring

section CommSemiring

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- **Derivative of the binomial series**: `d⁄dX (1 + X) ^ r = r • (1 + X) ^ (r - 1)`. -/
theorem derivative_binomialSeries (r : R) :
    d⁄dX (binomialSeries A r) = r • binomialSeries A (r - 1) := by
  ext n
  rw [coeff_derivative, coeff_smul]
  simp only [binomialSeries_coeff, Algebra.smul_def, mul_one]
  have hchoose : (n + 1) • Ring.choose r (n + 1) = r * Ring.choose (r - 1) n := by
    simpa [Nat.choose_one_right] using Ring.choose_smul_choose r (n := n + 1) (k := 1) (by omega)
  rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hchoose
  simpa [mul_comm] using congrArg (algebraMap R A) hchoose

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A] [Algebra R A]

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
  refine eq_of_mul_derivative_eq_mul (u := 1 + X) (w := C (r * s)) (by simp) ?_ ?_ ?_
  · rw [constantCoeff_subst_of_constantCoeff_zero' (by simp)]; simp
  · have hsplit : (binomialSeries R s).subst (binomialSeries R r - 1) =
        (binomialSeries R (s - 1)).subst (binomialSeries R r - 1) * binomialSeries R r := by
      have hmul : binomialSeries R s = binomialSeries R (s - 1) * (1 + X) := by
        rw [← binomialSeries_one (R := R), ← binomialSeries_add, sub_add_cancel]
      rw [hmul, subst_mul hsub, subst_add hsub, subst_one, subst_X hsub, add_sub_cancel]
    have hderiv := one_add_X_mul_derivative_binomialSeries (A := R) r
    rw [derivative_subst hsub, map_sub, derivative_one, sub_zero, derivative_binomialSeries,
      subst_smul hsub]
    calc (1 + X) * (s • (binomialSeries R (s - 1)).subst (binomialSeries R r - 1) *
          d⁄dX (binomialSeries R r))
      _ = s • (binomialSeries R (s - 1)).subst (binomialSeries R r - 1) *
            ((1 + X) * d⁄dX (binomialSeries R r)) := by simp only [smul_eq_C_mul]; ring
      _ = C (r * s) * (binomialSeries R s).subst (binomialSeries R r - 1) := by
          rw [hderiv, hsplit]; simp only [smul_eq_C_mul, map_mul]; ring
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

end CommRing

end BinomialSeries

section InvOneSubPow

variable {R : Type*} [CommRing R]

/-- Under `X ↦ -X`, the integer power `(1 - X) ^ (-k)` becomes the binomial series
`(1 + X) ^ (-k)`. -/
theorem rescale_neg_one_invOneSubPow_zpow (k : ℤ) :
    rescale (-1 : R) (↑(invOneSubPow R 1 ^ k) : R⟦X⟧) = binomialSeries R (-k) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h1 := rescale_neg_one_invOneSubPow (A := R) 1
    rw [Nat.cast_one] at h1
    rw [zpow_add_one, Units.val_mul, map_mul, ih, h1, neg_add, binomialSeries_add]
  | pred k ih =>
    have h1 : rescale (-1 : R) (↑(invOneSubPow R 1)⁻¹ : R⟦X⟧) = binomialSeries R (1 : ℤ) := by
      rw [← Units.inv_eq_val_inv, invOneSubPow_inv_eq_one_sub_pow, binomialSeries_one]
      simp [rescale_X, sub_eq_add_neg]
    rw [zpow_sub_one, Units.val_mul, map_mul, ih, h1, neg_sub, sub_eq_neg_add, binomialSeries_add]

end InvOneSubPow

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
    f.binomialPow r = (binomialSeries A r).subst (f - 1) := (rfl)

/-- The formal binomial power of a series with constant coefficient `1` has constant coefficient
`1`. -/
@[simp]
theorem constantCoeff_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    constantCoeff (f.binomialPow r) = 1 := by
  rw [binomialPow_def, constantCoeff_subst_of_constantCoeff_zero' (by simp [hf])]; simp

/-- For `constantCoeff f = 1`, `f.binomialPow r - 1` has zero constant coefficient and can be
substituted into any power series. -/
theorem hasSubst_binomialPow_sub_one {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    HasSubst (f.binomialPow r - 1) :=
  HasSubst.sub_one (constantCoeff_binomialPow hf r)

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
theorem binomialPow_zero (f : A⟦X⟧) : f.binomialPow (0 : R) = 1 := by
  rw [binomialPow_def, binomialSeries_zero, subst_one]

/-- At exponent `1`, the formal binomial power is the series itself. -/
@[simp]
theorem binomialPow_one {f : A⟦X⟧} (hf : constantCoeff f = 1) : f.binomialPow (1 : R) = f := by
  have hsub := HasSubst.sub_one hf
  rw [binomialPow_def, binomialSeries_one, subst_add hsub, subst_one, subst_X hsub, add_sub_cancel]

/-- At a natural number exponent, the formal binomial power is the ordinary power. -/
@[simp]
theorem binomialPow_natCast {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) :
    f.binomialPow (n : R) = f ^ n := by
  have hsub := HasSubst.sub_one hf
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
  rw [binomialPow_def, binomialSeries_add, subst_mul (HasSubst.sub_one hf), ← binomialPow_def,
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

/-- `f.binomialPow (-1 : R)` is the left inverse of `f`. -/
@[simp]
theorem binomialPow_neg_one_mul {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f.binomialPow (-1 : R) * f = 1 := by
  have h := binomialPow_neg_mul hf (1 : R)
  rwa [binomialPow_one hf] at h

/-- `f.binomialPow (-1 : R)` is the right inverse of `f`. -/
@[simp]
theorem mul_binomialPow_neg_one {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f * f.binomialPow (-1 : R) = 1 := by
  rw [mul_comm, binomialPow_neg_one_mul hf]

/-- Every formal binomial power of a series with constant coefficient `1` is a unit. -/
theorem isUnit_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    IsUnit (f.binomialPow r) :=
  isUnit_iff_exists.mpr ⟨f.binomialPow (-r), binomialPow_mul_neg hf r, binomialPow_neg_mul hf r⟩

/-- At exponent `-1`, the formal binomial power is `invOfUnit f 1`. -/
theorem binomialPow_neg_one {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f.binomialPow (-1 : R) = invOfUnit f 1 :=
  left_inv_eq_right_inv (binomialPow_neg_one_mul hf) (mul_invOfUnit f 1 hf)

/-- At a negated natural number `-(n : R)`, the formal binomial power is `(invOfUnit f 1) ^ n`. -/
theorem binomialPow_neg_natCast {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) :
    f.binomialPow (-(n : R)) = invOfUnit f 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, neg_add, binomialPow_add hf, ih, binomialPow_neg_one hf, pow_succ]

/-- For a unit `u : A⟦X⟧ˣ` with constant coefficient `1`, the formal binomial power at an integer
cast `(z : R)` is `↑(u ^ z)`. -/
@[simp]
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
  have hsub := HasSubst.sub_one hf
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

/-- If `n • r = -1`, then `(f.binomialPow r) ^ n * f = 1`. -/
theorem pow_binomialPow_mul_eq_one {f : A⟦X⟧} (hf : constantCoeff f = 1)
    {n : ℕ} {r : R} (hr : n • r = -1) : f.binomialPow r ^ n * f = 1 := by
  rw [pow_binomialPow hf, hr, binomialPow_neg_one_mul hf]

/-- Taking the formal binomial power of `f ^ n` scales the exponent by `n`. -/
theorem binomialPow_pow {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) (r : R) :
    (f ^ n).binomialPow r = f.binomialPow (n • r) := by
  rw [← binomialPow_natCast (R := R) hf n, binomialPow_binomialPow hf, nsmul_eq_mul]

/-- The linear coefficient of `f.binomialPow r` is `r • coeff 1 f`. -/
theorem coeff_one_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    coeff 1 (f.binomialPow r) = r • coeff 1 f := by
  rw [binomialPow_def, coeff_one_subst (by simp [hf])]; simp [Algebra.smul_def]

/-- **Chain rule for formal binomial powers**:
`d⁄dX (f.binomialPow r) = r • (f.binomialPow (r - 1) * d⁄dX f)`. -/
theorem derivative_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    d⁄dX (f.binomialPow r) = r • (f.binomialPow (r - 1) * d⁄dX f) := by
  have hsub := HasSubst.sub_one hf
  rw [binomialPow_def, derivative_subst hsub, map_sub, derivative_one, sub_zero,
    derivative_binomialSeries, subst_smul hsub, smul_mul_assoc, ← binomialPow_def]

/-- **Logarithmic derivative identity for formal binomial powers**:
`f * d⁄dX (f.binomialPow r) = r • (f.binomialPow r * d⁄dX f)`. -/
theorem mul_derivative_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    f * d⁄dX (f.binomialPow r) = r • (f.binomialPow r * d⁄dX f) := by
  rw [derivative_binomialPow hf, mul_smul_comm, ← mul_assoc]
  nth_rw 1 [← binomialPow_one (R := R) hf]
  rw [← binomialPow_add hf, add_sub_cancel]

/-- Substituting a substitutable series `g` commutes with `binomialPow`. -/
theorem subst_binomialPow {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : HasSubst g)
    (r : R) : (f.binomialPow r).subst g = binomialPow (f.subst g) r := by
  rw [binomialPow_def, subst_comp_subst_apply (HasSubst.sub_one hf) hg,
    subst_sub hg, subst_one, ← binomialPow_def]

/-- Rescaling the variable commutes with `binomialPow`. -/
theorem rescale_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (a : A) (r : R) :
    rescale a (f.binomialPow r) = (rescale a f).binomialPow r := by
  rw [rescale_eq_subst, rescale_eq_subst,
    subst_binomialPow hf (.of_constantCoeff_zero' (by simp))]

/-- Mapping coefficients along an `R`-algebra homomorphism commutes with `binomialPow`. -/
@[simp]
theorem map_algHom_binomialPow [CommRing B] [Algebra R B] {f : A⟦X⟧} (hf : constantCoeff f = 1)
    (φ : A →ₐ[R] B) (r : R) :
    (f.binomialPow r).map (φ : A →+* B) = (f.map (φ : A →+* B)).binomialPow r := by
  rw [binomialPow_def, binomialPow_def]
  refine (map_subst (HasSubst.sub_one hf) (h := (φ : A →+* B)) (binomialSeries A r)).trans ?_
  rw [map_algHom_binomialSeries]
  congr 1
  exact ((map (φ : A →+* B)).map_sub _ _).trans (by simp)

/-- Mapping coefficients along `algebraMap R A` commutes with `binomialPow`. -/
@[simp]
theorem map_algebraMap_binomialPow {f : R⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    (f.binomialPow r).map (algebraMap R A) = (f.map (algebraMap R A)).binomialPow r :=
  map_algHom_binomialPow hf (Algebra.ofId R A) r

/-- Mapping coefficients along a ring homomorphism between binomial rings maps both base and
exponent of `binomialPow`. -/
theorem map_binomialPow [CommRing S] [BinomialRing S] {f : R⟦X⟧} (hf : constantCoeff f = 1)
    (φ : R →+* S) (r : R) :
    (f.binomialPow r).map φ = (f.map φ).binomialPow (φ r) := by
  rw [binomialPow_def, binomialPow_def]
  refine (map_subst (HasSubst.sub_one hf) (h := φ) (binomialSeries R r)).trans ?_
  rw [map_binomialSeries]
  congr 1
  exact ((map φ).map_sub _ _).trans (by simp)

/-- Along a scalar tower `R → S → A` of binomial rings, `binomialPow` is compatible with mapping
the exponent along `algebraMap R S`. -/
theorem binomialPow_algebraMap [CommRing S] [BinomialRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] (f : A⟦X⟧) (r : R) :
    f.binomialPow (algebraMap R S r) = f.binomialPow r := by
  rw [binomialPow_def, binomialPow_def, binomialSeries_algebraMap]

/-- Over a ring with `HasUniqueDiv`, `binomialPow` distributes over products of principal units. -/
private theorem binomialPow_mul_of_hasUniqueDiv [HasUniqueDiv A] {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (r : R) :
    (f * g).binomialPow r = f.binomialPow r * g.binomialPow r := by
  have hfg : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, one_mul]
  refine eq_of_mul_derivative_eq_mul (u := f * g) (w := r • d⁄dX (f * g)) (by simp [hfg]) ?_ ?_ ?_
  · rw [constantCoeff_binomialPow hfg, map_mul, constantCoeff_binomialPow hf,
      constantCoeff_binomialPow hg, one_mul]
  · rw [mul_derivative_binomialPow hfg, smul_mul_assoc, mul_comm (d⁄dX (f * g))]
  · have hcalc : (f * g) * d⁄dX (f.binomialPow r * g.binomialPow r) =
        f * f.binomialPow r * (g * d⁄dX (g.binomialPow r)) +
          g * g.binomialPow r * (f * d⁄dX (f.binomialPow r)) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    rw [hcalc, mul_derivative_binomialPow hg r, mul_derivative_binomialPow hf r,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [Algebra.smul_def (R := R)]; ring

/-- **Multiplicativity of formal binomial powers in the base**: `(f * g) ^ r = f ^ r * g ^ r` for
any principal units `f, g : A⟦X⟧`, without any torsion hypothesis on `A`. -/
theorem binomialPow_mul {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (r : R) : (f * g).binomialPow r = f.binomialPow r * g.binomialPow r := by
  let := BinomialRing.toHasUniqueDiv (R := R)
  let F : (MvPolynomial (Bool × ℕ) R)⟦X⟧ := 1 + X * mk fun n => MvPolynomial.X (false, n)
  let G : (MvPolynomial (Bool × ℕ) R)⟦X⟧ := 1 + X * mk fun n => MvPolynomial.X (true, n)
  let φ : MvPolynomial (Bool × ℕ) R →ₐ[R] A :=
    MvPolynomial.aeval fun p => if p.1 then coeff (p.2 + 1) g else coeff (p.2 + 1) f
  have hF0 : constantCoeff F = 1 := by simp [F]
  have hG0 : constantCoeff G = 1 := by simp [G]
  have hFG0 : constantCoeff (F * G) = 1 := by rw [map_mul, hF0, hG0, one_mul]
  have hF : F.map (φ : MvPolynomial (Bool × ℕ) R →+* A) = f := by
    ext (_ | n) <;> simp [F, φ, hf, coeff_succ_X_mul]
  have hG : G.map (φ : MvPolynomial (Bool × ℕ) R →+* A) = g := by
    ext (_ | n) <;> simp [G, φ, hg, coeff_succ_X_mul]
  have h := congrArg (map (φ : MvPolynomial (Bool × ℕ) R →+* A))
    (binomialPow_mul_of_hasUniqueDiv hF0 hG0 r)
  rwa [map_algHom_binomialPow hFG0 φ, (map _).map_mul, (map _).map_mul,
    map_algHom_binomialPow hF0 φ, map_algHom_binomialPow hG0 φ, hF, hG] at h

/-- For a unit exponent `u : Rˣ`, `f ↦ f.binomialPow (u : R)` is injective on principal units. -/
theorem binomialPow_left_inj {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (u : Rˣ) :
    f.binomialPow (u : R) = g.binomialPow (u : R) ↔ f = g := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  simpa [hf, hg] using congrArg (fun p : A⟦X⟧ => p.binomialPow (↑u⁻¹ : R)) h

/-- For a unit exponent `u : Rˣ`, `f.binomialPow (u : R) = 1` if and only if `f = 1`. -/
@[simp]
theorem binomialPow_eq_one_iff {f : A⟦X⟧} (hf : constantCoeff f = 1) (u : Rˣ) :
    f.binomialPow (u : R) = 1 ↔ f = 1 := by
  simpa using binomialPow_left_inj hf constantCoeff_one u

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
  simpa [hf, hg] using
    X_pow_dvd_binomialPow_sub_binomialPow (constantCoeff_binomialPow hf _) h (↑u⁻¹ : R)

/-- The `m`-truncation of `f.binomialPow r` depends only on `trunc m f`. -/
theorem trunc_binomialPow_eq_of_trunc_eq {f g : A⟦X⟧} (hf : constantCoeff f = 1) {m : ℕ}
    (hfg : trunc m f = trunc m g) (r : R) :
    trunc m (f.binomialPow r) = trunc m (g.binomialPow r) := by
  have hdvd : X ^ m ∣ f - g := X_pow_dvd_iff.mpr fun n hn => by
    rw [map_sub, coeff_eq_of_trunc_eq hfg hn, sub_self]
  have hout := X_pow_dvd_binomialPow_sub_binomialPow hf hdvd r
  exact trunc_eq_trunc_iff.mpr fun n hn =>
    sub_eq_zero.mp (by simpa only [map_sub] using X_pow_dvd_iff.mp hout n hn)

/-- For a unit exponent `u : Rˣ`, two principal units have the same `m`-truncation of their
`u`-th binomial powers if and only if they have the same `m`-truncation. -/
theorem trunc_binomialPow_eq_trunc_binomialPow_iff {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (u : Rˣ) {m : ℕ} :
    trunc m (f.binomialPow (u : R)) = trunc m (g.binomialPow (u : R)) ↔
      trunc m f = trunc m g := by
  refine ⟨fun h => ?_, fun h => trunc_binomialPow_eq_of_trunc_eq hf h (u : R)⟩
  simpa [hf, hg] using
    trunc_binomialPow_eq_of_trunc_eq (constantCoeff_binomialPow hf _) h (↑u⁻¹ : R)

/-- Product-chain formula for `d⁄dX (X * f ^ (-r))`:
`d⁄dX (X * f.binomialPow (-r)) = f.binomialPow (-r - 1) * (f - r • (X * d⁄dX f))`. -/
theorem derivative_X_mul_binomialPow_neg {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    d⁄dX (X * f.binomialPow (-r)) = f.binomialPow (-r - 1) * (f - r • (X * d⁄dX f)) := by
  have hsplit : f.binomialPow (-r - 1) * f = f.binomialPow (-r) := by
    nth_rw 2 [← binomialPow_one (R := R) hf]
    rw [← binomialPow_add hf, sub_add_cancel]
  rw [Derivation.leibniz, derivative_X, derivative_binomialPow hf, smul_eq_mul, smul_eq_mul,
    mul_one, ← hsplit]
  simp only [Algebra.smul_def (R := R), map_neg]; ring

end BinomialPow

/-! ## Fractional-power formal reversion -/

section BinomialReversion

variable {R S A B : Type*} [CommRing R] [BinomialRing R] [CommRing A] [Algebra R A]

/-- Given `f : A⟦X⟧` with `constantCoeff f = 1`, unit exponent `a : Rˣ`, and arbitrary exponent
`b : R`, `f.binomialReversion a b` is the unique formal power series `S : A⟦X⟧` with
`constantCoeff S = 1` solving `S.binomialPow (a : R) * f.subst (X * S.binomialPow (-b)) = 1`.

It is constructed from the normalized series `f₁ = 1 + X * shift f` and the compositional inverse
`G` of `X * f₁.binomialPow (-b * a⁻¹)` as `(f₁.subst G).binomialPow (-(↑a⁻¹ : R))`. -/
noncomputable def binomialReversion (f : A⟦X⟧) (a : Rˣ) (b : R) : A⟦X⟧ :=
  let f₁ : A⟦X⟧ := 1 + X * mk fun n => coeff (n + 1) f
  let P : A⟦X⟧ := X * f₁.binomialPow (-b * (↑a⁻¹ : R))
  let G : A⟦X⟧ := P.substInvOfIsUnit (by simp [P, f₁])
  binomialPow (f₁.subst G) (-(↑a⁻¹ : R))

/-- Explicit formula for `f.binomialReversion a b`. -/
theorem binomialReversion_def (f : A⟦X⟧) (a : Rˣ) (b : R) :
    f.binomialReversion a b =
      let f₁ : A⟦X⟧ := 1 + X * mk fun n => coeff (n + 1) f
      let P : A⟦X⟧ := X * f₁.binomialPow (-b * (↑a⁻¹ : R))
      let G : A⟦X⟧ := P.substInvOfIsUnit (by simp [P, f₁])
      binomialPow (f₁.subst G) (-(↑a⁻¹ : R)) := (rfl)

private theorem normalize_eq_self {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    (1 : A⟦X⟧) + X * mk (fun n => coeff (n + 1) f) = f := by
  conv_rhs => rw [f.eq_X_mul_shift_add_const, hf, map_one, add_comm]

private theorem binomialReversion_normalize (f : A⟦X⟧) (a : Rˣ) (b : R) :
    (1 + X * mk fun n => coeff (n + 1) f).binomialReversion a b = f.binomialReversion a b := by
  rw [binomialReversion_def, binomialReversion_def]; dsimp only
  have h : (1 : A⟦X⟧) + X * mk (fun n => coeff (n + 1) (1 + X * mk fun m => coeff (m + 1) f)) =
      1 + X * mk (fun n => coeff (n + 1) f) :=
    normalize_eq_self (by simp)
  rw [substInvOfIsUnit_congr (by rw [h]) _ (by simp), h]

private theorem binomialReversion_eq_of_constantCoeff {f : A⟦X⟧} (hf : constantCoeff f = 1)
    (a : Rˣ) (b : R) :
    f.binomialReversion a b =
      binomialPow (f.subst ((X * f.binomialPow (-b * (↑a⁻¹ : R))).substInvOfIsUnit
        (by simp [hf]))) (-(↑a⁻¹ : R)) := by
  rw [binomialReversion_def]; dsimp only
  have hfeq := normalize_eq_self hf
  rw [substInvOfIsUnit_congr (by rw [hfeq]) _ (by simp [hf]), hfeq]

/-- Every formal binomial reversion has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_binomialReversion (f : A⟦X⟧) (a : Rˣ) (b : R) :
    constantCoeff (f.binomialReversion a b) = 1 := by
  rw [binomialReversion_def]; dsimp only
  refine constantCoeff_binomialPow ?_ _
  rw [constantCoeff_subst_of_constantCoeff_zero' (R := A) (S := A)
    (constantCoeff_substInvOfIsUnit _ _)]
  simp

private theorem X_mul_binomialPow_binomialReversion_eq_substInv {f : A⟦X⟧}
    (hf : constantCoeff f = 1) (a : Rˣ) (b : R) :
    X * (f.binomialReversion a b).binomialPow (-b) =
      (X * f.binomialPow (-b * (↑a⁻¹ : R))).substInvOfIsUnit (by simp [hf]) := by
  rw [binomialReversion_eq_of_constantCoeff hf]
  set P : A⟦X⟧ := X * f.binomialPow (-b * (↑a⁻¹ : R)) with hP
  have hP0 : constantCoeff P = 0 := by simp [P]
  have hP1 : IsUnit (P.coeff 1) := by simp [P, hf]
  set G : A⟦X⟧ := P.substInvOfIsUnit hP1
  have hG0 : constantCoeff G = 0 := constantCoeff_substInvOfIsUnit P hP1
  have hG : HasSubst G := .of_constantCoeff_zero' hG0
  have hfG0 : constantCoeff (f.subst G : A⟦X⟧) = 1 := by
    rw [constantCoeff_subst_of_constantCoeff_zero' hG0, hf, map_one]
  have hGmul : G * binomialPow (f.subst G) (-b * (↑a⁻¹ : R)) = X := by
    have hPG := P.subst_substInvOfIsUnit_right hP0 hP1
    conv_lhs at hPG => arg 2; rw [hP]
    rwa [subst_mul hG, subst_X hG, subst_binomialPow hf hG] at hPG
  rw [binomialPow_binomialPow hfG0, neg_mul_neg, mul_comm (↑a⁻¹ : R), ← hGmul, mul_assoc,
    ← binomialPow_add hfG0, neg_mul, neg_add_cancel, binomialPow_zero, mul_one]

/-- With `S = f.binomialReversion a b` (`constantCoeff f = 1`), `X * S ^ (-b)` is the
compositional inverse of `X * f ^ (-b * a⁻¹)`. -/
theorem subst_X_mul_binomialPow_binomialReversion {f : A⟦X⟧} (hf : constantCoeff f = 1)
    (a : Rˣ) (b : R) :
    (X * f.binomialPow (-b * (↑a⁻¹ : R))).subst
      (X * (f.binomialReversion a b).binomialPow (-b)) = X := by
  rw [X_mul_binomialPow_binomialReversion_eq_substInv hf]
  exact subst_substInvOfIsUnit_right _ (by simp) _

/-- **Characteristic equation of `binomialReversion`**: for `constantCoeff f = 1`, `a : Rˣ`, and
`b : R`, `S = f.binomialReversion a b` satisfies
`S.binomialPow (a : R) * f.subst (X * S.binomialPow (-b)) = 1`. -/
theorem binomialPow_binomialReversion_mul_subst {f : A⟦X⟧} (hf : constantCoeff f = 1)
    (a : Rˣ) (b : R) :
    (f.binomialReversion a b).binomialPow (a : R) *
      f.subst (X * (f.binomialReversion a b).binomialPow (-b)) = 1 := by
  rw [X_mul_binomialPow_binomialReversion_eq_substInv hf, binomialReversion_eq_of_constantCoeff hf]
  set P : A⟦X⟧ := X * f.binomialPow (-b * (↑a⁻¹ : R))
  have hP1 : IsUnit (P.coeff 1) := by simp [P, hf]
  have hfG0 : constantCoeff (f.subst (P.substInvOfIsUnit hP1) : A⟦X⟧) = 1 := by
    rw [constantCoeff_subst_of_constantCoeff_zero' (constantCoeff_substInvOfIsUnit P hP1),
      hf, map_one]
  rw [binomialPow_binomialPow hfG0, neg_mul, Units.inv_mul, binomialPow_neg_one_mul hfG0]

/-- **Congruence modulo `X ^ m` for `binomialReversion`**: if `constantCoeff g = 1` and
`X ^ m ∣ g ^ a * f(X * g ^ (-b)) - 1`, then `X ^ m ∣ g - f.binomialReversion a b`. -/
theorem X_pow_dvd_sub_binomialReversion {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (a : Rˣ) (b : R) {m : ℕ}
    (hdvd : X ^ m ∣ g.binomialPow (a : R) * f.subst (X * g.binomialPow (-b)) - 1) :
    X ^ m ∣ g - f.binomialReversion a b := by
  set S := f.binomialReversion a b
  have hS0 : constantCoeff S = 1 := constantCoeff_binomialReversion f a b
  set P : A⟦X⟧ := X * f.binomialPow (-b * (↑a⁻¹ : R))
  have hP0 : constantCoeff P = 0 := by simp [P]
  have hP1 : IsUnit (P.coeff 1) := by simp [P, hf]
  set H : A⟦X⟧ := X * g.binomialPow (-b)
  have hH0 : constantCoeff H = 0 := by simp [H]
  have hH : HasSubst H := .of_constantCoeff_zero' hH0
  have hfH0 : constantCoeff (f.subst H : A⟦X⟧) = 1 := by
    rw [constantCoeff_subst_of_constantCoeff_zero' hH0, hf, map_one]
  have hpow := X_pow_dvd_binomialPow_sub_binomialPow
    (by rw [map_mul, constantCoeff_binomialPow hg, hfH0, one_mul]) hdvd (-b * (↑a⁻¹ : R))
  have hexp : (a : R) * (-b * (↑a⁻¹ : R)) = -b := by
    rw [mul_comm (a : R), mul_assoc, Units.inv_mul, mul_one]
  rw [binomialPow_one_left, binomialPow_mul (constantCoeff_binomialPow hg _) hfH0,
    binomialPow_binomialPow hg, hexp, ← subst_binomialPow hf hH] at hpow
  have hXP : X ^ (m + 1) ∣ P.subst H - X := by
    have hPX : P.subst H - X =
        X * (g.binomialPow (-b) * (f.binomialPow (-b * (↑a⁻¹ : R))).subst H - 1) := by
      rw [subst_mul hH, subst_X hH, mul_sub, mul_one, mul_assoc]
    rw [hPX, pow_succ']
    exact mul_dvd_mul_left X hpow
  set G : A⟦X⟧ := X * S.binomialPow (-b)
  have hGeq : P.substInvOfIsUnit hP1 = G :=
    (X_mul_binomialPow_binomialReversion_eq_substInv hf a b).symm
  have hPH0 : constantCoeff (P.subst H : A⟦X⟧) = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero' hH0, hP0, map_zero]
  have hHG : X ^ m ∣ H - G := by
    have hinv := X_pow_dvd_subst_sub_subst hPH0 hXP (P.substInvOfIsUnit hP1)
    rw [← subst_comp_subst_apply (.of_constantCoeff_zero' hP0) hH,
      P.subst_substInvOfIsUnit_left hP0 hP1, X_subst, subst_X hH, hGeq] at hinv
    exact dvd_trans (pow_dvd_pow X (Nat.le_succ m)) hinv
  have hfHG : X ^ m ∣ f.subst H - f.subst G := X_pow_dvd_subst_sub_subst hH0 hHG f
  have hSchar : S.binomialPow (a : R) * f.subst G = 1 :=
    binomialPow_binomialReversion_mul_subst hf a b
  have hmul : X ^ m ∣ f.subst G * (g.binomialPow (a : R) - S.binomialPow (a : R)) := by
    have hident : f.subst G * (g.binomialPow (a : R) - S.binomialPow (a : R)) =
        (g.binomialPow (a : R) * f.subst H - 1) -
          g.binomialPow (a : R) * (f.subst H - f.subst G) := by
      linear_combination -hSchar
    rw [hident]
    exact dvd_sub hdvd (dvd_mul_of_dvd_right hfHG _)
  have hfG_unit : IsUnit (f.subst G) := by
    rw [isUnit_iff_constantCoeff, constantCoeff_subst_of_constantCoeff_zero' (by simp [G]),
      hf, map_one]
    exact isUnit_one
  exact (X_pow_dvd_binomialPow_sub_binomialPow_iff hg hS0 a).mp
    (hfG_unit.dvd_mul_left.mp hmul)

/-- **Uniqueness of `binomialReversion`**: `g = f.binomialReversion a b` if and only if
`constantCoeff g = 1` and `g.binomialPow (a : R) * f.subst (X * g.binomialPow (-b)) = 1`. -/
theorem eq_binomialReversion_iff {f g : A⟦X⟧} (hf : constantCoeff f = 1) (a : Rˣ) (b : R) :
    g = f.binomialReversion a b ↔
      constantCoeff g = 1 ∧ g.binomialPow (a : R) * f.subst (X * g.binomialPow (-b)) = 1 := by
  refine ⟨fun h =>
    h ▸ ⟨constantCoeff_binomialReversion f a b, binomialPow_binomialReversion_mul_subst hf a b⟩,
    fun ⟨hg0, hg⟩ => sub_eq_zero.mp (ext fun n => ?_)⟩
  have hdvd := X_pow_dvd_sub_binomialReversion hf hg0 a b (m := n + 1)
    (by rw [hg, sub_self]; exact dvd_zero _)
  simpa only [map_zero] using X_pow_dvd_iff.mp hdvd n (Nat.lt_succ_self n)

/-- The formal binomial reversion of `1` is `1`. -/
@[simp]
theorem binomialReversion_one (a : Rˣ) (b : R) : (1 : A⟦X⟧).binomialReversion a b = 1 :=
  ((eq_binomialReversion_iff (f := (1 : A⟦X⟧)) (g := 1) constantCoeff_one a b).mpr
    ⟨constantCoeff_one, by simp⟩).symm

/-- At `b = 0`, `f.binomialReversion a 0` is the `-(a⁻¹)`-th formal binomial power of `f`. -/
@[simp]
theorem binomialReversion_zero {f : A⟦X⟧} (hf : constantCoeff f = 1) (a : Rˣ) :
    f.binomialReversion a 0 = f.binomialPow (-(↑a⁻¹ : R)) := by
  refine ((eq_binomialReversion_iff hf a 0).mpr ⟨constantCoeff_binomialPow hf _, ?_⟩).symm
  rw [neg_zero, binomialPow_zero, mul_one, X_subst, binomialPow_binomialPow hf, neg_mul,
    Units.inv_mul, binomialPow_neg_one_mul hf]

/-- The linear coefficient of `f.binomialReversion a b` is `-(a⁻¹) • coeff 1 f`. -/
theorem coeff_one_binomialReversion (f : A⟦X⟧) (a : Rˣ) (b : R) :
    coeff 1 (f.binomialReversion a b) = -(↑a⁻¹ : R) • coeff 1 f := by
  rw [binomialReversion_def]; dsimp only
  set f₁ : A⟦X⟧ := 1 + X * mk fun n => coeff (n + 1) f
  have hf₁0 : constantCoeff f₁ = 1 := by simp [f₁]
  set P : A⟦X⟧ := X * f₁.binomialPow (-b * (↑a⁻¹ : R))
  have hP1 : IsUnit (P.coeff 1) := by simp [P, hf₁0]
  have hPcoeff1 : P.coeff 1 = 1 := by simp [P, hf₁0]
  set G : A⟦X⟧ := P.substInvOfIsUnit hP1
  have hG0 : constantCoeff G = 0 := constantCoeff_substInvOfIsUnit P hP1
  have hG1 : coeff 1 G = 1 := by
    rw [coeff_one_substInvOfIsUnit]
    have hspec : (hP1.unit : A) = 1 := (IsUnit.unit_spec hP1).trans hPcoeff1
    have hinv := hP1.unit.mul_inv
    rwa [hspec, one_mul] at hinv
  have hf₁G0 : constantCoeff (f₁.subst G : A⟦X⟧) = 1 := by
    rw [constantCoeff_subst_of_constantCoeff_zero' hG0, hf₁0, map_one]
  rw [coeff_one_binomialPow hf₁G0, coeff_one_subst hG0, hG1, mul_one,
    Algebra.algebraMap_self_apply]
  simp [f₁]

/-- Rescaling the variable commutes with `binomialReversion`. -/
theorem rescale_binomialReversion (f : A⟦X⟧) (c : A) (a : Rˣ) (b : R) :
    rescale c (f.binomialReversion a b) = (rescale c f).binomialReversion a b := by
  set f₁ : A⟦X⟧ := 1 + X * mk fun n => coeff (n + 1) f
  have hf₁0 : constantCoeff f₁ = 1 := by simp [f₁]
  have hres_f₁ : rescale c f₁ = 1 + X * mk fun n => coeff (n + 1) (rescale c f) := by
    ext (_ | n)
    · simp [f₁, coeff_rescale]
    · simp only [coeff_rescale, map_add, coeff_one, Nat.succ_ne_zero, ↓reduceIte, mul_zero,
        zero_add, coeff_succ_X_mul, coeff_mk, f₁]
  rw [← binomialReversion_normalize f, ← binomialReversion_normalize (rescale c f), ← hres_f₁]
  have hf₁c0 : constantCoeff (rescale c f₁) = 1 := by rw [constantCoeff_rescale, hf₁0]
  rw [eq_binomialReversion_iff hf₁c0 a b]
  refine ⟨by rw [constantCoeff_rescale, constantCoeff_binomialReversion], ?_⟩
  have hchar := congrArg (rescale c) (binomialPow_binomialReversion_mul_subst hf₁0 a b)
  rw [map_mul, map_one, rescale_binomialPow (constantCoeff_binomialReversion f₁ a b)] at hchar
  refine Eq.trans ?_ hchar
  congr 1
  have hG : HasSubst (X * (f₁.binomialReversion a b).binomialPow (-b)) :=
    .of_constantCoeff_zero' (by simp)
  have hG' : HasSubst (X * (rescale c (f₁.binomialReversion a b)).binomialPow (-b)) :=
    .of_constantCoeff_zero' (by simp)
  have hrc : HasSubst (c • X : A⟦X⟧) := .of_constantCoeff_zero' (by simp)
  conv_lhs => arg 2; rw [rescale_eq_subst]
  conv_rhs => rw [rescale_eq_subst]
  rw [subst_comp_subst_apply hrc hG', subst_comp_subst_apply hG hrc]
  congr 1
  rw [subst_smul hG', subst_X hG', subst_mul hrc, subst_X hrc, ← rescale_eq_subst,
    rescale_binomialPow (constantCoeff_binomialReversion f₁ a b), smul_mul_assoc]

/-- Mapping coefficients along an `R`-algebra homomorphism commutes with `binomialReversion`. -/
@[simp]
theorem map_algHom_binomialReversion [CommRing B] [Algebra R B] (f : A⟦X⟧)
    (φ : A →ₐ[R] B) (a : Rˣ) (b : R) :
    (f.binomialReversion a b).map (φ : A →+* B) = (f.map (φ : A →+* B)).binomialReversion a b := by
  set f₁ : A⟦X⟧ := 1 + X * mk fun n => coeff (n + 1) f
  have hf₁0 : constantCoeff f₁ = 1 := by simp [f₁]
  have hmap_f₁ :
      f₁.map (φ : A →+* B) = 1 + X * mk fun n => coeff (n + 1) (f.map (φ : A →+* B)) := by
    ext (_ | n) <;> simp [f₁, coeff_succ_X_mul]
  rw [← binomialReversion_normalize f, ← binomialReversion_normalize (f.map (φ : A →+* B)),
    ← hmap_f₁]
  have hf₁φ : constantCoeff (f₁.map (φ : A →+* B)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff, hf₁0, map_one]
  rw [eq_binomialReversion_iff hf₁φ a b]
  refine ⟨by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
    constantCoeff_binomialReversion, map_one], ?_⟩
  have hchar := congrArg (map (φ : A →+* B)) (binomialPow_binomialReversion_mul_subst hf₁0 a b)
  rw [(map _).map_mul, (map _).map_one,
    map_algHom_binomialPow (constantCoeff_binomialReversion f₁ a b) φ] at hchar
  refine Eq.trans ?_ hchar
  congr 1
  have hG : HasSubst (X * (f₁.binomialReversion a b).binomialPow (-b)) :=
    .of_constantCoeff_zero' (by simp)
  refine ((map_subst hG (h := (φ : A →+* B)) f₁).trans ?_).symm
  congr 1
  exact ((map (φ : A →+* B)).map_mul _ _).trans
    (by simp [f₁, map_algHom_binomialPow (constantCoeff_binomialReversion f₁ a b) φ])

/-- Mapping coefficients along `algebraMap R A` commutes with `binomialReversion`. -/
@[simp]
theorem map_algebraMap_binomialReversion (f : R⟦X⟧) (a : Rˣ) (b : R) :
    (f.binomialReversion a b).map (algebraMap R A) =
      (f.map (algebraMap R A)).binomialReversion a b :=
  map_algHom_binomialReversion f (Algebra.ofId R A) a b

/-- Mapping coefficients along a ring homomorphism between binomial rings maps both base and
exponents of `binomialReversion`. -/
theorem map_binomialReversion [CommRing S] [BinomialRing S] (f : R⟦X⟧) (φ : R →+* S)
    (a : Rˣ) (b : R) :
    (f.binomialReversion a b).map φ =
      (f.map φ).binomialReversion (Units.map φ.toMonoidHom a) (φ b) := by
  set f₁ : R⟦X⟧ := 1 + X * mk fun n => coeff (n + 1) f
  have hf₁0 : constantCoeff f₁ = 1 := by simp [f₁]
  have hmap_f₁ : f₁.map φ = 1 + X * mk fun n => coeff (n + 1) (f.map φ) := by
    ext (_ | n) <;> simp [f₁, coeff_succ_X_mul]
  rw [← binomialReversion_normalize f, ← binomialReversion_normalize (f.map φ), ← hmap_f₁]
  have hf₁φ : constantCoeff (f₁.map φ) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff, hf₁0, map_one]
  rw [eq_binomialReversion_iff hf₁φ (Units.map φ.toMonoidHom a) (φ b)]
  refine ⟨by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
    constantCoeff_binomialReversion, map_one], ?_⟩
  have hchar := congrArg (map φ) (binomialPow_binomialReversion_mul_subst hf₁0 a b)
  rw [(map φ).map_mul, (map φ).map_one,
    map_binomialPow (constantCoeff_binomialReversion f₁ a b) φ] at hchar
  refine Eq.trans ?_ hchar
  congr 1
  have hG : HasSubst (X * (f₁.binomialReversion a b).binomialPow (-b)) :=
    .of_constantCoeff_zero' (by simp)
  refine ((map_subst hG (h := φ) f₁).trans ?_).symm
  congr 1
  exact ((map φ).map_mul _ _).trans
    (by simp [f₁, map_binomialPow (constantCoeff_binomialReversion f₁ a b) φ])

/-- Along a scalar tower `R → S → A` of binomial rings, `binomialReversion` is compatible with
mapping the exponents along `algebraMap R S`. -/
theorem binomialReversion_unitsMap_algebraMap [CommRing S] [BinomialRing S] [Algebra R S]
    [Algebra S A] [IsScalarTower R S A] (f : A⟦X⟧) (a : Rˣ) (b : R) :
    f.binomialReversion (Units.map (algebraMap R S).toMonoidHom a) (algebraMap R S b) =
      f.binomialReversion a b := by
  set f₁ : A⟦X⟧ := 1 + X * mk fun n => coeff (n + 1) f
  have hf₁0 : constantCoeff f₁ = 1 := by simp [f₁]
  rw [← binomialReversion_normalize f (a := Units.map (algebraMap R S).toMonoidHom a),
    ← binomialReversion_normalize f (a := a)]
  refine ((eq_binomialReversion_iff hf₁0 (Units.map (algebraMap R S).toMonoidHom a)
    (algebraMap R S b)).mpr ⟨constantCoeff_binomialReversion f₁ a b, ?_⟩).symm
  simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, ← map_neg,
    binomialPow_algebraMap] using
    binomialPow_binomialReversion_mul_subst hf₁0 a b

/-- Uniqueness of the image of `binomialReversion` under an `R`-algebra homomorphism. -/
theorem eq_map_algHom_binomialReversion_iff [CommRing B] [Algebra R B] {f : A⟦X⟧}
    (hf : constantCoeff f = 1) (φ : A →ₐ[R] B) (a : Rˣ) (b : R) {g : B⟦X⟧} :
    g = (f.binomialReversion a b).map (φ : A →+* B) ↔
      constantCoeff g = 1 ∧
        g.binomialPow (a : R) * (f.map (φ : A →+* B)).subst (X * g.binomialPow (-b)) = 1 := by
  have hfφ : constantCoeff (f.map (φ : A →+* B)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff, hf, map_one]
  rw [map_algHom_binomialReversion]
  exact eq_binomialReversion_iff hfφ a b

/-- Uniqueness of the image of `binomialReversion` under `algebraMap R A`. -/
theorem eq_map_algebraMap_binomialReversion_iff {f : R⟦X⟧} (hf : constantCoeff f = 1)
    (a : Rˣ) (b : R) {g : A⟦X⟧} :
    g = (f.binomialReversion a b).map (algebraMap R A) ↔
      constantCoeff g = 1 ∧
        g.binomialPow (a : R) * (f.map (algebraMap R A)).subst (X * g.binomialPow (-b)) = 1 :=
  eq_map_algHom_binomialReversion_iff hf (Algebra.ofId R A) a b

/-- **Differential identity for `binomialReversion`**: if `f : A⟦X⟧` has constant coefficient `1`
and `M * (f - (b * (↑a⁻¹ : R)) • (X * d⁄dX f)) = 1`, then `S = f.binomialReversion a b` satisfies
`M.subst (X * S ^ (-b)) = S ^ (a - 1) * (S - b • (X * d⁄dX S))`. -/
theorem subst_X_mul_binomialPow_binomialReversion_of_mul_derivative {M f : A⟦X⟧}
    (hf : constantCoeff f = 1) (a : Rˣ) (b : R)
    (hode : M * (f - (b * (↑a⁻¹ : R)) • (X * d⁄dX f)) = 1) :
    M.subst (X * (f.binomialReversion a b).binomialPow (-b)) =
      (f.binomialReversion a b).binomialPow ((a : R) - 1) *
        (f.binomialReversion a b - b • (X * d⁄dX (f.binomialReversion a b))) := by
  set r : R := b * (↑a⁻¹ : R) with hr
  set S := f.binomialReversion a b
  have hS0 : constantCoeff S = 1 := constantCoeff_binomialReversion f a b
  set P : A⟦X⟧ := X * f.binomialPow (-r) with hP
  set G : A⟦X⟧ := X * S.binomialPow (-b) with hG_def
  have hG0 : constantCoeff G = 0 := by simp [G]
  have hG : HasSubst G := .of_constantCoeff_zero' hG0
  have hMP : M * d⁄dX P = f.binomialPow (-r - 1) := by
    rw [hP, derivative_X_mul_binomialPow_neg hf r, mul_left_comm, hode, mul_one]
  have hchain : (d⁄dX P).subst G * d⁄dX G = 1 := by
    have hPG := congrArg (d⁄dX) (subst_X_mul_binomialPow_binomialReversion hf a b)
    rwa [neg_mul, ← hr, ← hP, derivative_subst hG, derivative_X] at hPG
  have hMG : M.subst G = binomialPow (f.subst G) (-r - 1) * d⁄dX G := by
    rw [← subst_binomialPow hf hG, ← hMP, subst_mul hG, mul_assoc, hchain, mul_one]
  have hfG : f.subst G = S.binomialPow (-(a : R)) := by
    rw [← one_mul (f.subst G), ← binomialPow_neg_mul hS0 (a : R), mul_assoc,
      binomialPow_binomialReversion_mul_subst hf a b, mul_one]
  have hexp : (-(a : R)) * (-r - 1) + (-b - 1) = (a : R) - 1 := by
    have har : (a : R) * r = b := by
      rw [mul_comm (a : R), hr, mul_assoc, Units.inv_mul, mul_one]
    linear_combination har
  rw [hMG, hfG, hG_def, derivative_X_mul_binomialPow_neg hS0 b, binomialPow_binomialPow hS0,
    ← mul_assoc, ← binomialPow_add hS0, hexp]

end BinomialReversion

/-! ## Compatibility with formal logarithm and exponential over `ℚ`-algebras -/

section RatAlgebra

variable {R A : Type*} [CommRing R] [BinomialRing R] [CommRing A] [Algebra ℚ A] [Algebra R A]

/-- Over a `ℚ`-algebra, the formal logarithm of `binomialSeries A r` is `r • log A`. -/
@[simp]
theorem logOf_binomialSeries (r : R) : logOf (binomialSeries A r) = r • log A := by
  have : HasUniqueDiv A := .of_module_rat A
  refine derivative.ext ?_ (by simp [constantCoeff_logOf])
  have hunit : IsUnit (1 + X : A⟦X⟧) := isUnit_iff_constantCoeff.mpr (by simp)
  refine hunit.mul_left_cancel ((isUnit_binomialSeries r).mul_right_cancel ?_)
  calc (1 + X) * d⁄dX (logOf (binomialSeries A r)) * binomialSeries A r
    _ = (1 + X) * (logDeriv (binomialSeries A r) * binomialSeries A r) := by
      rw [logDeriv_def, mul_assoc]
    _ = (1 + X) * d⁄dX (binomialSeries A r) := by
      rw [logDeriv_mul _ (binomialSeries_constantCoeff r)]
    _ = r • binomialSeries A r := one_add_X_mul_derivative_binomialSeries r
    _ = (1 + X) * d⁄dX (r • log A) * binomialSeries A r := by
      have hlog : (1 + X) * d⁄dX (log A) = (1 : A⟦X⟧) := by
        simpa only [mul_comm] using derivative_log_mul_one_add_X (A := A)
      rw [Derivation.map_smul_of_tower, mul_smul_comm, hlog, smul_mul_assoc, one_mul]

/-- Over a `ℚ`-algebra, the formal logarithm of `f.binomialPow r` is `r • logOf f`. -/
@[simp]
theorem logOf_binomialPow {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    logOf (f.binomialPow r) = r • logOf f := by
  have hsub := HasSubst.sub_one hf
  have hinner : f.binomialPow r - 1 = (binomialSeries A r - 1).subst (f - 1) := by
    rw [binomialPow_def, subst_sub hsub, subst_one]
  rw [logOf_eq, hinner,
    ← subst_comp_subst_apply (TauCeti.hasSubst_binomialSeries_sub_one r) hsub,
    ← logOf_eq, logOf_binomialSeries, subst_smul hsub, ← logOf_eq]

/-- Over a `ℚ`-algebra, `exp (r • log A)` equals `binomialSeries A r`. -/
@[simp]
theorem subst_exp_smul_log (r : R) : (exp A).subst (r • log A) = binomialSeries A r := by
  rw [← logOf_binomialSeries, subst_exp_logOf (binomialSeries_constantCoeff r)]

/-- Over a `ℚ`-algebra, `exp (r • logOf f)` equals `f.binomialPow r`. -/
@[simp]
theorem subst_exp_smul_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) (r : R) :
    (exp A).subst (r • logOf f) = f.binomialPow r := by
  rw [← logOf_binomialPow hf r, subst_exp_logOf (constantCoeff_binomialPow hf r)]

end RatAlgebra

end PowerSeries
