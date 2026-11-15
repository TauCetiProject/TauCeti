/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.Data.ZMod.GCD
public import Mathlib.Algebra.Field.ZMod

/-!
# Stage-1 detection from Montgomery coordinate pairs

Let `p ∣ n` be prime. If a raw pair over `ZMod n` reduces to a representative of the
coordinate pair of `[m]P` over `ZMod p`, and `m` annihilates `P`, then `p` divides the gcd
of its denominator with `n`. Annihilation follows either from divisibility by the point
order or, by Lagrange's theorem, from divisibility by the native group's cardinality.
For an elliptic model the latter is the projective point count.

Only a vanishing cross difference with the coordinate pair is needed. The reduced raw
pair may even be zero: annihilation still forces its denominator to vanish. Consequently
these implications do not require `B ≠ 0`, ellipticity, or an odd characteristic. They
apply to any pair with the stated coordinate relation, not just outputs of a particular
formula.

Divisibility by `p` alone need not give a proper factor: every prime divisor might divide
the gcd. For positive `n`, a nonzero reduction of the denominator modulo another divisor
certifies that the gcd is strictly between `1` and `n`.

## References

* H. W. Lenstra Jr., *Factoring integers with elliptic curves*, Ann. of Math. 126 (1987),
  649–673, §2.
* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1.1.
-/

public section

namespace TauCeti.Montgomery

variable {n p m : ℕ} [Fact p.Prime] {A B : ZMod p}

/-- If the point order divides the multiplier, any raw pair whose reduction has vanishing
cross difference with the multiple's coordinate pair has denominator gcd divisible by `p`.
Nonzeroness of the reduced pair is not required. -/
theorem prime_dvd_gcd_of_addOrderOf_dvd (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n)) (hm : addOrderOf P ∣ m)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0) :
    p ∣ Nat.gcd R.z.val n := by
  have hmP := addOrderOf_dvd_iff_nsmul_eq_zero.mp hm
  rw [hmP, coordinates_zero, Pair.cross_def] at hR
  have hz : ZMod.castHom hpn (ZMod p) R.z = 0 := by
    simpa using hR
  exact (R.z.dvd_gcd_val_iff_castHom_eq_zero hpn).mpr hz

/-- **Stage-1 detection by the native group cardinality.** A multiple of the group order
annihilates every point, so a raw pair representing that multiple modulo `p` has denominator
gcd divisible by `p`. No ellipticity assumption is needed on the monic model. -/
theorem prime_dvd_gcd_of_card_dvd (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hm : Nat.card (model A B).toAffine.Point ∣ m)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_addOrderOf_dvd hpn P R ((addOrderOf_dvd_natCard P).trans hm) hR

/-- On an elliptic monic model the projective point count can replace the cardinality
of the native group in stage-1 detection. -/
theorem prime_dvd_gcd_of_pointCount_dvd [(model A B).IsElliptic] (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hm : (model A B).pointCount ∣ m)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0) :
    p ∣ Nat.gcd R.z.val n := by
  rw [WeierstrassCurve.pointCount_eq_card_point] at hm
  exact prime_dvd_gcd_of_card_dvd hpn P R hm hR

/-- Stage-1 annihilation modulo `p`, together with a denominator nonzero modulo another
divisor `q`, certifies a proper factor of the positive modulus. -/
theorem one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd [NeZero n] (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n)) (hm : addOrderOf P ∣ m)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0)
    {q : ℕ} (hqn : q ∣ n) (hq : ZMod.castHom hqn (ZMod q) R.z ≠ 0) :
    1 < Nat.gcd R.z.val n ∧ Nat.gcd R.z.val n < n := by
  apply R.z.one_lt_gcd_val_and_gcd_val_lt_of_castHom (Fact.out : p.Prime).one_lt hpn hqn
  · exact (R.z.dvd_gcd_val_iff_castHom_eq_zero hpn).mp
      (prime_dvd_gcd_of_addOrderOf_dvd hpn P R hm hR)
  · exact hq

end TauCeti.Montgomery
