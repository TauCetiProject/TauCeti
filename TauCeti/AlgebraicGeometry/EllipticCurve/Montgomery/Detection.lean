/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.Data.ZMod.GCD
public import TauCeti.NumberTheory.LcmUpto
public import Mathlib.Algebra.Field.ZMod

/-!
# Stage-1 detection from Montgomery coordinate pairs

Let `p ∣ n` be prime. If a raw pair over `ZMod n` reduces to a representative of the
coordinate pair of `[m]P` over `ZMod p`, and `m` annihilates `P`, then `p` divides the gcd
of its denominator with `n`. Annihilation follows either from divisibility by the point
order or, by Lagrange's theorem, from divisibility by the native group's cardinality.
For an elliptic model the latter is the projective point count.

Specializing the multiplier to `B₁.lcmUpto` gives stage-1 detection under a powersmoothness
bound `B₁`: `p` divides `Nat.gcd R.z.val n` whenever every prime-power divisor of
`addOrderOf P` (or of `Nat.card (model A B).toAffine.Point`, or of `(model A B).pointCount`
on an elliptic model) is at most `B₁`, and in particular whenever the order or count itself
is at most `B₁` (finiteness over `ZMod p` comes from `WeierstrassCurve.Affine.finite_point`
without assuming ellipticity).

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

/-! ### Stage-1 bound `Nat.lcmUpto` -/

/-- **Stage-1 detection at `B₁.lcmUpto` from a powersmooth point order.** If every prime-power
divisor of `addOrderOf P` is at most `B₁`, any raw pair over `ZMod n` whose reduction modulo
`p` has vanishing cross difference with `[B₁.lcmUpto]P` has denominator gcd divisible by `p`. -/
theorem prime_dvd_gcd_of_isPrimePow_dvd_addOrderOf_le {B₁ : ℕ} (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hP : ∀ q, IsPrimePow q → q ∣ addOrderOf P → q ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_addOrderOf_dvd hpn P R (Nat.dvd_lcmUpto_iff.mpr hP) hR

/-- If `addOrderOf P ≤ B₁`, the stage-1 multiplier `B₁.lcmUpto` annihilates `P` over the
finite field `ZMod p`, so any raw pair representing `[B₁.lcmUpto]P` modulo `p` has denominator
gcd divisible by `p`. -/
theorem prime_dvd_gcd_of_addOrderOf_le {B₁ : ℕ} (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n)) (hP : addOrderOf P ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_addOrderOf_dvd hpn P R
    (Nat.dvd_lcmUpto (addOrderOf_pos_iff.mpr (isOfFinAddOrder_of_finite P)) hP) hR

/-- **Stage-1 detection at `B₁.lcmUpto` from a powersmooth native group order.** If every
prime-power divisor of `Nat.card (model A B).toAffine.Point` is at most `B₁`, any raw pair
representing `[B₁.lcmUpto]P` modulo `p` has denominator gcd divisible by `p`. -/
theorem prime_dvd_gcd_of_isPrimePow_dvd_card_le {B₁ : ℕ} (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hcard : ∀ q, IsPrimePow q → q ∣ Nat.card (model A B).toAffine.Point → q ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_card_dvd hpn P R (Nat.dvd_lcmUpto_iff.mpr hcard) hR

/-- If `Nat.card (model A B).toAffine.Point ≤ B₁`, any raw pair representing `[B₁.lcmUpto]P`
modulo `p` has denominator gcd divisible by `p`. -/
theorem prime_dvd_gcd_of_card_le {B₁ : ℕ} (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hcard : Nat.card (model A B).toAffine.Point ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_card_dvd hpn P R (Nat.dvd_lcmUpto Nat.card_pos hcard) hR

/-- On an elliptic monic model whose projective point count is `B₁`-powersmooth, any raw pair
representing `[B₁.lcmUpto]P` modulo `p` has denominator gcd divisible by `p`. -/
theorem prime_dvd_gcd_of_isPrimePow_dvd_pointCount_le [(model A B).IsElliptic] {B₁ : ℕ}
    (hpn : p ∣ n) (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hcount : ∀ q, IsPrimePow q → q ∣ (model A B).pointCount → q ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_pointCount_dvd hpn P R (Nat.dvd_lcmUpto_iff.mpr hcount) hR

/-- On an elliptic monic model with `(model A B).pointCount ≤ B₁`, any raw pair representing
`[B₁.lcmUpto]P` modulo `p` has denominator gcd divisible by `p`. -/
theorem prime_dvd_gcd_of_pointCount_le [(model A B).IsElliptic] {B₁ : ℕ}
    (hpn : p ∣ n) (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hcount : (model A B).pointCount ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n := by
  rw [WeierstrassCurve.pointCount_eq_card_point] at hcount
  exact prime_dvd_gcd_of_card_le hpn P R hcount hR

/-- **Proper-factor certification at `B₁.lcmUpto`** from a `B₁`-powersmooth point order modulo
`p` and a nonzero denominator modulo another divisor `q`. -/
theorem one_lt_gcd_and_gcd_lt_of_isPrimePow_dvd_addOrderOf_le [NeZero n] {B₁ : ℕ}
    (hpn : p ∣ n) (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hP : ∀ q, IsPrimePow q → q ∣ addOrderOf P → q ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0)
    {q : ℕ} (hqn : q ∣ n) (hq : ZMod.castHom hqn (ZMod q) R.z ≠ 0) :
    1 < Nat.gcd R.z.val n ∧ Nat.gcd R.z.val n < n :=
  one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd hpn P R (Nat.dvd_lcmUpto_iff.mpr hP) hR hqn hq

end TauCeti.Montgomery
