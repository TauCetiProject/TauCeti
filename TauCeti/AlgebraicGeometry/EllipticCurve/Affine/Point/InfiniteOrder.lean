/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction

/-!
# Points of infinite order, certified by reduction at two primes

Let `A` be a Dedekind domain with fraction field `F`, and let `W` be an elliptic curve over `F`
with good reduction at a height-one prime `u` of `A`, so that reduction of points is a group
homomorphism `W(F) →+ W_k(k)` to the points of the reduced curve. Reduction is injective on the
torsion of order prime to `u` (Silverman AEC VII.3.1). So if a natural number `ℓ ∉ u` divides the
order of a torsion point `P`, it also divides the order of the reduction of `P`
(`WeierstrassCurve.Affine.Point.dvd_addOrderOf_reductionHom`).

This gives a finite certificate that a rational point has infinite order. Suppose `P ≠ 0`, that
`p ∈ u` and `q ∈ u'` for two primes `u` and `u'` of good reduction, and that the reductions of `P`
are killed by `m` and `n` respectively. A prime `ℓ` dividing the order of a torsion point `P`
divides `p * m`: it divides `p` when `ℓ ∈ u`, and otherwise it divides the order of the reduction,
which divides `m`. Likewise `ℓ ∣ q * n`. So when `p * m` and `q * n` are coprime, `P` is not
torsion (`WeierstrassCurve.Affine.Point.not_isOfFinAddOrder_of_coprime`). For a curve over `ℚ`
this is a computation in two finite point groups `W(𝔽_p)` and `W(𝔽_q)`, and a point of infinite
order shows that the Mordell–Weil rank is positive.

Only the injectivity on torsion prime to the residue characteristic is used, which is why the
residue characteristics `p` and `q` enter the coprimality condition: torsion of `p`-power order
may reduce to zero modulo `u`.

## Main results

All results are in the namespace `WeierstrassCurve.Affine.Point`.

* `dvd_addOrderOf_reductionHom`: at good reduction, a natural number `ℓ ∉ u` dividing the order of
  a torsion point divides the order of its reduction.
* `prime_dvd_mul_of_dvd_addOrderOf`: if `p ∈ u` and the reduction of a torsion point `P` is killed
  by `m`, every prime dividing the order of `P` divides `p * m`.
* `not_isOfFinAddOrder_of_coprime`: the two-prime certificate that a point has infinite order.

## Provenance

The two-prime certificate follows `WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red` in
Michael Stoll's `EllipticCurves` project (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0, commit `3bfe124`), `EllipticCurves/InfiniteOrder.lean`. That version assumes
injectivity of reduction on all torsion, available when `p ∉ u ^ (p - 1)`, and asks only that `m`
and `n` be coprime. The version here uses injectivity on torsion prime to `u` alone, so the residue
characteristics enter the coprimality condition, and it is derived from the prime-by-prime
statement `prime_dvd_mul_of_dvd_addOrderOf`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.3.1 and VIII.7.
-/

public section

namespace WeierstrassCurve.Affine.Point

open IsDedekindDomain IsLocalRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F] [DecidableEq F]
  (u : HeightOneSpectrum A) {W : Affine F}

section Prime

variable [IsIntegral (u.valuation F).valuationSubring W]
  [(integralModel (u.valuation F).valuationSubring W).IsElliptic]
  [DecidableEq (ResidueField (u.valuation F).valuationSubring)]

/-- **At good reduction, reduction keeps the divisors `ℓ ∉ u` of the order of a torsion point**: if
a natural number `ℓ ∉ u` divides the order of a torsion point `P`, it divides the order of the
reduction of `P`. -/
theorem dvd_addOrderOf_reductionHom {P : W.Point} (hP : IsOfFinAddOrder P) {ℓ : ℕ}
    (hℓu : (ℓ : A) ∉ u.asIdeal) (hℓP : ℓ ∣ addOrderOf P) :
    ℓ ∣ addOrderOf (reductionHom (u.valuation F) P) := by
  -- `Q = (n / ℓ) • P` has order `ℓ`
  set Q := (addOrderOf P / ℓ) • P with hQ
  have hQo : addOrderOf Q = ℓ := addOrderOf_nsmul_addOrderOf_sub hP.addOrderOf_pos.ne' hℓP
  have hℓQ : ℓ • Q = 0 := hQo ▸ addOrderOf_nsmul_eq_zero Q
  -- reduction is injective on `ℓ`-torsion, so `Q` and its reduction have the same order
  have key : addOrderOf Q ∣ addOrderOf (reductionHom (u.valuation F) Q) :=
    addOrderOf_dvd_of_nsmul_eq_zero (eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero u hℓu
      (by rw [map_nsmul, addOrderOf_nsmul_eq_zero]) (by rw [smul_comm, hℓQ, smul_zero]))
  rw [hQo, hQ, map_nsmul] at key
  exact key.trans (addOrderOf_smul_dvd _)

/-- **The primes of the order of a torsion point, seen at one prime of good reduction**: if
`p ∈ u` and the reduction of a torsion point `P` is killed by `m`, every prime dividing the order
of `P` divides `p * m`. -/
theorem prime_dvd_mul_of_dvd_addOrderOf {P : W.Point} (hP : IsOfFinAddOrder P) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓP : ℓ ∣ addOrderOf P) {p m : ℕ} (hp : (p : A) ∈ u.asIdeal)
    (hm : m • reductionHom (u.valuation F) P = 0) : ℓ ∣ p * m := by
  by_cases hℓu : (ℓ : A) ∈ u.asIdeal
  · -- `ℓ` and `p` both lie in `u`, so they are not coprime
    exact (by_contra fun h ↦ Ideal.IsPrime.notMem_of_isCoprime_of_mem
      ((hℓ.coprime_iff_not_dvd.mpr h).cast (R := A)) hℓu hp : ℓ ∣ p).mul_right m
  · exact ((dvd_addOrderOf_reductionHom u hP hℓu hℓP).trans
      (addOrderOf_dvd_of_nsmul_eq_zero hm)).mul_left p

end Prime

/-- **A point of infinite order, certified by reduction at two primes.** Let `u` and `u'` be
primes of good reduction for `W`, with `p ∈ u` and `q ∈ u'`, and let `P ≠ 0` be a point whose
reductions at `u` and `u'` are killed by `m` and `n`. If `p * m` and `q * n` are coprime, `P` has
infinite order. Over `ℚ`, `p` and `q` are the residue characteristics and the hypotheses on `m`
and `n` are computations in the finite groups `W(𝔽_p)` and `W(𝔽_q)`. -/
theorem not_isOfFinAddOrder_of_coprime (u' : HeightOneSpectrum A)
    [IsIntegral (u.valuation F).valuationSubring W]
    [(integralModel (u.valuation F).valuationSubring W).IsElliptic]
    [DecidableEq (ResidueField (u.valuation F).valuationSubring)]
    [IsIntegral (u'.valuation F).valuationSubring W]
    [(integralModel (u'.valuation F).valuationSubring W).IsElliptic]
    [DecidableEq (ResidueField (u'.valuation F).valuationSubring)]
    {P : W.Point} (hP : P ≠ 0) {p q m n : ℕ} (hp : (p : A) ∈ u.asIdeal)
    (hq : (q : A) ∈ u'.asIdeal) (hmn : (p * m).Coprime (q * n))
    (hm : m • reductionHom (u.valuation F) P = 0)
    (hn : n • reductionHom (u'.valuation F) P = 0) : ¬IsOfFinAddOrder P := by
  intro hfin
  -- a prime factor of the order of `P` would divide both `p * m` and `q * n`
  have h1 : addOrderOf P ≠ 1 := fun h ↦ hP (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hℓ := Nat.minFac_prime h1
  exact hℓ.not_dvd_one (hmn ▸ Nat.dvd_gcd
    (prime_dvd_mul_of_dvd_addOrderOf u hfin hℓ (Nat.minFac_dvd _) hp hm)
    (prime_dvd_mul_of_dvd_addOrderOf u' hfin hℓ (Nat.minFac_dvd _) hq hn))

end WeierstrassCurve.Affine.Point

end
