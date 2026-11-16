/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder.Relations

/-!
# Stage-1 detection for the binary Montgomery ladder

Combining reduction of a binary Montgomery-ladder derivation modulo a prime `p ∣ n`
(`LadderRel.map`) with the cross-difference invariant (`LadderRel.cross_coordinates`) and
coordinate-pair stage-1 detection (`prime_dvd_gcd_of_addOrderOf_dvd`) gives end-to-end stage-1
detection for `LadderRel` over `ZMod n`.

In the forward direction, `LadderRel.prime_dvd_gcd_of_addOrderOf_dvd` requires only that the
scaled constants `(N, D)` satisfy `4 * N = (A + 2) * D` modulo `p` and that the starting pair `S`
has vanishing cross difference with a native point `P` whose order divides `m`; no nonvanishing
hypothesis is needed on `2`, `B`, `D`, `S`, or `P`, and the curve model need not be elliptic.
Lagrange's theorem and `pointCount_eq_card_point` yield the corresponding cardinality and
projective point-count criteria.

In the exact characterization `LadderRel.prime_dvd_gcd_iff_addOrderOf_dvd`, assuming `2 ≠ 0`,
`B ≠ 0`, `D ≠ 0`, and `S ≠ 0` modulo `p` together with `P ≠ twoTorsionPoint A hB` guarantees that
`p` divides `Nat.gcd U.z.val n` if and only if `addOrderOf P ∣ m`. The hypothesis `P ≠ 0` is not
needed because both sides hold when `P = 0`, whereas excluding the distinguished two-torsion point
is necessary since differential addition annihilates its raw output even at `m = 1`. Combining
order divisibility modulo `p` with non-divisibility modulo a second prime `q ∣ n` certifies a
proper factor `1 < Nat.gcd U.z.val n < n` of a positive modulus `n`.

## Main results

* `TauCeti.Montgomery.LadderRel.prime_dvd_gcd_of_addOrderOf_dvd`: if `addOrderOf P ∣ m` modulo
  `p ∣ n`, then `p ∣ Nat.gcd U.z.val n` for every ladder derivation at index `m`.
* `TauCeti.Montgomery.LadderRel.prime_dvd_gcd_of_card_dvd` and
  `TauCeti.Montgomery.LadderRel.prime_dvd_gcd_of_pointCount_dvd`: the native group cardinality and
  projective point-count forms.
* `TauCeti.Montgomery.LadderRel.prime_dvd_gcd_iff_addOrderOf_dvd`: exact equivalence
  `p ∣ Nat.gcd U.z.val n ↔ addOrderOf P ∣ m` away from characteristic two, degenerate parameters,
  and the distinguished two-torsion point.
* `TauCeti.Montgomery.LadderRel.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd` and
  `TauCeti.Montgomery.LadderRel.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd`: proper-factor
  certificates from nonvanishing of the output denominator or non-annihilation at a second prime.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1.
* H. W. Lenstra Jr., *Factoring integers with elliptic curves*, Ann. of Math. 126 (1987),
  649–673, §2.
* P. Zimmermann, *20 years of ECM*, ANTS VII, Lecture Notes in Computer Science 4076 (2006),
  525–542, §1.1.
-/

public section

namespace TauCeti.Montgomery.LadderRel

variable {n p m : ℕ} [Fact p.Prime] {N D : ZMod n} {S U V : Pair (ZMod n)} {A B : ZMod p}

/-- **Stage-1 ladder detection by point order.** For any binary ladder derivation over `ZMod n` at
index `m`, if `(N, D)` reduces modulo `p ∣ n` to scaled constants for `A`, `S` reduces to a pair
with vanishing cross difference with `P`, and `addOrderOf P ∣ m`, then `p ∣ Nat.gcd U.z.val n`.
No nonvanishing hypothesis is needed on `2`, `B`, `D`, `S`, or `P`, and the model need not be
elliptic. -/
theorem prime_dvd_gcd_of_addOrderOf_dvd (h : LadderRel N D S m U V) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    (P : (model A B).toAffine.Point) (hm : addOrderOf P ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd U.z.val n :=
  Montgomery.prime_dvd_gcd_of_addOrderOf_dvd hpn P U hm
    ((h.map (ZMod.castHom hpn (ZMod p))).cross_coordinates hND hSP).1

/-- **Stage-1 ladder detection by native group cardinality.** A multiple of the group order
annihilates every point, so every binary ladder derivation at index `m` detects `p` in its output
denominator gcd. No ellipticity or nonvanishing hypothesis is needed. -/
theorem prime_dvd_gcd_of_card_dvd (h : LadderRel N D S m U V) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    (P : (model A B).toAffine.Point) (hm : Nat.card (model A B).toAffine.Point ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd U.z.val n :=
  h.prime_dvd_gcd_of_addOrderOf_dvd hpn hND P ((addOrderOf_dvd_natCard P).trans hm) hSP

/-- On an elliptic monic model, the projective point count can replace the native group cardinality
in stage-1 ladder detection. -/
theorem prime_dvd_gcd_of_pointCount_dvd [(model A B).IsElliptic] (h : LadderRel N D S m U V)
    (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    (P : (model A B).toAffine.Point) (hm : (model A B).pointCount ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd U.z.val n := by
  rw [WeierstrassCurve.pointCount_eq_card_point] at hm
  exact h.prime_dvd_gcd_of_card_dvd hpn hND P hm hSP

/-- **Exact stage-1 ladder detection.** Away from characteristic two, degenerate parameters
`B = 0` or `D = 0`, a zero reduced starting pair, and the distinguished two-torsion point, a prime
divisor `p ∣ n` divides the output denominator gcd of a binary ladder derivation at index `m` if
and only if `addOrderOf P ∣ m`. Infinity `P = 0` is included, since both sides hold trivially. -/
theorem prime_dvd_gcd_iff_addOrderOf_dvd (h : LadderRel N D S m U V) (hpn : p ∣ n)
    (h₂ : (2 : ZMod p) ≠ 0) (hB : B ≠ 0) (hD : ZMod.castHom hpn (ZMod p) D ≠ 0)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    (P : (model A B).toAffine.Point) (hS : S.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hPT : P ≠ twoTorsionPoint A hB) :
    p ∣ Nat.gcd U.z.val n ↔ addOrderOf P ∣ m := by
  by_cases hP : P = 0
  · subst hP
    have hm : addOrderOf (0 : (model A B).toAffine.Point) ∣ m := by simp
    exact iff_of_true (h.prime_dvd_gcd_of_addOrderOf_dvd hpn hND 0 hm hSP) hm
  · have hinv := (h.map (ZMod.castHom hpn (ZMod p))).coordinates h₂ hB hD hND hS hSP hP hPT
    exact Montgomery.prime_dvd_gcd_iff_addOrderOf_dvd hpn hB P U hinv.1 hinv.2.1

/-- Stage-1 ladder annihilation modulo `p`, together with an output denominator nonzero modulo
another divisor `q`, certifies a proper factor of the positive modulus `n`. -/
theorem one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd [NeZero n] (h : LadderRel N D S m U V)
    (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    (P : (model A B).toAffine.Point) (hm : addOrderOf P ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    {q : ℕ} (hqn : q ∣ n) (hq : ZMod.castHom hqn (ZMod q) U.z ≠ 0) :
    1 < Nat.gcd U.z.val n ∧ Nat.gcd U.z.val n < n :=
  Montgomery.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd hpn P U hm
    ((h.map (ZMod.castHom hpn (ZMod p))).cross_coordinates hND hSP).1 hqn hq

/-- **Proper-factor certification from differing point orders.** If a binary ladder derivation at
index `m` annihilates a point modulo `p ∣ n` and fails to annihilate a non-exceptional point modulo
a prime `q ∣ n` (where `2 ≠ 0`, `B' ≠ 0`, `D ≠ 0`, and `S ≠ 0`), then the output denominator gcd is
a proper factor of the positive modulus `n`. -/
theorem one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd [NeZero n]
    (h : LadderRel N D S m U V) (hpn : p ∣ n)
    (hNDp : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    (P : (model A B).toAffine.Point) (hmp : addOrderOf P ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    {q : ℕ} [Fact q.Prime] (hqn : q ∣ n) {A' B' : ZMod q}
    (h₂ : (2 : ZMod q) ≠ 0) (hB' : B' ≠ 0) (hDq : ZMod.castHom hqn (ZMod q) D ≠ 0)
    (hNDq : 4 * ZMod.castHom hqn (ZMod q) N = (A' + 2) * ZMod.castHom hqn (ZMod q) D)
    (Q : (model A' B').toAffine.Point) (hmq : ¬ addOrderOf Q ∣ m)
    (hSq : S.map (ZMod.castHom hqn (ZMod q)) ≠ 0)
    (hSQ : (S.map (ZMod.castHom hqn (ZMod q))).cross (Montgomery.coordinates A' B' Q) = 0)
    (hQT : Q ≠ twoTorsionPoint A' hB') :
    1 < Nat.gcd U.z.val n ∧ Nat.gcd U.z.val n < n := by
  refine h.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd hpn hNDp P hmp hSP hqn ?_
  rw [ne_eq, ← U.z.dvd_gcd_val_iff_castHom_eq_zero hqn,
    h.prime_dvd_gcd_iff_addOrderOf_dvd hqn h₂ hB' hDq hNDq Q hSq hSQ hQT]
  exact hmq

end TauCeti.Montgomery.LadderRel
