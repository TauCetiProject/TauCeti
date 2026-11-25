/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Frobenius.TwistedKernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Trace
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
import TauCeti.Algebra.CharP.Lemmas

/-!
# The order of the twisted Frobenius kernel

Let `W` be an elliptic curve over a finite field `k` with `q` elements and characteristic `p`, let
`a_q = q + 1 - #W(k)` be its Frobenius trace, and let `L` be a separably closed extension of `k`.
For `i ≥ 1` the twisted Frobenius kernel `B_i(W, L)` (`WeierstrassCurve.twistedFrobeniusKernel`)
has order

`#B_i(W, L) = 1 - a_q q ^ i + q ^ (2 i + 1)`.

This is the order of the even K-group `K_{2i}` of the elliptic curve, by the computation of the
K-theory of curves over finite fields (Weibel, Theorem VI.6.7).

The count runs through the endomorphism `r π - 1` of `W` over `L`, for an integer `r`, where `π`
is the base-changed Frobenius. It pulls the invariant differential back to its negative, so it is
nonzero and separable; over the separably closed field `L` its kernel, the points with
`r • π P = P`, therefore has `deg (r π - 1) = q r² - a_q r + 1` elements
(`TauCeti.Isogeny.Hom.ncard_fixedPoints_zsmul_ofIsogeny_baseChangeFrobenius`). For `r = q ^ i` with
`i ≥ 1` this degree is `1` modulo `p`, and every kernel point is killed by the degree through the
dual isogeny, so the kernel is prime-to-`p` torsion and coincides with `B_i(W, L)`.

## Main results

* `WeierstrassCurve.card_twistedFrobeniusKernel`: `#B_i(W, L) = 1 - a_q q ^ i + q ^ (2 i + 1)` for
  `i ≥ 1`.

## References

* C. A. Weibel, *The K-book*, VI.6.4 and Theorem VI.6.7.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5 and V.2.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- **The order of the twisted Frobenius kernel**: over a separably closed extension of a finite
field with `q` elements, for `i ≥ 1`, the twisted Frobenius kernel `B_i` of an elliptic curve with
Frobenius trace `a_q` has `1 - a_q q ^ i + q ^ (2 i + 1)` elements. For `i = 0` the group is the
prime-to-`p` part of the rational points instead, so the hypothesis `1 ≤ i` is needed. -/
theorem _root_.WeierstrassCurve.card_twistedFrobeniusKernel (L : Type*) [Field L] [DecidableEq L]
    [Algebra F L] [IsSepClosed L] {i : ℕ} (hi : 1 ≤ i) :
    (Nat.card (W.twistedFrobeniusKernel L i) : ℤ) =
      1 - W.frobeniusTrace * (Nat.card F : ℤ) ^ i + (Nat.card F : ℤ) ^ (2 * i + 1) := by
  set r : ℤ := ((Nat.card F ^ i : ℕ) : ℤ) with hr
  have hfix (P : (W⁄L).toAffine.Point) :
      (Nat.card F ^ i) • Point.map (FiniteField.frobeniusAlgHom F L) P = P ↔
        (r • ofIsogeny (baseChangeFrobenius L W)).pointMap P = P := by
    rw [zsmul_pointMap, pointMap_ofIsogeny_baseChangeFrobenius, hr, natCast_zsmul]
  -- The degree `q r² - a_q r + 1` of `r π - 1` is `1` in `F`, hence prime to `p`.
  set f := r • ofIsogeny (baseChangeFrobenius L W) - 1 with hf
  have hcop : f.degree.Coprime (ringChar F) := by
    refine coprime_ringChar_of_natCast_ne_zero (CharP.prime_ringChar F) ?_
    rw [← Int.cast_natCast, hf, degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_one]
    simp [hr, Nat.card_eq_fintype_card, Nat.one_le_iff_ne_zero.mp hi]
  have hpos : 0 < f.degree := by
    rw [Nat.pos_iff_ne_zero, Ne, degree_eq_zero_iff]
    exact zsmul_ofIsogeny_baseChangeFrobenius_sub_one_ne_zero W r
  -- So the twisted kernel is exactly the set of points fixed by `r π`.
  have hset : (W.twistedFrobeniusKernel L i : Set (W⁄L).toAffine.Point) =
      {P | (r • ofIsogeny (baseChangeFrobenius L W)).pointMap P = P} := by
    ext P
    simp only [SetLike.mem_coe, mem_twistedFrobeniusKernel_iff, Set.mem_ofPred_eq, hfix,
      and_iff_right_iff_imp]
    exact fun hP ↦ ⟨f.degree, hpos, hcop, degree_sub_one_nsmul_eq_zero_of_pointMap_eq_self hP⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset,
    ncard_fixedPoints_zsmul_ofIsogeny_baseChangeFrobenius, hr]
  push_cast
  ring

end TauCeti.Isogeny.Hom

end
