/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic.Ring

/-!
# Root-string Jacobi identities in Lie rings

In the derivation of Steinberg's rank-two Chevalley commutator relations from universal enveloping
algebra normal-ordering formulas, several intermediate Lie brackets along positive root strings of
lengths two and three vanish (or coincide up to integer multiples) automatically by the Jacobi
identity. This file proves those Lie-ring identities under integer-scaled bracket hypotheses,
assuming `IsAddTorsionFree` where division by `2` or `3` is required.

## Main results

* `TauCeti.zsmul_lie_eq_zero_of_lie_eq`: in any Lie ring, `⁅x, y⁆ = c • z`, `⁅x, w⁆ = 0`, and
  `d • ⁅y, w⁆ = 0` imply `(c * d) • ⁅z, w⁆ = 0`.
* `TauCeti.zsmul_lie_eq_zero_of_zsmul_lie_eq_two`: in an additively torsion-free Lie ring,
  `⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`, and `⁅y, z⁆ = 0` force `d • ⁅y, w⁆ = 0`.
* `TauCeti.zsmul_lie_eq_zero_of_g2_short_pair`: the corresponding vanishing bracket for a short-root
  pair of type `G₂`.
* `TauCeti.zsmul_lie_eq_zsmul_of_lie_eq_three_nsmul`,
  `TauCeti.zsmul_lie_fourth_eq_zero_of_lie_eq_three_nsmul`, and
  `TauCeti.zsmul_lie_third_eq_zero_of_lie_eq_three_nsmul_rev`: the Jacobi identities along the
  four-root positive chains of type `G₂`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.
-/

public section

namespace TauCeti

section LieRing

variable {L : Type*} [LieRing L]

/-- In a Lie ring, if `⁅x, y⁆ = c • z`, `⁅x, w⁆ = 0`, and `d • ⁅y, w⁆ = 0`, the Jacobi identity
gives `(c * d) • ⁅z, w⁆ = 0`. -/
theorem zsmul_lie_eq_zero_of_lie_eq {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxw : ⁅x, w⁆ = 0) (hyw : d • ⁅y, w⁆ = 0) :
    (c * d) • ⁅z, w⁆ = 0 := by
  rw [mul_zsmul, ← lie_zsmul, ← zsmul_lie, ← hxy, lie_lie, lie_zsmul, hyw, lie_zsmul, hxw,
    smul_zero, lie_zero, lie_zero, sub_self]

variable [IsAddTorsionFree L]

/-- In a torsion-free Lie ring, if `⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`, and
`⁅y, z⁆ = 0`, the Jacobi identity forces `d • ⁅y, w⁆ = 0`. -/
theorem zsmul_lie_eq_zero_of_zsmul_lie_eq_two {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w) (hyz : ⁅y, z⁆ = 0) :
    d • ⁅y, w⁆ = 0 := by
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (2 : ℤ)) (by decide)).mp ?_
  calc (2 : ℤ) • (d • ⁅y, w⁆) = c • ⁅y, ⁅x, z⁆⁆ := by
        rw [← mul_zsmul, ← lie_zsmul, ← hxz, lie_zsmul]
    _ = c • ⁅⁅y, x⁆, z⁆ + c • ⁅x, ⁅y, z⁆⁆ := by rw [leibniz_lie, smul_add]
    _ = 0 := by rw [← lie_skew y x, hxy, neg_lie, zsmul_lie, lie_self, hyz, lie_zero]; simp

/-- In a torsion-free Lie ring, the short-pair bracket hypotheses `⁅x, y⁆ = (2 * c) • z`,
`c • ⁅x, z⁆ = (3 * d) • w`, `c • ⁅z, y⁆ = (3 * a) • s`, and `⁅x, s⁆ = 0` force `d • ⁅y, w⁆ = 0`. -/
theorem zsmul_lie_eq_zero_of_g2_short_pair {x y z w s : L} {c d a : ℤ}
    (hxy : ⁅x, y⁆ = (2 * c) • z) (hxz : c • ⁅x, z⁆ = (3 * d) • w)
    (hzy : c • ⁅z, y⁆ = (3 * a) • s) (hxs : ⁅x, s⁆ = 0) : d • ⁅y, w⁆ = 0 := by
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (3 : ℤ)) (by decide)).mp ?_
  have hyz : c • ⁅y, z⁆ = -((3 * a) • s) := by rw [← lie_skew y z, smul_neg, hzy]
  calc (3 : ℤ) • (d • ⁅y, w⁆) = c • ⁅y, ⁅x, z⁆⁆ := by
        rw [← mul_zsmul, ← lie_zsmul, ← hxz, lie_zsmul]
    _ = c • ⁅⁅y, x⁆, z⁆ + ⁅x, c • ⁅y, z⁆⁆ := by rw [leibniz_lie, smul_add, lie_zsmul]
    _ = 0 := by
      rw [← lie_skew y x, hxy, neg_lie, zsmul_lie, lie_self, hyz, lie_neg, lie_zsmul, hxs]; simp

/-- In a torsion-free Lie ring, under the type-`G₂` scaled bracket hypotheses `⁅x, y⁆ = c • z`,
`c • ⁅x, z⁆ = (2 * d) • w`, `d • ⁅x, w⁆ = (3 * a) • m`, `(d * c) • ⁅w, z⁆ = (3 * b) • o`, and
`⁅y, z⁆ = 0`, the Jacobi identity gives `a • ⁅y, m⁆ = b • o`. -/
theorem zsmul_lie_eq_zsmul_of_lie_eq_three_nsmul {x y z w m o : L} {c d a b : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w)
    (hxw : d • ⁅x, w⁆ = (3 * a) • m) (hwz : (d * c) • ⁅w, z⁆ = (3 * b) • o)
    (hyz : ⁅y, z⁆ = 0) : a • ⁅y, m⁆ = b • o := by
  have hyw := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
  refine ((AddCommute.all _ _).zsmul_right_inj (n := (3 : ℤ)) (by decide)).mp ?_
  calc (3 : ℤ) • (a • ⁅y, m⁆) = d • ⁅y, ⁅x, w⁆⁆ := by
        rw [← mul_zsmul, ← lie_zsmul, ← hxw, lie_zsmul]
    _ = d • ⁅⁅y, x⁆, w⁆ + ⁅x, d • ⁅y, w⁆⁆ := by rw [leibniz_lie, smul_add, lie_zsmul]
    _ = (d * c) • ⁅w, z⁆ := by
      rw [hyw, lie_zero, add_zero, ← lie_skew y x, hxy, neg_lie, zsmul_lie, ← lie_skew z w,
        smul_neg, smul_neg, smul_neg, neg_neg, mul_zsmul]
    _ = (3 : ℤ) • (b • o) := by rw [hwz, mul_zsmul]

/-- Under the type-`G₂` hypotheses `⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`,
`(d * c) • ⁅w, z⁆ = (3 * b) • o`, and `⁅y, z⁆ = 0` in a torsion-free Lie ring, `b • ⁅y, o⁆ = 0`. -/
theorem zsmul_lie_fourth_eq_zero_of_lie_eq_three_nsmul {x y z w o : L} {c d b : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w)
    (hwz : (d * c) • ⁅w, z⁆ = (3 * b) • o) (hyz : ⁅y, z⁆ = 0) : b • ⁅y, o⁆ = 0 := by
  have hyw := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (3 : ℤ)) (by decide)).mp ?_
  calc (3 : ℤ) • (b • ⁅y, o⁆) = (d * c) • ⁅y, ⁅w, z⁆⁆ := by
        rw [← mul_zsmul, ← lie_zsmul, ← hwz, lie_zsmul]
    _ = c • ⁅d • ⁅y, w⁆, z⁆ + (d * c) • ⁅w, ⁅y, z⁆⁆ := by
      rw [leibniz_lie, smul_add, mul_comm d c, mul_zsmul, ← zsmul_lie, mul_comm c d]
    _ = 0 := by rw [hyw, hyz]; simp

/-- In a torsion-free Lie ring, under the reversed type-`G₂` hypotheses `c • ⁅z, y⁆ = (2 * d) • w`,
`d • ⁅y, w⁆ = (3 * a) • m`, `(d * c) • ⁅z, w⁆ = (3 * b) • o`, and `⁅y, o⁆ = 0`, the Jacobi identity
forces `(a * c) • ⁅m, z⁆ = 0`. -/
theorem zsmul_lie_third_eq_zero_of_lie_eq_three_nsmul_rev {y z w m o : L} {c d a b : ℤ}
    (hzy : c • ⁅z, y⁆ = (2 * d) • w) (hyw : d • ⁅y, w⁆ = (3 * a) • m)
    (hzw : (d * c) • ⁅z, w⁆ = (3 * b) • o) (hyo : ⁅y, o⁆ = 0) : (a * c) • ⁅m, z⁆ = 0 := by
  suffices hzm : (a * c) • ⁅z, m⁆ = 0 by rw [← lie_skew m z, smul_neg, hzm, neg_zero]
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (3 : ℤ)) (by decide)).mp ?_
  have h0 : (3 : ℤ) • ((a * c) • ⁅z, m⁆) = c • ⁅z, (3 * a) • m⁆ := by
    rw [lie_zsmul, ← mul_zsmul, ← mul_zsmul]; congr 1; ring
  calc (3 : ℤ) • ((a * c) • ⁅z, m⁆) = c • (d • ⁅⁅z, y⁆, w⁆) + c • (d • ⁅y, ⁅z, w⁆⁆) := by
        rw [h0, ← hyw, lie_zsmul, leibniz_lie, smul_add, smul_add]
    _ = d • ⁅c • ⁅z, y⁆, w⁆ + ⁅y, (d * c) • ⁅z, w⁆⁆ := by
      rw [zsmul_lie, lie_zsmul, ← mul_zsmul, ← mul_zsmul, ← mul_zsmul, mul_comm c d]
    _ = 0 := by rw [hzy, zsmul_lie, lie_self, hzw, lie_zsmul, hyo]; simp

end LieRing

end TauCeti
