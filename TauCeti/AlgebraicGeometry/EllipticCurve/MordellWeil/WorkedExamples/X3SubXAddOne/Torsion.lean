/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.InfiniteOrder
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.WorkedExamples.X3SubXAddOne.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount

/-!
# The rational torsion of `y² = x³ - x + 1` is trivial

Reduction modulo `3` and `5` gives point groups of orders `7` and `8`. A prime factor of the
order of a rational torsion point must therefore divide both `3 * 7` and `5 * 8`, which are
coprime. This proves that the rational point group is torsion-free, using only injectivity of
reduction on torsion prime to the residue characteristic.

This is the torsion calculation needed to identify this Mordell–Weil group with `ℤ` once its
rank is known to be one. The finite counts include the point at infinity and are evaluated by
the Lean kernel. The comparison of the valuation residue fields with `ZMod p` is explicit.

## Main results

* `TauCeti.WorkedExamples.card_point_curveX3SubXAddOne_zmod_three` and
  `TauCeti.WorkedExamples.card_point_curveX3SubXAddOne_zmod_five`: the finite point counts.
* `TauCeti.WorkedExamples.torsion_curveX3SubXAddOne_eq_bot`: rational torsion is trivial.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.3.1 and VIII.7.

## Provenance

The reduction certificate uses `Affine.Point.not_isOfFinAddOrder_of_coprime`, whose provenance
is Michael Stoll's `EllipticCurves` project (Apache-2.0, commit `3bfe124`). Its
`InfiniteOrderExample.lean` studies a point on the same equation at the same two primes; here
we count the entire reduced groups to exclude every nonzero rational torsion point.
-/

public section

open WeierstrassCurve Affine IsDedekindDomain IsLocalRing

namespace TauCeti.WorkedExamples

private instance prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private instance elliptic_zmod_three :
    (curveX3SubXAddOne.map (Int.castRingHom (ZMod 3))).IsElliptic := by
  rw [isElliptic_iff]
  decide

private instance elliptic_zmod_five :
    (curveX3SubXAddOne.map (Int.castRingHom (ZMod 5))).IsElliptic := by
  rw [isElliptic_iff]
  decide

private theorem card_point_curveX3SubXAddOne_zmod (p : ℕ) [Fact p.Prime]
    [(curveX3SubXAddOne.map (Int.castRingHom (ZMod p))).IsElliptic] :
    Nat.card (curveX3SubXAddOne.map (Int.castRingHom (ZMod p))).toAffine.Point =
      Fintype.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1 + 1} + 1 := by
  rw [← pointCount_eq_card_point, pointCount_def,
    Nat.card_congr (Equiv.subtypeEquivRight
      (q := fun xy : ZMod p × ZMod p ↦ xy.2 ^ 2 = xy.1 ^ 3 - xy.1 + 1)
      fun xy ↦ by rw [equation_iff]; simp [curveX3SubXAddOne, sub_eq_add_neg]),
    Nat.card_eq_fintype_card]

/-- The reduction of `y² = x³ - x + 1` modulo `3` has `7` points, including infinity. -/
theorem card_point_curveX3SubXAddOne_zmod_three :
    Nat.card (curveX3SubXAddOne.map (Int.castRingHom (ZMod 3))).toAffine.Point = 7 := by
  rw [card_point_curveX3SubXAddOne_zmod]
  decide

/-- The reduction of `y² = x³ - x + 1` modulo `5` has `8` points, including infinity. -/
theorem card_point_curveX3SubXAddOne_zmod_five :
    Nat.card (curveX3SubXAddOne.map (Int.castRingHom (ZMod 5))).toAffine.Point = 8 := by
  rw [card_point_curveX3SubXAddOne_zmod]
  decide

/-- **The rational torsion of `y² = x³ - x + 1` is trivial.** The reduced groups at `3` and `5`
have orders `7` and `8`, and `3 * 7` and `5 * 8` are coprime. -/
@[simp]
theorem torsion_curveX3SubXAddOne_eq_bot :
    AddCommGroup.torsion (curveX3SubXAddOne.baseChange ℚ).toAffine.Point = ⊥ := by
  classical
  let v := HeightOneSpectrum.ofPrime
    (Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp Nat.prime_three))
  let w := HeightOneSpectrum.ofPrime
    (Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp Nat.prime_five))
  have hv : v.asIdeal = Ideal.span {(3 : ℤ)} := rfl
  have hw : w.asIdeal = Ideal.span {(5 : ℤ)} := rfl
  have := curveX3SubXAddOne.isElliptic_integralModel_baseChange (K := ℚ) v (by
    rw [Δ_curveX3SubXAddOne, hv, Ideal.mem_span_singleton]; norm_num)
  have := curveX3SubXAddOne.isElliptic_integralModel_baseChange (K := ℚ) w (by
    rw [Δ_curveX3SubXAddOne, hw, Ideal.mem_span_singleton]; norm_num)
  apply le_antisymm ?_ bot_le
  intro P hP
  apply AddSubgroup.mem_bot.mpr
  by_contra hP0
  exact Point.not_isOfFinAddOrder_of_coprime v w (p := 3) (q := 5) (m := 7) (n := 8) hP0
    (hv ▸ Ideal.mem_span_singleton_self _) (hw ▸ Ideal.mem_span_singleton_self _) (by norm_num)
    (by simpa only [card_point_curveX3SubXAddOne_zmod_three] using
      curveX3SubXAddOne.card_nsmul_reductionHom_baseChange_eq_zero v 3 hv P)
    (by simpa only [card_point_curveX3SubXAddOne_zmod_five] using
      curveX3SubXAddOne.card_nsmul_reductionHom_baseChange_eq_zero w 5 hw P) hP

/-- The rational point group of `y² = x³ - x + 1` is torsion-free. -/
instance : HasUniqueDiv (curveX3SubXAddOne.baseChange ℚ).toAffine.Point where
  nsmul_right_injective _ hn a b h :=
    (AddCommGroup.isAddTorsionFree_iff_torsion_eq_bot.mpr
      torsion_curveX3SubXAddOne_eq_bot).eq_of_nsmul_eq_nsmul_of_addCommute hn (.all a b) h

end TauCeti.WorkedExamples
