/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.InfiniteOrder
import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.Data.ZMod.QuotientRing
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ResidueField

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

/-- The integral short equation `y² = x³ - x + 1`. -/
abbrev curveX3SubXAddOne : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 1⟩

/-- The discriminant of `y² = x³ - x + 1` is `-368 = -16 * 23`. -/
theorem Δ_curveX3SubXAddOne : curveX3SubXAddOne.Δ = -368 := by
  norm_num [curveX3SubXAddOne, Δ, b₂, b₄, b₆, b₈]

/-- `y² = x³ - x + 1` is an elliptic curve over `ℚ`. -/
instance : (curveX3SubXAddOne.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curveX3SubXAddOne]
  norm_num

private instance prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private instance elliptic_zmod_three :
    (curveX3SubXAddOne.map (Int.castRingHom (ZMod 3))).IsElliptic := by
  rw [isElliptic_iff]
  decide

private instance elliptic_zmod_five :
    (curveX3SubXAddOne.map (Int.castRingHom (ZMod 5))).IsElliptic := by
  rw [isElliptic_iff]
  decide

/-- The reduction of `y² = x³ - x + 1` modulo `3` has `7` points, including infinity. -/
theorem card_point_curveX3SubXAddOne_zmod_three :
    Nat.card (curveX3SubXAddOne.map (Int.castRingHom (ZMod 3))).toAffine.Point = 7 := by
  rw [← pointCount_eq_card_point, pointCount_def,
    Nat.card_congr (Equiv.subtypeEquivRight
      (q := fun xy : ZMod 3 × ZMod 3 ↦ xy.2 ^ 2 = xy.1 ^ 3 - xy.1 + 1)
      fun xy ↦ by rw [equation_iff]; simp [curveX3SubXAddOne]), Nat.card_eq_fintype_card]
  decide

/-- The reduction of `y² = x³ - x + 1` modulo `5` has `8` points, including infinity. -/
theorem card_point_curveX3SubXAddOne_zmod_five :
    Nat.card (curveX3SubXAddOne.map (Int.castRingHom (ZMod 5))).toAffine.Point = 8 := by
  rw [← pointCount_eq_card_point, pointCount_def,
    Nat.card_congr (Equiv.subtypeEquivRight
      (q := fun xy : ZMod 5 × ZMod 5 ↦ xy.2 ^ 2 = xy.1 ^ 3 - xy.1 + 1)
      fun xy ↦ by rw [equation_iff]; simp [curveX3SubXAddOne, sub_eq_add_neg]),
    Nat.card_eq_fintype_card]
  decide

section Reduction

variable (v : HeightOneSpectrum ℤ)

private instance integral_curveX3SubXAddOne :
    IsIntegral (v.valuation ℚ).valuationSubring (curveX3SubXAddOne.baseChange ℚ) :=
  have : IsIntegral ℤ (curveX3SubXAddOne.baseChange ℚ) := ⟨⟨curveX3SubXAddOne, rfl⟩⟩
  .of_isScalarTower (R := ℤ) _

private theorem integralModel_curveX3SubXAddOne :
    integralModel (v.valuation ℚ).valuationSubring (curveX3SubXAddOne.baseChange ℚ) =
      curveX3SubXAddOne.map (algebraMap ℤ (v.valuation ℚ).valuationSubring) :=
  integralModel_eq_of_baseChange_eq (by
    rw [WeierstrassCurve.baseChange, map_map, ← IsScalarTower.algebraMap_eq,
      WeierstrassCurve.baseChange])

private theorem elliptic_integralModel_curveX3SubXAddOne (hΔ : (-368 : ℤ) ∉ v.asIdeal) :
    (integralModel (v.valuation ℚ).valuationSubring
      (curveX3SubXAddOne.baseChange ℚ)).IsElliptic := by
  rwa [integralModel_curveX3SubXAddOne, isElliptic_iff, map_Δ, Δ_curveX3SubXAddOne,
    ← notMem_maximalIdeal, v.algebraMap_mem_maximalIdeal_valuationSubring_iff]

end Reduction

section PrimeReduction

variable (v : HeightOneSpectrum ℤ) (p : ℕ) [Fact p.Prime]
  (hv : v.asIdeal = Ideal.span {(p : ℤ)})

local notation "O" => Valuation.valuationSubring (HeightOneSpectrum.valuation ℚ v)
local notation "k" => ResidueField O
local notation "W" => WeierstrassCurve.baseChange curveX3SubXAddOne ℚ
local notation "V" => WeierstrassCurve.map (integralModel O W) (residue O)

include hv in
private theorem card_reduction_curveX3SubXAddOne
    [(curveX3SubXAddOne.map (Int.castRingHom (ZMod p))).IsElliptic] :
    Nat.card (V).toAffine.Point =
      Nat.card (curveX3SubXAddOne.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  classical
  let e : ZMod p ≃+* k := (Int.quotientSpanNatEquivZMod p).symm.trans
    ((Ideal.quotEquivOfEq hv).symm.trans (v.residueFieldEquivValuationSubring (K := ℚ)))
  have hV : V = (curveX3SubXAddOne.map (Int.castRingHom (ZMod p))).map e.toRingHom := by
    rw [integralModel_curveX3SubXAddOne, map_map, map_map]
    congr 1
    exact RingHom.ext_int _ _
  rw [hV]
  have : Finite k := Finite.of_equiv (ZMod p) e.toEquiv
  rw [← pointCount_eq_card_point, ← pointCount_eq_card_point, pointCount_def, pointCount_def]
  congr 1
  exact (Nat.card_congr ((e.toEquiv.prodCongr e.toEquiv).subtypeEquiv fun xy ↦
    (map_equation _ e.injective xy.1 xy.2).symm)).symm

include hv in
private theorem nsmul_reduction_curveX3SubXAddOne [DecidableEq k]
    [(integralModel O W).IsElliptic]
    [(curveX3SubXAddOne.map (Int.castRingHom (ZMod p))).IsElliptic]
    (P : (W).toAffine.Point) :
    Nat.card (curveX3SubXAddOne.map (Int.castRingHom (ZMod p))).toAffine.Point •
      Point.reductionHom (v.valuation ℚ) P = 0 := by
  classical
  rw [← card_reduction_curveX3SubXAddOne v p hv]
  exact card_nsmul_eq_zero'

end PrimeReduction

/-- **The rational torsion of `y² = x³ - x + 1` is trivial.** The reduced groups at `3` and `5`
have orders `7` and `8`, and `3 * 7` and `5 * 8` are coprime. -/
@[simp]
theorem torsion_curveX3SubXAddOne_eq_bot :
    AddCommGroup.torsion (curveX3SubXAddOne.baseChange ℚ).toAffine.Point = ⊥ := by
  classical
  have hex (p : ℕ) [Fact p.Prime] :
      ∃ v : HeightOneSpectrum ℤ, v.asIdeal = Ideal.span {(p : ℤ)} :=
    ⟨⟨Ideal.span {(p : ℤ)},
      (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp Fact.out),
      by simpa using (Fact.out : p.Prime).ne_zero⟩, rfl⟩
  obtain ⟨v, hv⟩ := hex 3
  obtain ⟨w, hw⟩ := hex 5
  have := elliptic_integralModel_curveX3SubXAddOne v (by
    rw [hv, Ideal.mem_span_singleton]; norm_num)
  have := elliptic_integralModel_curveX3SubXAddOne w (by
    rw [hw, Ideal.mem_span_singleton]; norm_num)
  apply le_antisymm ?_ bot_le
  intro P hP
  apply AddSubgroup.mem_bot.mpr
  by_contra hP0
  exact Point.not_isOfFinAddOrder_of_coprime v w (p := 3) (q := 5) (m := 7) (n := 8) hP0
    (hv ▸ Ideal.mem_span_singleton_self _) (hw ▸ Ideal.mem_span_singleton_self _) (by norm_num)
    (by simpa only [card_point_curveX3SubXAddOne_zmod_three] using
      nsmul_reduction_curveX3SubXAddOne v 3 hv P)
    (by simpa only [card_point_curveX3SubXAddOne_zmod_five] using
      nsmul_reduction_curveX3SubXAddOne w 5 hw P) hP

/-- The rational point group of `y² = x³ - x + 1` is torsion-free. -/
instance : IsAddTorsionFree (curveX3SubXAddOne.baseChange ℚ).toAffine.Point :=
  AddCommGroup.isAddTorsionFree_iff_torsion_eq_bot.mpr torsion_curveX3SubXAddOne_eq_bot

end TauCeti.WorkedExamples
