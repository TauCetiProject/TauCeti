/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.QuotientRing

/-!
# Reduction of integral equations at primes

An integral Weierstrass equation has good reduction at a height-one prime when its discriminant
lies outside that prime. For equations over `ℤ`, the valuation residue field at `(p)` is `ZMod p`.
Thus counting points on the equation over `ZMod p` gives the order of the reduced point group,
and that order annihilates every reduced rational point. These comparisons let finite point
counts supply torsion certificates for rational curves.
-/

public section

open IsDedekindDomain IsLocalRing

namespace WeierstrassCurve

/-- An integral equation has good reduction at `v` when its discriminant lies outside `v`. -/
theorem isElliptic_integralModel_baseChange {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (E : WeierstrassCurve R)
    (v : HeightOneSpectrum R) [Algebra R (v.valuation K).valuationSubring]
    [IsScalarTower R (v.valuation K).valuationSubring K] (hΔ : E.Δ ∉ v.asIdeal) :
    (integralModel (v.valuation K).valuationSubring (E.baseChange K)).IsElliptic := by
  rwa [integralModel_baseChange_eq_map, isElliptic_iff, map_Δ,
    ← notMem_maximalIdeal, v.algebraMap_mem_maximalIdeal_valuationSubring_iff]

section PrimeReduction

variable (E : WeierstrassCurve ℤ) (v : HeightOneSpectrum ℤ) (p : ℕ) [Fact p.Prime]
  (hv : v.asIdeal = Ideal.span {(p : ℤ)})

local notation "O" => Valuation.valuationSubring (HeightOneSpectrum.valuation ℚ v)
local notation "k" => ResidueField O
local notation "W" => WeierstrassCurve.baseChange E ℚ
local notation "V" => WeierstrassCurve.map (integralModel O W) (residue O)

include hv in
/-- At the prime `(p)`, the valuation reduction of an integral equation has as many points as
its reduction over `ZMod p`. -/
theorem card_point_reduction_baseChange [(E.map (Int.castRingHom (ZMod p))).IsElliptic] :
    Nat.card (V).toAffine.Point = Nat.card (E.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  classical
  let e : ZMod p ≃+* k := (Int.quotientSpanNatEquivZMod p).symm.trans
    ((Ideal.quotEquivOfEq hv).symm.trans
      (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal O).toRingEquiv)
  have hV : V = (E.map (Int.castRingHom (ZMod p))).map e.toRingHom := by
    rw [integralModel_baseChange_eq_map, map_map, map_map]
    congr 1
    exact RingHom.ext_int _ _
  have : Finite (ℤ ⧸ v.asIdeal) := Finite.of_equiv (ZMod p)
    ((Int.quotientSpanNatEquivZMod p).symm.trans (Ideal.quotEquivOfEq hv).symm).toEquiv
  rw [hV]
  rw [← pointCount_eq_card_point,
    ← pointCount_eq_card_point (E.map (Int.castRingHom (ZMod p))),
    pointCount_def, pointCount_def]
  congr 1
  exact (Nat.card_congr ((e.toEquiv.prodCongr e.toEquiv).subtypeEquiv fun xy ↦
    (Affine.map_equation _ e.injective xy.1 xy.2).symm)).symm

include hv in
/-- At good reduction at `(p)`, the order of the point group over `ZMod p` annihilates the
reduction of every rational point of an integral equation. -/
theorem card_nsmul_reductionHom_baseChange [DecidableEq k] [(integralModel O W).IsElliptic]
    [(E.map (Int.castRingHom (ZMod p))).IsElliptic] (P : (W).toAffine.Point) :
    Nat.card (E.map (Int.castRingHom (ZMod p))).toAffine.Point •
      Affine.Point.reductionHom (v.valuation ℚ) P = 0 := by
  classical
  rw [← card_point_reduction_baseChange E v p hv]
  exact card_nsmul_eq_zero'

end PrimeReduction

end WeierstrassCurve
