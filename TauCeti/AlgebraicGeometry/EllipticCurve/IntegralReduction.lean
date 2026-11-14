/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.AdicCompletion
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import Mathlib.Algebra.Field.ZMod
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# Reduction of integral equations at primes

An integral Weierstrass equation has good reduction at a height-one prime when its discriminant
lies outside that prime. For equations over `ℤ`, the valuation residue field at `(p)` is `ZMod p`.
Thus counting points on the equation over `ZMod p` gives the order of the reduced point group,
and that order annihilates every reduced rational point. These comparisons let finite point
counts supply torsion certificates for rational curves.

Over the completion `F_u` at a height-one prime `u` with finite residue field, the ring of
integers `𝒪[F_u]` of the valuative relation is `O_u`. Minimality over `𝒪[F_u]` therefore agrees
with minimality over `O_u` (`WeierstrassCurve.isMinimal_integer_adicCompletion_iff`), the reduced
nonsingular point group over `𝒪[F_u]` of any minimal equation has the same cardinality as the
reduction over `Valued.v.valuationSubring`
(`WeierstrassCurve.natCard_point_reduction_adicCompletion`), and an elliptic equation over `O_u`
has good reduction at `𝒪[F_u]` (`WeierstrassCurve.hasGoodReduction_baseChange_adicCompletion`).
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

/-- Reducing the integral model of an equation over `ℤ` agrees with mapping its reduction over
`ZMod p` along any homomorphism into the valuation residue field. -/
theorem map_integralModel_baseChange_eq_map (E : WeierstrassCurve ℤ)
    (v : HeightOneSpectrum ℤ) {p : ℕ}
    (f : ZMod p →+* ResidueField (v.valuation ℚ).valuationSubring) :
    (integralModel (v.valuation ℚ).valuationSubring (E.baseChange ℚ)).map
        (residue (v.valuation ℚ).valuationSubring) =
      (E.map (Int.castRingHom (ZMod p))).map f := by
  rw [integralModel_baseChange_eq_map, map_map, map_map]
  congr 1
  exact RingHom.ext_int _ _

section PrimeReduction

variable (E : WeierstrassCurve ℤ) (v : HeightOneSpectrum ℤ) (p : ℕ)
  (hv : v.asIdeal = Ideal.span {(p : ℤ)})

local notation "O" => Valuation.valuationSubring (HeightOneSpectrum.valuation ℚ v)
local notation "k" => ResidueField O
local notation "W" => WeierstrassCurve.baseChange E ℚ
local notation "V" => WeierstrassCurve.map (integralModel O W) (residue O)

include hv in
/-- At the prime `(p)`, the valuation reduction of an integral equation has as many points as
its reduction over `ZMod p`. -/
theorem card_point_reduction_baseChange :
    Nat.card (V).toAffine.Point = Nat.card (E.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  classical
  let e : ZMod p ≃+* k := (Int.quotientSpanNatEquivZMod p).symm.trans
    ((Ideal.quotEquivOfEq hv).symm.trans
      (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal O).toRingEquiv)
  rw [map_integralModel_baseChange_eq_map E v e.toRingHom,
    Nat.card_congr
      ((E.map (Int.castRingHom (ZMod p))).map e.toRingHom).toAffine.nonsingularPointEquiv,
    Nat.card_congr (E.map (Int.castRingHom (ZMod p))).toAffine.nonsingularPointEquiv]
  exact (Nat.card_congr ((e.toEquiv.prodCongr e.toEquiv).subtypeEquiv fun xy ↦
    (Affine.map_nonsingular _ e.injective xy.1 xy.2).symm).optionCongr).symm

include hv in
/-- At good reduction at `(p)`, the order of the point group over `ZMod p` annihilates the
reduction of every rational point of an integral equation. -/
theorem card_nsmul_reductionHom_baseChange_eq_zero [DecidableEq k] [(integralModel O W).IsElliptic]
    (P : (W).toAffine.Point) :
    Nat.card (E.map (Int.castRingHom (ZMod p))).toAffine.Point •
      Affine.Point.reductionHom (v.valuation ℚ) P = 0 := by
  classical
  have : NeZero p := ⟨fun h ↦ v.ne_bot (by rw [hv, h]; simp)⟩
  have : Finite (ℤ ⧸ v.asIdeal) := Finite.of_equiv (ZMod p)
    ((Int.quotientSpanNatEquivZMod p).symm.trans (Ideal.quotEquivOfEq hv).symm).toEquiv
  rw [← card_point_reduction_baseChange E v p hv]
  exact card_nsmul_eq_zero'

end PrimeReduction

section AdicCompletion

open ValuativeRel

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]

/-- An equation integral over `u.adicCompletionIntegers F` is integral over the definitionally
equal valuation subring `Valued.v.valuationSubring` used by the reduction and formal-group APIs. -/
instance isIntegral_valuationSubring_of_adicCompletionIntegers {u : HeightOneSpectrum A}
    (E : WeierstrassCurve (u.adicCompletion F)) [h : E.IsIntegral (u.adicCompletionIntegers F)] :
    E.IsIntegral (Valued.v : Valuation (u.adicCompletion F)
      (WithZero (Multiplicative ℤ))).valuationSubring :=
  h

section FiniteResidue

variable {u : HeightOneSpectrum A} [Finite (A ⧸ u.asIdeal)]

/-- Over an adic completion with finite residue field, minimality over `𝒪[F_u]` agrees with
minimality over `u.adicCompletionIntegers F`. -/
@[simp]
theorem isMinimal_integer_adicCompletion_iff (E : WeierstrassCurve (u.adicCompletion F)) :
    E.IsMinimal 𝒪[u.adicCompletion F] ↔ E.IsMinimal (u.adicCompletionIntegers F) := by
  suffices ∀ (T : ValuationSubring (u.adicCompletion F)) [IsDiscreteValuationRing T],
      u.adicCompletionIntegers F = T →
        (E.IsMinimal T ↔ E.IsMinimal (u.adicCompletionIntegers F)) by
    have hR : IsDiscreteValuationRing (valuation (u.adicCompletion F)).valuationSubring :=
      inferInstanceAs (IsDiscreteValuationRing 𝒪[u.adicCompletion F])
    exact this (valuation (u.adicCompletion F)).valuationSubring
      (ValuationSubring.toSubring_injective (u.integer_eq_adicCompletionIntegers (K := F)).symm)
  rintro T _ rfl
  exact Iff.rfl

/-- A Weierstrass equation minimal over `u.adicCompletionIntegers F` is minimal over `𝒪[F_u]`. -/
instance isMinimal_integer_adicCompletion (E : WeierstrassCurve (u.adicCompletion F))
    [E.IsMinimal (u.adicCompletionIntegers F)] :
    E.IsMinimal 𝒪[u.adicCompletion F] :=
  (isMinimal_integer_adicCompletion_iff E).mpr inferInstance

/-- For any minimal Weierstrass equation `E` over `F_u`, the reduction of `E` at `𝒪[F_u]` has the
same point cardinality as the reduction of its integral model over `Valued.v.valuationSubring`
(including at bad reduction). -/
theorem natCard_point_reduction_adicCompletion (E : WeierstrassCurve (u.adicCompletion F))
    [E.IsMinimal (u.adicCompletionIntegers F)] :
    Nat.card (E.reduction 𝒪[u.adicCompletion F]).toAffine.Point =
      Nat.card ((integralModel (Valued.v : Valuation (u.adicCompletion F)
        (WithZero (Multiplicative ℤ))).valuationSubring E).map (residue _)).toAffine.Point := by
  suffices ∀ (T : ValuationSubring (u.adicCompletion F)) [IsDiscreteValuationRing T]
      [E.IsMinimal T], u.adicCompletionIntegers F = T →
      Nat.card (E.reduction T).toAffine.Point =
        Nat.card ((integralModel (Valued.v : Valuation (u.adicCompletion F)
          (WithZero (Multiplicative ℤ))).valuationSubring E).map (residue _)).toAffine.Point by
    have hR : IsDiscreteValuationRing (valuation (u.adicCompletion F)).valuationSubring :=
      inferInstanceAs (IsDiscreteValuationRing 𝒪[u.adicCompletion F])
    have hmin : E.IsMinimal (valuation (u.adicCompletion F)).valuationSubring :=
      inferInstanceAs (E.IsMinimal 𝒪[u.adicCompletion F])
    exact this (valuation (u.adicCompletion F)).valuationSubring
      (ValuationSubring.toSubring_injective (u.integer_eq_adicCompletionIntegers (K := F)).symm)
  rintro T _ _ rfl
  rw [reduction]
  rfl

variable (C : WeierstrassCurve (u.adicCompletionIntegers F)) [C.IsElliptic]

/-- An elliptic equation over `O_u` has good reduction at the ring of integers `𝒪[F_u]` of the
valuative relation of `F_u`, which is `O_u`. -/
instance hasGoodReduction_baseChange_adicCompletion :
    (C.baseChange (u.adicCompletion F)).HasGoodReduction 𝒪[u.adicCompletion F] := by
  -- Stating this for every valuation subring `T` equal to `O_u` lets the equality
  -- `integer_eq_adicCompletionIntegers` be substituted. The coercion of `valuationSubring` to a
  -- type is by definition that of `Valuation.integer`, which is `𝒪[F_u]`.
  suffices ∀ (T : ValuationSubring (u.adicCompletion F)) [IsDiscreteValuationRing T],
      u.adicCompletionIntegers F = T → (C.baseChange (u.adicCompletion F)).HasGoodReduction T by
    have hR : IsDiscreteValuationRing (valuation (u.adicCompletion F)).valuationSubring :=
      inferInstanceAs (IsDiscreteValuationRing 𝒪[u.adicCompletion F])
    exact this (valuation (u.adicCompletion F)).valuationSubring
      (ValuationSubring.toSubring_injective (u.integer_eq_adicCompletionIntegers (K := F)).symm)
  rintro T _ rfl
  have : (C.baseChange (u.adicCompletion F)).IsIntegral (u.adicCompletionIntegers F) := ⟨C, rfl⟩
  rw [hasGoodReduction_iff_isUnit_integralModel_Δ, integralModel_baseChange_self]
  exact C.isUnit_Δ

/-- The reduction at `𝒪[F_u]` of an elliptic equation over `O_u` has as many points as its
reduction at `Valued.v.valuationSubring`, the ring used by the reduction homomorphism. -/
theorem natCard_point_reduction_baseChange_adicCompletion :
    Nat.card ((C.baseChange (u.adicCompletion F)).reduction 𝒪[u.adicCompletion F]).toAffine.Point =
      Nat.card ((integralModel (Valued.v : Valuation (u.adicCompletion F)
        (WithZero (Multiplicative ℤ))).valuationSubring (C.baseChange (u.adicCompletion F))).map
          (residue _)).toAffine.Point := by
  have : (C.baseChange (u.adicCompletion F)).IsMinimal (u.adicCompletionIntegers F) :=
    (isMinimal_integer_adicCompletion_iff _).mp
      (C.hasGoodReduction_baseChange_adicCompletion.toIsMinimal)
  exact natCard_point_reduction_adicCompletion (C.baseChange (u.adicCompletion F))

end FiniteResidue

end AdicCompletion

end WeierstrassCurve
