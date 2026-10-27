/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Splitting
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Idempotent
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule
public import TauCeti.Algebra.Ring.SpectralIdempotent
public import TauCeti.LinearAlgebra.Charpoly.Nilpotent
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero

/-!
# Multiplicity of a Fredholm zero and the Riesz summand

The complementary Fredholm factor of a Riesz splitting is a unit at its chosen scalar.
Over a complete ultrametric field, the finite factor is a power of `1 - a⁻¹ X` whose
exponent is the dimension of the projector's range. Consequently a good zero of order `h`
has a generalised eigenspace of dimension `h`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7, Proposition 12.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

namespace IsRieszProjection

section Ring

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [NormOneClass R] [TauCeti.NormedRing.IsTate R]
  [IsUltrametricDist R] [CompleteSpace R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {a : R} {h : ℕ}

/-- The Fredholm factor on the complementary Riesz summand is a unit at the chosen scalar.
This retains the unit assertion over coefficient rings with zero divisors. -/
theorem isUnit_evalAt_charPowerSeries_complement (hE : IsRieszProjection u a h E)
    (hu : u.IsRowCompact) :
    IsUnit ((u * (1 - E)).matrixCoeff.charPowerSeries.evalAt a) := by
  apply (hu.comp_clm (1 - E)).isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul
  have hunit := _root_.IsIdempotentElem.isUnit_add_mul_one_sub
    (A := C₀(I, R) →L[R] C₀(I, R)) hE.isIdempotentElem
    hE.one_sub_smul_mul_inverse hE.inverse_mul_one_sub_smul
    hE.mul_inverse_eq_zero hE.inverse_mul_eq_zero
  convert hunit using 1
  ext x : 1
  simp only [sub_apply, one_apply_eq_self, smul_apply, mul_apply_eq_comp, add_apply, comp_apply]
  abel

end Ring

section Field

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {a : K} {h : ℕ}

/-- The Fredholm factor on the finite Riesz summand is the expected pure power.
The nilpotence bound need not be the order of a zero. -/
theorem charPowerSeries_matrixCoeff_mul_eq_pow_finrank (hE : IsRieszProjection u a h E)
    (hu : u.IsRowCompact) (ha : a ≠ 0) :
    (u * E).matrixCoeff.charPowerSeries =
      (1 - PowerSeries.C a⁻¹ * PowerSeries.X) ^ Module.finrank K E.range := by
  -- Fix the additive group before forming endomorphisms of the range, so their ring
  -- structure uses the same additive monoid as the submodule and its normed structure.
  let : AddCommGroup E.range := inferInstance
  have := (hE.isRowCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
  -- Restrict to the finite range, presented as a retract by the projector E.
  let v : E.range →L[K] E.range := u.restrict hE.mapsTo_range
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp x.property
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id K E.range := by
    exact ContinuousLinearMap.ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr K E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract
      E.range.subtypeL E.rangeRestrict hri
  have hv := isPrCompact_of_finite (R := K) (M := E.range) (L := E.range) hM hM v
  let f : Module.End K E.range := v.toLinearMap
  -- On this range, nilpotence of 1 - a u is equivalent to nilpotence of u - a⁻¹.
  have hnil : IsNilpotent (f - a⁻¹ • (1 : Module.End K E.range)) := by
    have hC : IsNilpotent ((1 : Module.End K E.range) - a • f) := by
      refine ⟨h, ?_⟩
      have hrestrict : (1 : Module.End K E.range) - a • f =
          ((1 - a • u : C₀(I, K) →L[K] C₀(I, K)) : Module.End K C₀(I, K)).restrict
            hE.mapsTo_range_one_sub_smul := by
        ext x
        rfl
      rw [hrestrict]
      refine (Module.End.pow_restrict h
        (fun x hx ↦ hE.mapsTo_range_one_sub_smul hx)).trans ?_
      ext x : 1
      apply Subtype.ext
      have hx := congr($(hE.pow_mul_eq_zero) (x : C₀(I, K)))
      simpa only [LinearMap.coe_restrict_apply, ← toLinearMap_pow, coe_coe,
        mul_apply_eq_comp, hfix, zero_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] using hx
    have hscale : f - a⁻¹ • (1 : Module.End K E.range) =
        (-a⁻¹) • ((1 : Module.End K E.range) - a • f) := by
      simp only [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ ha, neg_smul, one_smul]
      module
    rw [hscale]
    exact hC.smul _
  have hext : E.range.subtypeL.comp (v.comp E.rangeRestrict) = u * E := by
    ext x
    rfl
  -- Presentation independence transports the finite characteristic-polynomial formula.
  have hchar := charPowerSeries_eq_projectiveCharpolyRev (R := K) (M := E.range) hM v
  rw [← hext, ← hv.charPowerSeries_eq hri, hchar,
    LinearMap.projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul f _ hnil]
  simp

/-- The dimension of the Riesz summand equals the order of the Fredholm zero, including
order zero. No discrete-valuation or spherical-completeness hypothesis is needed. -/
theorem finrank_range (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) :
    Module.finrank K E.range = h := by
  by_cases hh : h = 0
  · subst h
    have hrange : E.range = ⊥ := by
      rw [hE.eq_zero_of_order_zero]
      exact LinearMap.range_zero
    rw [hrange]
    exact finrank_bot K C₀(I, K)
  have ha : a ≠ 0 :=
    (hH.isUnit hu.isEntire_charPowerSeries (Matrix.constantCoeff_charPowerSeries _)
      (Nat.pos_of_ne_zero hh)).ne_zero
  let n := Module.finrank K E.range
  let S := (u * (1 - E)).matrixCoeff.charPowerSeries
  have hS : S.IsEntire := (hu.comp_clm (1 - E)).isEntire_charPowerSeries
  have hSa : IsUnit (S.evalAt a) := hE.isUnit_evalAt_charPowerSeries_complement hu
  -- Rewrite the normalised finite factor in the coordinate centred at a.
  have hlinear : (1 - PowerSeries.C a⁻¹ * PowerSeries.X : PowerSeries K) =
      (PowerSeries.X - PowerSeries.C a) * PowerSeries.C (-a⁻¹) := by
    have hmul : PowerSeries.C a * PowerSeries.C a⁻¹ = (1 : PowerSeries K) := by
      rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    rw [map_neg]
    linear_combination -hmul
  have hfactor : u.matrixCoeff.charPowerSeries =
      (PowerSeries.X - PowerSeries.C a) ^ n * (PowerSeries.C ((-a⁻¹) ^ n) * S) := by
    rw [hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hE.isIdempotentElem hE.commute,
      hE.charPowerSeries_matrixCoeff_mul_eq_pow_finrank hu ha, hlinear, mul_pow,
      ← map_pow, mul_assoc]
  have hG : (PowerSeries.C ((-a⁻¹) ^ n) * S).IsEntire :=
    (PowerSeries.isEntire_C _).mul hS
  have hGa : IsUnit ((PowerSeries.C ((-a⁻¹) ^ n) * S).evalAt a) := by
    rw [(PowerSeries.isEntire_C _).evalAt_mul hS, PowerSeries.evalAt_C,
      Algebra.algebraMap_self_apply]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero n (neg_ne_zero.mpr (inv_ne_zero ha)))).mul hSa
  have horder : ((PowerSeries.X - PowerSeries.C a) ^ n *
      (PowerSeries.C ((-a⁻¹) ^ n) * S)).IsGoodZero a n :=
    hG.isGoodZero_X_sub_C_pow_mul_iff.mpr hGa
  rw [← hfactor] at horder
  exact (hH.unique horder).symm

/-- Every stabilised generalised eigenspace has dimension equal to the order of the
corresponding Fredholm zero. -/
theorem finrank_ker_pow (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) {n : ℕ} (hn : h ≤ n) :
    Module.finrank K (LinearMap.ker (((1 - a • u) ^ n : C₀(I, K) →L[K] C₀(I, K)) :
      Module.End K C₀(I, K))) = h := by
  rw [hE.ker_pow_eq hn, ← hE.range_eq_ker]
  exact hE.finrank_range hu hH

/-- The finite factor in a Riesz splitting has the precise exponent given by the order of
the Fredholm zero. At order zero the factor is one, even when the scalar is zero. -/
theorem charPowerSeries_matrixCoeff_mul_eq_pow (hE : IsRieszProjection u a h E)
    (hu : u.IsRowCompact) (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) :
    (u * E).matrixCoeff.charPowerSeries = (1 - PowerSeries.C a⁻¹ * PowerSeries.X) ^ h := by
  by_cases hh : h = 0
  · subst h
    simp [hE.eq_zero_of_order_zero]
  have ha := (hH.isUnit hu.isEntire_charPowerSeries (Matrix.constantCoeff_charPowerSeries _)
    (Nat.pos_of_ne_zero hh)).ne_zero
  rw [hE.charPowerSeries_matrixCoeff_mul_eq_pow_finrank hu ha, hE.finrank_range hu hH]

end Field

end IsRieszProjection

end ContinuousLinearMap
