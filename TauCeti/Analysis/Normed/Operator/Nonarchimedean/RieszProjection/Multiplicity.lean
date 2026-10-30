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

The complementary Fredholm factor of a Riesz splitting is a unit at its chosen scalar, so the
finite factor carries the whole good zero of the Fredholm series. Over a coefficient ring, a good
zero of order `h` therefore forces the finite projective range of the Riesz projector to have
constant rank `h` on `Spec R`, and its Fredholm factor to be exactly `(1 - a⁻¹ X) ^ h`. Ranks are
computed at the points of `Spec R` algebraically, so nilpotent coefficient information is not
discarded. Over a complete ultrametric field, the finite factor is a power of `1 - a⁻¹ X` whose
exponent is the dimension of the projector's range even without a good-zero hypothesis, and a good
zero of order `h` has a generalised eigenspace of dimension `h`.

## Main results

* `ContinuousLinearMap.IsRieszProjection.isGoodZero_charPowerSeries_matrixCoeff_mul`: the finite
  Fredholm factor has a good zero of the same order.
* `ContinuousLinearMap.IsRieszProjection.rankAtStalk_range`: the range has constant rank `h`.
* `ContinuousLinearMap.IsRieszProjection.charPowerSeries_matrixCoeff_mul_eq_pow`,
  `ContinuousLinearMap.IsRieszProjection.charPowerSeries_matrixCoeff_eq_pow_mul`: the finite
  factor is `(1 - a⁻¹ X) ^ h`, and the Fredholm series splits off this factor.
* `ContinuousLinearMap.IsRieszProjection.finrank_range`: over a field, the generalised eigenspace
  has dimension `h`.

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
  convert hunit using 1
  ext x : 1
  simp only [sub_apply, one_apply_eq_self, smul_apply, mul_apply_eq_comp, add_apply, comp_apply]
  abel

/-- The Fredholm factor on the finite Riesz summand inherits the good zero of the Fredholm series,
with the same order, because the complementary factor is a unit there. -/
theorem isGoodZero_charPowerSeries_matrixCoeff_mul (hE : IsRieszProjection u a h E)
    (hu : u.IsRowCompact) (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) :
    (u * E).matrixCoeff.charPowerSeries.IsGoodZero a h := by
  rw [hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hE.isIdempotentElem hE.commute] at hH
  exact ((hu.comp_clm E).isEntire_charPowerSeries.isGoodZero_mul_iff_of_isUnit
    (hu.comp_clm (1 - E)).isEntire_charPowerSeries
    (hE.isUnit_evalAt_charPowerSeries_complement hu)).mp hH

/-- On the finite projective range of a Riesz projection at `a`, the restriction `f` of `u`
differs from `μ = a⁻¹` by a nilpotent endomorphism, and the Fredholm factor `H_(uE)` is the
reversed characteristic polynomial `det (1 - X f)`. The additive group of the range is fixed
first, so that its endomorphisms form a ring. -/
private theorem exists_charPowerSeries_eq_projectiveCharpolyRev (hE : IsRieszProjection u a h E)
    (hu : u.IsRowCompact) {μ : R} (hμa : μ * a = 1) :
    letI : AddCommGroup E.range := inferInstance
    ∃ (_ : Module.Finite R E.range) (_ : Module.Projective R E.range)
      (f : Module.End R E.range), IsNilpotent (f - μ • 1) ∧
        (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : PowerSeries R) := by
  -- Fix the additive group before forming endomorphisms of the range, so their ring
  -- structure uses the same additive monoid as the submodule and its normed structure.
  let : AddCommGroup E.range := inferInstance
  have := (hE.isRowCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
  -- Restrict to the finite range, presented as a retract by the projector E.
  let v : E.range →L[R] E.range := u.restrict hE.mapsTo_range
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp x.property
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range := by
    exact ContinuousLinearMap.ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract
      E.range.subtypeL E.rangeRestrict hri
  have := (hE.isRowCompact hu).projective_range_of_isIdempotentElem hE.isIdempotentElem
  have hv := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM v
  let f : Module.End R E.range := v.toLinearMap
  refine ⟨inferInstance, inferInstance, f, ?_, ?_⟩
  · -- On this range, nilpotence of 1 - a u is equivalent to nilpotence of u - μ.
    have hC : IsNilpotent ((1 : Module.End R E.range) - a • f) := by
      refine ⟨h, ?_⟩
      have hrestrict : (1 : Module.End R E.range) - a • f =
          ((1 - a • u : C₀(I, R) →L[R] C₀(I, R)) : Module.End R C₀(I, R)).restrict
            hE.mapsTo_range_one_sub_smul := by
        ext x
        rfl
      rw [hrestrict]
      refine (Module.End.pow_restrict h
        (fun x hx ↦ hE.mapsTo_range_one_sub_smul hx)).trans ?_
      ext x : 1
      apply Subtype.ext
      have hx := congr($(hE.pow_mul_eq_zero) (x : C₀(I, R)))
      simpa only [LinearMap.coe_restrict_apply, ← toLinearMap_pow, coe_coe,
        mul_apply_eq_comp, hfix, zero_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] using hx
    have hscale : f - μ • (1 : Module.End R E.range) =
        (-μ) • ((1 : Module.End R E.range) - a • f) := by
      rw [smul_sub, smul_smul, neg_mul, hμa]
      module
    rw [hscale]
    exact hC.smul _
  · have hext : E.range.subtypeL.comp (v.comp E.rangeRestrict) = u * E := by
      ext x
      rfl
    -- Presentation independence transports the finite characteristic-polynomial formula.
    have hchar := charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM v
    rw [← hext, ← hv.charPowerSeries_eq hri, hchar]

/-- **Constant rank of the Riesz summand.** At a good zero of order `h` the range of a Riesz
projection, a finitely generated projective module, has rank `h` at every point of `Spec R`.
Ranks are computed algebraically, so nilpotent coefficients are retained; at order zero the range
is zero. -/
theorem rankAtStalk_range (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = h := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have hE0 := hE.eq_zero_of_order_zero
    have : Subsingleton E.range := ⟨by rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩; simp [hE0]⟩
    simp
  have ha := hH.isUnit hu.isEntire_charPowerSeries (Matrix.constantCoeff_charPowerSeries _) hh
  -- fix the additive group of the range, as in the statement of the restriction lemma
  let : AddCommGroup E.range := inferInstance
  obtain ⟨_, _, f, hf, hchar⟩ :=
    hE.exists_charPowerSeries_eq_projectiveCharpolyRev hu (Ring.inverse_mul_cancel a ha)
  have hP := (hE.isGoodZero_charPowerSeries_matrixCoeff_mul hu hH).isUnit_evalAt_hasseDeriv
  rw [hchar, PowerSeries.evalAt_hasseDeriv_coe] at hP
  exact f.rankAtStalk_eq_of_isNilpotent_sub_smul (Ring.inverse_mul_cancel a ha) hf hP p

/-- **The determinant of the Riesz summand.** At a good zero of order `h`, the Fredholm factor on
the finite Riesz summand is exactly `(1 - a⁻¹ X) ^ h`, with `a⁻¹ = Ring.inverse a`, over any
coefficient ring. At order zero the factor is one, even when the scalar is not a unit. -/
theorem charPowerSeries_matrixCoeff_mul_eq_pow (hE : IsRieszProjection u a h E)
    (hu : u.IsRowCompact) (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) :
    (u * E).matrixCoeff.charPowerSeries =
      (1 - PowerSeries.C (Ring.inverse a) * PowerSeries.X) ^ h := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp [hE.eq_zero_of_order_zero]
  have ha := hH.isUnit hu.isEntire_charPowerSeries (Matrix.constantCoeff_charPowerSeries _) hh
  let : AddCommGroup E.range := inferInstance
  obtain ⟨_, _, f, hf, hchar⟩ :=
    hE.exists_charPowerSeries_eq_projectiveCharpolyRev hu (Ring.inverse_mul_cancel a ha)
  have hP := hE.isGoodZero_charPowerSeries_matrixCoeff_mul hu hH
  simp_rw [hchar, PowerSeries.isGoodZero_iff, PowerSeries.evalAt_hasseDeriv_coe] at hP
  rw [hchar, f.projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul_of_isUnit
    (Ring.inverse_mul_cancel a ha) hf hP.1 hP.2]
  simp

/-- **Factorisation along a Riesz splitting.** At a good zero of order `h`, the Fredholm series
factors as `(1 - a⁻¹ X) ^ h`, with `a⁻¹ = Ring.inverse a`, times the Fredholm factor of the
complementary summand, which is a unit at `a`
(`ContinuousLinearMap.IsRieszProjection.isUnit_evalAt_charPowerSeries_complement`). -/
theorem charPowerSeries_matrixCoeff_eq_pow_mul (hE : IsRieszProjection u a h E)
    (hu : u.IsRowCompact) (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) :
    u.matrixCoeff.charPowerSeries =
      (1 - PowerSeries.C (Ring.inverse a) * PowerSeries.X) ^ h *
        (u * (1 - E)).matrixCoeff.charPowerSeries := by
  rw [← hE.charPowerSeries_matrixCoeff_mul_eq_pow hu hH,
    hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hE.isIdempotentElem hE.commute]

end Ring

section Field

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {a : K} {h : ℕ}

/-- The Fredholm factor on the finite Riesz summand is the expected pure power.
The nilpotence bound need not be the order of a zero. -/
theorem charPowerSeries_matrixCoeff_mul_eq_pow_finrank (hE : IsRieszProjection u a h E)
    (hu : u.IsRowCompact) :
    (u * E).matrixCoeff.charPowerSeries =
      (1 - PowerSeries.C a⁻¹ * PowerSeries.X) ^ Module.finrank K E.range := by
  by_cases ha : a = 0
  · have hC : (1 - a • u : C₀(I, K) →L[K] C₀(I, K)) = 1 := by
      ext x
      simp [ha]
    have hzero : E = 0 := by simpa only [hC, one_pow, one_mul] using hE.pow_mul_eq_zero
    simp [ha, hzero]
  let : AddCommGroup E.range := inferInstance
  obtain ⟨_, _, f, hf, hchar⟩ :=
    hE.exists_charPowerSeries_eq_projectiveCharpolyRev hu (inv_mul_cancel₀ ha)
  rw [hchar, LinearMap.projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul f _ hf]
  simp

/-- The dimension of the Riesz summand equals the order of the Fredholm zero, including
order zero. No discrete-valuation or spherical-completeness hypothesis is needed. -/
theorem finrank_range (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) :
    Module.finrank K E.range = h := by
  have hr := hE.rankAtStalk_range hu hH ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- Every stabilised generalised eigenspace has dimension equal to the order of the
corresponding Fredholm zero. -/
theorem finrank_ker_pow (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries.IsGoodZero a h) {n : ℕ} (hn : h ≤ n) :
    Module.finrank K (LinearMap.ker (((1 - a • u) ^ n : C₀(I, K) →L[K] C₀(I, K)) :
      Module.End K C₀(I, K))) = h := by
  rw [hE.ker_pow_eq hn, ← hE.range_eq_ker]
  exact hE.finrank_range hu hH

end Field

end IsRieszProjection

end ContinuousLinearMap
