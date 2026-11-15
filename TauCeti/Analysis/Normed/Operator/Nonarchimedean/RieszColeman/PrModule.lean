/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Factorization
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Splitting
import TauCeti.RingTheory.PowerSeries.Dvd
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on modules with property (Pr)

Over a complete ultrametric Tate ring `R`, a module `M` with property `(Pr)` is a continuous linear
retract `r ∘ i = id` of `C₀(J, R)`. Existence of Riesz–Coleman projections compresses the
model-space projector (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`), row
compactness of `E` and finite projectivity of `ker Q*(u)` use `mul_aeval_divX_mul_eq_self`, and
`E.range` and `E.ker` inherit `(Pr)` and row-compact restrictions via `rangeRestrict` and
`projectionOntoKer`. Stalk rank `Q.natDegree` and `det (1 - X u|_{range E}) = Q` (`Q.coeff 0 = 1`)
transport via `ContinuousLinearMap.kerAevalCompCompEquiv`, while Fredholm multiplicativity
(`TauCeti.charPowerSeries_add_of_comp_eq_zero`) yields `(u * (1 - E)).charPowerSeries = S`.

## Main results

* `ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`,
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`,
  `finite_ker_aeval_reverse_of_isPrCompact`, and `projective_ker_aeval_reverse_of_isPrCompact`:
  existence, row compactness, and finite projectivity of `ker Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact_restrict_range`,
  `charPowerSeries_restrict_range`, `isPrCompact_restrict_ker`, `charPowerSeries_restrict_ker`, and
  `isCoprime_charPowerSeries_restrict_ker`: restrictions and coprimality on `E.range` and `E.ker`.
* `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`, `finrank_ker_aeval_reverse`, and
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`,
  `finrank_range_of_isPrCompact`: stalk rank and field dimension `Q.natDegree`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_eq`,
  `charPowerSeries_mul_one_sub_eq`, `charPowerSeries_restrict_range_eq`,
  `charPowerSeries_restrict_ker_eq`, and `projectiveCharpolyRev_restrict_range_of_isPrCompact`:
  normalized determinant formulas (`Q.coeff 0 = 1`).

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4, Theorem A4.2.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*, Algebra
  Number Theory **13** (2019), 93–158, §2.2, Theorem 2.2.2.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open scoped ZeroAtInfty TauCeti.RingOpNorm PowerSeries

namespace ContinuousLinearMap

section PrModule

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u E : M →L[R] M} {Q : R[X]}

/-- **Existence of the Riesz–Coleman projection on a module with property (Pr).** Every coprime
factorization `H_u = Q * S` with `IsUnit Q.leadingCoeff` admits a Riesz–Coleman projection. -/
theorem IsPrCompact.exists_rieszColemanProjection (hu : u.IsPrCompact) {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hfac
  exact ⟨_, ((hu.isRowCompact_comp i r).isRieszColemanProjection_rieszColemanProjection
    hQ hS hfac hcop).comp_comp_of_retract hri⟩

omit [CompleteSpace R] in
/-- Every Riesz–Coleman projection of a row-compact endomorphism on a `(Pr)` module with
`IsUnit Q.leadingCoeff` is row compact. -/
theorem IsRieszColemanProjection.isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) : E.IsPrCompact := by
  rw [← hE.mul_aeval_divX_mul_eq_self hQ]
  simpa only [mul_def] using (hu.comp_clm _ hu.hasPr_source).comp_clm E hu.hasPr_source

/-- For a row-compact endomorphism `u` on a `(Pr)` module admitting a Riesz–Coleman projection for
`Q` with `IsUnit Q.leadingCoeff`, `ker Q*(u)` is finitely generated over `R`. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Finite R (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact (hE.isPrCompact hQ hu).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- For a row-compact endomorphism `u` on a `(Pr)` module admitting a Riesz–Coleman projection for
`Q` with `IsUnit Q.leadingCoeff`, `ker Q*(u)` is projective over `R`. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Projective R (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact (hE.isPrCompact hQ hu).projective_range_of_isIdempotentElem hE.isIdempotentElem

omit [CompleteSpace R] in
/-- Restricting a row-compact endomorphism `u` on a `(Pr)` module to `E.range` is row compact. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict hE.mapsTo_range).IsPrCompact :=
  hu.restrict_range_of_isIdempotentElem hE.isIdempotentElem hE.mapsTo_range

/-- On a `(Pr)` module, `(u|_{E.range}).charPowerSeries = (u * E).charPowerSeries`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict hE.mapsTo_range).charPowerSeries = (u * E).charPowerSeries :=
  hu.charPowerSeries_restrict_range_of_isIdempotentElem hE.isIdempotentElem hE.mapsTo_range

omit [CompleteSpace R] in
/-- Restricting a row-compact endomorphism `u` on a `(Pr)` module to `E.ker` is row compact. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict hE.mapsTo_ker).IsPrCompact :=
  hu.restrict_ker_of_isIdempotentElem hE.isIdempotentElem hE.mapsTo_ker

/-- On a `(Pr)` module, `(u|_{E.ker}).charPowerSeries = (u * (1 - E)).charPowerSeries`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict hE.mapsTo_ker).charPowerSeries = (u * (1 - E)).charPowerSeries :=
  hu.charPowerSeries_restrict_ker_of_isIdempotentElem hE.isIdempotentElem hE.mapsTo_ker

/-- For a Riesz–Coleman projection `E` of a row-compact endomorphism `u` on a `(Pr)` module for `Q`
with `IsUnit Q.leadingCoeff`, `Q` is coprime to `(u|_{E.ker}).charPowerSeries`. -/
theorem IsRieszColemanProjection.isCoprime_charPowerSeries_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u.restrict hE.mapsTo_ker).charPowerSeries,
        IsEntire.mem_subring.mpr (hE.isPrCompact_restrict_ker hu).isEntire_charPowerSeries⟩ := by
  convert hE.isCoprime_charPowerSeries_complement hQ hu using 1
  exact Subtype.ext (hE.charPowerSeries_restrict_ker hu)

end PrModule

section Ring

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M]
  {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}

/-- **Constant stalk rank of `ker Q*(u)` on a `(Pr)` module.** Under `H_u = Q * S` coprime with
`IsUnit Q.leadingCoeff`, `ker Q*(u)` has rank `Q.natDegree` on `Spec R`. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse [ContinuousConstSMul R M]
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S) (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)) p = Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hfac
  let : AddCommGroup (LinearMap.ker (Polynomial.aeval u Q.reverse : Module.End R M)) :=
    inferInstance
  let : AddCommGroup (LinearMap.ker (Polynomial.aeval (i.comp (u.comp r)) Q.reverse :
    Module.End R C₀(J, R))) := inferInstance
  rw [Module.rankAtStalk_eq_of_equiv
    (kerAevalCompCompEquiv hri u (by rwa [coeff_zero_reverse])).symm.toLinearEquiv]
  exact hv.rankAtStalk_ker_aeval_reverse hQ hS hfac hcop p

/-- **Constant stalk rank of `range E` on a `(Pr)` module.** Under `H_u = Q * S` coprime with
`IsUnit Q.leadingCoeff`, `range E` has rank `Q.natDegree` on `Spec R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S) (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  rw [hE.range_eq_ker]; exact hu.rankAtStalk_ker_aeval_reverse hQ hS hfac hcop p

/-- **Reversed characteristic polynomial on a `(Pr)` module.** Under `H_u = Q * S` coprime with
`IsUnit Q.leadingCoeff` and `Q.coeff 0 = 1`, `det (1 - X u|_{range E}) = Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact
    [IsBoundedSMul R M] (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S) (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    letI := (hE.isPrCompact hQ hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
    letI := (hE.isPrCompact hQ hu).projective_range_of_isIdempotentElem hE.isIdempotentElem
    ((u.restrict hE.mapsTo_range : E.range →L[R] E.range) :
      Module.End R E.range).projectiveCharpolyRev = Q := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hfac
  have hF := hv.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop
  set F := (i.comp (u.comp r)).rieszColemanProjection Q
  let : AddCommGroup F.range := inferInstance
  let : AddCommGroup E.range := inferInstance
  have := (hF.isRowCompact hQ hv).finite_range_of_isIdempotentElem hF.isIdempotentElem
  have := (hF.isRowCompact hQ hv).projective_range_of_isIdempotentElem hF.isIdempotentElem
  have := (hE.isPrCompact hQ hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
  have := (hE.isPrCompact hQ hu).projective_range_of_isIdempotentElem hE.isIdempotentElem
  let e : F.range ≃ₗ[R] E.range := (LinearEquiv.ofEq _ _ hF.range_eq_ker).trans
    ((kerAevalCompCompEquiv hri u (by rwa [coeff_zero_reverse])).toLinearEquiv.trans
      (LinearEquiv.ofEq _ _ hE.range_eq_ker.symm))
  have hinter (y : F.range) : (u.restrict hE.mapsTo_range).toLinearMap (e y) =
      e ((i.comp (u.comp r) |>.restrict hF.mapsTo_range).toLinearMap y) := by
    have he (z : F.range) : (e z : M) = r z := by simp [e]
    apply Subtype.ext
    exact (coe_restrict_apply (f := u) (fun _ hx ↦ hE.mapsTo_range hx) (e y)).trans <| by
      rw [he, he]
      exact (DFunLike.congr_fun hri (u (r y.1))).symm.trans
        (congrArg r (coe_restrict_apply (f := i.comp (u.comp r))
          (fun _ hx ↦ hF.mapsTo_range hx) y).symm)
  have heq := LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq
    (θ := RingHom.id R) (θ' := RingHom.id R) e hinter
  rw [Polynomial.map_id] at heq
  exact heq.trans (hF.projectiveCharpolyRev_restrict_range hv hQ0 hQ hS hfac hcop)

/-- **Fredholm series of `u * E` on a `(Pr)` module.** Under `H_u = Q * S` coprime with
`IsUnit Q.leadingCoeff` and `Q.coeff 0 = 1`, `(u * E).charPowerSeries = (Q : R⟦X⟧)`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_eq [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hfac
  have hv := hu.isRowCompact_comp i r
  have hF := hv.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hEr (y : C₀(J, R)) : E (r y) = r ((i.comp (u.comp r)).rieszColemanProjection Q y) := by
    rw [hE.unique (hF.comp_comp_of_retract hri)]
    simp only [comp_apply, ← apply_comp_apply_of_mem_closure_adjoin hri hF.mem_closure_adjoin, hri']
  have hext : i.comp ((u * E).comp r) =
      i.comp (u.comp r) * (i.comp (u.comp r)).rieszColemanProjection Q :=
    ContinuousLinearMap.ext fun y ↦ by simp [mul_apply_eq_comp, hEr]
  rw [mul_def, (hu.comp_clm E hu.hasPr_source).charPowerSeries_eq hri, ← mul_def, hext]
  exact hF.charPowerSeries_matrixCoeff_mul_eq hv hQ0 hQ hS hfac hcop

/-- **Fredholm series of `u * (1 - E)` on a `(Pr)` module.** Under `H_u = Q * S` coprime with
`IsUnit Q.leadingCoeff` and `Q.coeff 0 = 1`, `(u * (1 - E)).charPowerSeries = S`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  have hsum : u * E + u * (1 - E) = u := by rw [← mul_add u E (1 - E), add_sub_cancel, mul_one]
  have hEc : E * (1 - E) = 0 := by rw [mul_sub E 1 E, mul_one, hE.isIdempotentElem.eq, sub_self]
  have hzero : (u * E).comp (u * (1 - E)) = 0 := by
    rw [← mul_def, mul_assoc, ← mul_assoc E, ← hE.commute.eq, mul_assoc u E, hEc, mul_zero,
      mul_zero]
  have hmul := TauCeti.charPowerSeries_add_of_comp_eq_zero
    (hu.comp_clm E hu.hasPr_source) (hu.comp_clm (1 - E) hu.hasPr_source) hzero
  rw [← mul_def, ← mul_def, hsum, hfac, hE.charPowerSeries_mul_eq hu hQ0 hQ hS hfac hcop] at hmul
  exact (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hQ0])).mul_left_cancel hmul.symm

/-- Under `H_u = Q * S` coprime with `IsUnit Q.leadingCoeff` and `Q.coeff 0 = 1`, `u|_{E.range}` has
Fredholm series `(Q : R⟦X⟧)`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_range_eq [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict hE.mapsTo_range).charPowerSeries = (Q : R⟦X⟧) :=
  (hE.charPowerSeries_restrict_range hu).trans (hE.charPowerSeries_mul_eq hu hQ0 hQ hS hfac hcop)

/-- Under `H_u = Q * S` coprime with `IsUnit Q.leadingCoeff` and `Q.coeff 0 = 1`, `u|_{E.ker}` has
Fredholm series `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker_eq [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict hE.mapsTo_ker).charPowerSeries = S :=
  (hE.charPowerSeries_restrict_ker hu).trans
    (hE.charPowerSeries_mul_one_sub_eq hu hQ0 hQ hS hfac hcop)

end Ring

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u E : M →L[K] M} {Q : K[X]} {S : K⟦X⟧}

/-- Over a complete ultrametric field, `ker Q*(u)` on a `(Pr)` space under `H_u = Q * S` coprime
has dimension `Q.natDegree`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse (hu : u.IsPrCompact) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : K⟦X⟧) * S) (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[K] M)) = Q.natDegree := by
  have hQ := PowerSeries.isUnit_leadingCoeff_of_coe_dvd u.charPowerSeries_ne_zero ⟨S, hfac⟩
  have hr := hu.rankAtStalk_ker_aeval_reverse hQ hS hfac hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[K] M)) := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, `range E` on a `(Pr)` space under `H_u = Q * S` coprime has
dimension `Q.natDegree`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact [IsBoundedSMul K M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : K⟦X⟧) * S) (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  rw [hE.range_eq_ker]; exact hu.finrank_ker_aeval_reverse hS hfac hcop

end Field

end ContinuousLinearMap
