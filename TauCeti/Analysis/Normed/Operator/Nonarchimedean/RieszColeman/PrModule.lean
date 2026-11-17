/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Decomposition
public import TauCeti.LinearAlgebra.End.Split
import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on modules with property (Pr)

Over a complete ultrametric normed commutative Tate ring `R`, a module `M` with property (Pr) is a
continuous linear retract `r ∘ i = id` of a model space `C₀(J, R)`. Let `u : M →L[R] M` be a
row-compact endomorphism (`ContinuousLinearMap.IsPrCompact`) whose Fredholm series admits a coprime
factorisation `H_u = Q * S`, where `Q` is a polynomial with invertible leading coefficient, `S` is
entire, and `Q` and `S` are coprime in `PowerSeries.IsEntire.subring R`. Since `H_u(0) = 1`, both
`Q(0)` and `S(0)` are automatically units of `R`, so normalising by `S(0)` reduces to `Q(0) = 1`
without changing `E` or `ker Q*(u)`.

Because `u.charPowerSeries` agrees with the Fredholm series of the extension `v = i ∘ u ∘ r` on
`C₀(J, R)`, and Riesz–Coleman projections compress along continuous linear retracts
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`), `u` admits a unique
Riesz–Coleman projection `E` at `Q`
(`ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`). The projector `E` is itself row
compact (`ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`), so its range `ker Q*(u)` is
a finitely generated projective `R`-module
(`ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact`,
`ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact`).

Passing to `B = 1 - lc(Q)⁻¹ Q*` (which vanishes at `0`), `c • Q*(v)` is the split-endomorphism
extension of `c • Q*(u)` along `r ∘ i = id` (`LinearMap.splitEnd_one_sub`), so
`LinearMap.kerSplitEndEquiv` identifies `ker Q*(v) ≃ₗ[R] ker Q*(u)` and transports the constant
rank `deg Q` on `Spec R` (`ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`).

Finally, if `F` is the Riesz–Coleman projection of `v` at `Q`, any `z ∈ ker r` satisfies `v z = 0`
and hence `v (F z) = 0`; writing `Q* = lc(Q) + (Q*).divX * X` and using that `lc(Q)` is a unit
yields `F (i (r y)) = F y` for all `y`. Consequently, with `E = r ∘ F ∘ i`, the extensions of
`u * E` and `u * (1 - E)` along `r ∘ i = id` equal `v * F` and `v * (1 - F)` on the nose.
Presentation independence then immediately gives `(u * E).charPowerSeries = Q` and
`(u * (1 - E)).charPowerSeries = S` when normalised by `Q(0) = 1`.

Over a complete ultrametric field `K`, `Q` is automatically nonzero with invertible leading
coefficient, and the constant rank specialises to `Module.finrank K (ker Q*(u)) = deg Q`.

## Main results

* `ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`: existence of the Riesz–Coleman
  projection of a row-compact operator on a (Pr) module.
* `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`: every Riesz–Coleman projection of a
  row-compact operator (with `lc(Q)` a unit) is row compact.
* `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact`:
  `ker Q*(u)` is finitely generated and projective over `R`.
* `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`: `ker Q*(u)` has
  constant rank `deg Q` at every prime ideal of `R`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq`: the Fredholm
  series of `u * E` is `Q` and that of `u * (1 - E)` is `S` when `Q(0) = 1`.
* `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`: over a field,
  `ker Q*(u)` has dimension `deg Q`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open scoped ZeroAtInfty PowerSeries TauCeti.RingOpNorm

open PowerSeries (IsEntire)

namespace ContinuousLinearMap

section PrModule

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {M : Type*} [SeminormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}

/-- **Existence of the Riesz–Coleman projection on a module with property (Pr).** Let `u` be a
row-compact endomorphism of a (Pr) module whose Fredholm series admits a coprime factorisation
`H_u = Q * S`, where `Q` is a polynomial with invertible leading coefficient and `S` is entire.
Then `u` admits a Riesz–Coleman projection at `Q` (which is unique by
`ContinuousLinearMap.IsRieszColemanProjection.unique`). -/
theorem IsPrCompact.exists_rieszColemanProjection (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hH
  exact ⟨_, ((hu.isRowCompact_comp i r).isRieszColemanProjection_rieszColemanProjection
    hH hQ hS hcop).comp_comp_of_retract hri⟩

omit [CompleteSpace R] in
/-- A Riesz–Coleman projection of a row-compact endomorphism of a (Pr) module is row compact
whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) : E.IsPrCompact := by
  rw [hE.eq_mul_aeval_divX_mul hQ]
  simpa only [mul_def] using ((hu.comp_clm _ hu.hasPr_source).comp_clm E hu.hasPr_source)

/-- The finite spectral summand `ker Q*(u)` of a row-compact endomorphism of a (Pr) module is
finitely generated whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact (hE.isPrCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The finite spectral summand `ker Q*(u)` of a row-compact endomorphism of a (Pr) module is
projective over `R` whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact (hE.isPrCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

omit [IsUltrametricDist R] [CompleteSpace R] [IsBoundedSMul R M] in
/-- On a retract `r ∘ i = id` into `N`, any Riesz–Coleman projection `F` of `v = i ∘ u ∘ r` at `Q`
with invertible leading coefficient satisfies `F (i (r y)) = F y`. -/
private theorem apply_retract_eq_of_isRieszColemanProjection {N : Type*}
    [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
    {i : M →L[R] N} {r : N →L[R] M} (hri : r.comp i = .id R M) {F : N →L[R] N}
    (hF : IsRieszColemanProjection (i.comp (u.comp r)) Q F) (hQ : IsUnit Q.leadingCoeff)
    (y : N) : F (i (r y)) = F y := by
  set v : N →L[R] N := i.comp (u.comp r)
  set z : N := y - i (r y)
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hvz : v z = 0 := by simp [v, z, hri']
  have hvFz : v (F z) = 0 := by
    have hc := congr($(hF.commute.eq) z)
    simpa only [mul_apply_eq_comp, hvz, map_zero] using hc
  have hrev : Q.reverse = C Q.leadingCoeff + Q.reverse.divX * X := by
    rw [← coeff_zero_reverse, add_comm, mul_comm Q.reverse.divX X, X_mul_divX_add]
  have hQz : Q.leadingCoeff • F z = 0 := by
    have hz := congr($(hF.aeval_reverse_mul_eq_zero) z)
    rw [hrev, map_add, aeval_C, map_mul, aeval_X, Algebra.algebraMap_eq_smul_one] at hz
    simpa only [mul_apply_eq_comp, add_apply, smul_apply, one_apply_eq_self, hvFz, map_zero,
      add_zero, zero_apply] using hz
  have hFz : F z = 0 := by
    have hc := Ring.inverse_mul_cancel Q.leadingCoeff hQ
    simpa only [smul_smul, hc, one_smul, smul_zero] using
      congrArg (Ring.inverse Q.leadingCoeff • ·) hQz
  exact (sub_eq_zero.mp (by simpa only [z, map_sub] using hFz)).symm

/-- **Determinant on the finite summand of a (Pr) module.** For a coprime polynomial factor `Q` of
`H_u = Q * S` with `Q(0) = 1` and `lc(Q)` a unit, the Fredholm series of `u * E` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_eq (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hH
  set v : C₀(J, R) →L[R] C₀(J, R) := i.comp (u.comp r)
  set F : C₀(J, R) →L[R] C₀(J, R) := v.rieszColemanProjection Q
  have hF : IsRieszColemanProjection v Q F :=
    hv.isRieszColemanProjection_rieszColemanProjection hH hQ hS hcop
  have hEq : E = r.comp (F.comp i) := hE.unique (hF.comp_comp_of_retract hri)
  have huE : (u * E).IsPrCompact := by simpa only [mul_def] using hu.comp_clm E hu.hasPr_source
  have hext : i.comp ((u * E).comp r) = v * F := by
    ext y : 1
    have hFy := apply_retract_eq_of_isRieszColemanProjection hri hF hQ y
    simpa only [comp_apply, mul_apply_eq_comp, hEq, v] using congrArg v hFy
  rw [huE.charPowerSeries_eq hri, hext]
  exact hF.charPowerSeries_matrixCoeff_mul_eq hv hH hQ0 hQ hS hcop

/-- **Determinant on the complementary summand of a (Pr) module.** For a coprime polynomial factor
`Q` of `H_u = Q * S` with `Q(0) = 1` and `lc(Q)` a unit, the Fredholm series of `u * (1 - E)` is
`S`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hH
  set v : C₀(J, R) →L[R] C₀(J, R) := i.comp (u.comp r)
  set F : C₀(J, R) →L[R] C₀(J, R) := v.rieszColemanProjection Q
  have hF : IsRieszColemanProjection v Q F :=
    hv.isRieszColemanProjection_rieszColemanProjection hH hQ hS hcop
  have hEq : E = r.comp (F.comp i) := hE.unique (hF.comp_comp_of_retract hri)
  have hu1E : (u * (1 - E)).IsPrCompact := by
    simpa only [mul_def] using hu.comp_clm (1 - E) hu.hasPr_source
  have hext : i.comp ((u * (1 - E)).comp r) = v * (1 - F) := by
    ext y : 1
    have hFy := apply_retract_eq_of_isRieszColemanProjection hri hF hQ y
    simpa only [comp_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self, map_sub, hEq, v]
      using congrArg (fun z ↦ v y - v z) hFy
  rw [hu1E.charPowerSeries_eq hri, hext]
  exact hF.charPowerSeries_matrixCoeff_mul_one_sub_eq hv hH hQ0 hQ hS hcop

end PrModule

section Ring

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M]
  [ContinuousConstSMul R M] {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}

omit [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R] in
/-- Scaling a linear map by a unit leaves its kernel unchanged. -/
private theorem ker_smul_eq_of_mul_eq_one {N : Type*} [AddCommGroup N] [Module R N]
    {c d : R} (hcd : c * d = 1) (g : N →ₗ[R] N) :
    LinearMap.ker (c • g) = LinearMap.ker g := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.smul_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have := congrArg (d • ·) h
  simpa only [smul_smul, mul_comm d c, hcd, one_smul, smul_zero] using this

omit [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R] in
/-- Extending `u` along a continuous linear retract `r ∘ i = id` preserves `ker Q*(u)` up to
linear equivalence whenever `Q` has invertible leading coefficient. -/
private noncomputable def ker_aeval_reverse_retract_equiv {N : Type*}
    [SeminormedAddCommGroup N] [Module R N] [ContinuousConstSMul R N]
    {i : M →L[R] N} {r : N →L[R] M} (hri : r.comp i = .id R M) (hQ : IsUnit Q.leadingCoeff) :
    LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse : N →L[R] N) : N →ₗ[R] N) ≃ₗ[R]
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
  let c : R := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : R[X] := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have hri' : r.toLinearMap.comp i.toLinearMap = LinearMap.id := by
    simpa only [toLinearMap_comp, coe_id] using congrArg ContinuousLinearMap.toLinearMap hri
  set v : N →L[R] N := i.comp (u.comp r)
  have hsplit :
      LinearMap.splitEnd r.toLinearMap i.toLinearMap hri'
        (c • (Polynomial.aeval u Q.reverse : M →L[R] M).toLinearMap) =
      c • (Polynomial.aeval v Q.reverse : N →L[R] N).toLinearMap := by
    have hBu : c • (Polynomial.aeval u Q.reverse : M →L[R] M).toLinearMap =
        1 - (Polynomial.aeval u B : M →L[R] M).toLinearMap := by
      ext x; simp [B, Algebra.algebraMap_eq_smul_one]
    have hBv : c • (Polynomial.aeval v Q.reverse : N →L[R] N).toLinearMap =
        1 - (Polynomial.aeval v B : N →L[R] N).toLinearMap := by
      ext x; simp [B, Algebra.algebraMap_eq_smul_one]
    rw [hBu, hBv, LinearMap.splitEnd_one_sub]
    congr 1
    exact (congrArg ContinuousLinearMap.toLinearMap (aeval_comp_comp_of_retract hri u hB0)).symm
  have e := LinearMap.kerSplitEndEquiv r.toLinearMap i.toLinearMap hri'
    (c • (Polynomial.aeval u Q.reverse : M →L[R] M).toLinearMap)
  rw [hsplit] at e
  exact (LinearEquiv.ofEq _ _ (ker_smul_eq_of_mul_eq_one hc _).symm).trans
    (e.trans (LinearEquiv.ofEq _ _ (ker_smul_eq_of_mul_eq_one hc _)))

/-- **Constant rank of `ker Q*(u)` on a (Pr) module.** For a coprime factorisation `H_u = Q * S`
with invertible leading coefficient, `ker Q*(u)` has rank `deg Q` at every prime ideal of `R`. No
Noetherianity, reducedness, or bounded scalar action hypothesis is needed. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) p =
      Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hH
  have heq := ker_aeval_reverse_retract_equiv (u := u) hri hQ
  have hker : Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) =
      Module.rankAtStalk (R := R)
        (LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse :
          C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R))) := by
    let : AddCommGroup
        (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := inferInstance
    let : AddCommGroup (LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse :
        C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R))) := inferInstance
    exact Module.rankAtStalk_eq_of_equiv heq.symm
  rw [hker]
  exact hv.rankAtStalk_ker_aeval_reverse hH hQ hS hcop p

omit [ContinuousConstSMul R M] in
/-- The range of a Riesz–Coleman projection on a (Pr) module has constant rank `deg Q` at every
prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  rw [hE.range_eq_ker]
  exact hu.rankAtStalk_ker_aeval_reverse hH hQ hS hcop p

end Ring

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u E : M →L[K] M} {Q : K[X]} {S : K⟦X⟧}

/-- Over a complete ultrametric field, `ker Q*(u)` on a (Pr) module has dimension `deg Q`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : K⟦X⟧) * S) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[K] M) : M →ₗ[K] M)) =
      Q.natDegree := by
  have hQne : Q ≠ 0 := fun h ↦ by
    have hc := congrArg PowerSeries.constantCoeff hH
    simp [h] at hc
  have hQ : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQne)
  have hr := hu.rankAtStalk_ker_aeval_reverse hH hQ hS hcop ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

omit [ContinuousConstSMul K M] in
/-- Over a complete ultrametric field, the range of a Riesz–Coleman projection on a (Pr) module has
dimension `deg Q`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact [IsBoundedSMul K M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : K⟦X⟧) * S) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  rw [hE.range_eq_ker]
  exact hu.finrank_ker_aeval_reverse hH hS hcop

end Field

end ContinuousLinearMap
