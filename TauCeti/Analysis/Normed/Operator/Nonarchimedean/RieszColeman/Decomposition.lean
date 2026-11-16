/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
import TauCeti.Algebra.Polynomial.AlgebraMap
import TauCeti.Algebra.Ring.SpectralIdempotent
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Idempotent
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coprime
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Splitting
import TauCeti.Analysis.Normed.Operator.RowCompact.Idempotent
import TauCeti.Analysis.Polynomial.Coleman.Coprime
import TauCeti.LinearAlgebra.End.Split
import TauCeti.RingTheory.Idempotents.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import TauCeti.RingTheory.PowerSeries.Entire.Division
import TauCeti.Topology.Algebra.Algebra.Center
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman spectral decomposition for coprime polynomial factors

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, `M` a seminormed
`R`-module with property (Pr), and `u : M →L[R] M` a row-compact endomorphism with Fredholm series
`H_u(T) = det (1 - T u)`. Suppose `H_u` factors as

`H_u = Q · S`,

where `Q : R[X]` has invertible leading coefficient, `S : R⟦X⟧` is entire, and `Q` and `S` are
coprime in the ring of entire series `PowerSeries.IsEntire.subring R` (evaluating at `0` shows that
`Q(0)` is automatically a unit). This file constructs the unique Riesz–Coleman projection `E` of
`u` for `Q` (`ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`, and on model spaces
`ContinuousLinearMap.IsRowCompact.exists_rieszColemanProjection`), yielding the closed `u`-stable
topological splitting

`M = ker Q*(u) ⊕ range Q*(u)`

(`ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`), where `Q* = Q.reverse`.

The finite summand `range E = ker Q*(u)` is finitely generated and projective
(`ContinuousLinearMap.IsRieszColemanProjection.finite_range_of_isPrCompact`,
`ContinuousLinearMap.IsRieszColemanProjection.projective_range_of_isPrCompact`), of constant rank
`deg Q` on `Spec R`
(`ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`,
`ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`); over a field its dimension is
`deg Q` (`ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`,
`ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`). The restriction of `u` to `range E`
is invertible (`ContinuousLinearMap.IsRieszColemanProjection.equivRange`). Under the normalisation
`Q(0) = 1`, `u|_{range E}` has reversed characteristic polynomial `Q`
(`ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range`,
`ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact`,
`ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_range`), while the
complementary summand `ker E = range Q*(u)` has Fredholm series `S`
(`ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub`).

## Proof method

Evaluating `H_u = Q · S` at `0` shows `Q(0)` is a unit, so rescaling `Q` and `S` reduces the
existence and rank statements to the normalised case `Q(0) = 1`. On a model space `C₀(I, R)`, let
`c` invert the leading coefficient of `Q` and set `B = 1 - c Q*`. Since `B(0) = 0`, `B(u)` is row
compact and its Fredholm series is Coleman's transform `D(B, H_u) = (1 - T) ^ deg Q · D(B, S)`.
Coprimality of `Q` and `S` forces `D(B, S)(1)` to be a unit, so `1` is a good zero of order
`d = deg Q` of `H_{B(u)}`. The Riesz projection `E` of `B(u)` at `1` of order `d` commutes with
`u`, lies in the operator-norm closure of `R[u]`, has finite projective range of constant rank `d`,
and satisfies `Q*(u) ^ d * E = 0` with `Q*(u)` invertible on `range (1 - E)`. Invertibility of
`Q*(u * (1 - E))` makes `Q` coprime to `H_{u(1 - E)}`, so `Q` divides the reversed characteristic
polynomial `P` of `u|_{range E}` in the ring of entire series; entire division and `deg P ≤ d`,
`P(0) = Q(0) = 1` force `P = Q` and hence `H_{u(1 - E)} = S`. Since `u|_{range E}` is invertible
(as `Q*(u)^d` vanishes on `range E`), Cayley–Hamilton on the finite projective module `range E`
refines `Q*(u)^d * E = 0` to `Q*(u) * E = 0`. Transport along a retract `r ∘ i = id` passes all
results to modules with property (Pr) without assuming Noetherianity, reducedness, or a global
basis of `range E`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`: Riesz–Coleman projections of
  row-compact operators are row compact whenever `Q` has invertible leading coefficient.
* `ContinuousLinearMap.IsRowCompact.exists_rieszColemanProjection`,
  `ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`: existence of the Riesz–Coleman
  projection for a coprime polynomial factor `Q` of the Fredholm series.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`: the finite summand has constant
  rank `Q.natDegree` on `Spec R`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker`: the Fredholm
  series of the finite summand is `Q` and that of the complementary summand is `S`.
* `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range` and
  `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact`
  identify the reversed characteristic polynomial of `u|_{range E}` with `Q`.
* `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`: over a complete ultrametric field,
  the finite summand has dimension `Q.natDegree`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A, A3–A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2, Theorem 2.2.2.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open scoped PowerSeries ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Compactness

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]

/-- A Riesz–Coleman projection of a row-compact endomorphism of a model space is row compact
whenever `Q` has invertible leading coefficient. Completeness of `R` is not needed. -/
theorem IsRieszColemanProjection.isRowCompact {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    [DecidableEq I] {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    E.IsRowCompact := by
  rw [hE.eq_mul_aeval_divX_mul hQ]
  simpa only [mul_def] using hu.comp_clm _

/-- A Riesz–Coleman projection of a row-compact endomorphism of a module with property (Pr) is row
compact whenever `Q` has invertible leading coefficient. Completeness of `R` is not needed. -/
theorem IsRieszColemanProjection.isPrCompact {M : Type*} [SeminormedAddCommGroup M] [Module R M]
    [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) : E.IsPrCompact := by
  rw [hE.eq_mul_aeval_divX_mul hQ]
  simpa only [mul_def] using hu.comp_clm _ hu.hasPr_source

variable [CompleteSpace R]

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism of a model space is
finitely generated whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.finite_range_of_isRowCompact {I : Type*} [TopologicalSpace I]
    [DiscreteTopology I] [DecidableEq I] {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R E.range :=
  (hE.isRowCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism of a model space is
projective over the coefficient ring whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.projective_range_of_isRowCompact {I : Type*} [TopologicalSpace I]
    [DiscreteTopology I] [DecidableEq I] {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R E.range :=
  (hE.isRowCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- The kernel `ker Q*(u)` of a row-compact endomorphism of a model space admitting a Riesz–Coleman
projection for `Q` is finitely generated whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isRowCompact {I : Type*}
    [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I] {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R (LinearMap.ker ((Polynomial.aeval u Q.reverse :
      C₀(I, R) →L[R] C₀(I, R)) : C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range_of_isRowCompact hu hQ

/-- The kernel `ker Q*(u)` of a row-compact endomorphism of a model space admitting a Riesz–Coleman
projection for `Q` is projective whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isRowCompact {I : Type*}
    [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I] {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R (LinearMap.ker ((Polynomial.aeval u Q.reverse :
      C₀(I, R) →L[R] C₀(I, R)) : C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range_of_isRowCompact hu hQ

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism of a module with property
(Pr) is finitely generated whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.finite_range_of_isPrCompact {M : Type*} [SeminormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R E.range :=
  (hE.isPrCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism of a module with property
(Pr) is projective over the coefficient ring whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.projective_range_of_isPrCompact {M : Type*}
    [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R E.range :=
  (hE.isPrCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- The kernel `ker Q*(u)` of a row-compact endomorphism of a module with property (Pr) admitting a
Riesz–Coleman projection for `Q` is finitely generated whenever `Q` has invertible leading
coefficient. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact {M : Type*}
    [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range_of_isPrCompact hu hQ

/-- The kernel `ker Q*(u)` of a row-compact endomorphism of a module with property (Pr) admitting a
Riesz–Coleman projection for `Q` is projective whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact {M : Type*}
    [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range_of_isPrCompact hu hQ

end Compactness

section ModelSpace

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]

/-- For `H_u = Q * S` with `Q(0) = 1`, invertible leading coefficient `c⁻¹`, `S` entire, and
`Q, S` coprime entire series, the Fredholm series of `B(u)` for `B = 1 - c Q*` has a good zero of
order `Q.natDegree` at `1`. -/
private theorem isGoodZero_aeval_one_sub_C_mul_reverse {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} {c : R} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1)
    (hc : c * Q.leadingCoeff = 1) (hS : S.IsEntire)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u (1 - C c * Q.reverse)).matrixCoeff.charPowerSeries.IsGoodZero 1
      Q.natDegree := by
  set B : R[X] := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have hS0 : PowerSeries.constantCoeff S = 1 := by
    have h0 := congrArg PowerSeries.constantCoeff hH
    simpa [Matrix.constantCoeff_charPowerSeries, hQ0] using h0.symm
  have hS0' : PowerSeries.coeff 0 S = 1 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hGS : (B.colemanDSeries S).IsEntire := by
    rw [← PowerSeries.colemanDEntire_coe hB0 hS0']
    exact PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS
      (by rwa [Polynomial.coeff_coe]) hS0'
  have hunit : IsUnit ((B.colemanDSeries S).evalAt (1 : R)) :=
    (isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc hS hS0).mpr hcop
  set G : R⟦X⟧ := PowerSeries.C ((-1 : R) ^ Q.natDegree) * B.colemanDSeries S
  have hG : G.IsEntire := (PowerSeries.isEntire_C _).mul hGS
  have hGunit : IsUnit (G.evalAt (1 : R)) := by
    rw [(PowerSeries.isEntire_C _).evalAt_mul hGS, PowerSeries.evalAt_C,
      Algebra.algebraMap_self_apply]
    exact (isUnit_neg_one.pow _).mul hunit
  have hfac : (1 - PowerSeries.X : R⟦X⟧) ^ Q.natDegree * B.colemanDSeries S =
      (PowerSeries.X - PowerSeries.C (1 : R)) ^ Q.natDegree * G := by
    have h1 : (1 - PowerSeries.X : R⟦X⟧) =
        PowerSeries.C (-1 : R) * (PowerSeries.X - PowerSeries.C (1 : R)) := by
      simp [map_neg, map_one]
    rw [h1, mul_pow, ← map_pow]
    ring
  rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hH, colemanDSeries_mul hB0,
    colemanDSeries_one_sub_C_mul_reverse_self hQ0 hc, hfac]
  exact hG.isGoodZero_X_sub_C_pow_mul_iff.mpr hGunit

/-- First stage of the model-space Riesz–Coleman construction: the Riesz projection `E` of
`B(u) = (1 - c Q*)(u)` at the good zero `1` of order `d = deg Q` lies in the closure of `R[u]`,
commutes with `u`, is row compact with constant rank `d`, kills `Q*(u)^d`, and inverts `Q*(u)` on
the complementary summand. -/
private theorem exists_candidate_rieszColeman {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : C₀(I, R) →L[R] C₀(I, R),
      IsIdempotentElem E ∧ Commute u E ∧ E.IsRowCompact ∧
      E ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) ∧
      Polynomial.aeval u Q.reverse ^ Q.natDegree * E = 0 ∧
      (∃ w : C₀(I, R) →L[R] C₀(I, R), Polynomial.aeval u Q.reverse * w = 1 - E ∧
        w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
        w ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R)))) ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) := by
  let c : R := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : R[X] := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have huB : (Polynomial.aeval u B).IsRowCompact := hu.aeval hB0
  have hGood := isGoodZero_aeval_one_sub_C_mul_reverse hu hQ0 hc hS hH hcop
  have hEr := huB.isRieszProjection_rieszProjection
    (fun _ hj ↦ hGood.evalAt_hasseDeriv_eq_zero hj) hGood.isUnit_evalAt_hasseDeriv
  set E := (Polynomial.aeval u B).rieszProjection 1 Q.natDegree
  have hsub : (Algebra.adjoin R {Polynomial.aeval u B} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
      Algebra.adjoin R {u} :=
    SetLike.coe_subset_coe.mpr <| Algebra.adjoin_le <| by
      simp [Polynomial.aeval_mem_adjoin_singleton (p := B) R u]
  have hE_cl : E ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
    closure_mono hsub hEr.mem_closure_adjoin
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  have hE_comm : Commute u E := by
    have hu_cent : u ∈ Subalgebra.centralizer R ({u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
      (Subalgebra.mem_centralizer_iff R).2 fun _ hx ↦ by rw [Set.mem_singleton_iff.1 hx]
    have hE_cl' : E ∈ (Algebra.adjoin R ({u} : Set (C₀(I, R) →L[R] C₀(I, R)))).topologicalClosure :=
      hE_cl
    exact (Subalgebra.mem_centralizer_iff R).1
      (Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer R _ hE_cl') u hu_cent
  have h1B : (1 : C₀(I, R) →L[R] C₀(I, R)) - (1 : R) • Polynomial.aeval u B =
      c • Polynomial.aeval u Q.reverse := by
    simp [B, Algebra.algebraMap_eq_smul_one]
  have hpow : Polynomial.aeval u Q.reverse ^ Q.natDegree * E = 0 := by
    have h0 := hEr.pow_mul_eq_zero
    rw [h1B, smul_pow, smul_mul_assoc] at h0
    have hscaled := congrArg (Q.leadingCoeff ^ Q.natDegree • ·) h0
    rw [smul_smul, ← mul_pow, mul_comm Q.leadingCoeff c, hc, one_pow, one_smul, smul_zero]
      at hscaled
    exact hscaled
  obtain ⟨w₀, hw₁, hw₂, hw₃, hw₄, hw_cl⟩ := hEr.exists_inverse
  refine ⟨E, hEr.isIdempotentElem, hE_comm, hEr.isRowCompact huB, hE_cl, hpow,
    ⟨c • w₀, ?_, ?_, ?_, ?_, ?_⟩, fun p ↦ hEr.rankAtStalk_range huB hGood p⟩
  · simpa only [h1B, smul_mul_assoc, mul_smul_comm] using hw₁
  · simpa only [h1B, smul_mul_assoc, mul_smul_comm] using hw₂
  · rw [mul_smul_comm, hw₃]; ext x : 1; simp
  · rw [smul_mul_assoc, hw₄]; ext x : 1; simp
  · exact map_mem_closure (continuous_const_smul c) (closure_mono hsub hw_cl)
      fun y hy ↦ (Algebra.adjoin R {u} : Subalgebra R _).smul_mem hy c

/-- If `Q*(u)` is invertible on the complement of a commuting idempotent `E`, then `Q` is coprime
to the Fredholm series of `u * (1 - E)` in the ring of entire series. -/
private theorem isCoprime_charPowerSeries_mul_one_sub {u E : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} (hQ : IsUnit Q.leadingCoeff) (hE_idem : IsIdempotentElem E)
    (hE_comm : Commute u E)
    (hE_inv : ∃ w : C₀(I, R) →L[R] C₀(I, R), Polynomial.aeval u Q.reverse * w = 1 - E ∧
      w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
      w ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R)))) :
    IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
        IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩ := by
  obtain ⟨w, hw₁, hw₂, -, -, -⟩ := hE_inv
  let c : R := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  have hunit1 : IsUnit (E + (c • Polynomial.aeval u Q.reverse) * (1 - E)) :=
    _root_.IsIdempotentElem.isUnit_add_mul_one_sub (w := Q.leadingCoeff • w) hE_idem
      (by rw [smul_mul_assoc, mul_smul_comm, smul_smul, hc, one_smul, hw₁])
      (by rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm Q.leadingCoeff c, hc, one_smul,
        hw₂])
  have hscaled : c • Polynomial.aeval (u * (1 - E)) Q.reverse =
      E + (c • Polynomial.aeval u Q.reverse) * (1 - E) := by
    have hidem1 : IsIdempotentElem (1 - E) := by
      ext x : 1
      have hEE : E (E x) = E x := congr($(hE_idem.eq) x)
      simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, map_sub, hEE, sub_self, sub_zero]
    have hcomm1 : Commute u (1 - E) := by
      ext x : 1
      simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, map_sub] using
        congrArg (u x - ·) (congr($(hE_comm.eq) x))
    rw [_root_.IsIdempotentElem.aeval_mul_of_commute (B := C₀(I, R) →L[R] C₀(I, R))
      hidem1 hcomm1, coeff_zero_reverse, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    ext x j
    simp only [smul_apply, add_apply, sub_apply, one_apply_eq_self, mul_apply_eq_comp, smul_eq_mul,
      sub_sub_cancel, mul_add, ← mul_assoc, hc, one_mul, add_comm]
  have hunit : IsUnit (Polynomial.aeval (u * (1 - E)) Q.reverse) := by
    have hu' : IsUnit ((IsUnit.of_mul_eq_one Q.leadingCoeff hc).unit •
        Polynomial.aeval (u * (1 - E)) Q.reverse) := by
      simpa only [Units.smul_def, IsUnit.unit_spec, hscaled] using hunit1
    exact (isUnit_smul_iff _ _).mp hu'
  exact ((hu.comp_clm (1 - E)).isUnit_aeval_reverse_iff hQ).mp hunit

/-- Second stage (determinant identification): for a commuting row-compact idempotent `E` whose
range has constant rank `deg Q` and on whose complement `Q*(u)` is invertible, `H_{u E} = Q`,
`H_{u (1 - E)} = S`, and the restriction `u|_{range E}` has reversed characteristic polynomial
`Q`. -/
private theorem candidate_charPowerSeries_eq {u E : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hE_idem : IsIdempotentElem E)
    (hE_comm : Commute u E) (hE_rc : E.IsRowCompact)
    (hE_inv : ∃ w : C₀(I, R) →L[R] C₀(I, R), Polynomial.aeval u Q.reverse * w = 1 - E ∧
      w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
      w ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))))
    (hE_rank : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) :
    letI : AddCommGroup E.range := inferInstance
    ∃ (_ : Module.Finite R E.range) (_ : Module.Projective R E.range)
      (hmaps : Set.MapsTo u E.range E.range),
      ((u.restrict hmaps : E.range →L[R] E.range).toLinearMap).projectiveCharpolyRev = Q ∧
      (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  let : AddCommGroup E.range := inferInstance
  have := hE_rc.finite_range_of_isIdempotentElem hE_idem
  have := hE_rc.projective_range_of_isIdempotentElem hE_idem
  have hmaps : Set.MapsTo u E.range E.range := by
    rw [LinearMap.coe_range, coe_coe]
    exact Function.Semiconj.mapsTo_range fun x ↦ congr($(hE_comm.eq.symm) x)
  have hfix (x : E.range) : E x = x :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE_idem x
  let v : E.range →L[R] E.range := u.restrict hmaps
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract _ _ hri
  have hv := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM v
  let f : Module.End R E.range := v.toLinearMap
  have hcharE : (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : R⟦X⟧) := by
    have hext : E.range.subtypeL.comp (v.comp E.rangeRestrict) = u * E := ext fun _ ↦ rfl
    rw [← hext, ← hv.charPowerSeries_eq hri,
      charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM v]
  have hPQ_eq : f.projectiveCharpolyRev = Q := by
    have : Nontrivial R := NormOneClass.nontrivial
    have hprod : (⟨f.projectiveCharpolyRev,
          IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe _)⟩ : IsEntire.subring R) *
        ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
          IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩ =
        ⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ *
          ⟨S, IsEntire.mem_subring.mpr hS⟩ :=
      Subtype.ext <| by
        simp only [Subring.coe_mul, ← hcharE,
          ← hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hE_idem hE_comm, hH]
    obtain ⟨⟨G, hG⟩, hPQ⟩ :=
      (isCoprime_charPowerSeries_mul_one_sub hu hQ hE_idem hE_comm hE_inv).dvd_of_dvd_mul_right
        ⟨⟨S, IsEntire.mem_subring.mpr hS⟩, hprod⟩
    obtain ⟨r, hr⟩ := TauCeti.PowerSeries.dvd_of_coe_eq_coe_mul_entire hQ
      (IsEntire.mem_subring.mp hG) (congrArg Subtype.val hPQ)
    have hr0 : r.coeff 0 = 1 := by
      simpa [hr, mul_coeff_zero, hQ0] using f.coeff_projectiveCharpolyRev_zero
    have hmul_lc : Q.leadingCoeff * r.leadingCoeff ≠ 0 :=
      mt hQ.mul_right_eq_zero.mp (leadingCoeff_ne_zero.mpr fun h ↦ by simp [h] at hr0)
    have hr_deg : r.natDegree = 0 := by
      have := hr ▸ natDegree_mul' hmul_lc
      have := f.natDegree_projectiveCharpolyRev_le fun p ↦ (hE_rank p).le; omega
    rw [hr, eq_C_of_natDegree_eq_zero hr_deg, hr0, map_one, mul_one]
  have hcharE' : (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) := by rw [hcharE, hPQ_eq]
  have hchar_comp : (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
    have hprod := hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hE_idem hE_comm
    rw [hH, hcharE'] at hprod
    exact ((PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hQ0])).mul_left_cancel hprod).symm
  exact ⟨inferInstance, inferInstance, hmaps, hPQ_eq, hcharE', hchar_comp⟩

omit [DiscreteTopology I] [CompleteSpace R] [TauCeti.NormedRing.IsTate R] [DecidableEq I] in
/-- Third stage (annihilation refinement): once `u|_{range E}` has reversed characteristic
polynomial `Q` and `Q*(u)^d * E = 0`, invertibility of `u|_{range E}` and Cayley–Hamilton refine
nilpotence to `Q*(u) * E = 0`. -/
private theorem aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hQ : IsUnit Q.leadingCoeff) (hE_idem : IsIdempotentElem E)
    (hE_pow : Polynomial.aeval u Q.reverse ^ Q.natDegree * E = 0)
    (hmaps : Set.MapsTo u E.range E.range)
    (hfin : letI : AddCommGroup E.range := inferInstance; Module.Finite R E.range)
    (hproj : letI : AddCommGroup E.range := inferInstance; Module.Projective R E.range)
    (hPQ : letI : AddCommGroup E.range := inferInstance
      letI := hfin; letI := hproj
      ((u.restrict hmaps : E.range →L[R] E.range).toLinearMap).projectiveCharpolyRev = Q) :
    Polynomial.aeval u Q.reverse * E = 0 := by
  let : AddCommGroup E.range := inferInstance
  have := hfin
  have := hproj
  let f : Module.End R E.range := (u.restrict hmaps).toLinearMap
  have hfix (x : E.range) : E x = x :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE_idem x
  have hcomp : u.toLinearMap.comp E.range.subtype = E.range.subtype.comp f := rfl
  have hinter (P : R[X]) (x : E.range) :
      (Polynomial.aeval f P x : C₀(I, R)) = Polynomial.aeval u P x := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hcomp P) x
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype, ← toLinearMap_aeval, coe_coe]
      using h.symm
  have hf_pow : Polynomial.aeval f (Q.reverse ^ Q.natDegree) = 0 := by
    ext x : 1
    apply Subtype.ext
    rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, hinter, map_pow]
    simpa only [mul_apply_eq_comp, hfix, zero_apply] using congr($hE_pow (x : C₀(I, R)))
  have hf_unit : IsUnit f :=
    Polynomial.isUnit_of_aeval_eq_zero (by
      rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, coeff_zero_reverse]
      exact hQ.pow _) hf_pow
  obtain ⟨n, hn, hch⟩ := f.exists_aeval_reflect_projectiveCharpolyRev_eq_zero
  rw [hPQ] at hn hch
  have href : Q.reflect n = X ^ (n - Q.natDegree) * Q.reverse := by
    have h := Polynomial.reflect_mul (1 : R[X]) Q (F := n - Q.natDegree) (by simp) le_rfl
    simpa only [one_mul, Nat.sub_add_cancel hn, reflect_one, reverse] using h
  have hfQ : Polynomial.aeval f Q.reverse = 0 := by
    rw [href, map_mul, map_pow, aeval_X] at hch
    exact (hf_unit.pow (n - Q.natDegree)).mul_right_eq_zero.mp hch
  ext x : 1
  have h := congrArg Subtype.val (LinearMap.congr_fun hfQ ⟨E x, ⟨x, rfl⟩⟩)
  simpa only [hinter, LinearMap.zero_apply, ZeroMemClass.coe_zero, mul_apply_eq_comp,
    zero_apply] using h

/-- Bundled model-space construction producing the Riesz–Coleman projection together with its
constant rank and both Fredholm factors. -/
private theorem exists_rieszColemanProjection_aux {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : C₀(I, R) →L[R] C₀(I, R), IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) ∧
      (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  obtain ⟨E, hE_idem, hE_comm, hE_rc, hE_cl, hE_pow, hE_inv, hE_rank⟩ :=
    exists_candidate_rieszColeman hu hQ0 hQ hS hH hcop
  obtain ⟨hfin, hproj, hmaps, hPQ, hcharE, hchar_comp⟩ :=
    candidate_charPowerSeries_eq hu hQ0 hQ hS hH hE_idem hE_comm hE_rc hE_inv hE_rank
  have hQzero := aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev hQ hE_idem hE_pow hmaps
    hfin hproj hPQ
  exact ⟨E, ⟨hE_idem, hE_comm, hE_cl, hQzero, hE_inv⟩, hE_rank, hcharE, hchar_comp⟩

/-- Bundled model-space construction without the normalisation `Q(0) = 1`: evaluating `H_u = Q · S`
at `0` shows `Q(0)` is a unit, so rescaling `Q` and `S` reduces to
`exists_rieszColemanProjection_aux`. -/
private theorem exists_rieszColemanProjection_of_factorization {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : C₀(I, R) →L[R] C₀(I, R), IsRieszColemanProjection u Q E ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  have hQ0_mul : Q.coeff 0 * PowerSeries.constantCoeff S = 1 := by
    have h0 := congrArg PowerSeries.constantCoeff hH
    simpa [Matrix.constantCoeff_charPowerSeries] using h0.symm
  let c : Rˣ := Units.mkOfMulEqOne (Q.coeff 0) (PowerSeries.constantCoeff S) hQ0_mul
  set Q' : R[X] := c⁻¹ • Q
  set S' : R⟦X⟧ := (c : R) • S
  have hQ'0 : Q'.coeff 0 = 1 := by
    dsimp only [Q']
    rw [Units.smul_def, Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul]
    exact c.inv_mul
  have hQ'deg : Q'.natDegree = Q.natDegree :=
    Polynomial.natDegree_smul_of_smul_regular Q (IsSMulRegular.all _)
  have hQ'lc : IsUnit Q'.leadingCoeff := by
    have hlc : Q'.leadingCoeff = (↑c⁻¹ : R) * Q.leadingCoeff := by
      rw [Polynomial.leadingCoeff, hQ'deg]
      dsimp only [Q']
      rw [Units.smul_def, Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul,
        Polynomial.coeff_natDegree]
    rw [hlc]
    exact c⁻¹.isUnit.mul hQ
  have hS' : S'.IsEntire := hS.smul (c : R)
  have hQ'coe : (Q' : R⟦X⟧) = (↑c⁻¹ : R) • (Q : R⟦X⟧) := by
    ext n
    simp [Q', Units.smul_def, Polynomial.smul_eq_C_mul]
  have hH' : u.matrixCoeff.charPowerSeries = (Q' : R⟦X⟧) * S' := by
    rw [hH, hQ'coe]
    dsimp only [S']
    rw [smul_mul_smul_comm, Units.inv_mul, one_smul]
  have hcop' : IsCoprime
      (⟨Q', IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q')⟩ : IsEntire.subring R)
      ⟨S', IsEntire.mem_subring.mpr hS'⟩ := by
    obtain ⟨A, B, hAB⟩ := hcop
    refine ⟨⟨(c : R) • (A : R⟦X⟧), IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp A.2).smul _)⟩,
      ⟨(↑c⁻¹ : R) • (B : R⟦X⟧),
        IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp B.2).smul _)⟩, ?_⟩
    apply Subtype.ext
    have hAB' := congrArg Subtype.val hAB
    simp only [Subring.coe_add, Subring.coe_mul, OneMemClass.coe_one] at hAB' ⊢
    dsimp only [S']
    rw [hQ'coe, smul_mul_smul_comm, Units.mul_inv, one_smul, smul_mul_smul_comm, Units.inv_mul,
      one_smul, hAB']
  obtain ⟨E, hE, hrank, -, -⟩ := exists_rieszColemanProjection_aux hu hQ'0 hQ'lc hS' hH' hcop'
  refine ⟨E, ?_, fun p ↦ (hrank p).trans hQ'deg⟩
  simpa [Q'] using hE.units_smul c

/-- **Existence of the Riesz–Coleman projection on model spaces.** Let `u` be a row-compact
endomorphism of `C₀(I, R)` whose principal-minor Fredholm series factors as `H_u = Q · S`, where
`Q` is a polynomial with invertible leading coefficient, `S` is entire, and `Q` and `S` are coprime
in the ring of entire series. Then `u` has a (unique) Riesz–Coleman projection for `Q`. -/
theorem IsRowCompact.exists_rieszColemanProjection {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  obtain ⟨E, hE, -⟩ := exists_rieszColemanProjection_of_factorization hu hQ hS hH hcop
  exact ⟨E, hE⟩

/-- **Constant rank of the Riesz–Coleman summand on model spaces.** Under a coprime factorisation
`H_u = Q · S`, the range `ker Q*(u)` of the Riesz–Coleman projection has constant rank `deg Q` at
every prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  obtain ⟨E₀, hE₀, hrank⟩ := exists_rieszColemanProjection_of_factorization hu hQ hS hH hcop
  exact hE.unique hE₀ ▸ hrank p

/-- **Determinant of the finite Riesz–Coleman summand on model spaces.** Under a coprime
factorisation `H_u = Q · S` with `Q(0) = 1`, the Fredholm series of `u * E` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) := by
  obtain ⟨E₀, hE₀, -, hcharE, -⟩ := exists_rieszColemanProjection_aux hu hQ0 hQ hS hH hcop
  exact hE.unique hE₀ ▸ hcharE

/-- **Determinant of the complementary Riesz–Coleman summand on model spaces.** Under a coprime
factorisation `H_u = Q · S` with `Q(0) = 1`, the Fredholm series of `u * (1 - E)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  obtain ⟨E₀, hE₀, -, -, hchar_comp⟩ := exists_rieszColemanProjection_aux hu hQ0 hQ hS hH hcop
  exact hE.unique hE₀ ▸ hchar_comp

/-- **Characteristic polynomial of `u` on the finite Riesz–Coleman summand on model spaces.** Under
a coprime factorisation `H_u = Q · S` with `Q(0) = 1`, the reversed characteristic polynomial
`det (1 - X u|_{range E})` of the restriction of `u` to the finite projective summand `range E` is
`Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    haveI := hE.finite_range_of_isRowCompact hu hQ
    haveI := hE.projective_range_of_isRowCompact hu hQ
    (u.toLinearMap.restrict hE.mapsTo_range).projectiveCharpolyRev = Q := by
  let : AddCommGroup E.range := inferInstance
  have := hE.finite_range_of_isRowCompact hu hQ
  have := hE.projective_range_of_isRowCompact hu hQ
  have hfix (y : E.range) : E y = y :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE.isIdempotentElem y
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ext fun y ↦ Subtype.ext (hfix y)
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract _ _ hri
  let w : E.range →L[R] E.range := u.restrict hE.mapsTo_range
  have hw := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM w
  have hext : E.range.subtypeL.comp (w.comp E.rangeRestrict) = u * E := ext fun _ ↦ rfl
  have hcoe : ((w.toLinearMap.projectiveCharpolyRev : R[X]) : R⟦X⟧) = (Q : R⟦X⟧) := by
    rw [← charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM w,
      hw.charPowerSeries_eq hri, hext, hE.charPowerSeries_matrixCoeff_mul hu hQ0 hQ hS hH hcop]
  exact Polynomial.coe_injective R hcoe

end ModelSpace

section PrModule

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M]

omit [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R] in
/-- For `B = 1 - c Q*` with `c * lc(Q) = 1`, `ker (1 - B(T)) = ker Q*(T)`. -/
private theorem ker_one_sub_aeval_eq_ker_aeval_reverse {L : Type*} [SeminormedAddCommGroup L]
    [Module R L] [ContinuousConstSMul R L] (T : L →L[R] L) {Q : R[X]} {c : R}
    (hc : c * Q.leadingCoeff = 1) :
    LinearMap.ker ((1 : Module.End R L) -
        (Polynomial.aeval T (1 - C c * Q.reverse) : L →ₗ[R] L)) =
      LinearMap.ker ((Polynomial.aeval T Q.reverse : L →L[R] L) : L →ₗ[R] L) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, one_apply_eq_self, coe_coe,
    map_sub, map_one, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, sub_apply,
    mul_apply_eq_comp, smul_apply, sub_sub_cancel]
  exact ⟨fun h ↦ by
    simpa [smul_smul, mul_comm Q.leadingCoeff c, hc] using
      congrArg (fun y : L ↦ Q.leadingCoeff • y) h,
    fun h ↦ by simp [h]⟩

omit [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R] in
/-- Along a retract `r ∘ i = id`, when `Q` has invertible leading coefficient, `r` and `i` identify
`ker Q*(i ∘ u ∘ r)` with `ker Q*(u)`. -/
private noncomputable def kerAevalReverseRetractEquiv {N : Type*} [SeminormedAddCommGroup N]
    [Module R N] [ContinuousConstSMul R M] [ContinuousConstSMul R N] {i : M →L[R] N}
    {r : N →L[R] M} (hri : r.comp i = .id R M) (u : M →L[R] M) {Q : R[X]}
    (hQ : IsUnit Q.leadingCoeff) :
    LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse : N →L[R] N) : N →ₗ[R] N) ≃ₗ[R]
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
  let c : R := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : R[X] := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have hri' : r.toLinearMap.comp i.toLinearMap = LinearMap.id := by
    simpa only [toLinearMap_comp, coe_id] using congrArg ContinuousLinearMap.toLinearMap hri
  have hsplit : LinearMap.splitEnd r.toLinearMap i.toLinearMap hri'
      ((1 : Module.End R M) - (Polynomial.aeval u B : M →ₗ[R] M)) =
      (1 : Module.End R N) - (Polynomial.aeval (i.comp (u.comp r)) B : N →ₗ[R] N) := by
    rw [LinearMap.splitEnd_one_sub, aeval_comp_comp_of_retract hri u hB0, toLinearMap_comp,
      toLinearMap_comp]
  exact (LinearEquiv.ofEq _ _
      (by rw [← ker_one_sub_aeval_eq_ker_aeval_reverse (i.comp (u.comp r)) hc, ← hsplit])).trans
    ((LinearMap.kerSplitEndEquiv r.toLinearMap i.toLinearMap hri'
      ((1 : Module.End R M) - (Polynomial.aeval u B : M →ₗ[R] M))).trans
      (LinearEquiv.ofEq _ _ (ker_one_sub_aeval_eq_ker_aeval_reverse u hc)))

/-- **Constant rank of `ker Q*(u)` on a module with property (Pr).** Under a coprime factorisation
`H_u = Q · S`, the kernel `ker Q*(u)` has constant rank `deg Q` at every prime ideal of `R`. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse [ContinuousConstSMul R M] {u : M →L[R] M}
    (hu : u.IsPrCompact) {Q : R[X]} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) p =
      Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hH
  obtain ⟨F, hF⟩ := hv.exists_rieszColemanProjection hQ hS hH hcop
  have hker : Module.rankAtStalk (R := R)
        (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) =
      Module.rankAtStalk (R := R) (LinearMap.ker
        ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse : C₀(J, R) →L[R] C₀(J, R)) :
          C₀(J, R) →ₗ[R] C₀(J, R))) := by
    let : AddCommGroup
        (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := inferInstance
    let : AddCommGroup (LinearMap.ker
        ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse : C₀(J, R) →L[R] C₀(J, R)) :
          C₀(J, R) →ₗ[R] C₀(J, R))) := inferInstance
    exact Module.rankAtStalk_eq_of_equiv (kerAevalReverseRetractEquiv hri u hQ).symm
  rw [hker, ← hF.range_eq_ker]
  exact hF.rankAtStalk_range hv hQ hS hH hcop p

section BoundedSMul

variable [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}

/-- **Existence of the Riesz–Coleman projection on a module with property (Pr).** Let `u` be a
row-compact endomorphism of a module with property (Pr) whose Fredholm series factors as
`H_u = Q · S`, where `Q` is a polynomial with invertible leading coefficient, `S` is entire, and
`Q` and `S` are coprime in the ring of entire series. Then `u` has a (unique) Riesz–Coleman
projection for `Q`. -/
theorem IsPrCompact.exists_rieszColemanProjection (hu : u.IsPrCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hH
  obtain ⟨F, hF⟩ := (hu.isRowCompact_comp i r).exists_rieszColemanProjection hQ hS hH hcop
  exact ⟨r.comp (F.comp i), hF.comp_comp_of_retract hri⟩

/-- **Constant rank of the finite Riesz–Coleman summand on a module with property (Pr).** Under a
coprime factorisation `H_u = Q · S`, the range of the Riesz–Coleman projection has constant rank
`deg Q` at every prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  rw [hE.range_eq_ker]
  exact hu.rankAtStalk_ker_aeval_reverse hQ hS hH hcop p

/-- **Determinant of `u * E` on a module with property (Pr).** Under a coprime factorisation
`H_u = Q · S` with `Q(0) = 1`, the Fredholm series of `u * E` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hH
  obtain ⟨F, hF⟩ := hv.exists_rieszColemanProjection hQ hS hH hcop
  have hEF : E = r.comp (F.comp i) := hE.unique (hF.comp_comp_of_retract hri)
  have hF_ext : i.comp (E.comp r) = F := hEF ▸ hF.comp_comp_eq_of_retract hri hQ
  have hmul : i.comp ((u.comp E).comp r) = i.comp (u.comp r) * F := by
    ext y : 1
    simpa only [comp_apply, mul_apply_eq_comp, hri'] using congr(i (u (r $(congr($hF_ext y)))))
  rw [mul_def, (hu.comp_clm E hu.hasPr_source).charPowerSeries_eq hri, hmul]
  exact hF.charPowerSeries_matrixCoeff_mul hv hQ0 hQ hS hH hcop

/-- **Determinant of `u * (1 - E)` on a module with property (Pr).** Under a coprime factorisation
`H_u = Q · S` with `Q(0) = 1`, the Fredholm series of `u * (1 - E)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  have hsum : u * E + u * (1 - E) = u := by
    rw [← mul_add, add_sub_cancel, mul_one]
  have hzero : (u * E).comp (u * (1 - E)) = 0 := by
    rw [← mul_def, mul_assoc, ← mul_assoc E, ← hE.commute.eq, mul_assoc u E,
      hE.isIdempotentElem.mul_one_sub_self, mul_zero, mul_zero]
  have hprod : u.charPowerSeries = (u * E).charPowerSeries * (u * (1 - E)).charPowerSeries := by
    conv_lhs => rw [← hsum]
    exact TauCeti.charPowerSeries_add_of_comp_eq_zero (hu.comp_clm E hu.hasPr_source)
      (hu.comp_clm (1 - E) hu.hasPr_source) hzero
  rw [hH, hE.charPowerSeries_mul hu hQ0 hQ hS hH hcop] at hprod
  have hQunit : IsUnit (Q : R⟦X⟧) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hQ0])
  exact (hQunit.mul_left_cancel hprod).symm

/-- **Fredholm series on the finite Riesz–Coleman summand.** Under a coprime factorisation
`H_u = Q · S` with `Q(0) = 1`, the Fredholm series of the restriction of `u` to `range E` is
`Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict fun _ hx ↦ hE.mapsTo_range hx).charPowerSeries = (Q : R⟦X⟧) := by
  have hfix (x : E.range) : E x = x :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE.isIdempotentElem x
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr R E.range := hu.hasPr_source.of_retract _ _ hri
  have hleft : E.rangeRestrict.comp (u.comp E.range.subtypeL) =
      u.restrict (fun _ hx ↦ hE.mapsTo_range hx) := by
    ext x
    exact (congr($(hE.commute.eq) (x : M)).symm).trans (congrArg u (hfix x))
  have hright : (u.comp E.range.subtypeL).comp E.rangeRestrict = u * E := ext fun _ ↦ rfl
  rw [← hleft, ← (hu.comp_clm E.range.subtypeL hM).charPowerSeries_comp_comm E.rangeRestrict,
    hright]
  exact hE.charPowerSeries_mul hu hQ0 hQ hS hH hcop

/-- **Fredholm series on the complementary Riesz–Coleman summand.** Under a coprime factorisation
`H_u = Q · S` with `Q(0) = 1`, the Fredholm series of the restriction of `u` to
`ker E = range Q*(u)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict fun _ hx ↦ hE.mapsTo_ker hx).charPowerSeries = S := by
  have hmem (x : M) : (1 - E) x ∈ E.ker := by
    apply LinearMap.mem_ker.mpr
    have hid := congr($(hE.isIdempotentElem.eq) x)
    simpa only [coe_coe, sub_apply, one_apply_eq_self, map_sub, mul_apply_eq_comp,
      sub_eq_zero] using hid.symm
  let rK : M →L[R] E.ker := (1 - E).codRestrict E.ker hmem
  have hri : rK.comp E.ker.subtypeL = .id R E.ker := by
    ext x
    have hx : E x = 0 := LinearMap.mem_ker.mp x.property
    simp [rK, hx]
  have hK : TauCeti.HasPr R E.ker := hu.hasPr_source.of_retract _ _ hri
  have hleft : rK.comp (u.comp E.ker.subtypeL) = u.restrict (fun _ hx ↦ hE.mapsTo_ker hx) := by
    ext x
    have hx : E (u x) = 0 := LinearMap.mem_ker.mp (hE.mapsTo_ker x.property)
    simp [rK, hx]
  have hright : (u.comp E.ker.subtypeL).comp rK = u * (1 - E) := ext fun _ ↦ rfl
  rw [← hleft, ← (hu.comp_clm E.ker.subtypeL hK).charPowerSeries_comp_comm rK, hright]
  exact hE.charPowerSeries_mul_one_sub hu hQ0 hQ hS hH hcop

/-- **Characteristic polynomial of `u` on the finite Riesz–Coleman summand.** Under a coprime
factorisation `H_u = Q · S` with `Q(0) = 1`, the reversed characteristic polynomial
`det (1 - X u|_{range E})` of the restriction of `u` to the finite projective summand `range E` is
`Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    haveI := hE.finite_range_of_isPrCompact hu hQ
    haveI := hE.projective_range_of_isPrCompact hu hQ
    (u.toLinearMap.restrict hE.mapsTo_range).projectiveCharpolyRev = Q := by
  classical
  let : AddCommGroup E.range := inferInstance
  have := hE.finite_range_of_isPrCompact hu hQ
  have := hE.projective_range_of_isPrCompact hu hQ
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hH
  obtain ⟨F, hF⟩ := hv.exists_rieszColemanProjection hQ hS hH hcop
  have hEF : E = r.comp (F.comp i) := hE.unique (hF.comp_comp_of_retract hri)
  have hF_ext : i.comp (E.comp r) = F := hEF ▸ hF.comp_comp_eq_of_retract hri hQ
  let : AddCommGroup F.range := inferInstance
  have := hF.finite_range_of_isRowCompact hv hQ
  have := hF.projective_range_of_isRowCompact hv hQ
  -- Identify `E.range` with `F.range` via `i`, transporting `projectiveCharpolyRev` without
  -- needing a norm (only a seminorm) on `M`.
  let e : E.range ≃ₗ[R] F.range := (rangeEquivOfRetract E hri).trans
    (LinearEquiv.ofEq _ _ (by
      simpa only [toLinearMap_comp] using
        congrArg (fun T : C₀(J, R) →L[R] C₀(J, R) ↦ LinearMap.range (T : C₀(J, R) →ₗ[R] C₀(J, R)))
          hF_ext))
  have he_coe (y : E.range) : (e y : C₀(J, R)) = i y :=
    coe_rangeEquivOfRetract_apply E hri y
  have hinter (x : E.range) :
      ((i.comp (u.comp r)).toLinearMap.restrict hF.mapsTo_range) (e x) =
        e ((u.toLinearMap.restrict hE.mapsTo_range) x) := by
    apply SetLike.coe_eq_coe.mp
    simp only [LinearMap.coe_restrict_apply, toLinearMap_comp, LinearMap.comp_apply, coe_coe,
      he_coe, hri']
    rfl
  have htr := LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq (θ := RingHom.id R) e hinter
  rw [Polynomial.map_id] at htr
  rw [← htr]
  exact hF.projectiveCharpolyRev_restrict_range hv hQ0 hQ hS hH hcop

end BoundedSMul

end PrModule

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u E : M →L[K] M} {Q : K[X]} {S : K⟦X⟧}

/-- **Dimension of `ker Q*(u)` over a field.** Over a complete ultrametric field, under a coprime
factorisation `H_u = Q · S`, the kernel `ker Q*(u)` has dimension `deg Q`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse (hu : u.IsPrCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hH : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[K] M) : M →ₗ[K] M)) =
      Q.natDegree := by
  have hr := hu.rankAtStalk_ker_aeval_reverse hQ hS hH hcop ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- **Dimension of the finite Riesz–Coleman summand over a field.** Over a complete ultrametric
field, under a coprime factorisation `H_u = Q · S`, the range of the Riesz–Coleman projection has
dimension `deg Q`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact [IsBoundedSMul K M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hH : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  rw [hE.range_eq_ker]
  exact hu.finrank_ker_aeval_reverse hQ hS hH hcop

end Field

end ContinuousLinearMap
