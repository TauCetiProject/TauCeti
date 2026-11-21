/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coprime
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
import TauCeti.Algebra.Polynomial.AlgebraMap
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Analysis.Polynomial.Coleman.Coprime
import TauCeti.RingTheory.PowerSeries.Entire.Division

/-!
# The Riesz–Coleman decomposition on model spaces

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1` and Tate scalars, let
`u : C₀(I, R) →L[R] C₀(I, R)` be a row-compact operator, and suppose its Fredholm series
`H_u = det (1 - T u)` admits a factorisation

  `H_u = Q * S`

where `Q : R[X]` has `IsUnit Q.leadingCoeff`, `S` is an entire power series, and `Q` and `S` are
coprime in the subring `PowerSeries.IsEntire.subring R` of entire series (note that `H_u(0) = 1`
forces `Q(0)` to be a unit, so rescaling `Q` by `Q(0)⁻¹` reduces to the normalised case
`Q(0) = 1`).

Following Coleman (Appendix A4), set `c = Ring.inverse Q.leadingCoeff` and consider the polynomial
`B = 1 - c Q*`, where `Q* = Q.reverse`. Note that `u.rieszColemanProjection (C b * Q) =
u.rieszColemanProjection Q` for any unit `b` (`ContinuousLinearMap.rieszColemanProjection_C_mul`).
In the normalised case `Q(0) = 1`, since `B(0) = 0`, the operator `v = B(u)` is row compact,
and by polynomial spectral mapping its Fredholm series is

  `H_v(T) = D(B, H_u)(T) = D(B, Q)(T) * D(B, S)(T) = (1 - T) ^ (deg Q) * D(B, S)(T)`.

Because `Q` and `S` are coprime entire series, `D(B, S)(1)` is a unit in `R`, so `H_v` has a good
zero of order `d = deg Q` at `T = 1`. The Riesz projector

  `u.rieszColemanProjection Q = v.rieszProjection 1 (deg Q)`

therefore cuts out a finite projective `u`-stable summand `range E` of constant rank `deg Q` on
`Spec R` on whose complement `1 - v = c Q*(u)` is invertible.

Comparing `H_u = Q * S` with the multiplicative splitting `H_u = H_(uE) * H_(u(1-E))`, where
`H_(uE)` is the reversed characteristic polynomial `P = det (1 - X (u|_{range E}))` of degree at
most `deg Q` and `Q*(u * (1 - E))` is invertible on `C₀(I, R)`, coprimality of `Q` and
`H_(u(1-E))` forces `Q ∣ P` in entire series; when `Q(0) = 1`, monic division by `c Q` and degree
comparison yield `P = Q` and `H_(u(1-E)) = S`. Finally, constant-rank Cayley–Hamilton on the finite
projective module `range E` upgrades nilpotence of `Q*(u)` on `range E` to the exact annihilation
`Q*(u) * E = 0`, establishing `IsRieszColemanProjection u Q (u.rieszColemanProjection Q)`.

## Main definitions

* `ContinuousLinearMap.rieszColemanProjection`: the explicit Riesz–Coleman projector
  `(B(u)).rieszProjection 1 Q.natDegree` for `B = 1 - lc(Q)⁻¹ Q*`.

## Main results

* `ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection` and
  `ContinuousLinearMap.IsRowCompact.exists_isRieszColemanProjection`: existence of the
  Riesz–Coleman projection for a coprime polynomial factorisation `H_u = Q * S` on `C₀(I, R)`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRowCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range`, and
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse`: `range E = ker Q*(u)` has constant
  stalk rank `deg Q` on `Spec R` (and dimension `deg Q` over a field).
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub`, and
  `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range`: when
  `Q(0) = 1`, the Fredholm factors on the two summands are `H_(uE) = Q` and `H_(u(1-E)) = S`, and
  `det (1 - X (u|_{range E}))` equals `Q`.
* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`,
  `ContinuousLinearMap.IsRieszColemanProjection.inverse_mapCoeffs`,
  `ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_mapCoeffs`, and
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`: compatibility with
  bounded unital ring homomorphisms `f : R →+* S` and invariance of stalk rank / kernel dimension.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open scoped PowerSeries ZeroAtInfty NNReal TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Defs

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]

/-- The **Riesz–Coleman projector** of an endomorphism `u : C₀(I, R) →L[R] C₀(I, R)` attached to a
polynomial `Q : R[X]`: the Riesz projector at `1` of order `Q.natDegree` of the operator `B(u)`,
where `B = 1 - lc(Q)⁻¹ Q*` and `Q* = Q.reverse`. -/
noncomputable def rieszColemanProjection (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    C₀(I, R) →L[R] C₀(I, R) :=
  (Polynomial.aeval u (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection
    1 Q.natDegree

/-- Unfolding of `ContinuousLinearMap.rieszColemanProjection`. -/
theorem rieszColemanProjection_def (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    u.rieszColemanProjection Q =
      (Polynomial.aeval u
        (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection
        1 Q.natDegree :=
  (rfl)

/-- For `Q = 1`, the explicit Riesz–Coleman projector is `0`. -/
@[simp]
theorem rieszColemanProjection_one (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.rieszColemanProjection 1 = 0 := by
  simp [rieszColemanProjection_def]

/-- Scaling `Q` by a unit scalar does not change `u.rieszColemanProjection Q` when
`Q.leadingCoeff` is a unit. -/
theorem rieszColemanProjection_C_mul (u : C₀(I, R) →L[R] C₀(I, R)) {Q : R[X]}
    (hQ : IsUnit Q.leadingCoeff) {b : R} (hb : IsUnit b) :
    u.rieszColemanProjection (Polynomial.C b * Q) = u.rieszColemanProjection Q := by
  obtain ⟨a, hba⟩ := hb.exists_right_inv
  have hdeg : (Polynomial.C b * Q).natDegree = Q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hba)
  have hrev : (Polynomial.C b * Q).reverse = Polynomial.C b * Q.reverse := by
    rw [Polynomial.reverse, Polynomial.reverse, hdeg, Polynomial.reflect_C_mul]
  have hlc : (Polynomial.C b * Q).leadingCoeff = b * Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, hdeg, Polynomial.coeff_C_mul]
  have hc : Ring.inverse (b * Q.leadingCoeff) * (b * Q.leadingCoeff) = 1 :=
    Ring.inverse_mul_cancel _ (hb.mul hQ)
  have hc' : Ring.inverse Q.leadingCoeff * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  have hinv : Ring.inverse (b * Q.leadingCoeff) * b = Ring.inverse Q.leadingCoeff := by
    calc Ring.inverse (b * Q.leadingCoeff) * b
        = (Ring.inverse (b * Q.leadingCoeff) * b) *
            (Q.leadingCoeff * Ring.inverse Q.leadingCoeff) := by
          rw [mul_comm Q.leadingCoeff, hc', mul_one]
      _ = (Ring.inverse (b * Q.leadingCoeff) * (b * Q.leadingCoeff)) *
            Ring.inverse Q.leadingCoeff := by ring
      _ = Ring.inverse Q.leadingCoeff := by rw [hc, one_mul]
  rw [rieszColemanProjection_def, rieszColemanProjection_def, hdeg, hlc, hrev,
    ← mul_assoc, ← Polynomial.C_mul, hinv]

end Defs

section Decomposition

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]

/-- Under a coprime factorisation `H_u = Q * S`, the operator `B(u)` for `B = 1 - lc(Q)⁻¹ Q*` has a
good Fredholm zero at `1` of order `Q.natDegree`. -/
private theorem isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u
      (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)).matrixCoeff
      |>.charPowerSeries.IsGoodZero 1 Q.natDegree := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : R[X] := 1 - Polynomial.C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have hS0 : PowerSeries.constantCoeff S = 1 := by
    have h := congrArg PowerSeries.constantCoeff hQS
    simpa [hQ0] using h.symm
  have hS0' : PowerSeries.coeff 0 S = 1 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hEe : (B.colemanDSeries S).IsEntire :=
    PowerSeries.colemanDEntire_coe (F := S) hB0 hS0' ▸
      PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS
        (by rwa [Polynomial.coeff_coe]) hS0'
  have hunitS : IsUnit ((B.colemanDSeries S).evalAt (1 : R)) :=
    (isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc hS hS0).mpr hcop
  set g : R⟦X⟧ := PowerSeries.C ((-1 : R) ^ Q.natDegree) * B.colemanDSeries S
  have hg : g.IsEntire := (PowerSeries.isEntire_C _).mul hEe
  have hgu : IsUnit (g.evalAt (1 : R)) := by
    rw [(PowerSeries.isEntire_C _).evalAt_mul hEe, PowerSeries.evalAt_C]
    exact (isUnit_one.neg.pow Q.natDegree).mul hunitS
  have hpow : ((1 - PowerSeries.X : R⟦X⟧) ^ Q.natDegree) * B.colemanDSeries S =
      (PowerSeries.X - PowerSeries.C 1) ^ Q.natDegree * g := by
    have h1 : (1 - PowerSeries.X : R⟦X⟧) =
        (PowerSeries.X - PowerSeries.C 1) * PowerSeries.C (-1) := by
      ext n; simp [sub_eq_add_neg, add_comm]
    rw [h1, mul_pow, ← map_pow, mul_assoc]
  rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hQS, colemanDSeries_mul hB0,
    colemanDSeries_one_sub_C_mul_reverse_self hQ0 hc, hpow]
  exact hg.isGoodZero_X_sub_C_pow_mul_iff.mpr hgu

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- For a Riesz projection `E` of `1 - lc(Q)⁻¹ Q*(u)` at `1` commuting with `u`, the operator
`Q*(u * (1 - E))` is invertible when `Q.leadingCoeff` is a unit. -/
private theorem isUnit_aeval_mul_one_sub_reverse_of_isRieszProjection
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    {u E : M →L[R] M} {Q : R[X]} (hQ : IsUnit Q.leadingCoeff)
    (hEv : IsRieszProjection
      (Polynomial.aeval u (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse))
      1 Q.natDegree E)
    (hEu : Commute u E) :
    IsUnit (Polynomial.aeval (u * (1 - E)) Q.reverse) := by
  set c := Ring.inverse Q.leadingCoeff
  have hcq : Q.leadingCoeff * c = 1 := mul_comm c _ ▸ Ring.inverse_mul_cancel _ hQ
  have h1v : (1 - (1 : R) • Polynomial.aeval u (1 - Polynomial.C c * Q.reverse) : M →L[R] M) =
      c • Polynomial.aeval u Q.reverse := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hunit := _root_.IsIdempotentElem.isUnit_add_mul_one_sub
    (A := M →L[R] M) hEv.isIdempotentElem
    hEv.one_sub_smul_mul_inverse hEv.inverse_mul_one_sub_smul
  rw [h1v] at hunit
  have hulc : IsUnit (Q.leadingCoeff • (1 : M →L[R] M)) :=
    Algebra.algebraMap_eq_smul_one (A := M →L[R] M) Q.leadingCoeff ▸
      hQ.map (algebraMap R (M →L[R] M))
  have heq : (Q.leadingCoeff • (1 : M →L[R] M)) *
      (E + (c • Polynomial.aeval u Q.reverse) * (1 - E)) =
      Polynomial.aeval (u * (1 - E)) Q.reverse := by
    rw [aeval_mul_one_sub_of_isIdempotentElem hEv.isIdempotentElem hEu, coeff_zero_reverse,
      smul_one_mul, smul_add, smul_mul_assoc, smul_smul, hcq, one_smul, add_comm]
  exact heq ▸ hulc.mul hunit

/-- Algebraic properties of `E = u.rieszColemanProjection Q` inherited directly from its definition
as a Riesz projection of `B(u)`, prior to sharpening nilpotence of `Q*(u)` on `range E` to `0`. -/
private theorem rieszColemanProjection_aux {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let E := u.rieszColemanProjection Q
    let B := 1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse
    IsRieszProjection (Polynomial.aeval u B) 1 Q.natDegree E ∧
      Commute u E ∧
      E ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) ∧
      (∃ w : C₀(I, R) →L[R] C₀(I, R), Polynomial.aeval u Q.reverse * w = 1 - E ∧
        w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
        w ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R)))) ∧
      IsUnit (Polynomial.aeval (u * (1 - E)) Q.reverse) := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : R[X] := 1 - Polynomial.C c * Q.reverse
  set v := Polynomial.aeval u B
  set E := u.rieszColemanProjection Q
  have hv : v.IsRowCompact := hu.aeval (coeff_zero_one_sub_C_mul_reverse hc)
  have hv_good := isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hu hQ0 hQ hS hQS hcop
  have hEv : IsRieszProjection v 1 Q.natDegree E :=
    hv.isRieszProjection_rieszProjection
      (fun _ ↦ hv_good.evalAt_hasseDeriv_eq_zero) hv_good.isUnit_evalAt_hasseDeriv
  have hsub : closure (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
      closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
    closure_mono (Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      (Polynomial.aeval_mem_adjoin_singleton R u)))
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hET : E ∈ T := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
    exact hsub hEv.mem_closure_adjoin
  have hEu : Commute u E := by
    rw [Commute, SemiconjBy]
    exact (Subalgebra.mem_centralizer_iff R).mp
      (Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer R {u} hET) u
      ((Subalgebra.mem_centralizer_iff R).mpr fun _ hy ↦ by rw [Set.mem_singleton_iff.mp hy])
  have h1v : (1 - (1 : R) • v : C₀(I, R) →L[R] C₀(I, R)) = c • Polynomial.aeval u Q.reverse := by
    simp [v, B, Algebra.algebraMap_eq_smul_one]
  have hwT : c • hEv.inverse ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    rw [← Subalgebra.topologicalClosure_coe]
    refine T.smul_mem ?_ c
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
    exact hsub hEv.inverse_mem_closure_adjoin
  refine ⟨hEv, hEu, hsub hEv.mem_closure_adjoin, ⟨c • hEv.inverse, ?_, ?_, ?_, ?_, hwT⟩,
    isUnit_aeval_mul_one_sub_reverse_of_isRieszProjection hQ hEv hEu⟩
  · rw [mul_smul_comm, ← smul_mul_assoc, ← h1v, hEv.one_sub_smul_mul_inverse]
  · rw [smul_mul_assoc, ← mul_smul_comm, ← h1v, hEv.inverse_mul_one_sub_smul]
  · rw [mul_smul_comm, hEv.mul_inverse_eq_zero]; ext x : 1; simp
  · rw [smul_mul_assoc, hEv.inverse_mul_eq_zero]; ext x : 1; simp

/-- Core determinant and Cayley–Hamilton step: for `E = u.rieszColemanProjection Q`, the Fredholm
factors satisfy `H_(uE) = Q` and `H_(u(1-E)) = S`, and `Q*(u) * E = 0`. -/
private theorem charPowerSeries_and_aeval_reverse_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let E := u.rieszColemanProjection Q
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S ∧
      Polynomial.aeval u Q.reverse * E = 0 := by
  obtain ⟨hEv, hEu, -, -, hunit_compl⟩ := rieszColemanProjection_aux hu hQ0 hQ hS hQS hcop
  set E := u.rieszColemanProjection Q
  have hc : Ring.inverse Q.leadingCoeff * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  have hv :
      (Polynomial.aeval u
        (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)).IsRowCompact :=
    hu.aeval (coeff_zero_one_sub_C_mul_reverse hc)
  have hv_good := isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hu hQ0 hQ hS hQS hcop
  have hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree :=
    hEv.rankAtStalk_range hv hv_good
  let : AddCommGroup E.range := inferInstance
  have := (hEv.isRowCompact hv).finite_range_of_isIdempotentElem hEv.isIdempotentElem
  have := (hEv.isRowCompact hv).projective_range_of_isIdempotentElem hEv.isIdempotentElem
  have hu_maps : ∀ x ∈ E.range, u x ∈ E.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨u y, congr($(hEu.eq.symm) y)⟩
  let f : Module.End R E.range := (u.restrict hu_maps).toLinearMap
  have hcharE : (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : R⟦X⟧) :=
    (hEv.isRowCompact hv).charPowerSeries_matrixCoeff_mul_eq_projectiveCharpolyRev
      hEv.isIdempotentElem hu_maps
  set P := f.projectiveCharpolyRev
  set S' := (u * (1 - E)).matrixCoeff.charPowerSeries
  have hS' : S'.IsEntire := (hu.comp_clm (1 - E)).isEntire_charPowerSeries
  have hsplit : (Q : R⟦X⟧) * S = (P : R⟦X⟧) * S' := by
    rw [← hQS, hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hEv.isIdempotentElem hEu, hcharE]
  have hcop' := ((hu.comp_clm (1 - E)).isUnit_aeval_reverse_iff hQ).mp hunit_compl
  have hdvd : (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) ∣
      ⟨P, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P)⟩ :=
    hcop'.dvd_of_dvd_mul_right ⟨⟨S, IsEntire.mem_subring.mpr hS⟩, Subtype.ext hsplit.symm⟩
  have hPQ : P = Q := TauCeti.PowerSeries.eq_of_coe_dvd_of_natDegree_le hQ hdvd
    (LinearMap.natDegree_projectiveCharpolyRev_le (fun p ↦ (hrank p).le) f)
    (hQ0 ▸ isRegular_one.left) (f.coeff_projectiveCharpolyRev_zero.trans hQ0.symm)
  refine ⟨hPQ ▸ hcharE,
    TauCeti.PowerSeries.eq_of_coe_mul_eq_coe_mul_of_isEntire hQ hS' hS (hPQ ▸ hsplit.symm), ?_⟩
  have hfQ : Polynomial.aeval f Q.reverse = 0 := by
    rw [← hPQ]
    exact LinearMap.aeval_reverse_projectiveCharpolyRev_eq_zero_of_rankAtStalk_le
      (f := f) (fun p ↦ by simpa [P, hPQ] using (hrank p).le)
  have hcomp : u.toLinearMap.comp E.range.subtype = E.range.subtype.comp f := by
    ext x
    simp [f]
  have haeval := Module.End.aeval_comp_of_comp_eq hcomp Q.reverse
  rw [hfQ, LinearMap.comp_zero] at haeval
  ext x : 1
  have hx := LinearMap.congr_fun haeval ⟨E x, ⟨x, rfl⟩⟩
  simpa only [LinearMap.comp_apply, Submodule.coe_subtype, ← toLinearMap_aeval, coe_coe,
    mul_apply_eq_comp, LinearMap.zero_apply, zero_apply] using hx

/-- Rescales a general coprime factorisation `u_series = Q * S` (with `u_series(0) = 1`) to the
normalised case `Q₁(0) = 1` via `b = S(0)` and `a = Q(0)`. -/
private theorem exists_normalised_factorisation {R : Type*} [NormedCommRing R]
    {u_series : R⟦X⟧} (hu0 : PowerSeries.constantCoeff u_series = 1)
    {Q : R[X]} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u_series = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ (b : R) (Q₁ : R[X]) (S₁ : R⟦X⟧) (hS₁ : S₁.IsEntire),
      IsUnit b ∧ Q₁ = Polynomial.C b * Q ∧ Q₁.coeff 0 = 1 ∧ IsUnit Q₁.leadingCoeff ∧
      Q₁.natDegree = Q.natDegree ∧ u_series = (Q₁ : R⟦X⟧) * S₁ ∧
      IsCoprime (⟨Q₁, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q₁)⟩ :
        IsEntire.subring R) ⟨S₁, IsEntire.mem_subring.mpr hS₁⟩ := by
  set a : R := Q.coeff 0
  set b : R := PowerSeries.constantCoeff S
  have hba : b * a = 1 := by
    have h0 := congrArg PowerSeries.constantCoeff hQS
    simpa [hu0, a, b, mul_comm] using h0.symm
  have hbu : IsUnit b := IsUnit.of_mul_eq_one a hba
  set Q₁ : R[X] := Polynomial.C b * Q
  set S₁ : R⟦X⟧ := PowerSeries.C a * S
  have hQ₁0 : Q₁.coeff 0 = 1 := by simp [Q₁, hba, a]
  have hQ₁deg : Q₁.natDegree = Q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hba)
  have hQ₁lc : IsUnit Q₁.leadingCoeff := by
    have hlc : Q₁.leadingCoeff = b * Q.leadingCoeff := by
      rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, hQ₁deg, Polynomial.coeff_C_mul]
    rw [hlc]
    exact hbu.mul hQ
  have hS₁ : S₁.IsEntire := (PowerSeries.isEntire_C a).mul hS
  have hQS₁ : u_series = (Q₁ : R⟦X⟧) * S₁ := by
    rw [hQS]
    simp only [Q₁, S₁, Polynomial.coe_mul, Polynomial.coe_C]
    calc (Q : R⟦X⟧) * S = PowerSeries.C (b * a) * ((Q : R⟦X⟧) * S) := by rw [hba, map_one, one_mul]
      _ = PowerSeries.C b * (Q : R⟦X⟧) * (PowerSeries.C a * S) := by rw [map_mul]; ring
  have hcop₁ : IsCoprime
      (⟨Q₁, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q₁)⟩ : IsEntire.subring R)
      ⟨S₁, IsEntire.mem_subring.mpr hS₁⟩ := by
    obtain ⟨x, y, hxy⟩ := hcop
    refine ⟨⟨PowerSeries.C a, IsEntire.mem_subring.mpr (PowerSeries.isEntire_C a)⟩ * x,
      ⟨PowerSeries.C b, IsEntire.mem_subring.mpr (PowerSeries.isEntire_C b)⟩ * y, ?_⟩
    apply Subtype.ext
    have hxy' := congrArg Subtype.val hxy
    simp only [Subring.coe_add, Subring.coe_mul, OneMemClass.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Q₁, S₁] at hxy' ⊢
    calc PowerSeries.C a * x.val * (PowerSeries.C b * (Q : R⟦X⟧)) +
          PowerSeries.C b * y.val * (PowerSeries.C a * S)
        = PowerSeries.C (b * a) * (x.val * (Q : R⟦X⟧) + y.val * S) := by rw [map_mul]; ring
      _ = 1 := by rw [hba, map_one, one_mul, hxy']
  exact ⟨b, Q₁, S₁, hS₁, hbu, rfl, hQ₁0, hQ₁lc, hQ₁deg, hQS₁, hcop₁⟩

/-- **The Riesz–Coleman projector at a coprime polynomial factor.** Let `u` be row compact on
`C₀(I, R)`, and suppose `H_u = Q * S` where `Q.leadingCoeff` is a unit, `S` is entire, and `Q`,
`S` are coprime entire series. Then `u.rieszColemanProjection Q` is a Riesz–Coleman projection of
`u` for `Q`. The factorisation forces `Q(0)` to be a unit, covering both normalised (`Q(0) = 1`)
and monic polynomial factors. -/
theorem IsRowCompact.isRieszColemanProjection_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) := by
  obtain ⟨b, Q₁, S₁, hS₁, hb, rfl, hQ₁0, hQ₁lc, -, hQS₁, hcop₁⟩ :=
    exists_normalised_factorisation (Matrix.constantCoeff_charPowerSeries _) hQ hS hQS hcop
  obtain ⟨hEv, hEu, hEmem, hex, -⟩ := rieszColemanProjection_aux hu hQ₁0 hQ₁lc hS₁ hQS₁ hcop₁
  obtain ⟨-, -, hzero⟩ :=
    charPowerSeries_and_aeval_reverse_rieszColemanProjection hu hQ₁0 hQ₁lc hS₁ hQS₁ hcop₁
  have hE₁ : IsRieszColemanProjection u (Polynomial.C b * Q)
      (u.rieszColemanProjection (Polynomial.C b * Q)) :=
    ⟨hEv.isIdempotentElem, hEu, hEmem, hzero, hex⟩
  rw [rieszColemanProjection_C_mul u hQ hb] at hE₁
  exact (IsRieszColemanProjection.iff_C_mul hb).mp hE₁

/-- **Existence of the Riesz–Coleman projection on model spaces.** Let `u` be row compact on
`C₀(I, R)`, and suppose `H_u = Q * S` where `Q.leadingCoeff` is a unit, `S` is entire, and `Q`,
`S` are coprime entire series. Then `u` admits a Riesz–Coleman projection for `Q`. -/
theorem IsRowCompact.exists_isRieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : C₀(I, R) →L[R] C₀(I, R), IsRieszColemanProjection u Q E :=
  ⟨u.rieszColemanProjection Q, hu.isRieszColemanProjection_rieszColemanProjection hQ hS hQS hcop⟩

namespace IsRieszColemanProjection

/-- Any Riesz–Coleman projection of a row-compact operator `u` at a coprime factorisation
`H_u = Q * S`, with `IsUnit Q.leadingCoeff` and `S` entire, agrees with the explicit
Riesz–Coleman projector `u.rieszColemanProjection Q`. -/
theorem eq_rieszColemanProjection {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    E = u.rieszColemanProjection Q :=
  hE.unique (hu.isRieszColemanProjection_rieszColemanProjection hQ hS hQS hcop)

/-- **Constant stalk rank of the Riesz–Coleman summand.** For a row-compact operator `u` with a
coprime factorisation `H_u = Q * S`, where `IsUnit Q.leadingCoeff` and `S` is entire, the finite
projective summand `range E = ker Q*(u)` has rank `Q.natDegree` at every prime ideal of `R`. -/
theorem rankAtStalk_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  obtain ⟨b, Q₁, S₁, hS₁, hb, rfl, hQ₁0, hQ₁lc, hQ₁deg, hQS₁, hcop₁⟩ :=
    exists_normalised_factorisation (Matrix.constantCoeff_charPowerSeries _) hQ hS hQS hcop
  have hE₁ : IsRieszColemanProjection u (Polynomial.C b * Q) E := hE.of_C_mul hb
  rw [hE₁.unique (hu.isRieszColemanProjection_rieszColemanProjection hQ₁lc hS₁ hQS₁ hcop₁)]
  obtain ⟨hEv, -⟩ := rieszColemanProjection_aux hu hQ₁0 hQ₁lc hS₁ hQS₁ hcop₁
  have hc : Ring.inverse (Polynomial.C b * Q).leadingCoeff *
      (Polynomial.C b * Q).leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ₁lc
  rw [← hQ₁deg]
  exact hEv.rankAtStalk_range (hu.aeval (coeff_zero_one_sub_C_mul_reverse hc))
    (isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hu hQ₁0 hQ₁lc hS₁ hQS₁ hcop₁) p

/-- **Fredholm factor on the finite Riesz–Coleman summand.** For a row-compact operator `u` with a
coprime factorisation `H_u = Q * S`, where `Q(0) = 1`, `IsUnit Q.leadingCoeff`, and `S` is entire,
the Fredholm series of `u * E` is `Q`. -/
theorem charPowerSeries_matrixCoeff_mul {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) := by
  rw [hE.eq_rieszColemanProjection hu hQ hS hQS hcop]
  exact (charPowerSeries_and_aeval_reverse_rieszColemanProjection hu hQ0 hQ hS hQS hcop).1

/-- **Fredholm factor on the complementary Riesz–Coleman summand.** For a row-compact operator `u`
with a coprime factorisation `H_u = Q * S`, where `Q(0) = 1`, `IsUnit Q.leadingCoeff`, and `S` is
entire, the Fredholm series of `u * (1 - E)` is `S`. -/
theorem charPowerSeries_matrixCoeff_mul_one_sub {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  rw [hE.eq_rieszColemanProjection hu hQ hS hQS hcop]
  exact (charPowerSeries_and_aeval_reverse_rieszColemanProjection hu hQ0 hQ hS hQS hcop).2.1

/-- **Characteristic polynomial of `u` on the finite Riesz–Coleman summand.** For a row-compact
operator `u` with a coprime factorisation `H_u = Q * S`, where `Q(0) = 1`, `IsUnit Q.leadingCoeff`,
and `S` is entire, the reversed characteristic polynomial `det (1 - X (u|_{range E}))` equals `Q`.
-/
theorem projectiveCharpolyRev_restrict_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    haveI : Module.Finite R E.range := hE.finite_range hQ hu
    haveI : Module.Projective R E.range := hE.projective_range hQ hu
    (((u.restrict fun _ hx ↦ hE.mapsTo_range hx).toLinearMap).projectiveCharpolyRev) = Q := by
  let : AddCommGroup E.range := inferInstance
  have := hE.finite_range hQ hu
  have := hE.projective_range hQ hu
  apply Polynomial.coe_inj.mp
  rw [← (hE.isRowCompact hQ hu).charPowerSeries_matrixCoeff_mul_eq_projectiveCharpolyRev
    hE.isIdempotentElem fun _ hx ↦ hE.mapsTo_range hx]
  exact hE.charPowerSeries_matrixCoeff_mul hu hQ0 hQ hS hQS hcop

end IsRieszColemanProjection

/-- **Constant stalk rank of `ker Q*(u)`.** For a row-compact operator `u` with a coprime
factorisation `H_u = Q * S`, where `IsUnit Q.leadingCoeff` and `S` is entire, the kernel
`ker Q*(u)` has rank `Q.natDegree` at every prime ideal of `R`. -/
theorem IsRowCompact.rankAtStalk_ker_aeval_reverse {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)).ker p =
      Q.natDegree := by
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ hS hQS hcop
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range hu hQ hS hQS hcop p

end Decomposition

section Field

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Over a complete ultrametric field, the finite Riesz–Coleman summand `range E = ker Q*(u)` of a
row-compact operator `u` has dimension `Q.natDegree` whenever `H_u = Q * S` is a coprime
factorisation into a polynomial `Q` and an entire series `S`. -/
theorem IsRieszColemanProjection.finrank_range {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : K[X]}
    {S : K⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hS : S.IsEntire) (hQS : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQne : Q ≠ 0 := by
    rintro rfl
    have h0 := congrArg PowerSeries.constantCoeff hQS
    simp at h0
  have hQ : IsUnit Q.leadingCoeff := (leadingCoeff_ne_zero.mpr hQne).isUnit
  have hr := hE.rankAtStalk_range hu hQ hS hQS hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, `ker Q*(u)` has dimension `Q.natDegree` whenever
`H_u = Q * S` is a coprime factorisation into a polynomial `Q` and an entire series `S`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) {Q : K[X]} {S : K⟦X⟧}
    (hS : S.IsEntire) (hQS : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)).ker =
      Q.natDegree := by
  have hQne : Q ≠ 0 := by
    rintro rfl
    have h0 := congrArg PowerSeries.constantCoeff hQS
    simp at h0
  have hQ : IsUnit Q.leadingCoeff := (leadingCoeff_ne_zero.mpr hQne).isUnit
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ hS hQS hcop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range hu hS hQS hcop

end Field

section BaseChange

variable {I R S : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [TauCeti.NormedRing.IsTate S]

/-- **Riesz–Coleman projections under bounded base change.** When `Q.leadingCoeff` is a unit, the
coefficientwise extension of a Riesz–Coleman projection of `u` for `Q` is a Riesz–Coleman
projection of `u.mapCoeffs f hf` for `Q.map f`. No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have hrev := reverse_map_of_isUnit_leadingCoeff hQ f
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨?_, ?_, mapCoeffs_mem_closure_adjoin f hf hE.mem_closure_adjoin, ?_,
    ⟨w.mapCoeffs f hf, ?_, ?_, ?_, ?_, mapCoeffs_mem_closure_adjoin f hf hw⟩⟩
  · simpa [IsIdempotentElem] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.isIdempotentElem.eq
  · simpa [Commute, SemiconjBy] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.commute.eq
  · rw [hrev, aeval_mapCoeffs, ← mapCoeffs_mul, hE.aeval_reverse_mul_eq_zero, mapCoeffs_zero]
  · rw [hrev, aeval_mapCoeffs, ← mapCoeffs_mul, hw₁, mapCoeffs_sub, mapCoeffs_one]
  · rw [hrev, aeval_mapCoeffs, ← mapCoeffs_mul, hw₂, mapCoeffs_sub, mapCoeffs_one]
  · rw [← mapCoeffs_mul, hw₃, mapCoeffs_zero]
  · rw [← mapCoeffs_mul, hw₄, mapCoeffs_zero]

/-- The complementary inverse of a Riesz–Coleman projection commutes with bounded base change. -/
theorem IsRieszColemanProjection.inverse_mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (hE.mapCoeffs hQ f hf).inverse = hE.inverse.mapCoeffs f hf := by
  have hrev := reverse_map_of_isUnit_leadingCoeff hQ f
  refine ((hE.mapCoeffs hQ f hf).eq_inverse ?_ ?_).symm
  · rw [hrev, aeval_mapCoeffs, ← mapCoeffs_mul, hE.aeval_reverse_mul_inverse, mapCoeffs_sub,
      mapCoeffs_one]
  · rw [← mapCoeffs_mul, hE.mul_inverse_eq_zero, mapCoeffs_zero]

/-- **Bounded base change of the explicit Riesz–Coleman projector.** For a row-compact operator `u`
with a coprime factorisation `H_u = Q * S'`, where `IsUnit Q.leadingCoeff` and `S'` is entire, the
explicit Riesz–Coleman projector of `u.mapCoeffs f hf` for `Q.map f` is the coefficientwise
extension of `u.rieszColemanProjection Q`. -/
theorem IsRowCompact.rieszColemanProjection_mapCoeffs [IsUltrametricDist R]
    [CompleteSpace R] {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S' : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire)
    (hQS' : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).rieszColemanProjection (Q.map f) =
      (u.rieszColemanProjection Q).mapCoeffs f hf := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · ext x i; exact Subsingleton.elim _ _
  obtain ⟨b, Q₁, S₁, hS₁, hb, hQ₁, hQ₁0, hQ₁lc, -, hQS₁, hcop₁⟩ :=
    exists_normalised_factorisation (Matrix.constantCoeff_charPowerSeries _) hQ hS' hQS' hcop
  have hc : Ring.inverse Q₁.leadingCoeff * Q₁.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ₁lc
  have hdeg : (Q₁.map f).natDegree = Q₁.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero f (hQ₁lc.map f).ne_zero
  have hlc : (Q₁.map f).leadingCoeff = f Q₁.leadingCoeff :=
    leadingCoeff_map_of_leadingCoeff_ne_zero f (hQ₁lc.map f).ne_zero
  have hBmap : 1 - Polynomial.C (Ring.inverse (Q₁.map f).leadingCoeff) * (Q₁.map f).reverse =
      (1 - Polynomial.C (Ring.inverse Q₁.leadingCoeff) * Q₁.reverse).map f := by
    rw [hlc, ← hQ₁lc.map_ringInverse f, reverse_map_of_isUnit_leadingCoeff hQ₁lc f]
    simp [Polynomial.map_sub, Polynomial.map_mul]
  have hv :
      (Polynomial.aeval u
        (1 - Polynomial.C (Ring.inverse Q₁.leadingCoeff) * Q₁.reverse)).IsRowCompact :=
    hu.aeval (coeff_zero_one_sub_C_mul_reverse hc)
  have hv_good :=
    isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hu hQ₁0 hQ₁lc hS₁ hQS₁ hcop₁
  have hnorm : (u.mapCoeffs f hf).rieszColemanProjection (Q₁.map f) =
      (u.rieszColemanProjection Q₁).mapCoeffs f hf := by
    rw [rieszColemanProjection_def, rieszColemanProjection_def, hdeg, hBmap, aeval_mapCoeffs,
      ← map_one f, hv.rieszProjection_mapCoeffs f hf hv_good.isUnit_evalAt_hasseDeriv]
  have hQflc : IsUnit (Q.map f).leadingCoeff := by
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero]
    exact hQ.map f
  rw [hQ₁, Polynomial.map_mul, Polynomial.map_C] at hnorm
  rwa [rieszColemanProjection_C_mul _ hQflc (hb.map f),
    rieszColemanProjection_C_mul u hQ hb] at hnorm

/-- After bounded base change, the Riesz–Coleman summand of a coprime factorisation `H_u = Q * S'`
has constant stalk rank `Q.natDegree` at every prime ideal of `S`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_mapCoeffs [IsUltrametricDist R] [CompleteSpace R]
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S' : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire)
    (hQS' : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (q : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (E.mapCoeffs f hf).range q = Q.natDegree := by
  have : Nontrivial S :=
    ⟨⟨1, 0, fun h ↦ q.isPrime.ne_top ((Ideal.eq_top_iff_one q.asIdeal).2 (h ▸ q.asIdeal.zero_mem))⟩⟩
  have hQdeg : (Q.map f).natDegree = Q.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero
  have hQlc : IsUnit (Q.map f).leadingCoeff := by
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero]
    exact hQ.map f
  have hQmap : ((Q.map f : S[X]) : S⟦X⟧) = PowerSeries.map f (Q : R⟦X⟧) := by
    ext n; simp
  have hHS : (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
      ((Q.map f : S[X]) : S⟦X⟧) * PowerSeries.map f S' := by
    rw [hu.charPowerSeries_map f hf, hQS', map_mul, hQmap]
  have hFS : (PowerSeries.map f S').IsEntire := hS'.map f hf.choose_spec
  have hcopS : IsCoprime
      (⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
        IsEntire.subring S)
      ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr hFS⟩ := by
    have h := hcop.map (IsEntire.mapHom f hf.choose_spec)
    rwa [show IsEntire.mapHom f hf.choose_spec
        ⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ =
        ⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ from
        Subtype.ext ((IsEntire.coe_mapHom _ _ _).trans hQmap.symm),
      show IsEntire.mapHom f hf.choose_spec
        ⟨S', IsEntire.mem_subring.mpr hS'⟩ =
        ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr hFS⟩ from
        Subtype.ext (IsEntire.coe_mapHom _ _ _)] at h
  rw [← hQdeg]
  exact (hE.mapCoeffs hQ f hf).rankAtStalk_range (hu.mapCoeffs f hf) hQlc hFS hHS hcopS q

end BaseChange

section FieldBaseChange

variable {I K L : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- **Bounded field extension preserves `dim ker Q*(u)`.** For a coprime factorisation `H_u = Q * S`
of the Fredholm series of a row-compact operator `u` on `C₀(I, K)`, bounded coefficient extension
along `f : K →+* L` preserves the dimension of `ker Q*(u)`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖)
    {Q : K[X]} {S : K⟦X⟧} (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank L (Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
        C₀(I, L) →L[L] C₀(I, L)).ker =
      Module.finrank K (Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)).ker := by
  have hQne : Q ≠ 0 := by
    rintro rfl
    have h0 := congrArg PowerSeries.constantCoeff hQS
    simp at h0
  have hQ : IsUnit Q.leadingCoeff := (leadingCoeff_ne_zero.mpr hQne).isUnit
  have hQdeg : (Q.map f).natDegree = Q.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero
  have hQmap : ((Q.map f : L[X]) : L⟦X⟧) = PowerSeries.map f (Q : K⟦X⟧) := by
    ext n; simp
  have hHL : (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
      ((Q.map f : L[X]) : L⟦X⟧) * PowerSeries.map f S := by
    rw [hu.charPowerSeries_map f hf, hQS, map_mul, hQmap]
  have hFL : (PowerSeries.map f S).IsEntire := hS.map f hf.choose_spec
  have hcopL : IsCoprime
      (⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
        IsEntire.subring L)
      ⟨PowerSeries.map f S, IsEntire.mem_subring.mpr hFL⟩ := by
    have h := hcop.map (IsEntire.mapHom f hf.choose_spec)
    rwa [show IsEntire.mapHom f hf.choose_spec
        ⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ =
        ⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ from
        Subtype.ext ((IsEntire.coe_mapHom _ _ _).trans hQmap.symm),
      show IsEntire.mapHom f hf.choose_spec
        ⟨S, IsEntire.mem_subring.mpr hS⟩ =
        ⟨PowerSeries.map f S, IsEntire.mem_subring.mpr hFL⟩ from
        Subtype.ext (IsEntire.coe_mapHom _ _ _)] at h
  rw [(hu.mapCoeffs f hf).finrank_ker_aeval_reverse hFL hHL hcopL,
    hu.finrank_ker_aeval_reverse hS hQS hcop, hQdeg]

end FieldBaseChange

end ContinuousLinearMap
