/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coprime
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
import TauCeti.Algebra.Polynomial.AlgebraMap
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Analysis.Polynomial.Coleman.Coprime
import TauCeti.RingTheory.PowerSeries.Dvd
import TauCeti.RingTheory.PowerSeries.Entire.Coprime
import TauCeti.RingTheory.PowerSeries.Entire.Division
import TauCeti.Topology.Algebra.Algebra.Basic

/-!
# The Riesz–Coleman decomposition on model spaces

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, let
`u : C₀(I, R) →L[R] C₀(I, R)` be a row-compact operator, and suppose its Fredholm series
`H_u = det (1 - T u)` admits a factorisation

  `H_u = Q * S`

where `Q : R[X]` has `IsUnit Q.leadingCoeff`, `S` is an entire power series, and `Q` and `S` are
coprime in the subring `PowerSeries.IsEntire.subring R` of entire series (note that `H_u(0) = 1`
forces `Q(0)` to be a unit, so rescaling `Q` by `Q(0)⁻¹` reduces to the normalised case
`Q(0) = 1`).

Following Coleman (Appendix A4), set `c = Ring.inverse Q.leadingCoeff` and consider the polynomial
`B = 1 - c Q*`, where `Q* = Q.reverse`. Since `IsUnit Q.leadingCoeff` gives `B(0) = 0`, the
operator `v = B(u)` is row compact before any normalisation. Note also that
`u.rieszColemanProjection (C b * Q) = u.rieszColemanProjection Q` for any unit `b`
(`ContinuousLinearMap.rieszColemanProjection_C_mul`).

Working with the normalised pair `(Q₁, S₁) = (Q(0)⁻¹ Q, Q(0) S)` satisfying `Q₁(0) = 1` (which
leaves `B`, `v`, and the projector unchanged), polynomial spectral mapping gives

  `H_v(T) = D(B, H_u)(T) = D(B, Q₁)(T) * D(B, S₁)(T) = (1 - T) ^ (deg Q₁) * D(B, S₁)(T)`.

Because `Q₁` and `S₁` are coprime entire series, `D(B, S₁)(1)` is a unit in `R`, so `H_v` has a
good zero of order `d = deg Q₁ = deg Q` at `T = 1`. The Riesz projector

  `u.rieszColemanProjection Q = v.rieszProjection 1 (deg Q)`

therefore cuts out a finite projective `u`-stable summand `range E` of constant rank `deg Q` on
`Spec R` on whose complement `1 - v = c Q*(u)` is invertible.

Comparing `H_u = Q₁ * S₁` with the multiplicative splitting `H_u = H_(uE) * H_(u(1-E))`, where
`H_(uE)` is the reversed characteristic polynomial `P = det (1 - X (u|_{range E}))` of degree at
most `deg Q₁` and `Q₁*(u * (1 - E))` is invertible on `C₀(I, R)`, coprimality of `Q₁` and
`H_(u(1-E))` forces `Q₁ ∣ P` in entire series; monic division by `lc(Q₁)⁻¹ Q₁` (using `Q₁(0) = 1`)
and degree comparison yield `P = Q₁` and `H_(u(1-E)) = S₁`. Constant-rank Cayley–Hamilton on the
finite projective module `range E` then yields exact annihilation `Q₁*(u) * E = 0` directly from
`P = Q₁` and the rank bound `rankAtStalk E.range p ≤ deg Q₁`, establishing
`IsRieszColemanProjection u Q (u.rieszColemanProjection Q)` together with the Fredholm factor
identities `H_(uE) = Q(0)⁻¹ Q` and `H_(u(1-E)) = Q(0) S` (which simplify to `Q` and `S` when
`Q(0) = 1`).

## Main definitions

* `ContinuousLinearMap.rieszColemanProjection`: the explicit Riesz–Coleman projector
  `(B(u)).rieszProjection 1 Q.natDegree` for `B = 1 - lc(Q)⁻¹ Q*`.

## Main results

* `ContinuousLinearMap.IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse`,
  `ContinuousLinearMap.IsRowCompact.isRieszProjection_rieszColemanProjection`,
  `ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`, and
  `ContinuousLinearMap.IsRowCompact.exists_isRieszColemanProjection`: good Fredholm zero after
  Coleman's polynomial transform, Riesz-projection characterization, and existence of the
  Riesz–Coleman projection for a coprime polynomial factorisation `H_u = Q * S` on `C₀(I, R)`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRowCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range`, and
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse`: `range E = ker Q*(u)` has constant
  stalk rank `deg Q` on `Spec R` (and dimension `deg Q` over a field).
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub`, and
  `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range`: the Fredholm
  factors on the two summands are `H_(uE) = C (Ring.inverse (Q.coeff 0)) * Q` and
  `H_(u(1-E)) = C (Q.coeff 0) * S`, and
  `det (1 - X (u|_{range E})) = C (Ring.inverse (Q.coeff 0)) * Q`
  (simplifying to `Q` and `S` when `Q(0) = 1`).

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

/-- Scaling `Q` by a unit scalar does not change `u.rieszColemanProjection Q`. -/
@[simp]
theorem rieszColemanProjection_C_mul (u : C₀(I, R) →L[R] C₀(I, R)) {Q : R[X]}
    {b : R} (hb : IsUnit b) :
    u.rieszColemanProjection (Polynomial.C b * Q) = u.rieszColemanProjection Q := by
  rw [rieszColemanProjection_def, rieszColemanProjection_def,
    Polynomial.natDegree_C_mul_of_isUnit hb,
    Polynomial.C_inverse_leadingCoeff_mul_reverse_C_mul hb]

end Defs

section Decomposition

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]

/-- **Good zero after Coleman's polynomial transform.** For a row-compact `u` under a coprime
factorisation `H_u = Q * S` with `IsUnit Q.leadingCoeff`, the operator `B(u)` for
`B = 1 - lc(Q)⁻¹ Q*` has a good Fredholm zero at `1` of order `Q.natDegree`. -/
theorem IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u
      (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)).matrixCoeff
      |>.charPowerSeries.IsGoodZero 1 Q.natDegree := by
  obtain ⟨hb, hS₁, hQ₁0, hQ₁, hQ₁deg, hQS₁, hcop₁⟩ :=
    IsEntire.normalized_factorization (Matrix.constantCoeff_charPowerSeries _) hQ hS hQS hcop
  rw [← hQ₁deg, ← Polynomial.C_inverse_leadingCoeff_mul_reverse_C_mul hb Q]
  set Q₁ := Polynomial.C (Ring.inverse (Q.coeff 0)) * Q
  set S₁ : R⟦X⟧ := PowerSeries.C (Q.coeff 0) * S
  set c := Ring.inverse Q₁.leadingCoeff
  have hc : c * Q₁.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ₁
  set B : R[X] := 1 - Polynomial.C c * Q₁.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have hS0 : PowerSeries.constantCoeff S₁ = 1 := by
    simpa [hQ₁0] using (congrArg PowerSeries.constantCoeff hQS₁).symm
  have hS0' : PowerSeries.coeff 0 S₁ = 1 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hEe : (B.colemanDSeries S₁).IsEntire :=
    PowerSeries.colemanDEntire_coe (F := S₁) hB0 hS0' ▸
      PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS₁
        (by rwa [Polynomial.coeff_coe]) hS0'
  have hunitS : IsUnit ((B.colemanDSeries S₁).evalAt (1 : R)) :=
    (isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc hS₁ hS0).mpr hcop₁
  set g : R⟦X⟧ := PowerSeries.C ((-1 : R) ^ Q₁.natDegree) * B.colemanDSeries S₁
  have hg : g.IsEntire := (PowerSeries.isEntire_C _).mul hEe
  have hgu : IsUnit (g.evalAt (1 : R)) := by
    rw [(PowerSeries.isEntire_C _).evalAt_mul hEe, PowerSeries.evalAt_C]
    exact (isUnit_one.neg.pow Q₁.natDegree).mul hunitS
  have hpow : ((1 - PowerSeries.X : R⟦X⟧) ^ Q₁.natDegree) * B.colemanDSeries S₁ =
      (PowerSeries.X - PowerSeries.C 1) ^ Q₁.natDegree * g := by
    have h1 : (1 - PowerSeries.X : R⟦X⟧) =
        (PowerSeries.X - PowerSeries.C 1) * PowerSeries.C (-1) := by
      ext n; simp [sub_eq_add_neg, add_comm]
    rw [h1, mul_pow, ← map_pow, mul_assoc]
  rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hQS₁, colemanDSeries_mul hB0,
    colemanDSeries_one_sub_C_mul_reverse_self hQ₁0 hc, hpow]
  exact hg.isGoodZero_X_sub_C_pow_mul_iff.mpr hgu

/-- For row-compact `u` under a coprime factorisation `H_u = Q * S` with `IsUnit Q.leadingCoeff`,
`u.rieszColemanProjection Q` is the Riesz projection of `(1 - lc(Q)⁻¹ Q*)(u)` at `1` of order
`Q.natDegree`. -/
theorem IsRowCompact.isRieszProjection_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszProjection
      (Polynomial.aeval u (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse))
      1 Q.natDegree (u.rieszColemanProjection Q) := by
  have hv := hu.aeval (coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ))
  have hGood := hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hQ hS hQS hcop
  exact hv.isRieszProjection_rieszProjection
    (fun _ ↦ hGood.evalAt_hasseDeriv_eq_zero) hGood.isUnit_evalAt_hasseDeriv

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- For a Riesz projection `E` of `1 - lc(Q)⁻¹ Q*(u)` at `1`, scaling `hEv.inverse` by
`lc(Q)⁻¹` provides a complementary inverse of `Q*(u)` on `ker E` lying in the closure of `R[u]`.
-/
private theorem exists_inverse_aeval_reverse_of_isRieszProjection
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    {u E : M →L[R] M} {Q : R[X]}
    (hEv : IsRieszProjection
      (Polynomial.aeval u (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse))
      1 Q.natDegree E)
    (hsub : closure (Algebra.adjoin R
          {Polynomial.aeval u (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)} :
            Set (M →L[R] M)) ⊆
        closure (Algebra.adjoin R {u} : Set (M →L[R] M))) :
    ∃ w : M →L[R] M, Polynomial.aeval u Q.reverse * w = 1 - E ∧
      w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
      w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
  set c := Ring.inverse Q.leadingCoeff
  have h1v : (1 - (1 : R) • Polynomial.aeval u (1 - Polynomial.C c * Q.reverse) : M →L[R] M) =
      c • Polynomial.aeval u Q.reverse := by
    simpa only [one_smul] using Polynomial.one_sub_aeval_one_sub_C_mul u c Q.reverse
  refine ⟨c • hEv.inverse, ?_, ?_, ?_, ?_,
    (Algebra.adjoin R {u}).topologicalClosure.smul_mem (hsub hEv.inverse_mem_closure_adjoin) c⟩
  · rw [mul_smul_comm, ← smul_mul_assoc, ← h1v, hEv.one_sub_smul_mul_inverse]
  · rw [smul_mul_assoc, ← mul_smul_comm, ← h1v, hEv.inverse_mul_one_sub_smul]
  · rw [mul_smul_comm, hEv.mul_inverse_eq_zero, smul_zero]
  · rw [smul_mul_assoc, hEv.inverse_mul_eq_zero, smul_zero]

/-- Core determinant and Cayley–Hamilton step: for `E = u.rieszColemanProjection Q`, the Fredholm
factors satisfy `H_(uE) = Q` and `H_(u(1-E)) = S`, and `Q*(u) * E = 0`. -/
private theorem charPowerSeries_and_aeval_reverse_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hE_idem : IsIdempotentElem (u.rieszColemanProjection Q))
    (hEu : Commute u (u.rieszColemanProjection Q))
    (hunit_compl : IsUnit (Polynomial.aeval (u * (1 - u.rieszColemanProjection Q)) Q.reverse))
    (hE_rc : (u.rieszColemanProjection Q).IsRowCompact)
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (R := R) (u.rieszColemanProjection Q).range p = Q.natDegree) :
    let E := u.rieszColemanProjection Q
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S ∧
      Polynomial.aeval u Q.reverse * E = 0 := by
  set E := u.rieszColemanProjection Q
  let : AddCommGroup E.range := inferInstance
  have := hE_rc.finite_range_of_isIdempotentElem hE_idem
  have := hE_rc.projective_range_of_isIdempotentElem hE_idem
  have hu_maps : ∀ x ∈ E.range, u x ∈ E.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨u y, congr($(hEu.eq.symm) y)⟩
  let f : Module.End R E.range := (u.restrict hu_maps).toLinearMap
  have hcharE : (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : R⟦X⟧) :=
    hE_rc.charPowerSeries_matrixCoeff_mul_eq_projectiveCharpolyRev hE_idem hu_maps
  set P := f.projectiveCharpolyRev
  set S' := (u * (1 - E)).matrixCoeff.charPowerSeries
  have hS' : S'.IsEntire := (hu.comp_clm (1 - E)).isEntire_charPowerSeries
  have hsplit : (Q : R⟦X⟧) * S = (P : R⟦X⟧) * S' := by
    rw [← hQS, hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hE_idem hEu, hcharE]
  have hcop' := ((hu.comp_clm (1 - E)).isUnit_aeval_reverse_iff hQ).mp hunit_compl
  have hdvd : IsEntire.polynomialHom Q ∣ IsEntire.polynomialHom P :=
    hcop'.dvd_of_dvd_mul_right ⟨⟨S, IsEntire.mem_subring.mpr hS⟩, Subtype.ext <| by
      rw [Subring.coe_mul, Subring.coe_mul, IsEntire.coe_polynomialHom,
        IsEntire.coe_polynomialHom]
      exact hsplit.symm⟩
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

/-- Normalised-case construction of `E = u.rieszColemanProjection Q`: returns the Riesz–Coleman
projection certificate, constant stalk rank, and both Fredholm factor identities when `Q(0) = 1`.
-/
private theorem rieszColemanProjection_aux {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let E := u.rieszColemanProjection Q
    IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) ∧
      (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : R[X] := 1 - Polynomial.C c * Q.reverse
  set v := Polynomial.aeval u B
  set E := u.rieszColemanProjection Q
  have hv : v.IsRowCompact := hu.aeval (coeff_zero_one_sub_C_mul_reverse hc)
  have hv_good := hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hQ hS hQS hcop
  have hEv : IsRieszProjection v 1 Q.natDegree E :=
    hu.isRieszProjection_rieszColemanProjection hQ hS hQS hcop
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  have hsub : Algebra.elemental R v ≤ Algebra.elemental R u :=
    Algebra.elemental.le_of_mem (Algebra.elemental.isClosed R u)
      (Algebra.mem_elemental_iff.mpr (subset_closure (Polynomial.aeval_mem_adjoin_singleton R u)))
  have hclosure : ∀ {x}, x ∈ closure (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) →
      x ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
    fun hx ↦ Algebra.mem_elemental_iff.mp (hsub (Algebra.mem_elemental_iff.mpr hx))
  have hE_mem : E ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
    hclosure hEv.mem_closure_adjoin
  have hEu : Commute u E :=
    (Subalgebra.mem_centralizer_iff R).mp
      (Algebra.elemental.le_centralizer_centralizer R u (Algebra.mem_elemental_iff.mpr hE_mem)) u
      ((Subalgebra.mem_centralizer_iff R).mpr fun _ hy ↦ by rw [Set.mem_singleton_iff.mp hy])
  have hex := exists_inverse_aeval_reverse_of_isRieszProjection hEv fun _ hx ↦ hclosure hx
  have hunit_compl : IsUnit (Polynomial.aeval (u * (1 - E)) Q.reverse) := by
    obtain ⟨w, hw₁, hw₂, _⟩ := hex
    -- `Q*(u) * E = 0` is proved below from `hunit_compl`, so use the idempotent criterion directly.
    exact Polynomial.isUnit_aeval_mul_one_sub_of_isIdempotentElem (u := u) (e := E) (w := w)
      (P := Q.reverse) hEv.isIdempotentElem hEu (Polynomial.coeff_zero_reverse Q ▸ hQ) hw₁ hw₂
  have hE_rc := hEv.isRowCompact hv
  have hrank := hEv.rankAtStalk_range hv hv_good
  obtain ⟨hcharE, hcharCompl, hzero⟩ :=
    charPowerSeries_and_aeval_reverse_rieszColemanProjection hu hQ0 hQ hS hQS
      hEv.isIdempotentElem hEu hunit_compl hE_rc hrank
  exact ⟨⟨hEv.isIdempotentElem, hEu, hE_mem, hzero, hex⟩,
    hrank, hcharE, hcharCompl⟩

/-- Wraps `rieszColemanProjection_aux` by normalising `Q` once and returning the Riesz–Coleman
projection certificate, the constant stalk rank, and both Fredholm factor identities for the
original factorisation `H_u = Q * S`. -/
private theorem rieszColemanProjection_spec
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let E := u.rieszColemanProjection Q
    IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) ∧
      (u * E).matrixCoeff.charPowerSeries =
        ((Polynomial.C (Ring.inverse (Q.coeff 0)) * Q : R[X]) : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = PowerSeries.C (Q.coeff 0) * S := by
  obtain ⟨hb, hS₁, hQ₁0, hQ₁lc, hQ₁deg, hQS₁, hcop₁⟩ :=
    IsEntire.normalized_factorization (Matrix.constantCoeff_charPowerSeries _) hQ hS hQS hcop
  obtain ⟨hE₁, hrank₁, hcharE, hcharCompl⟩ :=
    rieszColemanProjection_aux hu hQ₁0 hQ₁lc hS₁ hQS₁ hcop₁
  rw [rieszColemanProjection_C_mul u hb] at hE₁ hrank₁ hcharE hcharCompl
  exact ⟨(isRieszColemanProjection_C_mul_iff hb).mp hE₁,
    fun p ↦ (hrank₁ p).trans hQ₁deg, hcharE, hcharCompl⟩

/-- **The Riesz–Coleman projector at a coprime polynomial factor.** Let `u` be row compact on
`C₀(I, R)`, and suppose `H_u = Q * S` where `Q.leadingCoeff` is a unit, `S` is entire, and `Q`,
`S` are coprime entire series. Then `u.rieszColemanProjection Q` is a Riesz–Coleman projection of
`u` for `Q`. The factorisation forces `Q(0)` to be a unit, covering both normalised (`Q(0) = 1`)
and monic polynomial factors. -/
theorem IsRowCompact.isRieszColemanProjection_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) :=
  (rieszColemanProjection_spec hu hQ hS hQS hcop).1

/-- **Existence of the Riesz–Coleman projection on model spaces.** Let `u` be row compact on
`C₀(I, R)`, and suppose `H_u = Q * S` where `Q.leadingCoeff` is a unit, `S` is entire, and `Q`,
`S` are coprime entire series. Then `u` admits a Riesz–Coleman projection for `Q`. -/
theorem IsRowCompact.exists_isRieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
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
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    E = u.rieszColemanProjection Q :=
  hE.unique (hu.isRieszColemanProjection_rieszColemanProjection hQ hS hQS hcop)

/-- **Constant stalk rank of the Riesz–Coleman summand.** For a row-compact operator `u` with a
coprime factorisation `H_u = Q * S`, where `IsUnit Q.leadingCoeff` and `S` is entire, the finite
projective summand `range E = ker Q*(u)` has rank `Q.natDegree` at every prime ideal of `R`. -/
theorem rankAtStalk_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  obtain ⟨hE', hrank, -, -⟩ := rieszColemanProjection_spec hu hQ hS hQS hcop
  rw [hE.unique hE']
  exact hrank p

/-- **Fredholm factor on the finite Riesz–Coleman summand.** For a row-compact operator `u` with a
coprime factorisation `H_u = Q * S`, where `IsUnit Q.leadingCoeff` and `S` is entire, the
Fredholm series of `u * E` is the normalised polynomial `C (Ring.inverse (Q.coeff 0)) * Q`
(which simplifies to `Q` when `Q.coeff 0 = 1`). -/
theorem charPowerSeries_matrixCoeff_mul {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries =
      ((Polynomial.C (Ring.inverse (Q.coeff 0)) * Q : R[X]) : R⟦X⟧) := by
  obtain ⟨hE', -, hchar, -⟩ := rieszColemanProjection_spec hu hQ hS hQS hcop
  rw [hE.unique hE']
  exact hchar

/-- **Fredholm factor on the complementary Riesz–Coleman summand.** For a row-compact operator `u`
with a coprime factorisation `H_u = Q * S`, where `IsUnit Q.leadingCoeff` and `S` is entire, the
Fredholm series of `u * (1 - E)` is `C (Q.coeff 0) * S` (which simplifies to `S` when
`Q.coeff 0 = 1`). -/
theorem charPowerSeries_matrixCoeff_mul_one_sub {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = PowerSeries.C (Q.coeff 0) * S := by
  obtain ⟨hE', -, -, hchar⟩ := rieszColemanProjection_spec hu hQ hS hQS hcop
  rw [hE.unique hE']
  exact hchar

/-- **Characteristic polynomial of `u` on the finite Riesz–Coleman summand.** For a row-compact
operator `u` with a coprime factorisation `H_u = Q * S`, where `IsUnit Q.leadingCoeff` and `S` is
entire, the reversed characteristic polynomial `det (1 - X (u|_{range E}))` equals
`C (Ring.inverse (Q.coeff 0)) * Q` (which simplifies to `Q` when `Q.coeff 0 = 1`). -/
theorem projectiveCharpolyRev_restrict_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    haveI : Module.Finite R E.range := hE.finite_range hQ hu
    haveI : Module.Projective R E.range := hE.projective_range hQ hu
    (((u.restrict fun _ hx ↦ hE.mapsTo_range hx).toLinearMap).projectiveCharpolyRev) =
      Polynomial.C (Ring.inverse (Q.coeff 0)) * Q := by
  let : AddCommGroup E.range := inferInstance
  have := hE.finite_range hQ hu
  have := hE.projective_range hQ hu
  apply Polynomial.coe_inj.mp
  rw [← (hE.isRowCompact hQ hu).charPowerSeries_matrixCoeff_mul_eq_projectiveCharpolyRev
    hE.isIdempotentElem fun _ hx ↦ hE.mapsTo_range hx]
  exact hE.charPowerSeries_matrixCoeff_mul hu hQ hS hQS hcop

end IsRieszColemanProjection

/-- **Constant stalk rank of `ker Q*(u)`.** For a row-compact operator `u` with a coprime
factorisation `H_u = Q * S`, where `IsUnit Q.leadingCoeff` and `S` is entire, the kernel
`ker Q*(u)` has rank `Q.natDegree` at every prime ideal of `R`. -/
theorem IsRowCompact.rankAtStalk_ker_aeval_reverse {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)).ker p =
      Q.natDegree := by
  obtain ⟨hE, hrank, -, -⟩ := rieszColemanProjection_spec hu hQ hS hQS hcop
  rw [← hE.range_eq_ker]
  exact hrank p

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
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQ := PowerSeries.isUnit_leadingCoeff_of_eq_coe_mul
    (Matrix.constantCoeff_charPowerSeries _) hQS
  have hr := hE.rankAtStalk_range hu hQ hS hQS hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, `ker Q*(u)` has dimension `Q.natDegree` whenever
`H_u = Q * S` is a coprime factorisation into a polynomial `Q` and an entire series `S`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) {Q : K[X]} {S : K⟦X⟧}
    (hS : S.IsEntire) (hQS : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)).ker =
      Q.natDegree := by
  have hQ := PowerSeries.isUnit_leadingCoeff_of_eq_coe_mul
    (Matrix.constantCoeff_charPowerSeries _) hQS
  have hr := hu.rankAtStalk_ker_aeval_reverse hQ hS hQS hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup (Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)).ker :=
    inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

end Field

end ContinuousLinearMap
