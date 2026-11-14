/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Factorization
import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on modules with property (Pr)

Over a complete ultrametric Tate ring `R`, a module `M` with property `(Pr)` is a continuous linear
retract `r ∘ i = id` of `C₀(J, R)`. Compressing Riesz–Coleman projections along `r` and `i`
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`) transfers existence, row
compactness, finite projectivity, constant stalk rank `Q.natDegree`, normalized determinant
identities (`Q.coeff 0 = 1`), and field dimensions to `(Pr)` modules, while showing that `E.ker`
again has `(Pr)` with `(u|_{E.ker}).charPowerSeries = (u * (1 - E)).charPowerSeries`.

## Main results

* `ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`,
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact`:
  existence, row compactness of `E`, and finite projectivity of `ker Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.hasPr_ker_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact_restrict_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker`: `(Pr)` property and
  Fredholm series on `E.ker`.
* `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`: stalk rank and field
  dimension `Q.natDegree`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker_eq`,
  `IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact`:
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

private theorem mem_ker_aeval_reverse_iff_aeval_eq_self {R E : Type*} [CommRing R]
    [TopologicalSpace E] [AddCommGroup E] [Module R E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul R E] (w : E →L[R] E) {Q : R[X]} (hQ : IsUnit Q.leadingCoeff) (z : E) :
    z ∈ LinearMap.ker (Polynomial.aeval w Q.reverse : E →ₗ[R] E) ↔
      Polynomial.aeval w (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse) z = z := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  have h1B : 1 - Polynomial.aeval w (1 - C c * Q.reverse) = c • Polynomial.aeval w Q.reverse := by
    simp [Algebra.algebraMap_eq_smul_one]
  refine ⟨fun hz ↦ ?_, fun hz ↦ LinearMap.mem_ker.mpr ?_⟩
  · have hz' : Polynomial.aeval w Q.reverse z = 0 := hz
    have h := congr($h1B z)
    simp only [sub_apply, one_apply_eq_self, smul_apply, hz', smul_zero, sub_eq_zero] at h
    exact h.symm
  · have h := congr($h1B z)
    simp only [sub_apply, one_apply_eq_self, hz, sub_self, smul_apply] at h
    calc Polynomial.aeval w Q.reverse z
        = Q.leadingCoeff • (c • Polynomial.aeval w Q.reverse z) := by
          rw [← mul_smul, mul_comm, hc, one_smul]
      _ = 0 := by rw [← h, smul_zero]

/-- Along `r ∘ i = id`, `ker Q*(i ∘ u ∘ r) ≃ₗ[R] ker Q*(u)` when `IsUnit Q.leadingCoeff`. -/
private noncomputable def kerAevalReverseRetractEquiv {R M N : Type*} [CommRing R]
    [TopologicalSpace M] [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [TopologicalSpace N] [AddCommGroup N] [Module R N]
    [IsTopologicalAddGroup N] [ContinuousConstSMul R N] {i : M →L[R] N} {r : N →L[R] M}
    (hri : r.comp i = .id R M) (u : M →L[R] M) {Q : R[X]} (hQ : IsUnit Q.leadingCoeff) :
    LinearMap.ker (Polynomial.aeval (i.comp (u.comp r)) Q.reverse : N →ₗ[R] N) ≃ₗ[R]
      LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M) := by
  set B := 1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse with hB_def
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ)
  have hB_ext : Polynomial.aeval (i.comp (u.comp r)) B = i.comp ((Polynomial.aeval u B).comp r) :=
    aeval_comp_comp_of_retract hri u hB0
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  let kerN := LinearMap.ker (Polynomial.aeval (i.comp (u.comp r)) Q.reverse : N →ₗ[R] N)
  let kerM := LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)
  refine LinearEquiv.ofLinearMap
    ((r.toLinearMap.comp kerN.subtype).codRestrict kerM fun y ↦ ?_)
    ((i.toLinearMap.comp kerM.subtype).codRestrict kerN fun x ↦ ?_)
    (by ext x; exact hri' x.1) (by
      ext y
      have hy := (mem_ker_aeval_reverse_iff_aeval_eq_self (i.comp (u.comp r)) hQ y.1).mp y.2
      rw [← hB_def, hB_ext, comp_apply, comp_apply] at hy
      calc i (r y.1) = i (r (i (Polynomial.aeval u B (r y.1)))) := by conv_lhs => rw [← hy]
        _ = y.1 := by rw [hri', hy])
  · have hy := (mem_ker_aeval_reverse_iff_aeval_eq_self (i.comp (u.comp r)) hQ y.1).mp y.2
    rw [← hB_def, hB_ext] at hy
    exact (mem_ker_aeval_reverse_iff_aeval_eq_self u hQ (r y.1)).mpr
      (by rw [← hB_def]; simpa [hri'] using congr(r $hy))
  · have hx := (mem_ker_aeval_reverse_iff_aeval_eq_self u hQ x.1).mp x.2
    refine (mem_ker_aeval_reverse_iff_aeval_eq_self (i.comp (u.comp r)) hQ (i x.1)).mpr ?_
    rw [← hB_def, hB_ext]; rw [← hB_def] at hx; simp [hri', hx]

section PrModule

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {M : Type*} [SeminormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]}

/-- **Existence of the Riesz–Coleman projection on a module with property (Pr).** Every coprime
factorization `H_u = Q * S` with `IsUnit Q.leadingCoeff` admits a Riesz–Coleman projection. -/
theorem IsPrCompact.exists_rieszColemanProjection (hu : u.IsPrCompact) {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
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

/-- On a `(Pr)` module, `ker Q*(u)` is finitely generated when `IsUnit Q.leadingCoeff`. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Finite R (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact (hE.isPrCompact hQ hu).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- On a `(Pr)` module, `ker Q*(u)` is projective over `R` when `IsUnit Q.leadingCoeff`. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Projective R (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact (hE.isPrCompact hQ hu).projective_range_of_isIdempotentElem hE.isIdempotentElem

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- The complementary closed summand `E.ker` on a `(Pr)` module again has property `(Pr)`. -/
theorem IsRieszColemanProjection.hasPr_ker_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) : TauCeti.HasPr R E.ker := by
  let rK : M →L[R] E.ker := (1 - E).codRestrict E.ker fun x ↦ LinearMap.mem_ker.mpr <| by
    simpa [sub_eq_zero] using congr($(hE.isIdempotentElem.eq) x).symm
  refine hu.hasPr_source.of_retract E.ker.subtypeL rK ?_
  ext x : 1; apply Subtype.ext
  have hx : E x.1 = 0 := x.2
  simp [rK, hx]

omit [CompleteSpace R] in
/-- The restriction of `u` to `E.ker` is row compact as an endomorphism of `E.ker`. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict hE.mapsTo_ker).IsPrCompact := by
  let rK : M →L[R] E.ker := (1 - E).codRestrict E.ker fun x ↦ LinearMap.mem_ker.mpr <| by
    simpa [sub_eq_zero] using congr($(hE.isIdempotentElem.eq) x).symm
  have hKer := hE.hasPr_ker_of_isPrCompact hu
  have heq : u.restrict hE.mapsTo_ker = rK.comp (u.comp E.ker.subtypeL) := by
    ext x : 1; apply Subtype.ext; change u x.1 = (1 - E) (u x.1)
    have hx : E (u x.1) = 0 := hE.mapsTo_ker x.2
    simp [hx]
  rw [heq]; exact (hu.comp_clm E.ker.subtypeL hKer).clm_comp rK hKer

/-- On any `(Pr)` module, `(u|_{E.ker}).charPowerSeries = (u * (1 - E)).charPowerSeries`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict hE.mapsTo_ker).charPowerSeries = (u * (1 - E)).charPowerSeries := by
  let rK : M →L[R] E.ker := (1 - E).codRestrict E.ker fun x ↦ LinearMap.mem_ker.mpr <| by
    simpa [sub_eq_zero] using congr($(hE.isIdempotentElem.eq) x).symm
  have h₁ : rK.comp (u.comp E.ker.subtypeL) = u.restrict hE.mapsTo_ker := by
    ext x : 1; apply Subtype.ext; change (1 - E) (u x.1) = u x.1
    have hx : E (u x.1) = 0 := hE.mapsTo_ker x.2
    simp [hx]
  have h₂ : (u.comp E.ker.subtypeL).comp rK = u * (1 - E) := by ext x; rfl
  rw [← h₁, ← h₂]
  exact ((hu.comp_clm E.ker.subtypeL (hE.hasPr_ker_of_isPrCompact hu)).charPowerSeries_comp_comm
    rK).symm

end PrModule

section Ring

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M]
  {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}

/-- **Constant stalk rank of `ker Q*(u)` on a `(Pr)` module.** Under `H_u = Q * S` coprime with
`IsUnit Q.leadingCoeff`, `ker Q*(u)` has rank `Q.natDegree` on `Spec R`. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse [ContinuousConstSMul R M]
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)) p = Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hfac
  let : AddCommGroup (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)) := inferInstance
  let : AddCommGroup (LinearMap.ker (Polynomial.aeval (i.comp (u.comp r)) Q.reverse :
    C₀(J, R) →ₗ[R] C₀(J, R))) := inferInstance
  rw [Module.rankAtStalk_eq_of_equiv (kerAevalReverseRetractEquiv hri u hQ).symm]
  exact (hv.isRieszColemanProjection_rieszColemanProjection hQ hS hfac
    hcop).rankAtStalk_ker_aeval_reverse hv hQ hS hfac hcop p

/-- **Constant stalk rank of `range E` on a `(Pr)` module.** -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  rw [hE.range_eq_ker]; exact hu.rankAtStalk_ker_aeval_reverse hQ hS hfac hcop p

/-- Along `r ∘ i = id`, `E ∘ r = r ∘ F` for `F = (i ∘ u ∘ r).rieszColemanProjection Q`. -/
private theorem retract_rieszColemanProjection_comp_eq [IsBoundedSMul R M]
    {J : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
    {i : M →L[R] C₀(J, R)} {r : C₀(J, R) →L[R] M} (hri : r.comp i = .id R M)
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hfac : (i.comp (u.comp r)).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection (i.comp (u.comp r)) Q ((i.comp (u.comp r)).rieszColemanProjection Q) ∧
      E.comp r = r.comp ((i.comp (u.comp r)).rieszColemanProjection Q) := by
  have hF := (hu.isRowCompact_comp i r).isRieszColemanProjection_rieszColemanProjection
    hQ hS hfac hcop
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  refine ⟨hF, ContinuousLinearMap.ext fun y ↦ ?_⟩
  rw [hE.unique (hF.comp_comp_of_retract hri)]
  simp only [comp_apply, ← apply_comp_apply_of_mem_closure_adjoin hri hF.mem_closure_adjoin, hri']

/-- **Reversed characteristic polynomial on a `(Pr)` module.** When `Q.coeff 0 = 1`,
`det (1 - X u|_{range E}) = Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact
    [IsBoundedSMul R M] (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
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
    ((kerAevalReverseRetractEquiv hri u hQ).trans (LinearEquiv.ofEq _ _ hE.range_eq_ker.symm))
  have hinter (y : F.range) : (u.restrict hE.mapsTo_range).toLinearMap (e y) =
      e ((i.comp (u.comp r) |>.restrict hF.mapsTo_range).toLinearMap y) := by
    apply Subtype.ext; change u (r y.1) = r (i (u (r y.1)))
    simpa using (DFunLike.congr_fun hri (u (r y.1))).symm
  have heq := LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq
    (θ := RingHom.id R) (θ' := RingHom.id R) e hinter
  rw [Polynomial.map_id] at heq
  exact heq.trans (hF.projectiveCharpolyRev_restrict_range hv hQ0 hQ hS hfac hcop)

/-- **Fredholm series of `u * E` on a `(Pr)` module.** When `Q.coeff 0 = 1`,
`(u * E).charPowerSeries = (Q : R⟦X⟧)`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_eq [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hfac
  obtain ⟨hF, hEr⟩ := retract_rieszColemanProjection_comp_eq hri hE hu hQ hS hfac hcop
  have hext : i.comp ((u * E).comp r) =
      i.comp (u.comp r) * (i.comp (u.comp r)).rieszColemanProjection Q :=
    ContinuousLinearMap.ext fun y ↦ by
      simpa only [comp_apply, mul_apply_eq_comp] using congr(i (u $(congr($hEr y))))
  rw [mul_def, (hu.comp_clm E hu.hasPr_source).charPowerSeries_eq hri, ← mul_def, hext]
  exact hF.charPowerSeries_matrixCoeff_mul_eq (hu.isRowCompact_comp i r) hQ0 hQ hS hfac hcop

/-- **Fredholm series of `u * (1 - E)` on a `(Pr)` module.** When `Q.coeff 0 = 1`,
`(u * (1 - E)).charPowerSeries = S`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hfac
  obtain ⟨hF, hEr⟩ := retract_rieszColemanProjection_comp_eq hri hE hu hQ hS hfac hcop
  have hext : i.comp ((u * (1 - E)).comp r) =
      i.comp (u.comp r) * (1 - (i.comp (u.comp r)).rieszColemanProjection Q) :=
    ContinuousLinearMap.ext fun y ↦ by
      have hy := congr($hEr y); simp only [comp_apply] at hy; simp [mul_apply_eq_comp, hy]
  rw [mul_def, (hu.comp_clm (1 - E) hu.hasPr_source).charPowerSeries_eq hri, ← mul_def, hext]
  exact hF.charPowerSeries_matrixCoeff_mul_one_sub_eq
    (hu.isRowCompact_comp i r) hQ0 hQ hS hfac hcop

/-- When `Q.coeff 0 = 1`, `u|_{E.ker}` on the complementary `(Pr)` summand has Fredholm series
`S`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker_eq [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire) (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict hE.mapsTo_ker).charPowerSeries = S := by
  rw [hE.charPowerSeries_restrict_ker hu]
  exact hE.charPowerSeries_mul_one_sub_eq hu hQ0 hQ hS hfac hcop

end Ring

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u E : M →L[K] M} {Q : K[X]} {S : K⟦X⟧}

/-- Over a complete ultrametric field, `ker Q*(u)` on a `(Pr)` space under `H_u = Q * S` coprime
has dimension `Q.natDegree`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse (hu : u.IsPrCompact) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[K] M)) = Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff := (leadingCoeff_ne_zero.mpr fun h0 ↦ by
    simpa [h0, u.constantCoeff_charPowerSeries] using
      congrArg (PowerSeries.constantCoeff (R := K)) hfac).isUnit
  have hr := hu.rankAtStalk_ker_aeval_reverse hQ hS hfac hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[K] M)) := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, `range E` on a `(Pr)` space under `H_u = Q * S` coprime has
dimension `Q.natDegree`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact [IsBoundedSMul K M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  rw [hE.range_eq_ker]; exact hu.finrank_ker_aeval_reverse hS hfac hcop

end Field

end ContinuousLinearMap
