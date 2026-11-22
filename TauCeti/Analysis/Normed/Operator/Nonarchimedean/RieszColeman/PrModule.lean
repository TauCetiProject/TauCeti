/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Decomposition
import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman projections on modules with property (Pr)

Over a complete ultrametric norm-one Tate commutative ring `R`, a Banach module `M` with property
`(Pr)` is a continuous linear retract `r ∘ i = id` of a model space `C₀(J, R)`. Both the Fredholm
series `H_u = det (1 - T u)` of a `(Pr)`-compact operator `u : M →L[R] M`
(`ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`) and Riesz–Coleman projections
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`) transport along such a
retract. Consequently, every coprime polynomial factorisation

  `H_u = Q * S`

into a polynomial `Q : R[X]` with `IsUnit Q.leadingCoeff` and an entire power series `S` coprime to
`Q` in `PowerSeries.IsEntire.subring R` yields a unique Riesz–Coleman projector `E` on `M`
(`ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection`).

When `Q.leadingCoeff` is a unit, `E` factors through `u` and is therefore itself `(Pr)`-compact
(`ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`), so its range `ker Q*(u)` is a
finitely generated projective `R`-module of constant stalk rank `Q.natDegree` on `Spec R` (and of
dimension `Q.natDegree` over a complete ultrametric field). Moreover, extending `E` back to
`C₀(J, R)` recovers the model-space Riesz–Coleman projector `E' = i ∘ E ∘ r`
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`), identifying `range E`
topologically and linearly with `range E'`
(`ContinuousLinearMap.IsRieszColemanProjection.rangeEquivOfRetract`) and, when `Q(0) = 1`,
transporting the Fredholm factors `H_(uE) = Q`, `H_(u(1-E)) = S`, `H_(u|_{range E}) = Q`,
`H_(u|_{ker E}) = S`, and `det (1 - X (u|_{range E})) = Q` to `M`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact_restrict_range`, and
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact_restrict_ker`: when `Q.leadingCoeff`
  is a unit, Riesz–Coleman projections of `(Pr)`-compact operators are `(Pr)`-compact, and
  restrictions to `range E` and `ker E` are `(Pr)`-compact.
* `ContinuousLinearMap.IsRieszColemanProjection.finite_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact`, and
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact`:
  when `Q.leadingCoeff` is a unit, `range E = ker Q*(u)` is finitely generated and projective over
  `R`.
* `ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection`: existence of the
  Riesz–Coleman projection on modules with property `(Pr)` for a coprime factorisation
  `H_u = Q * S`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`, and
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`: constant stalk rank `deg Q` on
  `Spec R` and dimension `deg Q` over a field.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker`, and
  `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact`
  give `H_(uE) = Q`, `H_(u(1-E)) = S`, `H_(u|_{range E}) = Q`, `H_(u|_{ker E}) = S`, and
  `det (1 - X (u|_{range E})) = Q`.

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
open scoped PowerSeries ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Compact

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u E : M →L[R] M} {Q : R[X]}

/-- A Riesz–Coleman projection of a `(Pr)`-compact endomorphism is `(Pr)`-compact whenever
`Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) : E.IsPrCompact := by
  rw [← hE.mul_smul_aeval_divX_reverse_mul hQ]
  simpa only [mul_def] using hu.comp_clm _ hu.hasPr_source

/-- On a module with property `(Pr)`, the restriction of a `(Pr)`-compact endomorphism `u` to the
range of a Riesz–Coleman projection is `(Pr)`-compact. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict fun _ hx ↦
      (isRieszColemanProjection_def.mp hE).mapsTo_range hx).IsPrCompact :=
  have htop := ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (isRieszColemanProjection_def.mp hE).isIdempotentElem
  hu.restrict_of_retract _ (r := E.range.projectionOntoL E.ker htop)
    (ext fun x ↦ by simp)

/-- On a module with property `(Pr)`, the restriction of a `(Pr)`-compact endomorphism `u` to the
kernel of a Riesz–Coleman projection is `(Pr)`-compact. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict fun _ hx ↦
      (isRieszColemanProjection_def.mp hE).mapsTo_ker hx).IsPrCompact :=
  have htop := (ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (isRieszColemanProjection_def.mp hE).isIdempotentElem).symm
  hu.restrict_of_retract _ (r := E.ker.projectionOntoL E.range htop)
    (ext fun x ↦ by simp)

variable [CompleteSpace R]

/-- On a module with property `(Pr)`, when `Q.leadingCoeff` is a unit, the range of a Riesz–Coleman
projection of a `(Pr)`-compact operator is finitely generated. -/
theorem IsRieszColemanProjection.finite_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Finite R E.range :=
  (hE.isPrCompact hQ hu).finite_range_of_isIdempotentElem
    (isRieszColemanProjection_def.mp hE).isIdempotentElem

/-- On a module with property `(Pr)`, when `Q.leadingCoeff` is a unit, the range of a Riesz–Coleman
projection of a `(Pr)`-compact operator is projective over the coefficient ring. -/
theorem IsRieszColemanProjection.projective_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Projective R E.range :=
  (hE.isPrCompact hQ hu).projective_range_of_isIdempotentElem
    (isRieszColemanProjection_def.mp hE).isIdempotentElem

/-- On a module with property `(Pr)`, when `Q.leadingCoeff` is a unit, `ker Q*(u)` for a
Riesz–Coleman projection of a `(Pr)`-compact operator is finitely generated. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Finite R (Polynomial.aeval u Q.reverse : M →L[R] M).ker := by
  have hker := by simpa only [pow_one] using (isRieszColemanProjection_def.mp hE).range_eq_ker
  rw [← hker]
  exact hE.finite_range_of_isPrCompact hQ hu

/-- On a module with property `(Pr)`, when `Q.leadingCoeff` is a unit, `ker Q*(u)` for a
Riesz–Coleman projection of a `(Pr)`-compact operator is projective over the coefficient ring. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Projective R (Polynomial.aeval u Q.reverse : M →L[R] M).ker := by
  have hker := by simpa only [pow_one] using (isRieszColemanProjection_def.mp hE).range_eq_ker
  rw [← hker]
  exact hE.projective_range_of_isPrCompact hQ hu

end Compact

section KerRank

universe u

variable {R : Type*} {M : Type u} [NormedCommRing R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M]

/-- **Constant stalk rank of `ker Q*(u)` on a module with property `(Pr)`.** For a `(Pr)`-compact
operator `u` with a coprime factorisation `H_u = Q * S`, where `IsUnit Q.leadingCoeff` and `S` is
entire, the kernel `ker Q*(u)` has rank `Q.natDegree` at every prime ideal of `R`. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse {u : M →L[R] M} (hu : u.IsPrCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Polynomial.aeval u Q.reverse : M →L[R] M).ker p =
      Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hQS
  have heq := (ContinuousLinearMap.kerAevalEquivOfRetract hri u (P := Q.reverse)
    (by simpa only [coeff_zero_reverse] using hQ)).toLinearEquiv
  have hrank : Module.rankAtStalk (R := R) (Polynomial.aeval u Q.reverse : M →L[R] M).ker =
      Module.rankAtStalk (R := R)
        (Polynomial.aeval (i.comp (u.comp r)) Q.reverse : C₀(J, R) →L[R] C₀(J, R)).ker := by
    let : AddCommGroup (Polynomial.aeval u Q.reverse : M →L[R] M).ker := inferInstance
    let : AddCommGroup (Polynomial.aeval (i.comp (u.comp r)) Q.reverse :
      C₀(J, R) →L[R] C₀(J, R)).ker := inferInstance
    exact Module.rankAtStalk_eq_of_equiv heq.symm
  rw [hrank]
  exact hv.rankAtStalk_ker_aeval_reverse hQ hS hQS hcop p

end KerRank

section RetractHelper

universe u

variable {R : Type*} {M : Type u} [NormedCommRing R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M]

/-- Packages a `(Pr)` retract presentation `r ∘ i = id` of `M` into a model space `C₀(J, R)`
together with the row-compact extension `i ∘ u ∘ r`, its Fredholm factorisation, and its explicit
Riesz–Coleman projection. -/
private theorem exists_retract_isRieszColemanProjection {u : M →L[R] M} (hu : u.IsPrCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ (J : Type u) (_ : TopologicalSpace J) (_ : DiscreteTopology J) (_ : DecidableEq J)
      (i : M →L[R] C₀(J, R)) (r : C₀(J, R) →L[R] M),
      r.comp i = .id R M ∧
      (i.comp (u.comp r)).IsRowCompact ∧
      (i.comp (u.comp r)).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S ∧
      IsRieszColemanProjection (i.comp (u.comp r)) Q
        ((i.comp (u.comp r)).rieszColemanProjection Q) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hQS
  exact ⟨J, inferInstance, inferInstance, inferInstance, i, r, hri, hv, hQS,
    hv.isRieszColemanProjection_rieszColemanProjection hQ hS hQS hcop⟩

end RetractHelper

section Decomposition

variable {R : Type*} {M : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- **The Riesz–Coleman projection at a coprime polynomial factor on `(Pr)` modules.** Let `u` be
a `(Pr)`-compact endomorphism of `M`, and suppose `H_u = Q * S` where `Q.leadingCoeff` is a unit,
`S` is entire, and `Q`, `S` are coprime entire series. Then `u` admits a Riesz–Coleman projection
for `Q`. -/
theorem IsPrCompact.exists_isRieszColemanProjection {u : M →L[R] M} (hu : u.IsPrCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : M →L[R] M, IsRieszColemanProjection u Q E := by
  obtain ⟨J, _, _, _, i, r, hri, -, -, hE'⟩ :=
    exists_retract_isRieszColemanProjection hu hQ hS hQS hcop
  exact ⟨_, hE'.comp_comp_of_retract hri⟩

namespace IsRieszColemanProjection

/-- **Constant stalk rank of the Riesz–Coleman summand on a module with property `(Pr)`.** For a
`(Pr)`-compact operator `u` with a coprime factorisation `H_u = Q * S`, where `IsUnit
Q.leadingCoeff` and `S` is entire, the finite projective summand `range E = ker Q*(u)` has rank
`Q.natDegree` at every prime ideal of `R`. -/
theorem rankAtStalk_range_of_isPrCompact {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  have hker := by simpa only [pow_one] using (isRieszColemanProjection_def.mp hE).range_eq_ker
  rw [hker]
  exact hu.rankAtStalk_ker_aeval_reverse hQ hS hQS hcop p

/-- **Fredholm factor on the finite Riesz–Coleman summand on a module with property `(Pr)`.** For a
`(Pr)`-compact operator `u` with a coprime factorisation `H_u = Q * S`, where `Q(0) = 1`,
`IsUnit Q.leadingCoeff`, and `S` is entire, the Fredholm series of `u * E` is `Q`. -/
theorem charPowerSeries_mul_of_isPrCompact {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) := by
  obtain ⟨J, _, _, _, i, r, hri, hv, hQS', hE'⟩ :=
    exists_retract_isRieszColemanProjection hu hQ hS hQS hcop
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hE'_eq := hE.comp_comp_eq_of_retract hri hE' hQ
  have huE : (u * E).IsPrCompact := by simpa only [mul_def] using hu.comp_clm E hu.hasPr_source
  have hext : i.comp ((u * E).comp r) =
      i.comp (u.comp r) * (i.comp (u.comp r)).rieszColemanProjection Q := by
    ext y : 1
    simp only [← hE'_eq, mul_apply_eq_comp, comp_apply, hri']
  rw [huE.charPowerSeries_eq hri, hext]
  exact hE'.charPowerSeries_matrixCoeff_mul hv hQ0 hQ hS hQS' hcop

/-- **Fredholm factor on the complementary Riesz–Coleman summand on a module with property `(Pr)`.**
For a `(Pr)`-compact operator `u` with a coprime factorisation `H_u = Q * S`, where `Q(0) = 1`,
`IsUnit Q.leadingCoeff`, and `S` is entire, the Fredholm series of `u * (1 - E)` is `S`. -/
theorem charPowerSeries_mul_one_sub_of_isPrCompact {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  obtain ⟨J, _, _, _, i, r, hri, hv, hQS', hE'⟩ :=
    exists_retract_isRieszColemanProjection hu hQ hS hQS hcop
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hE'_eq := hE.comp_comp_eq_of_retract hri hE' hQ
  have huE : (u * (1 - E)).IsPrCompact := by
    simpa only [mul_def] using hu.comp_clm (1 - E) hu.hasPr_source
  have hext : i.comp ((u * (1 - E)).comp r) =
      i.comp (u.comp r) * (1 - (i.comp (u.comp r)).rieszColemanProjection Q) := by
    ext y : 1
    simp only [← hE'_eq, mul_apply_eq_comp, comp_apply, sub_apply, one_apply_eq_self, map_sub,
      hri']
  rw [huE.charPowerSeries_eq hri, hext]
  exact hE'.charPowerSeries_matrixCoeff_mul_one_sub hv hQ0 hQ hS hQS' hcop

/-- **Fredholm series on the finite Riesz–Coleman summand.** Under a coprime factorisation
`H_u = Q * S` with `Q(0) = 1`, the Fredholm series of the restriction of `u` to `range E` is `Q`.
-/
theorem charPowerSeries_restrict_range {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict fun _ hx ↦
      (isRieszColemanProjection_def.mp hE).mapsTo_range hx).charPowerSeries = (Q : R⟦X⟧) := by
  have hE_idem := (isRieszColemanProjection_def.mp hE).isIdempotentElem
  have htop := ContinuousLinearMap.IsIdempotentElem.isTopCompl hE_idem
  rw [hu.charPowerSeries_restrict_of_retract _ (r := E.range.projectionOntoL E.ker htop)
    (ext fun x ↦ by simp)]
  have hproj : E.range.subtypeL.comp (E.range.projectionOntoL E.ker htop) = E :=
    (ContinuousLinearMap.IsIdempotentElem.eq_projectionL hE_idem).symm
  rw [hproj, ← mul_def]
  exact hE.charPowerSeries_mul_of_isPrCompact hu hQ0 hQ hS hQS hcop

/-- **Fredholm series on the complementary Riesz–Coleman summand.** Under a coprime factorisation
`H_u = Q * S` with `Q(0) = 1`, the Fredholm series of the restriction of `u` to `ker E =
range Q*(u)` is `S`. -/
theorem charPowerSeries_restrict_ker {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict fun _ hx ↦ (isRieszColemanProjection_def.mp hE).mapsTo_ker hx).charPowerSeries =
      S := by
  have hE_idem := (isRieszColemanProjection_def.mp hE).isIdempotentElem
  have htop := ContinuousLinearMap.IsIdempotentElem.isTopCompl hE_idem
  rw [hu.charPowerSeries_restrict_of_retract _ (r := E.ker.projectionOntoL E.range htop.symm)
    (ext fun x ↦ by simp)]
  have hproj : E.ker.subtypeL.comp (E.ker.projectionOntoL E.range htop.symm) = 1 - E := by
    change E.ker.projectionL E.range htop.symm = 1 - E
    rw [Submodule.projectionL_eq_id_sub_projectionL htop,
      ← ContinuousLinearMap.IsIdempotentElem.eq_projectionL hE_idem, ← one_def]
  rw [hproj, ← mul_def]
  exact hE.charPowerSeries_mul_one_sub_of_isPrCompact hu hQ0 hQ hS hQS hcop

/-- **Characteristic polynomial of `u` on the finite Riesz–Coleman summand.** For a `(Pr)`-compact
operator `u` with a coprime factorisation `H_u = Q * S`, where `Q(0) = 1`, `IsUnit Q.leadingCoeff`,
and `S` is entire, the reversed characteristic polynomial `det (1 - X (u|_{range E}))` equals `Q`.
-/
theorem projectiveCharpolyRev_restrict_range_of_isPrCompact {u E : M →L[R] M} {Q : R[X]}
    {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    haveI : Module.Finite R E.range := hE.finite_range_of_isPrCompact hQ hu
    haveI : Module.Projective R E.range := hE.projective_range_of_isPrCompact hQ hu
    (((u.restrict fun _ hx ↦
      (isRieszColemanProjection_def.mp hE).mapsTo_range hx).toLinearMap).projectiveCharpolyRev) =
      Q := by
  classical
  have htop := ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (isRieszColemanProjection_def.mp hE).isIdempotentElem
  have hrange : TauCeti.HasPr R E.range :=
    hu.hasPr_source.of_retract E.range.subtypeL (E.range.projectionOntoL E.ker htop)
      (ext fun x ↦ by simp)
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R E.range).mp hrange
  let : AddCommGroup E.range := inferInstance
  let : NormedAddCommGroup E.range := NormedAddCommGroup.ofSeparation fun x hx ↦ by
    have hinsep : Inseparable x 0 :=
      Metric.inseparable_iff.2 (by simpa only [dist_zero_right] using hx)
    have hi : i x = 0 := by simpa only [map_zero] using (hinsep.map i.continuous).eq
    have hri_x := DFunLike.congr_fun hri x
    simpa only [comp_apply, hi, map_zero, id_apply] using hri_x.symm
  have : Module.Finite R E.range := hE.finite_range_of_isPrCompact hQ hu
  apply Polynomial.coe_inj.mp
  rw [← ContinuousLinearMap.charPowerSeries_eq_projectiveCharpolyRev hrange]
  exact hE.charPowerSeries_restrict_range hu hQ0 hQ hS hQS hcop

end IsRieszColemanProjection

end Decomposition

section FieldKer

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]

/-- Over a complete ultrametric field, `ker Q*(u)` on a module with property `(Pr)` has dimension
`Q.natDegree` whenever `H_u = Q * S` is a coprime factorisation into a polynomial `Q` and an entire
series `S`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse {u : M →L[K] M} (hu : u.IsPrCompact)
    {Q : K[X]} {S : K⟦X⟧} (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (Polynomial.aeval u Q.reverse : M →L[K] M).ker = Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr fun h0 ↦
      u.charPowerSeries_ne_zero (by simp [hQS, h0]))
  have hr := hu.rankAtStalk_ker_aeval_reverse hQ hS hQS hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup (Polynomial.aeval u Q.reverse : M →L[K] M).ker := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

end FieldKer

section FieldRange

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [IsBoundedSMul K M]

/-- Over a complete ultrametric field, the finite Riesz–Coleman summand `range E = ker Q*(u)` of a
`(Pr)`-compact operator `u` has dimension `Q.natDegree` under a coprime factorisation
`H_u = Q * S` into a polynomial `Q` and an entire series `S`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact {u E : M →L[K] M} {Q : K[X]}
    {S : K⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hS : S.IsEntire) (hQS : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hker := by simpa only [pow_one] using (isRieszColemanProjection_def.mp hE).range_eq_ker
  rw [hker]
  exact hu.finrank_ker_aeval_reverse hS hQS hcop

end FieldRange

end ContinuousLinearMap
