/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Decomposition

/-!
# Riesz–Coleman projections on modules with property (Pr)

Over a complete ultrametric norm-one Tate commutative ring `R`, a Banach module `M` with property
`(Pr)` is a continuous linear retract `r ∘ i = id` of a model space `C₀(J, R)`. Both the Fredholm
series `H_u = det (1 - T u)` of a `(Pr)`-compact operator `u : M →L[R] M`
(`ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`) and Riesz–Coleman projections
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`) transport along such a
retract. Consequently, every coprime polynomial factorisation

  `H_u = Q * S`

into a polynomial `Q : R[X]` with `Q(0) = 1` and `IsUnit Q.leadingCoeff` and an entire power series
`S` coprime to `Q` in `PowerSeries.IsEntire.subring R` yields a unique Riesz–Coleman projector `E`
on `M` (`ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection`).

When `Q.leadingCoeff` is a unit, `E` factors through `u` and is therefore itself `(Pr)`-compact
(`ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`), so its range `ker Q*(u)` is a
finitely generated projective `R`-module of constant stalk rank `Q.natDegree` on `Spec R` (and of
dimension `Q.natDegree` over a complete ultrametric field). Moreover, extending `E` back to
`C₀(J, R)` recovers the model-space Riesz–Coleman projector `E' = i ∘ E ∘ r`
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`), identifying `range E`
topologically and linearly with `range E'`
(`ContinuousLinearMap.IsRieszColemanProjection.equivRangeOfRetract`) and transporting the Fredholm
factors `H_(uE) = Q`, `H_(u(1-E)) = S`, and `det (1 - X (u|_{range E})) = Q` to `M`.

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection.equivRangeOfRetract`: continuous linear equivalence
  `E.range ≃L[R] E'.range` induced by a continuous linear retract `r ∘ i = id`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`: Riesz–Coleman projections of
  `(Pr)`-compact operators are `(Pr)`-compact.
* `ContinuousLinearMap.IsRieszColemanProjection.finite_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact`, and
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact`:
  `range E = ker Q*(u)` is finitely generated and projective over `R`.
* `ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection`: existence of the
  Riesz–Coleman projection on modules with property `(Pr)` for a coprime factorisation
  `H_u = Q * S`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`, and
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`: constant stalk rank `deg Q` on
  `Spec R` and dimension `deg Q` over a field.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub_of_isPrCompact`, and
  `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact`
  give `H_(uE) = Q`, `H_(u(1-E)) = S`, and `det (1 - X (u|_{range E})) = Q`.

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

variable [CompleteSpace R]

/-- On a module with property `(Pr)`, the range of a Riesz–Coleman projection of a `(Pr)`-compact
operator is finitely generated. -/
theorem IsRieszColemanProjection.finite_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Finite R E.range :=
  (hE.isPrCompact hQ hu).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- On a module with property `(Pr)`, the range of a Riesz–Coleman projection of a `(Pr)`-compact
operator is projective over the coefficient ring. -/
theorem IsRieszColemanProjection.projective_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Projective R E.range :=
  (hE.isPrCompact hQ hu).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- On a module with property `(Pr)`, `ker Q*(u)` for a Riesz–Coleman projection of a `(Pr)`-compact
operator is finitely generated. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Finite R (Polynomial.aeval u Q.reverse : M →L[R] M).ker := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range_of_isPrCompact hQ hu

/-- On a module with property `(Pr)`, `ker Q*(u)` for a Riesz–Coleman projection of a `(Pr)`-compact
operator is projective over the coefficient ring. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    Module.Projective R (Polynomial.aeval u Q.reverse : M →L[R] M).ker := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range_of_isPrCompact hQ hu

end Compact

section RetractEquiv

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {u E : M →L[R] M} {E' : N →L[R] N} {Q : R[X]}
  {i : M →L[R] N} {r : N →L[R] M}

/-- Along a continuous linear retract `r ∘ i = id`, `i` and `r` restrict to a continuous linear
equivalence between the ranges of the Riesz–Coleman projections of `u` and `i ∘ u ∘ r`. -/
noncomputable def IsRieszColemanProjection.equivRangeOfRetract (hri : r.comp i = .id R M)
    (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) : E.range ≃L[R] E'.range :=
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hi_semi : Function.Semiconj i u (i.comp (u.comp r)) := fun x ↦ by simp [hri']
  have hr_semi : Function.Semiconj r (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  have hi : ∀ x ∈ E.range, i x ∈ E'.range :=
    fun _ hx ↦ hE.mapsTo_range_of_semiconj hE' i.toLinearMap hi_semi hx
  have hr : ∀ y ∈ E'.range, r y ∈ E.range :=
    fun _ hy ↦ hE'.mapsTo_range_of_semiconj hE r.toLinearMap hr_semi hy
  ContinuousLinearEquiv.equivOfInverse (i.restrict hi) (r.restrict hr)
    (fun ⟨x, _⟩ ↦ Subtype.ext (hri' x))
    (fun ⟨y, hy⟩ ↦ Subtype.ext <| by
      have hEy : E' y = y :=
        (LinearMap.IsIdempotentElem.mem_range_iff
          (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE'.isIdempotentElem)).mp hy
      have hE_eq : E = r.comp (E'.comp i) := hE.unique (hE'.comp_comp_of_retract hri)
      have hE'_eq : i.comp (E.comp r) = E' := hE_eq ▸ hE'.comp_comp_eq_of_retract hri hQ
      have h1 : i (r (E' y)) = E' y := calc
        i (r (E' y)) = i (E (r y)) := congrArg i (hE'.semiconj hE r.toLinearMap hr_semi y)
        _ = (i.comp (E.comp r)) y := rfl
        _ = E' y := DFunLike.congr_fun hE'_eq y
      rwa [hEy] at h1)

/-- The retract range equivalence `equivRangeOfRetract` acts in the forward direction by `i`. -/
@[simp]
theorem IsRieszColemanProjection.coe_equivRangeOfRetract_apply (hri : r.comp i = .id R M)
    (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.equivRangeOfRetract hri hE' hQ x : N)) = i x :=
  (rfl)

/-- The inverse retract range equivalence `equivRangeOfRetract.symm` acts by `r`. -/
@[simp]
theorem IsRieszColemanProjection.coe_equivRangeOfRetract_symm_apply (hri : r.comp i = .id R M)
    (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (y : E'.range) :
    (((hE.equivRangeOfRetract hri hE' hQ).symm y : M)) = r y :=
  (rfl)

end RetractEquiv

section Decomposition

variable {R M : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- **The Riesz–Coleman projection at a coprime polynomial factor on `(Pr)` modules.** Let `u` be
a `(Pr)`-compact endomorphism of `M`, and suppose `H_u = Q * S` where `Q(0) = 1`, `Q.leadingCoeff`
is a unit, `S` is entire, and `Q`, `S` are coprime entire series. Then `u` admits a Riesz–Coleman
projection for `Q`. -/
theorem IsPrCompact.exists_isRieszColemanProjection {u : M →L[R] M} (hu : u.IsPrCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : M →L[R] M, IsRieszColemanProjection u Q E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hQS
  exact ⟨_, ((hu.isRowCompact_comp i r).isRieszColemanProjection_rieszColemanProjection
    hQ0 hQ hS hQS hcop).comp_comp_of_retract hri⟩

namespace IsRieszColemanProjection

/-- **Constant stalk rank of the Riesz–Coleman summand on a module with property `(Pr)`.** Under a
coprime factorisation `H_u = Q * S`, the finite projective summand `range E = ker Q*(u)` has rank
`Q.natDegree` at every prime ideal of `R`. -/
theorem rankAtStalk_range_of_isPrCompact {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hQS
  have hE' := hv.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hQS hcop
  have hrank : Module.rankAtStalk (R := R) E.range =
      Module.rankAtStalk (R := R) ((i.comp (u.comp r)).rieszColemanProjection Q).range := by
    let : AddCommGroup E.range := inferInstance
    let : AddCommGroup ((i.comp (u.comp r)).rieszColemanProjection Q).range := inferInstance
    exact Module.rankAtStalk_eq_of_equiv (hE.equivRangeOfRetract hri hE' hQ).toLinearEquiv
  rw [hrank]
  exact hE'.rankAtStalk_range hv hQ0 hQ hS hQS hcop p

/-- **Fredholm factor on the finite Riesz–Coleman summand on a module with property `(Pr)`.** Under
a coprime factorisation `H_u = Q * S`, the Fredholm series of `u * E` is `Q`. -/
theorem charPowerSeries_mul_of_isPrCompact {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  set v := i.comp (u.comp r)
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hQS
  set E' := v.rieszColemanProjection Q
  have hE' := hv.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hQS hcop
  have hE_eq : E = r.comp (E'.comp i) := hE.unique (hE'.comp_comp_of_retract hri)
  have hE'_eq : i.comp (E.comp r) = E' := hE_eq ▸ hE'.comp_comp_eq_of_retract hri hQ
  have huE : (u * E).IsPrCompact := by simpa only [mul_def] using hu.comp_clm E hu.hasPr_source
  have hext : i.comp ((u * E).comp r) = v * E' := by
    ext y : 1
    simp only [v, ← hE'_eq, mul_apply_eq_comp, comp_apply, hri']
  rw [huE.charPowerSeries_eq hri, hext]
  exact hE'.charPowerSeries_matrixCoeff_mul hv hQ0 hQ hS hQS hcop

/-- **Fredholm factor on the complementary Riesz–Coleman summand on a module with property `(Pr)`.**
Under a coprime factorisation `H_u = Q * S`, the Fredholm series of `u * (1 - E)` is `S`. -/
theorem charPowerSeries_mul_one_sub_of_isPrCompact {u E : M →L[R] M} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  set v := i.comp (u.comp r)
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hQS
  set E' := v.rieszColemanProjection Q
  have hE' := hv.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hQS hcop
  have hE_eq : E = r.comp (E'.comp i) := hE.unique (hE'.comp_comp_of_retract hri)
  have hE'_eq : i.comp (E.comp r) = E' := hE_eq ▸ hE'.comp_comp_eq_of_retract hri hQ
  have huE : (u * (1 - E)).IsPrCompact := by
    simpa only [mul_def] using hu.comp_clm (1 - E) hu.hasPr_source
  have hext : i.comp ((u * (1 - E)).comp r) = v * (1 - E') := by
    ext y : 1
    simp only [v, ← hE'_eq, mul_apply_eq_comp, comp_apply, sub_apply, one_apply_eq_self, map_sub,
      hri']
  rw [huE.charPowerSeries_eq hri, hext]
  exact hE'.charPowerSeries_matrixCoeff_mul_one_sub hv hQ0 hQ hS hQS hcop

/-- **Characteristic polynomial of `u` on the finite Riesz–Coleman summand.** Under a coprime
factorisation `H_u = Q * S` on a module with property `(Pr)`, the reversed characteristic polynomial
`det (1 - X (u|_{range E}))` equals `Q`. -/
theorem projectiveCharpolyRev_restrict_range_of_isPrCompact {u E : M →L[R] M} {Q : R[X]}
    {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    haveI : Module.Finite R E.range := hE.finite_range_of_isPrCompact hQ hu
    haveI : Module.Projective R E.range := hE.projective_range_of_isPrCompact hQ hu
    (((u.restrict fun _ hx ↦ hE.mapsTo_range hx).toLinearMap).projectiveCharpolyRev) = Q := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  set v := i.comp (u.comp r)
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hQS
  set E' := v.rieszColemanProjection Q
  have hE' := hv.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hQS hcop
  let : AddCommGroup E.range := inferInstance
  let : AddCommGroup E'.range := inferInstance
  have := hE.finite_range_of_isPrCompact hQ hu
  have := hE.projective_range_of_isPrCompact hQ hu
  have := hE'.finite_range hQ hv
  have := hE'.projective_range hQ hv
  let e := (hE.equivRangeOfRetract hri hE' hQ).toLinearEquiv
  let f : Module.End R E.range := (u.restrict fun _ hx ↦ hE.mapsTo_range hx).toLinearMap
  let g : Module.End R E'.range := (v.restrict fun _ hy ↦ hE'.mapsTo_range hy).toLinearMap
  have hfg (x : E.range) : g (e x) = e (f x) := by
    apply Subtype.ext
    simp [e, f, g, v, hri']
  have hchar := LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq e hfg
  rw [Polynomial.map_id] at hchar
  exact hchar.symm.trans (hE'.projectiveCharpolyRev_restrict_range hv hQ0 hQ hS hQS hcop)

end IsRieszColemanProjection

/-- **Constant stalk rank of `ker Q*(u)` on a module with property `(Pr)`.** Under a coprime
factorisation `H_u = Q * S`, the kernel `ker Q*(u)` has rank `Q.natDegree` at every prime ideal
of `R`. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse {u : M →L[R] M} (hu : u.IsPrCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Polynomial.aeval u Q.reverse : M →L[R] M).ker p =
      Q.natDegree := by
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection hQ0 hQ hS hQS hcop
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range_of_isPrCompact hu hQ0 hQ hS hQS hcop p

end Decomposition

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [IsBoundedSMul K M]

/-- Over a complete ultrametric field, the finite Riesz–Coleman summand `range E = ker Q*(u)` on a
module with property `(Pr)` has dimension `Q.natDegree`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact {u E : M →L[K] M} {Q : K[X]}
    {S : K⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hr := hE.rankAtStalk_range_of_isPrCompact hu hQ0 hQ hS hQS hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, `ker Q*(u)` on a module with property `(Pr)` has dimension
`Q.natDegree` whenever `H_u = Q * S` is a coprime factorisation into a polynomial `Q` with
`Q(0) = 1` and an entire series `S`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse {u : M →L[K] M} (hu : u.IsPrCompact)
    {Q : K[X]} {S : K⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (Polynomial.aeval u Q.reverse : M →L[K] M).ker = Q.natDegree := by
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection hQ0 hQ hS hQS hcop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range_of_isPrCompact hu hQ0 hQ hS hQS hcop

end Field

end ContinuousLinearMap
