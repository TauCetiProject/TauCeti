/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Coleman.ModelSpace

/-!
# Riesz–Coleman decompositions on modules with property (Pr)

Over a complete ultrametric normed commutative ring `R` with Tate scalars, a module `M` with
property (Pr) is a continuous linear retract `r ∘ i = id` of a model space `C₀(J, R)`. Riesz–Coleman
projections compress along such retracts
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`), and the Fredholm series
`H_u` of a row-compact endomorphism `u : M →L[R] M` agrees with that of `i ∘ u ∘ r`
(`ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`).

Consequently, whenever `H_u = Q · S` with `Q ∈ R[X]`, `Q(0) = 1`, `IsUnit Q.leadingCoeff`, `S`
entire, and `Q`, `S` coprime in `IsEntire.subring R`:

* `u` admits a unique Riesz–Coleman projection `E` for `Q`
  (`ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection`,
  `ContinuousLinearMap.IsRieszColemanProjection.unique`);
* `E` is row compact (`ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`), so `range E =
  ker Q*(u)` is finitely generated and projective of constant rank `deg Q` on `Spec R`
  (`ContinuousLinearMap.IsRieszColemanProjection.finite_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`);
* the reversed characteristic polynomial of `u|_{range E}` is `Q`, while the two block Fredholm
  series `H_{u E}` and `H_{u(1 - E)}` equal `Q` and `S`
  (`IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq`);
* over a complete ultrametric field `K`, `dim_K (range E) = dim_K (ker Q*(u)) = deg Q`
  (`ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`).

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

section PrModule

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u E : M →L[R] M} {Q : R[X]} {S : PowerSeries R}

/-- **Existence of the Riesz–Coleman projection on a module with property (Pr).** Let `u` be a
row-compact endomorphism of a module with property (Pr), let `Q : R[X]` satisfy `Q(0) = 1` and
`IsUnit Q.leadingCoeff`, and let `S` be an entire power series coprime to `Q` in
`IsEntire.subring R` with `H_u = Q · S`. Then `u` admits a Riesz–Coleman projection for `Q`. -/
theorem IsPrCompact.exists_isRieszColemanProjection
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hfac
  exact ⟨_, ((hu.isRowCompact_comp i r).isRieszColemanProjection_rieszColemanProjection
    hQ0 hQ hS hfac hcop).comp_comp_of_retract hri⟩

omit [CompleteSpace R] in
/-- A Riesz–Coleman projection of a row-compact endomorphism on a module with property (Pr) is row
compact whenever `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) : E.IsPrCompact := by
  rw [hE.eq_neg_inverse_smul_mul_aeval_divX hQ, mul_def]
  exact (hu.comp_clm _ hu.hasPr_source).smul _

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism on a module with
property (Pr) is finitely generated when `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.finite_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R E.range :=
  (hE.isPrCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism on a module with
property (Pr) is projective when `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.projective_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R E.range :=
  (hE.isPrCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- The kernel `ker Q*(u)` of a row-compact endomorphism on a module with property (Pr) admitting a
Riesz–Coleman projection is finitely generated when `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range_of_isPrCompact hu hQ

/-- The kernel `ker Q*(u)` of a row-compact endomorphism on a module with property (Pr) admitting a
Riesz–Coleman projection is projective when `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range_of_isPrCompact hu hQ

omit [IsUltrametricDist R] [CompleteSpace R] [IsBoundedSMul R M] in
/-- For a Riesz–Coleman projection `E'` of `i ∘ u ∘ r` along a retract `r ∘ i = id` with
`IsUnit Q.leadingCoeff`, `i ∘ r` fixes `E'` on both sides. -/
private theorem comp_apply_eq_and_apply_comp_eq {N : Type*} [NormedAddCommGroup N] [Module R N]
    [IsBoundedSMul R N] {i : M →L[R] N} {r : N →L[R] M} (hri : r.comp i = .id R M)
    {E' : N →L[R] N} (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (y : N) :
    i (r (E' y)) = E' y ∧ E' (i (r y)) = E' y := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hir : i (r (E' y)) = E' y := by
    have hEq := congr($(hE'.eq_neg_inverse_smul_mul_aeval_divX hQ) y)
    simp only [smul_apply, mul_apply_eq_comp] at hEq
    rw [hEq, map_smul, map_smul]
    congr 1
    simp only [comp_apply, hri']
  exact ⟨hir, (apply_comp_apply_of_mem_closure_adjoin hri hE'.mem_closure_adjoin y).symm.trans hir⟩

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Along a retract `r ∘ i = id` of `M` through a normed module `N`, a Riesz–Coleman projection
`E'` of `i ∘ u ∘ r` for `Q` with `IsUnit Q.leadingCoeff` satisfies `E = r ∘ E' ∘ i` and induces a
linear equivalence `E.range ≃ₗ[R] E'.range` intertwining `u` with `i ∘ u ∘ r`. -/
private noncomputable def rangeEquivOfRetract {N : Type*} [NormedAddCommGroup N] [Module R N]
    [IsBoundedSMul R N] {i : M →L[R] N} {r : N →L[R] M} (hri : r.comp i = .id R M)
    (hE : IsRieszColemanProjection u Q E) {E' : N →L[R] N}
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E') (hQ : IsUnit Q.leadingCoeff) :
    E.range ≃ₗ[R] E'.range := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hEE' : E = r.comp (E'.comp i) := hE.unique (hE'.comp_comp_of_retract hri)
  have hir_E' (y : N) : i (r (E' y)) = E' y := (comp_apply_eq_and_apply_comp_eq hri hE' hQ y).1
  have hE'_ir (y : N) : E' (i (r y)) = E' y := (comp_apply_eq_and_apply_comp_eq hri hE' hQ y).2
  have hmaps_i (x : M) (hx : x ∈ E.range) : i x ∈ E'.range := by
    rcases hx with ⟨z, rfl⟩
    exact ⟨i z, by simp only [coe_coe, hEE', comp_apply, hir_E']⟩
  have hmaps_r (y : N) (hy : y ∈ E'.range) : r y ∈ E.range := by
    rcases hy with ⟨w, rfl⟩
    exact ⟨r w, by simp only [coe_coe, hEE', comp_apply, hE'_ir]⟩
  exact LinearEquiv.ofLinearMap
    (i.toLinearMap.restrict hmaps_i)
    (r.toLinearMap.restrict hmaps_r)
    (LinearMap.ext fun y ↦ Subtype.ext <| by
      rcases y.property with ⟨w, hw⟩
      simpa [← hw] using hir_E' w)
    (LinearMap.ext fun x ↦ Subtype.ext (hri' x))

/-- **Constant rank of the Riesz–Coleman summand on a (Pr) module.** For a coprime factorisation
`H_u = Q · S` with `Q(0) = 1` and `IsUnit Q.leadingCoeff`, `range E` has rank `deg Q` at every
prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hu' := hu.isRowCompact_comp i r
  have hfac' : (i.comp (u.comp r)).matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S :=
    (hu.charPowerSeries_eq hri).symm.trans hfac
  have hE' := hu'.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hfac' hcop
  let : AddCommGroup E.range := inferInstance
  let : AddCommGroup ((i.comp (u.comp r)).rieszColemanProjection Q).range := inferInstance
  have heq := Module.rankAtStalk_eq_of_equiv (rangeEquivOfRetract hri hE hE' hQ)
  rw [congrFun heq p]
  exact hE'.rankAtStalk_range hu' hQ0 hQ hS hfac' hcop p

/-- **Constant rank of `ker Q*(u)` on a (Pr) module.** For a coprime factorisation `H_u = Q · S`
with `Q(0) = 1` and `IsUnit Q.leadingCoeff`, `ker Q*(u)` has rank `deg Q` at every prime ideal. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) p =
      Q.natDegree := by
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection hQ0 hQ hS hfac hcop
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range_of_isPrCompact hu hQ0 hQ hS hfac hcop p

/-- **Characteristic polynomial of the Riesz–Coleman summand on a (Pr) module.** On the finite
projective summand `range E`, the reversed characteristic polynomial `det (1 - X u|_{range E})`
equals `Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    haveI := hE.finite_range_of_isPrCompact hu hQ
    haveI := hE.projective_range_of_isPrCompact hu hQ
    (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).toLinearMap.projectiveCharpolyRev = Q := by
  classical
  let : AddCommGroup E.range := inferInstance
  have := hE.finite_range_of_isPrCompact hu hQ
  have := hE.projective_range_of_isPrCompact hu hQ
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hu' := hu.isRowCompact_comp i r
  have hfac' : (i.comp (u.comp r)).matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S :=
    (hu.charPowerSeries_eq hri).symm.trans hfac
  have hE' := hu'.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hfac' hcop
  let E' := (i.comp (u.comp r)).rieszColemanProjection Q
  let : AddCommGroup E'.range := inferInstance
  have := hE'.finite_range hu' hQ
  have := hE'.projective_range hu' hQ
  let e := rangeEquivOfRetract hri hE hE' hQ
  let f₀ : Module.End R E.range := (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).toLinearMap
  let g₀ : Module.End R E'.range :=
    ((i.comp (u.comp r)).restrict (fun _ hx ↦ hE'.mapsTo_range hx)).toLinearMap
  have hfg (x : E.range) : g₀ (e x) = e (f₀ x) := Subtype.ext <| by
    change i (u (r (i x))) = i (u x)
    rw [hri']
  have hmap := LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq
    (θ := RingHom.id R) (θ' := RingHom.id R) e hfg
  rw [Polynomial.map_id] at hmap
  exact hmap.symm.trans (hE'.projectiveCharpolyRev_restrict_range hu' hQ0 hQ hS hfac' hcop)

/-- **Finite Fredholm factor of a Riesz–Coleman splitting on a (Pr) module.** For a coprime
factorisation `H_u = Q · S` with `Q(0) = 1` and `IsUnit Q.leadingCoeff`, `(u * E).charPowerSeries`
equals `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : PowerSeries R) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hu' := hu.isRowCompact_comp i r
  have hfac' : (i.comp (u.comp r)).matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S :=
    (hu.charPowerSeries_eq hri).symm.trans hfac
  let E' := (i.comp (u.comp r)).rieszColemanProjection Q
  have hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E' :=
    hu'.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hfac' hcop
  have hEE' : E = r.comp (E'.comp i) := hE.unique (hE'.comp_comp_of_retract hri)
  have hE'_ir (y : C₀(J, R)) : E' (i (r y)) = E' y :=
    (comp_apply_eq_and_apply_comp_eq hri hE' hQ y).2
  have hcomp : i.comp ((u * E).comp r) = i.comp (u.comp r) * E' := by
    ext y
    simp only [comp_apply, mul_apply_eq_comp, hEE', hE'_ir]
  rw [mul_def, (hu.comp_clm E hu.hasPr_source).charPowerSeries_eq hri, ← mul_def, hcomp]
  exact hE'.charPowerSeries_matrixCoeff_mul_eq hu' hQ0 hQ hS hfac' hcop

/-- **Complementary Fredholm factor of a Riesz–Coleman splitting on a (Pr) module.** For a coprime
factorisation `H_u = Q · S` with `Q(0) = 1` and `IsUnit Q.leadingCoeff`,
`(u * (1 - E)).charPowerSeries` equals `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hu' := hu.isRowCompact_comp i r
  have hfac' : (i.comp (u.comp r)).matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S :=
    (hu.charPowerSeries_eq hri).symm.trans hfac
  let E' := (i.comp (u.comp r)).rieszColemanProjection Q
  have hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E' :=
    hu'.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hfac' hcop
  have hEE' : E = r.comp (E'.comp i) := hE.unique (hE'.comp_comp_of_retract hri)
  have hE'_ir (y : C₀(J, R)) : E' (i (r y)) = E' y :=
    (comp_apply_eq_and_apply_comp_eq hri hE' hQ y).2
  have hcomp : i.comp ((u * (1 - E)).comp r) = i.comp (u.comp r) * (1 - E') := by
    ext y
    simp only [comp_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self]
    rw [hEE', comp_apply, comp_apply, hE'_ir, ← map_sub r]
  rw [mul_def, (hu.comp_clm (1 - E) hu.hasPr_source).charPowerSeries_eq hri, ← mul_def, hcomp]
  exact hE'.charPowerSeries_matrixCoeff_mul_one_sub_eq hu' hQ0 hQ hS hfac' hcop

end PrModule

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [IsBoundedSMul K M]
  {u E : M →L[K] M} {Q : K[X]} {S : PowerSeries K}

/-- Over a complete ultrametric field, the range of the Riesz–Coleman projection on a module with
property (Pr) for a coprime factor `Q` with `Q(0) = 1` of `H_u = Q · S` has dimension `deg Q`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : PowerSeries K) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff :=
    Ne.isUnit (leadingCoeff_ne_zero.mpr fun h0 ↦ by simp [h0] at hQ0)
  have hr := hE.rankAtStalk_range_of_isPrCompact hu hQ0 hQ hS hfac hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, `ker Q*(u)` on a module with property (Pr) has dimension
`deg Q` whenever `H_u = Q · S` is a coprime factorisation with `Q(0) = 1`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : PowerSeries K) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[K] M) : M →ₗ[K] M)) = Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff :=
    Ne.isUnit (leadingCoeff_ne_zero.mpr fun h0 ↦ by simp [h0] at hQ0)
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection hQ0 hQ hS hfac hcop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range_of_isPrCompact hu hQ0 hS hfac hcop

end Field

end ContinuousLinearMap
