/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.ModelSpace
public import TauCeti.LinearAlgebra.Charpoly.Projective
import TauCeti.LinearAlgebra.End.Split
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on modules with property (Pr)

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, `M` a Banach module
with property (Pr) over `R`, and `u : M →L[R] M` a row-compact endomorphism with Fredholm series
`H_u(T) = det (1 - T u)`. Suppose `H_u = Q * S`, where `Q ∈ R[T]` satisfies `Q(0) = 1` and has
invertible leading coefficient, `S ∈ R⟦T⟧` is entire, and `Q` and `S` are coprime in the ring of
entire series `PowerSeries.IsEntire.subring R`.

Presenting `M` as a continuous linear retract `r ∘ i = id` of a model space `C₀(J, R)` transports
the model-space Riesz–Coleman decomposition (`RieszColeman.ModelSpace`) to `M`:

* `u` admits a unique Riesz–Coleman projection `E` at `Q`
  (`ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection`);
* `ker Q*(u)` has constant rank `Q.natDegree` over `Spec R`
  (`ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`), and dimension
  `Q.natDegree` over a field (`ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`); the kernel rank
  and dimension statements require only `ContinuousConstSMul R M`;
* the restrictions of `u` to `range E` and `ker E` are row compact
  (`ContinuousLinearMap.IsRieszColemanProjection.isPrCompact_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact_restrict_ker`), with Fredholm series
  `Q` and `S` respectively
  (`ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker`);
* on the finitely generated projective summand `range E = ker Q*(u)`, the reversed characteristic
  polynomial `det (1 - X u|_{range E})` equals `Q`
  (`ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range`).

No Noetherianity, reducedness, or freeness is assumed, and the case `Q = 1` (giving `E = 0` and
rank zero) is included.

## Main results

* `ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection`: existence of the
  Riesz–Coleman projection on a module with property (Pr).
* `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`: constant rank
  `Q.natDegree` over `Spec R`.
* `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact_restrict_ker`: compactness of the
  restrictions of `u` to the two summands.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker`: identification of
  the Fredholm series on both summands.
* `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range`:
  `det (1 - X u|_{range E}) = Q`.
* `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`: over a field,
  `ker Q*(u)` and `range E` have dimension `Q.natDegree`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  Algebra Number Theory **13** (2019), §2.2.
-/

public section

open scoped ZeroAtInfty PowerSeries TauCeti.RingOpNorm

namespace ContinuousLinearMap

section PrModule

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u E : M →L[R] M} {Q : Polynomial R} {S : R⟦X⟧}

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Retract factorisation of `u` restricted to `E.range` through `E.rangeRestrict`. -/
private theorem restrict_range_retract (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    TauCeti.HasPr R E.range ∧
      u.restrict hE.mapsTo_range = E.rangeRestrict.comp (u.comp E.range.subtypeL) := by
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp x.property
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ext fun x ↦ Subtype.ext (hfix x)
  refine ⟨hu.hasPr_source.of_retract E.range.subtypeL E.rangeRestrict hri,
    ext fun x ↦ Subtype.ext ?_⟩
  exact (hfix ⟨u x, hE.mapsTo_range x.property⟩).symm

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Retract factorisation of `u` restricted to `E.ker` through `1 - E`. -/
private theorem restrict_ker_retract (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    ∃ r : M →L[R] E.ker, TauCeti.HasPr R E.ker ∧
      u.restrict hE.mapsTo_ker = r.comp (u.comp E.ker.subtypeL) ∧
      (u.comp E.ker.subtypeL).comp r = u * (1 - E) := by
  let r : M →L[R] E.ker := (1 - E).codRestrict E.ker fun x ↦
    LinearMap.mem_ker.mpr <| by
      have hEE : E (E x) = E x := congr($hE.isIdempotentElem.eq x)
      simp [hEE]
  have hri : r.comp E.ker.subtypeL = .id R E.ker := ext fun x ↦ Subtype.ext <| by
    have hx : E x = 0 := LinearMap.mem_ker.mp x.property
    simp [r, hx]
  refine ⟨r, hu.hasPr_source.of_retract E.ker.subtypeL r hri, ext fun x ↦ Subtype.ext ?_,
    ext fun _ ↦ rfl⟩
  have hux : E (u x) = 0 := LinearMap.mem_ker.mp (hE.mapsTo_ker x.property)
  simp only [comp_apply, Submodule.coe_subtypeL, Submodule.coe_subtype, r,
    coe_codRestrict_apply, sub_apply, one_apply_eq_self, hux, sub_zero]
  exact coe_restrict_apply _ x

omit [CompleteSpace R] in
/-- The restriction of a row-compact endomorphism `u` to the range of a Riesz–Coleman projection
is row compact. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_range (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) : (u.restrict hE.mapsTo_range).IsPrCompact := by
  obtain ⟨hM, heq⟩ := restrict_range_retract hE hu
  rw [heq]
  exact (hu.comp_clm E.range.subtypeL hM).clm_comp E.rangeRestrict hM

omit [CompleteSpace R] in
/-- The restriction of a row-compact endomorphism `u` to the kernel of a Riesz–Coleman projection
is row compact. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_ker (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) : (u.restrict hE.mapsTo_ker).IsPrCompact := by
  obtain ⟨r, hM, heq, -⟩ := restrict_ker_retract hE hu
  rw [heq]
  exact (hu.comp_clm E.ker.subtypeL hM).clm_comp r hM

/-- The Fredholm series of `u` restricted to the range of a Riesz–Coleman projection equals the
Fredholm series of `u * E`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_range_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict hE.mapsTo_range).charPowerSeries = (u * E).charPowerSeries := by
  obtain ⟨hM, heq⟩ := restrict_range_retract hE hu
  have hext : (u.comp E.range.subtypeL).comp E.rangeRestrict = u * E := ext fun _ ↦ rfl
  rw [heq, ← (hu.comp_clm E.range.subtypeL hM).charPowerSeries_comp_comm E.rangeRestrict, hext]

/-- The Fredholm series of `u` restricted to the kernel of a Riesz–Coleman projection equals the
Fredholm series of `u * (1 - E)`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) :
    (u.restrict hE.mapsTo_ker).charPowerSeries = (u * (1 - E)).charPowerSeries := by
  obtain ⟨r, hM, heq, hext⟩ := restrict_ker_retract hE hu
  rw [heq, ← (hu.comp_clm E.ker.subtypeL hM).charPowerSeries_comp_comm r, hext]

/-- **Riesz–Coleman decomposition on modules with property (Pr).** Let `u` be a row-compact
endomorphism of a module `M` with property (Pr) whose Fredholm series factors as `Q * S` with
`Q(0) = 1`, `Q.leadingCoeff` a unit, `S` entire, and `Q` coprime to `S` in the ring of entire
series. Then `u` admits a Riesz–Coleman projection at `Q`. The case `Q = 1` is included (giving
the zero projection). -/
theorem IsPrCompact.exists_isRieszColemanProjection (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hfac
  obtain ⟨F, hF⟩ := (hu.isRowCompact_comp i r).exists_isRieszColemanProjection hQ0 hQ hS hfac hcop
  exact ⟨r.comp (F.comp i), hF.comp_comp_of_retract hri⟩

/-- Shared Fredholm-series transport along a `(Pr)` retract for both summands `u * E` and
`u * (1 - E)`. -/
private theorem charPowerSeries_mul_and_one_sub (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) ∧ (u * (1 - E)).charPowerSeries = S := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  rw [hu.charPowerSeries_eq hri] at hfac
  have hv := hu.isRowCompact_comp i r
  obtain ⟨F, hF⟩ := hv.exists_isRieszColemanProjection hQ0 hQ hS hfac hcop
  have hEeq : E = r.comp (F.comp i) := hE.unique (hF.comp_comp_of_retract hri)
  have hFext := hF.eq_comp_comp_of_retract hri hQ
  have hFy (y : C₀(J, R)) : r (F y) = E (r y) := by
    simpa only [comp_apply, hri', ← hEeq] using congrArg r (congr($hFext y))
  have huE : (u * E).IsPrCompact := by simpa only [mul_def] using hu.comp_clm E hu.hasPr_source
  have hu1E : (u * (1 - E)).IsPrCompact := by
    simpa only [mul_def] using hu.comp_clm (1 - E) hu.hasPr_source
  refine ⟨?_, ?_⟩
  · have hmul_eq : i.comp ((u * E).comp r) = i.comp (u.comp r) * F := ext fun y ↦ by simp [hFy]
    rw [huE.charPowerSeries_eq hri, hmul_eq]
    exact hF.charPowerSeries_matrixCoeff_mul_eq hv hQ0 hQ hS hfac hcop
  · have hmul_eq : i.comp ((u * (1 - E)).comp r) = i.comp (u.comp r) * (1 - F) :=
      ext fun y ↦ by simp [hFy]
    rw [hu1E.charPowerSeries_eq hri, hmul_eq]
    exact hF.charPowerSeries_matrixCoeff_mul_one_sub_eq hv hQ0 hQ hS hfac hcop

/-- **Finite-summand Fredholm determinant on a (Pr) module.** Under a coprime factorisation
`H_u = Q * S`, the Fredholm series of `u * E` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_eq (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) :=
  (charPowerSeries_mul_and_one_sub hE hu hQ0 hQ hS hfac hcop).1

/-- **Complementary-summand Fredholm determinant on a (Pr) module.** Under a coprime factorisation
`H_u = Q * S`, the Fredholm series of `u * (1 - E)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S :=
  (charPowerSeries_mul_and_one_sub hE hu hQ0 hQ hS hfac hcop).2

/-- **Fredholm series on the finite summand.** Under a coprime factorisation `H_u = Q * S`, the
Fredholm series of `u` restricted to `range E = ker Q*(u)` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict hE.mapsTo_range).charPowerSeries = (Q : R⟦X⟧) := by
  rw [hE.charPowerSeries_restrict_range_eq hu]
  exact hE.charPowerSeries_mul_eq hu hQ0 hQ hS hfac hcop

/-- **Fredholm series on the complementary summand.** Under a coprime factorisation `H_u = Q * S`,
the Fredholm series of `u` restricted to `ker E = range Q*(u)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict hE.mapsTo_ker).charPowerSeries = S := by
  rw [hE.charPowerSeries_restrict_ker_eq hu]
  exact hE.charPowerSeries_mul_one_sub_eq hu hQ0 hQ hS hfac hcop

/-- **Characteristic polynomial of `u` on the finite projective summand.** Under a coprime
factorisation `H_u = Q * S` on any (Pr) module `M`, the reversed characteristic polynomial
`det (1 - X u|_{range E})` of `u` on the finite projective summand `range E = ker Q*(u)` is `Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    haveI := hE.finite_range_of_isPrCompact hu hQ
    haveI := hE.projective_range_of_isPrCompact hu hQ
    ((u.restrict hE.mapsTo_range : E.range →L[R] E.range) :
      Module.End R E.range).projectiveCharpolyRev = Q := by
  classical
  have := hE.finite_range_of_isPrCompact hu hQ
  have := hE.projective_range_of_isPrCompact hu hQ
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  rw [hu.charPowerSeries_eq hri] at hfac
  have hv := hu.isRowCompact_comp i r
  obtain ⟨F, hF⟩ := hv.exists_isRieszColemanProjection hQ0 hQ hS hfac hcop
  have hEeq : E = r.comp (F.comp i) := hE.unique (hF.comp_comp_of_retract hri)
  subst hEeq
  let : AddCommGroup F.range := inferInstance
  have hF_pr : F.IsPrCompact := isPrCompact_iff_isRowCompact.2 (hF.isRowCompact hv hQ)
  have := hF_pr.finite_range_of_isIdempotentElem hF.isIdempotentElem
  have := hF_pr.projective_range_of_isIdempotentElem hF.isIdempotentElem
  have htrans :
      (((i.comp (u.comp r)).restrict hF.mapsTo_range : F.range →L[R] F.range) :
        Module.End R F.range).projectiveCharpolyRev =
      (((u.restrict hE.mapsTo_range : (r.comp (F.comp i)).range →L[R]
        (r.comp (F.comp i)).range) :
        Module.End R (r.comp (F.comp i)).range).projectiveCharpolyRev).map (RingHom.id R) := by
    let eeq := LinearEquiv.ofEq (r.comp (F.comp i)).range
      (LinearMap.range (r.toLinearMap ∘ₗ F.toLinearMap ∘ₗ i.toLinearMap))
      (by simp only [toLinearMap_comp])
    refine LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq
      (eeq.trans (hF.rangeEquivOfRetract hri hQ)) fun x ↦ Subtype.ext ?_
    calc (((i.comp (u.comp r)).restrict hF.mapsTo_range : F.range →L[R] F.range)
            ((hF.rangeEquivOfRetract hri hQ) (eeq x)) : C₀(J, R))
        = i (u (r ((hF.rangeEquivOfRetract hri hQ) (eeq x) : C₀(J, R)))) :=
            coe_restrict_apply _ _
      _ = i (u (r (i x))) := by
            rw [IsRieszColemanProjection.coe_rangeEquivOfRetract_apply]
            exact congrArg (fun y ↦ i (u (r (i y)))) (LinearEquiv.coe_ofEq_apply _ x)
      _ = i (u x) := congrArg (fun y ↦ i (u y)) (hri' x)
      _ = i ((u.restrict hE.mapsTo_range : (r.comp (F.comp i)).range →L[R]
            (r.comp (F.comp i)).range) x : M) :=
            (congrArg i (coe_restrict_apply _ _)).symm
      _ = ((hF.rangeEquivOfRetract hri hQ)
            (eeq ((u.restrict hE.mapsTo_range : (r.comp (F.comp i)).range →L[R]
              (r.comp (F.comp i)).range) x)) : C₀(J, R)) :=
            ((IsRieszColemanProjection.coe_rangeEquivOfRetract_apply hri hF hQ _).trans
              (congrArg i (LinearEquiv.coe_ofEq_apply _ _))).symm
  rw [Polynomial.map_id] at htrans
  rw [← htrans]
  obtain ⟨hMF, -⟩ := restrict_range_retract hF (isPrCompact_iff_isRowCompact.2 hv)
  have hchar := charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := F.range) hMF
    ((i.comp (u.comp r)).restrict hF.mapsTo_range)
  apply Polynomial.coe_inj.mp
  rw [← hchar, hF.charPowerSeries_restrict_range_eq (isPrCompact_iff_isRowCompact.2 hv), mul_def,
    (hv.comp_clm F).charPowerSeries_eq_charPowerSeries_matrixCoeff, ← mul_def]
  exact hF.charPowerSeries_matrixCoeff_mul_eq hv hQ0 hQ hS hfac hcop

end PrModule

section Rank

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M]
  {u E : M →L[R] M} {Q : Polynomial R} {S : R⟦X⟧}

/-- **Constant rank of `ker Q*(u)` on a (Pr) module.** Under a coprime factorisation `H_u = Q * S`,
the kernel `ker Q*(u)` has constant rank `Q.natDegree` at every prime ideal of `R`. Only
`ContinuousConstSMul R M` is needed. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) p =
      Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hfac
  have hv := hu.isRowCompact_comp i r
  have hri' : r.toLinearMap ∘ₗ i.toLinearMap = LinearMap.id := by
    simpa only [toLinearMap_comp, coe_id] using congrArg ContinuousLinearMap.toLinearMap hri
  have heq :
      LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse :
        C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R)) ≃ₗ[R]
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
    have e := LinearMap.kerAevalEquivOfRetract r.toLinearMap i.toLinearMap hri' u.toLinearMap
      (p := Q.reverse) (by rwa [Polynomial.coeff_zero_reverse])
    convert e using 2 <;> simp only [toLinearMap_aeval, toLinearMap_comp]
  have hker : Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) =
      Module.rankAtStalk (R := R)
        (LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse :
          C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R))) := by
    let : AddCommGroup (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) :=
      inferInstance
    let : AddCommGroup (LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse :
      C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R))) := inferInstance
    exact Module.rankAtStalk_eq_of_equiv heq.symm
  rw [hker]
  exact hv.rankAtStalk_ker_aeval_reverse hQ0 hQ hS hfac hcop p

/-- **Constant rank of the Riesz–Coleman summand on a (Pr) module.** Under a coprime factorisation
`H_u = Q * S`, the range of the Riesz–Coleman projection at `Q` has constant rank `Q.natDegree`
at every prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact [IsBoundedSMul R M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  rw [hE.range_eq_ker]
  exact hu.rankAtStalk_ker_aeval_reverse hQ0 hQ hS hfac hcop p

end Rank

section PrModuleField

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u E : M →L[K] M} {Q : Polynomial K} {S : K⟦X⟧}

/-- Over a complete ultrametric field, `ker Q*(u)` has dimension `Q.natDegree` for a coprime
polynomial factor `Q` of `H_u` on a module with property (Pr). -/
theorem IsPrCompact.finrank_ker_aeval_reverse (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring K)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[K] M) : M →ₗ[K] M)) =
      Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff :=
    (Polynomial.leadingCoeff_ne_zero.mpr fun h0 ↦ by simp [h0] at hQ0).isUnit
  have hr := hu.rankAtStalk_ker_aeval_reverse hQ0 hQ hS hfac hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[K] M) : M →ₗ[K] M)) :=
    inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- Over a complete ultrametric field, the range of the Riesz–Coleman projection attached to a
coprime polynomial factor `Q` of `H_u` on a module with property (Pr) has dimension
`Q.natDegree`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact [IsBoundedSMul K M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hS : S.IsEntire)
    (hfac : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring K)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  rw [hE.range_eq_ker]
  exact hu.finrank_ker_aeval_reverse hQ0 hS hfac hcop

end PrModuleField

end ContinuousLinearMap
