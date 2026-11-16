/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.ModelSpace
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on modules with property (Pr)

Over a complete ultrametric normed commutative ring `R` with Tate scalars, a module `M` with
property (Pr) (`TauCeti.HasPr R M`) is a continuous linear retract `r ∘ i = id` of a model space
`C₀(J, R)`. Riesz–Coleman projections compress along such retracts
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`), and when `Q` has invertible
leading coefficient the extension `i ∘ E ∘ r` recovers the model-space projector `F`
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`).

Consequently, every coprime factorisation `H_u = Q * S` of the Fredholm series of a row-compact
endomorphism `u` of `M`, with `Q` a polynomial with invertible leading coefficient and `S` entire,
produces a unique Riesz–Coleman projection `E`
(`ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`).
The projection `E` is itself row compact, so `range E = ker Q*(u)` is finitely generated and
projective of constant stalk rank `deg Q` on `Spec R` (and dimension `deg Q` over a field). When
`Q(0) = 1`, the Fredholm series of `u * E` and of `u` restricted to `range E` both equal `Q`, and
the Fredholm series of `u * (1 - E)` and of `u` restricted to `ker E` both equal `S`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`: every Riesz–Coleman projection of a
  row-compact endomorphism (for `Q` with invertible leading coefficient) is row compact.
* `ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`: existence of the Riesz–Coleman
  projector on a module with property (Pr) for a coprime factorisation `H_u = Q * S`.
* `ContinuousLinearMap.IsRieszColemanProjection.finite_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact`:
  `range E = ker Q*(u)` is finitely generated and projective.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`: constant rank `deg Q` on
  `Spec R`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker`: identification of
  the Fredholm factors `Q` and `S` on the two spectral summands.
* `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`: over a complete ultrametric field,
  `range E = ker Q*(u)` has dimension `deg Q`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm PowerSeries
open PowerSeries (IsEntire)

namespace ContinuousLinearMap

section PrModule

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u E : M →L[R] M} {Q : Polynomial R} {S : R⟦X⟧}

/-- A Riesz–Coleman projection of a row-compact endomorphism of a module with property (Pr), for a
polynomial `Q` with invertible leading coefficient, is row compact. -/
theorem IsRieszColemanProjection.isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) : E.IsPrCompact := by
  rw [← hE.mul_aeval_divX_mul_eq hQ]
  simpa only [mul_def] using (hu.comp_clm _ hu.hasPr_source).comp_clm E hu.hasPr_source

variable [CompleteSpace R]

/-- **Riesz–Coleman decomposition on a module with property (Pr).** Let `u` be a row-compact
endomorphism of a module with property (Pr) whose Fredholm series admits a coprime factorisation
`H_u = Q * S` in the ring of entire series, where `Q` is a polynomial with invertible leading
coefficient and `S` is entire. Then `u` has a Riesz–Coleman projection for `Q`. The factorisation
forces `Q(0)` to be a unit, covering both normalised (`Q(0) = 1`) and monic polynomial factors. -/
theorem IsPrCompact.exists_rieszColemanProjection (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hH
  obtain ⟨F, hF⟩ := (hu.isRowCompact_comp i r).exists_rieszColemanProjection hH hQ hS hcop
  exact ⟨_, hF.comp_comp_of_retract hri⟩

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism of a module with
property (Pr) is finitely generated. -/
theorem IsRieszColemanProjection.finite_range_of_isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) : Module.Finite R E.range :=
  (hE.isPrCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism of a module with
property (Pr) is projective over the coefficient ring. -/
theorem IsRieszColemanProjection.projective_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R E.range :=
  (hE.isPrCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- The kernel `ker Q*(u)` of a row-compact endomorphism of a module with property (Pr) admitting
a Riesz–Coleman projection is finitely generated. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range_of_isPrCompact hu hQ

/-- The kernel `ker Q*(u)` of a row-compact endomorphism of a module with property (Pr) admitting
a Riesz–Coleman projection is projective over the coefficient ring. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range_of_isPrCompact hu hQ

/-- **Constant rank on (Pr) modules.** The range of a Riesz–Coleman projection for a coprime
factorisation `H_u = Q * S` on a module with property (Pr) has constant rank `deg Q` on `Spec R`.
No Noetherianity or reducedness hypothesis is imposed. -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hH
  have hv := hu.isRowCompact_comp i r
  obtain ⟨F, hF⟩ := hv.exists_rieszColemanProjection hH hQ hS hcop
  have hFE : i.comp (E.comp r) = F := hE.comp_comp_eq_of_retract hri hQ hF
  have heq : E.range ≃ₗ[R] F.range :=
    (rangeEquivOfRetract E hri).trans (LinearEquiv.ofEq _ _ (by rw [← hFE]; rfl))
  have hrank : Module.rankAtStalk (R := R) E.range = Module.rankAtStalk (R := R) F.range := by
    let : AddCommGroup E.range := inferInstance
    let : AddCommGroup F.range := inferInstance
    exact Module.rankAtStalk_eq_of_equiv heq
  rw [hrank]
  exact hF.rankAtStalk_range hv hH hQ hS hcop p

/-- **Determinant on the finite summand on (Pr) modules.** For a normalised coprime factorisation
`H_u = Q * S` with `Q(0) = 1`, the Fredholm series of `u * E` equals `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  rw [hu.charPowerSeries_eq hri] at hH
  have hv := hu.isRowCompact_comp i r
  obtain ⟨F, hF⟩ := hv.exists_rieszColemanProjection hH hQ hS hcop
  have hFE : i.comp (E.comp r) = F := hE.comp_comp_eq_of_retract hri hQ hF
  have huE : (u * E).IsPrCompact := hu.comp_clm E hu.hasPr_source
  have hext : i.comp ((u * E).comp r) = i.comp (u.comp r) * F := by
    ext y : 1
    simp [← hFE, hri']
  rw [huE.charPowerSeries_eq hri, hext]
  exact hF.charPowerSeries_matrixCoeff_mul hv hH hQ0 hQ hS hcop

/-- **Determinant on the complementary summand on (Pr) modules.** For a normalised coprime
factorisation `H_u = Q * S` with `Q(0) = 1`, the Fredholm series of `u * (1 - E)` equals `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  rw [hu.charPowerSeries_eq hri] at hH
  have hv := hu.isRowCompact_comp i r
  obtain ⟨F, hF⟩ := hv.exists_rieszColemanProjection hH hQ hS hcop
  have hFE : i.comp (E.comp r) = F := hE.comp_comp_eq_of_retract hri hQ hF
  have huE : (u * (1 - E)).IsPrCompact := hu.comp_clm (1 - E) hu.hasPr_source
  have hext : i.comp ((u * (1 - E)).comp r) = i.comp (u.comp r) * (1 - F) := by
    ext y : 1
    simp [← hFE, hri']
  rw [huE.charPowerSeries_eq hri, hext]
  exact hF.charPowerSeries_matrixCoeff_mul_one_sub hv hH hQ0 hQ hS hcop

/-- **Fredholm series of the restriction to `range E`.** For a normalised coprime factorisation
`H_u = Q * S` with `Q(0) = 1`, the restriction of `u` to the finite projective summand `range E`
has Fredholm series `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict hE.mapsTo_range).charPowerSeries = (Q : R⟦X⟧) := by
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ext fun x ↦ Subtype.ext (IsIdempotentElem.apply_coe_range hE.isIdempotentElem x)
  have hPr : TauCeti.HasPr R E.range :=
    hu.hasPr_source.of_retract E.range.subtypeL E.rangeRestrict hri
  have hfac : u.restrict hE.mapsTo_range = E.rangeRestrict.comp (u.comp E.range.subtypeL) := by
    ext x
    exact (IsIdempotentElem.apply_coe_range hE.isIdempotentElem ⟨u x, hE.mapsTo_range x.2⟩).symm
  have hrev : (u.comp E.range.subtypeL).comp E.rangeRestrict = u * E := by
    ext x
    rfl
  rw [hfac, ← (hu.comp_clm E.range.subtypeL hPr).charPowerSeries_comp_comm E.rangeRestrict, hrev]
  exact hE.charPowerSeries_mul hu hH hQ0 hQ hS hcop

/-- **Fredholm series of the restriction to `ker E`.** For a normalised coprime factorisation
`H_u = Q * S` with `Q(0) = 1`, the restriction of `u` to the complementary summand `ker E` has
Fredholm series `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict hE.mapsTo_ker).charPowerSeries = S := by
  let rK : M →L[R] E.ker := (1 - E).codRestrict E.ker fun x ↦ by
    apply LinearMap.mem_ker.mpr
    have hid := congr($(hE.isIdempotentElem.eq) x)
    simpa only [coe_coe, sub_apply, one_apply_eq_self, map_sub, mul_apply_eq_comp,
      sub_eq_zero] using hid.symm
  have hri : rK.comp E.ker.subtypeL = .id R E.ker := by
    ext x
    have hx : E x = 0 := LinearMap.mem_ker.mp x.2
    simp [rK, hx]
  have hPr : TauCeti.HasPr R E.ker := hu.hasPr_source.of_retract E.ker.subtypeL rK hri
  have hfac : u.restrict hE.mapsTo_ker = rK.comp (u.comp E.ker.subtypeL) := by
    ext x
    have hx : E (u x) = 0 := LinearMap.mem_ker.mp (hE.mapsTo_ker x.2)
    simp [rK, hx]
    rfl
  have hrev : (u.comp E.ker.subtypeL).comp rK = u * (1 - E) := by
    ext x
    rfl
  rw [hfac, ← (hu.comp_clm E.ker.subtypeL hPr).charPowerSeries_comp_comm rK, hrev]
  exact hE.charPowerSeries_mul_one_sub hu hH hQ0 hQ hS hcop

end PrModule

section KernelRank

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M]
  {u : M →L[R] M} {Q : Polynomial R} {S : R⟦X⟧}

/-- For a coprime factorisation `H_u = Q * S` on a module with property (Pr), the kernel
`ker Q*(u)` has constant rank `deg Q` on `Spec R`. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) p = Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  rw [hu.charPowerSeries_eq hri] at hH
  set v : C₀(J, R) →L[R] C₀(J, R) := i.comp (u.comp r)
  have hv : v.IsRowCompact := hu.isRowCompact_comp i r
  obtain ⟨F, hF⟩ := hv.exists_rieszColemanProjection hH hQ hS hcop
  have hr : u.toLinearMap ∘ₗ r.toLinearMap = r.toLinearMap ∘ₗ v.toLinearMap :=
    LinearMap.ext fun y ↦ by simp [v, hri']
  have hi : v.toLinearMap ∘ₗ i.toLinearMap = i.toLinearMap ∘ₗ u.toLinearMap :=
    LinearMap.ext fun x ↦ by simp [v, hri']
  have hra (y : C₀(J, R)) :
      Polynomial.aeval u Q.reverse (r y) = r (Polynomial.aeval v Q.reverse y) := by
    have h := congr($(Module.End.aeval_comp_of_comp_eq hr Q.reverse) y)
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h
  have hia (x : M) :
      Polynomial.aeval v Q.reverse (i x) = i (Polynomial.aeval u Q.reverse x) := by
    have h := congr($(Module.End.aeval_comp_of_comp_eq hi Q.reverse) x)
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h
  have hF_fix (y : C₀(J, R)) : i (r (F y)) = F y := by
    have hmul := congr($(hF.mul_aeval_divX_mul_eq hQ) y)
    have hval : F y = i (u (r (Polynomial.aeval v
        (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse).divX (F y)))) := by
      simpa only [v, mul_apply_eq_comp, comp_apply] using hmul.symm
    conv_lhs => rw [hval]
    rw [hri', ← hval]
  let Ku := LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)
  let Kv := LinearMap.ker ((Polynomial.aeval v Q.reverse : C₀(J, R) →L[R] C₀(J, R)) :
    C₀(J, R) →ₗ[R] C₀(J, R))
  have heq : Ku ≃ₗ[R] Kv :=
    LinearEquiv.ofLinearMap
      (i.toLinearMap.restrict (p := Ku) (q := Kv) fun x hx ↦ by
        simp only [Ku, Kv, LinearMap.mem_ker, coe_coe] at hx ⊢
        rw [hia, hx, map_zero])
      (r.toLinearMap.restrict (p := Kv) (q := Ku) fun y hy ↦ by
        simp only [Ku, Kv, LinearMap.mem_ker, coe_coe] at hy ⊢
        rw [hra, hy, map_zero])
      (LinearMap.ext fun y ↦ Subtype.ext (by
        have hyF : y.1 ∈ F.range := by rw [hF.range_eq_ker]; exact y.2
        have hFy : F y.1 = y.1 :=
          IsIdempotentElem.apply_coe_range hF.isIdempotentElem ⟨y.1, hyF⟩
        simpa only [LinearMap.comp_apply, LinearMap.restrict_apply, LinearMap.id_apply, coe_coe,
          hFy] using hF_fix y.1))
      (LinearMap.ext fun x ↦ Subtype.ext (by
        simpa only [LinearMap.comp_apply, LinearMap.restrict_apply, LinearMap.id_apply,
          coe_coe] using hri' x.1))
  have hker : Module.rankAtStalk (R := R) Ku = Module.rankAtStalk (R := R) Kv := by
    let : AddCommGroup Ku := inferInstance
    let : AddCommGroup Kv := inferInstance
    exact Module.rankAtStalk_eq_of_equiv heq
  rw [show Module.rankAtStalk (R := R) Ku p = Module.rankAtStalk (R := R) Kv p from
    congrFun hker p]
  exact hv.rankAtStalk_ker_aeval_reverse hH hQ hS hcop p

end KernelRank

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u E : M →L[K] M} {Q : Polynomial K} {S : K⟦X⟧}

/-- Over a complete ultrametric field, for a coprime factorisation `H_u = Q * S` on a module with
property (Pr), the kernel `ker Q*(u)` has dimension `deg Q`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : K⟦X⟧) * S) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[K] M) : M →ₗ[K] M)) = Q.natDegree := by
  have hQne : Q ≠ 0 := by
    rintro rfl
    have h0 := congrArg PowerSeries.constantCoeff hH
    simp at h0
  have hQ : IsUnit Q.leadingCoeff := (Polynomial.leadingCoeff_ne_zero.2 hQne).isUnit
  have hr := hu.rankAtStalk_ker_aeval_reverse hH hQ hS hcop ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- Over a complete ultrametric field, the range of a Riesz–Coleman projection on a module with
property (Pr) has dimension `deg Q`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact [IsBoundedSMul K M]
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries = (Q : K⟦X⟧) * S) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  rw [hE.range_eq_ker]
  exact hu.finrank_ker_aeval_reverse hH hS hcop

end Field

end ContinuousLinearMap
