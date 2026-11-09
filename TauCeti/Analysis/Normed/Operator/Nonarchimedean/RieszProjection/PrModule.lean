/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
public import TauCeti.LinearAlgebra.End.Split
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero

/-!
# Riesz projections on modules with property (Pr)

Over a complete ultrametric norm-one Tate ring, a module with property (Pr) is a continuous linear
retract `r ∘ i = id` of a model space `C₀(J, R)`. Riesz projections compress along such retracts
(`ContinuousLinearMap.IsRieszProjection.comp_comp_of_retract`), and the Fredholm series `H_u` of
a row-compact `u` is that of its extension
(`ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`). Hence a good zero `a` of order
`h` of `H_u` gives a Riesz projection of `u` at `a` of order `h`
(`ContinuousLinearMap.IsPrCompact.exists_isRieszProjection`), and it is unique
(`ContinuousLinearMap.IsRieszProjection.unique`). Its range is the generalised eigenspace
`ker (1 - a • u) ^ h` (`ContinuousLinearMap.IsRieszProjection.range_eq_ker`). A Riesz projection
of a row-compact operator is row compact (`ContinuousLinearMap.IsRieszProjection.isPrCompact`), so
the generalised eigenspace is finitely generated and projective
(`ContinuousLinearMap.IsRieszProjection.finite_ker_pow_of_isPrCompact`,
`ContinuousLinearMap.IsRieszProjection.projective_ker_pow_of_isPrCompact`). As on model spaces, the
coefficient ring may have nilpotents and the eigenspace need not be free. Its rank at every
prime is the order of the good zero; over a field this is its dimension. The rank comparison
uses only the inclusion and retraction of a (Pr) presentation, not a finite free complement.
Order zero, exponent zero, and the zero module are included.

## Main results

* `ContinuousLinearMap.IsPrCompact.exists_isRieszProjection`: the Riesz projection of a row-compact
  operator on a module with property (Pr) at a good zero of its Fredholm series.
* `ContinuousLinearMap.IsRieszProjection.isPrCompact`: Riesz projections of row-compact operators
  are row compact.
* `ContinuousLinearMap.IsRieszProjection.finite_ker_pow_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszProjection.projective_ker_pow_of_isPrCompact`: the generalised
  eigenspace is a finitely generated projective module.
* `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_pow`,
  `ContinuousLinearMap.IsRieszProjection.rankAtStalk_range_of_isPrCompact`: the rank at every
  prime ideal equals the order of the good zero.
* `ContinuousLinearMap.IsPrCompact.finrank_ker_pow`,
  `ContinuousLinearMap.IsRieszProjection.finrank_range_of_isPrCompact`: over a field, the
  dimension equals the order of the good zero.
* `ContinuousLinearMap.IsPrCompact.finrank_maxGenEigenspace`: over a field, the algebraic
  multiplicity of a nonzero eigenvalue `μ` is the order of the zero of the Fredholm series at
  `μ⁻¹`.
* `ContinuousLinearMap.IsPrCompact.finrank_maxGenEigenspace_eq_order_taylor`: the same, stated
  with the order of the Taylor translate of the Fredholm series at `μ⁻¹`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

section PrModule

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {M : Type*} [SeminormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] {u E : M →L[R] M} {a : R} {h : ℕ}

/-- **The Riesz projection at a good zero on a module with property (Pr).** Let `u` be a
row-compact endomorphism of a module with property (Pr), and `a` a good zero of order `h` of its
Fredholm series `H_u`: `ΔʲH_u(a) = 0` for `j < h` and `ΔʰH_u(a)` is a unit. Then `u` has a Riesz
projection at `a` of order `h`. -/
theorem IsPrCompact.exists_isRieszProjection [NormOneClass R]
    (hu : u.IsPrCompact) (ha : u.charPowerSeries.IsGoodZero a h) :
    ∃ E, IsRieszProjection u a h E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at ha
  obtain ⟨hH, hc⟩ := PowerSeries.isGoodZero_iff.1 ha
  exact ⟨_, ((hu.isRowCompact_comp i r).isRieszProjection_rieszProjection hH hc)
    |>.comp_comp_of_retract hri⟩

omit [CompleteSpace R] in
/-- A Riesz projection of a row-compact endomorphism of a module with property (Pr) is row
compact, including when its nilpotence bound is zero. -/
theorem IsRieszProjection.isPrCompact (hE : IsRieszProjection u a h E) (hu : u.IsPrCompact) :
    E.IsPrCompact := by
  let C : M →L[R] M := 1 - a • u
  -- The geometric sum expresses `E` as the row-compact factor `a • u` followed by bounded maps.
  have hEq : E = (1 - C) * (∑ i ∈ Finset.range h, C ^ i) * E := by
    rw [mul_neg_geom_sum C h]
    simp only [C, sub_mul (α := M →L[R] M), one_mul, hE.pow_mul_eq_zero,
      sub_zero (G := M →L[R] M)]
  have hc : (1 - C).IsPrCompact := by
    simpa only [C, sub_sub_cancel (1 : M →L[R] M) (a • u)] using hu.smul a
  rw [hEq]
  simpa only [mul_def] using
    ((hc.comp_clm _ hu.hasPr_source).comp_clm E hu.hasPr_source)

/-- The stabilised generalised eigenspace `ker (1 - a • u) ^ n`, `n ≥ h`, of a row-compact
endomorphism of a module with property (Pr) is finitely generated. -/
theorem IsRieszProjection.finite_ker_pow_of_isPrCompact (hE : IsRieszProjection u a h E)
    (hu : u.IsPrCompact) {n : ℕ} (hn : h ≤ n) :
    Module.Finite R (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← (hE.of_le hn).range_eq_ker]
  exact (hE.isPrCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The stabilised generalised eigenspace `ker (1 - a • u) ^ n`, `n ≥ h`, of a row-compact
endomorphism of a module with property (Pr) is projective over the coefficient ring. -/
theorem IsRieszProjection.projective_ker_pow_of_isPrCompact (hE : IsRieszProjection u a h E)
    (hu : u.IsPrCompact) {n : ℕ} (hn : h ≤ n) :
    Module.Projective R (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← (hE.of_le hn).range_eq_ker]
  exact (hE.isPrCompact hu).projective_range_of_isIdempotentElem hE.isIdempotentElem

end PrModule

section Ring

variable {R M : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M]
  {u E : M →L[R] M} {a : R} {h n : ℕ}

/-- At a good Fredholm zero of order `h`, every stabilized generalized eigenspace on a
module with property (Pr) has rank `h` at every prime ideal of the coefficient ring.
No Noetherianity or reducedness hypothesis is imposed. -/
theorem IsPrCompact.rankAtStalk_ker_pow (hu : u.IsPrCompact)
    (hH : u.charPowerSeries.IsGoodZero a h) (hn : h ≤ n) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) p = h := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hH
  obtain ⟨hzero, hunit⟩ := PowerSeries.isGoodZero_iff.mp hH
  have hF := hv.isRieszProjection_rieszProjection hzero hunit
  -- Extension adds a zero block, so it does not change these spectral kernels.
  have hri' : r.toLinearMap.comp i.toLinearMap = LinearMap.id := by
    simpa only [toLinearMap_comp, coe_id] using
      congrArg ContinuousLinearMap.toLinearMap hri
  have heq :
      LinearMap.ker (((1 - a • i.comp (u.comp r)) ^ n :
        C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R)) ≃ₗ[R]
      LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M) := by
    have e := LinearMap.kerSplitEndEquiv r.toLinearMap i.toLinearMap hri'
      ((1 - a • u.toLinearMap) ^ n)
    rw [map_pow, LinearMap.splitEnd_one_sub] at e
    convert e using 2 <;>
      simp only [toLinearMap_pow, toLinearMap_sub, toLinearMap_one, toLinearMap_smul,
        toLinearMap_comp, LinearMap.comp_smul, LinearMap.smul_comp]
  have hker : Module.rankAtStalk (R := R)
      (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) =
      Module.rankAtStalk (R := R)
        (LinearMap.ker (((1 - a • i.comp (u.comp r)) ^ n :
          C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R))) := by
    -- Fixing the additive groups selects the submodule, rather than normed, structures.
    let : AddCommGroup (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) :=
      inferInstance
    let : AddCommGroup (LinearMap.ker (((1 - a • i.comp (u.comp r)) ^ n :
        C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R))) := inferInstance
    exact Module.rankAtStalk_eq_of_equiv heq.symm
  rw [hker, hF.ker_pow_eq hn, ← hF.range_eq_ker]
  exact hF.rankAtStalk_range hv hH p

/-- The range of any Riesz projection at a good Fredholm zero on a module with property
(Pr) has constant rank equal to the order of that zero. -/
theorem IsRieszProjection.rankAtStalk_range_of_isPrCompact [IsBoundedSMul R M]
    (hE : IsRieszProjection u a h E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries.IsGoodZero a h) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = h := by
  rw [hE.range_eq_ker]
  exact hu.rankAtStalk_ker_pow hH le_rfl p

end Ring

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u E : M →L[K] M} {a : K} {h n : ℕ}

/-- Over a complete ultrametric field, a good Fredholm zero of order `h` on a module
with property (Pr) has stabilized generalized eigenspaces of dimension `h`. -/
theorem IsPrCompact.finrank_ker_pow (hu : u.IsPrCompact)
    (hH : u.charPowerSeries.IsGoodZero a h) (hn : h ≤ n) :
    Module.finrank K (LinearMap.ker (((1 - a • u) ^ n : M →L[K] M) : M →ₗ[K] M)) = h := by
  have hr := hu.rankAtStalk_ker_pow hH hn ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- The range of a Riesz projection on a module with property (Pr) has dimension equal
to the order of the good Fredholm zero. This includes order zero. -/
theorem IsRieszProjection.finrank_range_of_isPrCompact [IsBoundedSMul K M]
    (hE : IsRieszProjection u a h E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries.IsGoodZero a h) : Module.finrank K E.range = h := by
  rw [hE.range_eq_ker]
  exact hu.finrank_ker_pow hH le_rfl

/-- **Algebraic multiplicities are orders of Fredholm zeros.** Over a complete ultrametric field,
if the Fredholm series of a row-compact endomorphism `u` of a module with property (Pr) has a good
zero of order `h` at `μ⁻¹`, then the maximal generalised eigenspace of `u` at the nonzero scalar
`μ` has dimension `h`. In particular `μ` is an eigenvalue when `h` is positive. -/
theorem IsPrCompact.finrank_maxGenEigenspace [IsBoundedSMul K M] (hu : u.IsPrCompact) {μ : K}
    (hμ : μ ≠ 0) (hH : u.charPowerSeries.IsGoodZero μ⁻¹ h) :
    Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) = h := by
  obtain ⟨E, hE⟩ := hu.exists_isRieszProjection hH
  rw [hE.maxGenEigenspace_eq_range (inv_mul_cancel₀ hμ)]
  exact hE.finrank_range_of_isPrCompact hu hH

/-- Over a complete ultrametric field, the algebraic multiplicity of a nonzero scalar `μ` for a
row-compact endomorphism `u` of a module with property (Pr) is the order of the zero of the
Fredholm series at `μ⁻¹`, that is, the order of the Taylor translate `taylor μ⁻¹ H_u`. -/
theorem IsPrCompact.finrank_maxGenEigenspace_eq_order_taylor [IsBoundedSMul K M]
    (hu : u.IsPrCompact) {μ : K} (hμ : μ ≠ 0) :
    (Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ∞) =
      (PowerSeries.taylor μ⁻¹ u.charPowerSeries).order := by
  obtain ⟨h, hh⟩ := hu.isEntire_charPowerSeries.exists_isGoodZero u.charPowerSeries_ne_zero μ⁻¹
  rw [hu.finrank_maxGenEigenspace hμ hh, PowerSeries.isGoodZero_iff_order_taylor_eq.mp hh]

end Field

end ContinuousLinearMap
