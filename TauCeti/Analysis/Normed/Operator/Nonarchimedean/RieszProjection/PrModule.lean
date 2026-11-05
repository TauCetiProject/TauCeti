/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
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
coefficient ring may have nilpotents and the eigenspace need not be free.

## Main results

* `ContinuousLinearMap.IsPrCompact.exists_isRieszProjection`: the Riesz projection of a row-compact
  operator on a module with property (Pr) at a good zero of its Fredholm series.
* `ContinuousLinearMap.IsRieszProjection.isPrCompact`: Riesz projections of row-compact operators
  are row compact.
* `ContinuousLinearMap.IsRieszProjection.finite_ker_pow_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszProjection.projective_ker_pow_of_isPrCompact`: the generalised
  eigenspace is a finitely generated projective module.

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

end ContinuousLinearMap
