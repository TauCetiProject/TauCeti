/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.FunctionalCalculus
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Entire

/-!
# Entire spectral mapping on modules with property (Pr)

For a row-compact endomorphism `u` of a module with property (Pr), an entire series `B` with
zero constant coefficient has row-compact value `B(u)`. Its presentation-independent Fredholm
series is the entire Coleman transform of that of `u`:

`(B.evalAt u).charPowerSeries = PowerSeries.colemanDEntire B u.charPowerSeries`.

Extension through any continuous linear retract commutes with this evaluation. Thus the
model-space spectral mapping theorem transports to modules that need not admit an
orthonormal basis, including finite projective modules of nonconstant rank. No reducedness or
Noetherian hypothesis on the coefficient ring is required.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A3.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Filter Topology
open scoped TauCeti.RingOpNorm PowerSeries

namespace ContinuousLinearMap

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [TauCeti.NormedRing.IsTate R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u : M →L[R] M} {B : R⟦X⟧}

/-- An entire series with zero constant coefficient preserves row compactness on modules with
property (Pr). Completeness of the module follows from its retract presentation. -/
theorem IsPrCompact.evalAt [CompleteSpace R] (hu : u.IsPrCompact) (hB : B.IsEntire)
    (hB₀ : PowerSeries.coeff 0 B = 0) : (B.evalAt u).IsPrCompact := by
  have := hu.hasPr_source.completeSpace
  apply isPrCompact_of_tendsto (l := atTop)
    (v := fun n : ℕ ↦ Polynomial.aeval u (PowerSeries.trunc (n + 1) B))
  · simpa only [norm_sub_rev, Function.comp_apply] using tendsto_iff_norm_sub_tendsto_zero.mp
      ((hB.tendsto_aeval_trunc u).comp (tendsto_add_atTop_nat 1))
  · exact Eventually.of_forall fun n ↦ hu.aeval (by simp [PowerSeries.coeff_trunc, hB₀])

/-- **Entire spectral mapping on (Pr) modules.** Evaluating a zero-constant entire series at a
row-compact endomorphism transforms its intrinsic Fredholm series by Coleman's entire
transform, independently of any retract presentation. -/
theorem IsPrCompact.charPowerSeries_eq_colemanDEntire [CompleteSpace R] [NormOneClass R]
    (hu : u.IsPrCompact) (hB : B.IsEntire) (hB₀ : PowerSeries.coeff 0 B = 0) :
    (B.evalAt u).charPowerSeries = PowerSeries.colemanDEntire B u.charPowerSeries := by
  classical
  have := hu.hasPr_source.completeSpace
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [(hu.evalAt hB hB₀).charPowerSeries_eq hri, hu.charPowerSeries_eq hri,
    ← evalAt_comp_comp_of_retract hri u hB hB₀]
  exact (hu.isRowCompact_comp i r).charPowerSeries_eq_colemanDEntire hB hB₀

end ContinuousLinearMap
