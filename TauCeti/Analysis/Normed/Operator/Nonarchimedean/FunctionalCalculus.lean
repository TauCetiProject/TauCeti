/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Entire
public import TauCeti.Analysis.Polynomial.Coleman.Entire

/-!
# Entire spectral mapping for Fredholm series

For a row-compact endomorphism `u` of `C₀(I, R)` and an entire power series `B` with
`B(0) = 0`, the Fredholm series of `B(u)` is the entire Coleman transform of the Fredholm
series of `u`:

`H_(B(u)) = colemanDEntire B H_u`.

The coefficient ring may be any complete ultrametric norm-one Tate ring, including rings
with nilpotents. The statement uses the existing entire evaluation in the bounded
endomorphism algebra. Polynomial truncations converge there in operator norm, so their
Fredholm coefficients converge. Polynomial spectral mapping identifies the other limit
with the entire Coleman transform. Thus the identity retains coefficient-ring information
without choosing eigenvalues or a splitting field.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A3.
-/

public section

open Filter Topology
open scoped ZeroAtInfty TauCeti.RingOpNorm PowerSeries

namespace ContinuousLinearMap

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {u : C₀(I, R) →L[R] C₀(I, R)} {B : R⟦X⟧}

/-- **Entire spectral mapping for Fredholm series.** Evaluating a zero-constant entire
function at a row-compact operator transforms its Fredholm series by Coleman's entire
transform. This includes empty model spaces and coefficient rings with nilpotents. -/
theorem IsRowCompact.charPowerSeries_eq_colemanDEntire (hu : u.IsRowCompact)
    (hB : B.IsEntire) (hB₀ : PowerSeries.coeff 0 B = 0) :
    (B.evalAt u).matrixCoeff.charPowerSeries =
      PowerSeries.colemanDEntire B u.matrixCoeff.charPowerSeries := by
  let v : ℕ → C₀(I, R) →L[R] C₀(I, R) :=
    fun n ↦ Polynomial.aeval u (PowerSeries.trunc (n + 1) B)
  have htrunc (n : ℕ) : (PowerSeries.trunc (n + 1) B).coeff 0 = 0 := by
    simp [PowerSeries.coeff_trunc, hB₀]
  have hv : Tendsto (fun n ↦ ‖v n - B.evalAt u‖) atTop (𝓝 0) := by
    have hsum := (hB.hasSum_evalAt u).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [v, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Function.comp_apply] using
      tendsto_iff_norm_sub_tendsto_zero.1 hsum
  ext k
  have hcoeff := tendsto_charCoeff_matrixCoeff_of_tendsto
    (Eventually.of_forall fun n ↦ hu.aeval (htrunc n))
    (hu.evalAt (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff] using hB₀)) hv k
  simp only [← Matrix.coeff_charPowerSeries,
    hu.charPowerSeries_matrixCoeff_aeval (htrunc _)] at hcoeff
  exact tendsto_nhds_unique hcoeff
    (PowerSeries.tendsto_coeff_colemanDSeries_trunc hB
      (PowerSeries.isEntire_iff.2 (Matrix.isRestricted_charPowerSeries
        hu.norm_matrixCoeff_le_rowNorm hu.tendsto_rowNorm)) hB₀
      (by simp) k)

end ContinuousLinearMap
