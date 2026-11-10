/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Cyclicity
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Entire
public import TauCeti.Analysis.Polynomial.Coleman.Entire
public import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Resolvent
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

/-!
# Spectral mapping for Fredholm determinants under polynomials and entire functions

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1` and Tate scalars, and
let `u` be a row-compact endomorphism of the model space `C₀(I, R)`. For a polynomial `B` with
`B(0) = 0`, the operator `B(u)` is row compact, and its Fredholm determinant is obtained from that
of `u` by Coleman's transform:

`det (1 - T B(u)) = D(B, det (1 - T u))`
(`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_aeval`).

The right side `Polynomial.colemanDSeries B F` depends only on the power series `F`, not on `u`
or its eigenvalues, so the Fredholm determinant of `B(u)` is determined by that of `u`. Over a
field, if `det (1 - T u) = ∏ (1 - αᵢ T)` the identity reads `det (1 - T B(u)) = ∏ (1 - B(αᵢ) T)`:
the nonzero eigenvalues `αᵢ` of `u` are replaced by the `B(αᵢ)`. The hypothesis `B(0) = 0` is
needed: on an infinite model space `B(u)` is row compact only if `B(0) = 0`
(`ContinuousLinearMap.IsRowCompact.isRowCompact_evalAt_iff_constantCoeff_eq_zero`).

The proof first treats an output truncation `π_S ∘ u` to a finite set `S` of coordinates. Since
`B(0) = 0`, the rows of `B(π_S ∘ u)` outside `S` vanish, and its block on `S` is `B(A)` for the
block `A` of `u` on `S` (`ContinuousLinearMap.submatrix_matrixCoeff_aeval_indicatorCLM_comp`).
So its determinant is `det (1 - T B(A))`
(`ContinuousLinearMap.charPowerSeries_matrixCoeff_aeval_indicatorCLM_comp`), which is the finite
transform of `det (1 - T A)` (`Matrix.colemanDBounded_charpolyRev`). The general case follows by
letting `S` grow: `B(π_S ∘ u)` converges to `B(u)` in operator norm, each Fredholm coefficient is
continuous in operator norm on row-compact operators, and each coefficient of Coleman's transform
is continuous for coefficientwise convergence (`Polynomial.continuous_coeff_colemanDSeries`).

The same identity holds for an entire series `B` with `B(0) = 0`, with `B(u) = Σ bₘ uᵐ` the
norm-convergent evaluation `PowerSeries.evalAt` in the operator algebra and the entire transform
`PowerSeries.colemanDEntire` on the right
(`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_evalAt`). Here the polynomials are
the truncations of `B`: their values at `u` converge to `B(u)` in operator norm
(`PowerSeries.IsEntire.tendsto_aeval_trunc`), and their polynomial-input transforms converge
coefficientwise to the entire transform (`PowerSeries.tendsto_coeff_colemanDSeries_trunc`).

## Main results

* `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_aeval`: spectral mapping
  `det (1 - T B(u)) = D(B, det (1 - T u))` for a polynomial `B`.
* `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_evalAt`: spectral mapping for an
  entire series `B`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A3.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap Polynomial
open scoped ZeroAtInfty PowerSeries

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

variable [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {u : C₀(I, R) →L[R] C₀(I, R)}

open scoped PowerSeries.WithPiTopology in
/-- **Spectral mapping for Fredholm determinants.** If `u` is a row-compact endomorphism of a model
space and `B` is a polynomial with `B(0) = 0`, the Fredholm determinant of `B(u)` is Coleman's
transform of that of `u`: `det (1 - T B(u)) = D(B, det (1 - T u))`. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_aeval (hu : u.IsRowCompact) {B : R[X]}
    (hB0 : B.coeff 0 = 0) :
    (Polynomial.aeval u B).matrixCoeff.charPowerSeries =
      B.colemanDSeries u.matrixCoeff.charPowerSeries := by
  set w := fun S : Finset I ↦ (indicatorCLM R (S : Set I)).comp u
  have hw : Tendsto (fun S ↦ ‖w S - u‖) atTop (𝓝 0) := hu.tendsto_ringOpNorm_indicatorCLM_comp_sub
  have hwc (S : Finset I) : (w S).IsRowCompact := isRowCompact_indicatorCLM_comp S u
  -- `B(π_S ∘ u)` converges to `B(u)` in operator norm, by continuity of polynomial evaluation
  have hBw : Tendsto (fun S ↦ ‖Polynomial.aeval (w S) B - Polynomial.aeval u B‖) atTop
      (𝓝 0) := by
    have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
    exact tendsto_iff_norm_sub_tendsto_zero.mp
      (((Polynomial.continuous_aeval B).tendsto u).comp (tendsto_iff_norm_sub_tendsto_zero.mpr hw))
  -- and the determinants of the truncations `π_S ∘ u` converge coefficientwise to that of `u`
  have hH : Tendsto (fun S ↦ (w S).matrixCoeff.charPowerSeries) atTop
      (𝓝 u.matrixCoeff.charPowerSeries) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    simpa only [Matrix.coeff_charPowerSeries] using
      tendsto_charCoeff_matrixCoeff_of_tendsto (.of_forall hwc) hu hw n
  ext k
  refine tendsto_nhds_unique ?_ (((continuous_coeff_colemanDSeries B k).tendsto _).comp hH)
  rw [Matrix.coeff_charPowerSeries]
  refine (tendsto_charCoeff_matrixCoeff_of_tendsto (.of_forall fun S ↦ (hwc S).aeval hB0)
    (hu.aeval hB0) hBw k).congr fun S ↦ ?_
  -- for a truncation, this is the finite matrix spectral mapping
  rw [Function.comp_apply, ← Matrix.coeff_charPowerSeries,
    charPowerSeries_matrixCoeff_aeval_indicatorCLM_comp S u hB0,
    charPowerSeries_matrixCoeff_indicatorCLM_comp,
    colemanDSeries_coe_of_natDegree_le hB0 (Matrix.natDegree_charpolyRev_le _),
    Matrix.colemanDBounded_charpolyRev _ le_rfl]

omit [NormOneClass R] in
/-- **Spectral mapping for Fredholm determinants under entire functions.** If `u` is a row-compact
endomorphism of a model space and `B` is an entire series with `B(0) = 0`, the Fredholm determinant
of `B(u)` is Coleman's entire transform of that of `u`: `det (1 - T B(u)) = D(B, det (1 - T u))`. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_evalAt (hu : u.IsRowCompact) {B : R⟦X⟧}
    (hB : B.IsEntire) (hB0 : PowerSeries.constantCoeff B = 0) :
    (B.evalAt u).matrixCoeff.charPowerSeries =
      B.colemanDEntire u.matrixCoeff.charPowerSeries := by
  have hB0' : PowerSeries.coeff 0 B = 0 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hw0 (m : ℕ) : (PowerSeries.trunc (m + 1) B).coeff 0 = 0 := by
    simp [PowerSeries.coeff_trunc, hB0']
  -- the truncations of `B`, evaluated at `u`, converge to `B(u)` in operator norm
  have hw : Tendsto (fun m ↦ ‖Polynomial.aeval u (PowerSeries.trunc (m + 1) B) - B.evalAt u‖)
      atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp
      ((hB.tendsto_aeval_trunc u).comp (tendsto_add_atTop_nat 1))
  -- so the Fredholm coefficients of these polynomials in `u` converge to those of `B(u)`, and
  -- by polynomial spectral mapping they are the coefficients of the polynomial-input transforms
  ext k
  refine tendsto_nhds_unique ?_ (PowerSeries.tendsto_coeff_colemanDSeries_trunc hB
    hu.isEntire_charPowerSeries hB0' (by simp) k)
  rw [Matrix.coeff_charPowerSeries]
  refine (tendsto_charCoeff_matrixCoeff_of_tendsto (.of_forall fun m ↦ hu.aeval (hw0 m))
    (hu.evalAt hB0) hw k).congr fun m ↦ ?_
  rw [← Matrix.coeff_charPowerSeries, hu.charPowerSeries_matrixCoeff_aeval (hw0 m)]

end ContinuousLinearMap
