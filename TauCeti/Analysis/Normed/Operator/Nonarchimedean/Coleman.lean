/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Cyclicity
public import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

/-!
# Spectral mapping for Fredholm determinants under polynomials

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
block `A` of `u` on `S`. So its determinant is `det (1 - T B(A))`, which is the finite transform
of `det (1 - T A)` (`Matrix.colemanDBounded_charpolyRev`). The general case follows by letting
`S` grow: `B(π_S ∘ u)` converges to `B(u)` in operator norm, each Fredholm coefficient is
continuous in operator norm on row-compact operators, and each coefficient of Coleman's transform
is continuous for coefficientwise convergence (`Polynomial.continuous_coeff_colemanDSeries`).

## Main results

* `ContinuousLinearMap.submatrix_matrixCoeff_aeval_indicatorCLM_comp`: the block on `S` of
  `Q(π_S ∘ u)` is `Q(A)` for every polynomial `Q`.
* `ContinuousLinearMap.charPowerSeries_matrixCoeff_aeval_indicatorCLM_comp`: for `B(0) = 0`,
  the determinant of `B(π_S ∘ u)` is the polynomial `det (1 - T B(A))`.
* `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_aeval`: spectral mapping
  `det (1 - T B(u)) = D(B, det (1 - T u))`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A3.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap Polynomial
open scoped ZeroAtInfty

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

namespace ContinuousLinearMap

section NormedCommRing

variable [NormedCommRing R]

/-- For a finite set `S` of output coordinates and any polynomial `Q`, the block on `S` of the
matrix of `Q(π_S ∘ u)` is `Q(A)`, where `A` is the block of `u` on `S`: the rows of `π_S ∘ u`
outside `S` vanish, so the products of matrices only involve indices in `S`. -/
theorem submatrix_matrixCoeff_aeval_indicatorCLM_comp (S : Finset I)
    (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    (aeval ((indicatorCLM R (S : Set I)).comp u) Q).matrixCoeff.submatrix (Subtype.val : S → I)
        (Subtype.val : S → I) =
      aeval (u.matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : S → I)) Q := by
  set w := (indicatorCLM R (S : Set I)).comp u
  -- the rows of `w` outside `S` vanish, and its block on `S` is that of `u`
  have hw : ∀ i ∉ S, ∀ j, w.matrixCoeff i j = 0 := fun i hi _ ↦ by simp [w, hi]
  have hblock : w.matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : S → I) =
      u.matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : S → I) := by
    ext i i'
    simp [w]
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, matrixCoeff_add, Matrix.submatrix_add, Pi.add_apply, Pi.add_apply, hp,
      hq]
  | monomial j a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, matrixCoeff_smul,
      Matrix.submatrix_smul, Pi.smul_apply, Pi.smul_apply, submatrix_matrixCoeff_pow hw, hblock]

/-- **Spectral mapping for an output truncation.** If `B(0) = 0`, the Fredholm determinant of
`B(π_S ∘ u)` is the polynomial `det (1 - T B(A))` for the block `A` of `u` on `S`, since the rows
of `B(π_S ∘ u)` outside `S` vanish. -/
theorem charPowerSeries_matrixCoeff_aeval_indicatorCLM_comp (S : Finset I)
    (u : C₀(I, R) →L[R] C₀(I, R)) {B : R[X]} (hB0 : B.coeff 0 = 0) :
    (aeval ((indicatorCLM R (S : Set I)).comp u) B).matrixCoeff.charPowerSeries =
      ((aeval (u.matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : S → I)) B).charpolyRev :
        PowerSeries R) := by
  set w := (indicatorCLM R (S : Set I)).comp u
  obtain ⟨B', rfl⟩ := X_dvd_iff.2 hB0
  -- `B(w) = π_S ∘ (u ∘ B'(w))` is an output truncation
  have hw : aeval w (X * B') = (indicatorCLM R (S : Set I)).comp (u.comp (aeval w B')) := by
    rw [map_mul, aeval_X, mul_def, comp_assoc]
  have hblock :
      (u.comp (aeval w B')).matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : S → I) =
      (aeval w (X * B')).matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : S → I) := by
    ext i i'
    simp [hw]
  rw [← submatrix_matrixCoeff_aeval_indicatorCLM_comp, ← hblock, hw,
    charPowerSeries_matrixCoeff_indicatorCLM_comp]

end NormedCommRing

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

end ContinuousLinearMap
