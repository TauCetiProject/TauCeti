/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.FiniteCompression
public import TauCeti.Analysis.Normed.Operator.RowCompact.Sequence

/-!
# Continuity of Fredholm series in operator norm

A norm-convergent family of operators on `C₀(I, R)` whose entries share a null row majorant
has determinants converging in every positive-radius Gauss norm; in particular so does a
norm-convergent sequence of row-compact operators. This continuity permits finite determinant
identities to pass to limits of row-compact operators. The finite identities apply to output
truncations `π_S ∘ u` to a finite set `S` of coordinates, whose determinant is the polynomial
determinant of the finite block of `u` on `S`
(`ContinuousLinearMap.charPowerSeries_matrixCoeff_indicatorCLM_comp`).

The determinant is `u.matrixCoeff.charPowerSeries`.
Scalars may be complete ultrametric norm-one Tate rings, not just fields.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

namespace ContinuousLinearMap

open ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R]

/-- The determinant of the output truncation `π_S ∘ u` to a finite set `S` is the polynomial
`det (1 - X A)` for the finite block `A` of the matrix of `u` on `S`, since the rows of
`π_S ∘ u` outside `S` vanish. -/
theorem charPowerSeries_matrixCoeff_indicatorCLM_comp (S : Finset I)
    (u : C₀(I, R) →L[R] C₀(I, R)) :
    ((indicatorCLM R (S : Set I)).comp u).matrixCoeff.charPowerSeries =
      ((u.matrixCoeff.submatrix (Subtype.val : S → I) Subtype.val).charpolyRev :
        PowerSeries R) := by
  have hmatrix : ((indicatorCLM R (S : Set I)).comp u).matrixCoeff =
      Matrix.of fun i k ↦ if i ∈ S then u.matrixCoeff i k else 0 := by
    ext i k
    simp [Set.indicator_apply]
  rw [hmatrix, TauCeti.charPowerSeries_outputTruncation]

end ContinuousLinearMap

namespace TauCeti

open Filter Finset Topology ContinuousLinearMap
open scoped ZeroAtInfty RingOpNorm

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [NormedRing.IsTate R]
  {u : C₀(I, R) →L[R] C₀(I, R)} {v : ℕ → C₀(I, R) →L[R] C₀(I, R)}

/-- If operators `w a` on `C₀(I, R)` converge in operator norm to `w₀`, and all their entries
are bounded by a common null row majorant `r`, then their Fredholm series converge in Gauss norm
at every positive radius. -/
theorem tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_tendsto_ringOpNorm_of_le
    [CompleteSpace R] [NormOneClass R] {α : Type*} {l : Filter α}
    {w : α → C₀(I, R) →L[R] C₀(I, R)} {w₀ : C₀(I, R) →L[R] C₀(I, R)} {r : I → ℝ}
    (hr : Tendsto r cofinite (𝓝 0)) (hw : ∀ a i j, ‖(w a).matrixCoeff i j‖ ≤ r i)
    (hw₀ : ∀ i j, ‖w₀.matrixCoeff i j‖ ≤ r i) (h : Tendsto (fun a ↦ ‖w a - w₀‖) l (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun a ↦ ((w a).matrixCoeff.charPowerSeries -
      w₀.matrixCoeff.charPowerSeries).gaussNorm norm ρ) l (𝓝 0) :=
  tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_tendstoUniformly hw hw₀ hr
    (tendstoUniformly_matrixCoeff_of_tendsto h) hρ

/-- The Fredholm series of a norm-convergent sequence of row-compact operators converge in
Gauss norm at every positive radius. Unlike coefficientwise convergence of arbitrary entire
series, operator-norm convergence supplies uniform control of the determinant tails. -/
theorem tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_tendsto_ringOpNorm
    [CompleteSpace R] [NormOneClass R] (h : Tendsto (fun n ↦ ‖u - v n‖) atTop (𝓝 0))
    (hv : ∀ n, (v n).IsRowCompact) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n ↦ ((v n).matrixCoeff.charPowerSeries -
      u.matrixCoeff.charPowerSeries).gaussNorm norm ρ) atTop (𝓝 0) := by
  obtain ⟨r, _, hr, hu, hv⟩ := exists_common_row_majorant_of_tendsto_ringOpNorm h hv
  exact tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_tendsto_ringOpNorm_of_le
    hr hv hu (by simpa only [← neg_sub u, ringOpNorm_neg] using h) hρ

end TauCeti
