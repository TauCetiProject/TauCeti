/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# Lipschitz maps are in every local `W^{1,p}` class

A globally Lipschitz map from a finite-dimensional real normed space `E` into a finite-dimensional
real normed space `F` is in the local class `W^{1,p}` on every set, for every exponent and every
additive Haar measure (`LipschitzWith.memWkpLoc_one`). More generally, a map locally Lipschitz on
an open set `Ω` lies in `W^{1,p}_loc(Ω; F)` for every exponent (`LocallyLipschitzOn.memWkpLoc_one`).
By Rademacher's theorem its Fréchet derivative is a weak derivative, and that derivative is bounded
by the local Lipschitz constant on compact subsets.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.2.3, Theorem 4.5.
-/

public section

open MeasureTheory TopologicalSpace Filter Metric
open scoped ENNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E}

/-- A globally Lipschitz map from a finite-dimensional real normed space into a finite-dimensional
real normed space is in the local class `W^{1,p}` on every set, for every exponent: its Fréchet
derivative is a weak derivative bounded by the Lipschitz constant. -/
theorem _root_.LipschitzWith.memWkpLoc_one [FiniteDimensional ℝ F] {K : NNReal} {u : E → F}
    (hu : LipschitzWith K u) : MemWkpLoc p U 1 u μ := by
  refine memWkpLoc_succ_iff.2 ⟨hu.continuous.continuousOn.memLpLoc, fderiv ℝ u, ?_,
    memWkpLoc_zero_iff.2 ?_⟩
  · have hΩ : LocallyLipschitzOn ((⊤ : Opens E) : Set E) u :=
      hu.locallyLipschitz.locallyLipschitzOn
    exact (hΩ.hasWeakFDerivOn_fderiv (μ := μ)).mono le_top
  · refine memLpLoc_iff.2 fun L _ hL => ?_
    have : IsFiniteMeasure (μ.restrict L) := ⟨by simpa using hL.measure_lt_top⟩
    exact MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hu)

/-- A map locally Lipschitz on an open set `Ω` of a finite-dimensional real normed space, with
values in a finite-dimensional real normed space, lies in `W^{1,p}_loc(Ω; F)` for every exponent:
its Fréchet derivative is a weak derivative and is bounded on every compact subset of `Ω`. -/
theorem _root_.LocallyLipschitzOn.memWkpLoc_one [FiniteDimensional ℝ F] {Ω : Opens E}
    {u : E → F} (hu : LocallyLipschitzOn (Ω : Set E) u) : MemWkpLoc p Ω 1 u μ := by
  refine hu.continuousOn.memWkpLoc_one_iff_of_isOpen.2
    ⟨fderiv ℝ u, hu.hasWeakFDerivOn_fderiv (μ := μ), memLpLoc_iff.2 fun L hLΩ hL => ?_⟩
  obtain ⟨δ, hδ, hδΩ⟩ := hL.exists_cthickening_subset_open Ω.isOpen hLΩ
  obtain ⟨C, hC⟩ := (hu.mono hδΩ).exists_lipschitzOnWith_of_compact hL.cthickening
  have : IsFiniteMeasure (μ.restrict L) := ⟨by simpa using hL.measure_lt_top⟩
  refine MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable C
    ((ae_restrict_iff' hL.measurableSet).2 (Eventually.of_forall fun x hx => ?_))
  have hmem : cthickening δ L ∈ nhds x :=
    Filter.mem_of_superset (isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx))
      (thickening_subset_cthickening _ _)
  exact norm_fderiv_le_of_lipschitzOn ℝ hmem hC

end TauCeti
