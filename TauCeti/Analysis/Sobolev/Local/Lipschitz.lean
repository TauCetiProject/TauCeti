/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# Locally Lipschitz maps are in every local `W^{1,p}` class

A map between finite-dimensional real normed spaces that is locally Lipschitz on an open set `Ω`
lies in `TauCeti.MemWkpLoc p Ω 1` for every exponent `p`, including `p = ∞`
(`LocallyLipschitzOn.memWkpLoc_one`). By Rademacher's theorem its Fréchet derivative `fderiv ℝ u`
is its weak derivative on `Ω`, and on each compact subset of `Ω` it is bounded by a local
Lipschitz constant on a compact thickening. As an immediate consequence, a globally Lipschitz map
lies in `MemWkpLoc p U 1` on every subset `U` (`LipschitzWith.memWkpLoc_one`).

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.8.2, Theorem 4.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open MeasureTheory Metric Set TopologicalSpace Filter

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {p : ENNReal} {Ω : Opens E} {U : Set E}

/-- A map between finite-dimensional real normed spaces that is locally Lipschitz on an open set `Ω`
lies in `MemWkpLoc p Ω 1` for every exponent `p` (including `p = ∞`), with weak derivative
`fderiv ℝ u` locally bounded on compact subsets of `Ω`. -/
theorem _root_.LocallyLipschitzOn.memWkpLoc_one {u : E → F}
    (hu : LocallyLipschitzOn Ω u) : MemWkpLoc p Ω 1 u := by
  refine memWkpLoc_one_iff_of_isOpen.2 ⟨hu.continuousOn.memLpLoc, fderiv ℝ u,
    hu.hasWeakFDerivOn_fderiv, memLpLoc_iff.2 fun L hLΩ hL => ?_⟩
  obtain ⟨δ, hδ, hδΩ⟩ := hL.exists_cthickening_subset_open Ω.isOpen hLΩ
  obtain ⟨C, hC⟩ := (hu.mono hδΩ).exists_lipschitzOnWith_of_compact hL.cthickening
  have : IsFiniteMeasure (volume.restrict L) := ⟨by simpa using hL.measure_lt_top⟩
  refine MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hL.isClosed.measurableSet] with x hx
  exact norm_fderiv_le_of_lipschitzOn ℝ (mem_of_superset
    (isOpen_thickening.mem_nhds (self_subset_thickening hδ L hx))
    (thickening_subset_cthickening δ L)) hC

/-- A globally Lipschitz map between finite-dimensional real normed spaces lies in `MemWkpLoc p U 1`
on every set `U` and for every exponent `p`. -/
theorem _root_.LipschitzWith.memWkpLoc_one {K : NNReal} {u : E → F}
    (hu : LipschitzWith K u) : MemWkpLoc p U 1 u :=
  ((hu.locallyLipschitz.locallyLipschitzOn : LocallyLipschitzOn (⊤ : Opens E) u).memWkpLoc_one
    (p := p)).mono (subset_univ U)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- On any finite-dimensional real normed space (not necessarily carrying an inner product),
`x ↦ ‖x‖` belongs to `MemWkpLoc p U 1` for every exponent `p` and subset `U`. -/
theorem memWkpLoc_one_norm : MemWkpLoc p U 1 (fun x : E => ‖x‖) :=
  lipschitzWith_one_norm.memWkpLoc_one

end TauCeti
