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

A globally Lipschitz map from the plane into a finite-dimensional space is in the local class
`W^{1,p}` on every set, for every exponent (`LipschitzWith.memWkpLoc_one`). By Rademacher's
theorem its Fréchet derivative is a weak derivative, and that derivative is bounded by the
Lipschitz constant.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open MeasureTheory TopologicalSpace Filter

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set ℂ}

/-- A globally Lipschitz map from the plane into a finite-dimensional space is in the local
class `W^{1,p}` on every set, for every exponent: its Fréchet derivative is a weak derivative
bounded by the Lipschitz constant. -/
theorem _root_.LipschitzWith.memWkpLoc_one [FiniteDimensional ℝ F] {K : NNReal} {u : ℂ → F}
    (hu : LipschitzWith K u) : MemWkpLoc p U 1 u := by
  refine memWkpLoc_succ_iff.2 ⟨hu.continuous.continuousOn.memLpLoc, fderiv ℝ u, ?_,
    memWkpLoc_zero_iff.2 ?_⟩
  · have hΩ : LocallyLipschitzOn ((⊤ : Opens ℂ) : Set ℂ) u :=
      hu.locallyLipschitz.locallyLipschitzOn
    exact (hΩ.hasWeakFDerivOn_fderiv (μ := volume)).mono le_top
  · refine memLpLoc_iff.2 fun L _ hL => ?_
    have : IsFiniteMeasure (volume.restrict L) := ⟨by simpa using hL.measure_lt_top⟩
    exact MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hu)

end TauCeti
