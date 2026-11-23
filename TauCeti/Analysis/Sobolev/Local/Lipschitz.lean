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
# Lipschitz maps and maps with Lipschitz derivative in local Sobolev classes

A map from the plane into a finite-dimensional space which is locally Lipschitz on an open set is
in the local class `W^{1,p}` there, for every exponent (`LocallyLipschitzOn.memWkpLoc_one`). By
Rademacher's theorem its Fréchet derivative is a weak derivative, and that derivative is bounded
near each point by a local Lipschitz constant. A globally Lipschitz map is therefore in `W^{1,p}`
on every set (`LipschitzWith.memWkpLoc_one`), and a differentiable map whose derivative is
locally Lipschitz is in `W^{2,p}` (`DifferentiableOn.memWkpLoc_two_of_locallyLipschitzOn_fderiv`):
it is `C^{1,1}`, hence `W^{2,∞}`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open MeasureTheory TopologicalSpace Filter Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set ℂ}

/-- A map from the plane into a finite-dimensional space which is locally Lipschitz on an open
set `Ω` is in the local class `W^{1,p}` on `Ω`, for every exponent: its Fréchet derivative is a
weak derivative, bounded near each point of `Ω` by a local Lipschitz constant. -/
theorem _root_.LocallyLipschitzOn.memWkpLoc_one [FiniteDimensional ℝ F] {Ω : Opens ℂ}
    {u : ℂ → F} (hu : LocallyLipschitzOn Ω u) : MemWkpLoc p Ω 1 u := by
  refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hu.continuousOn.memLpLoc, fderiv ℝ u,
    hu.hasWeakFDerivOn_fderiv, memWkpLoc_zero_iff.2 <|
      memLpLoc_of_forall_eventually_norm_le (measurable_fderiv ℝ u).aestronglyMeasurable
        fun z hz => ?_⟩
  obtain ⟨K, t, ht, hK⟩ := hu hz
  rw [nhdsWithin_eq_nhds.2 (Ω.isOpen.mem_nhds hz)] at ht
  exact ⟨K, (eventually_mem_nhds_iff.2 ht).mono fun _ hw => norm_fderiv_le_of_lipschitzOn ℝ hw hK⟩

/-- A globally Lipschitz map from the plane into a finite-dimensional space is in the local
class `W^{1,p}` on every set, for every exponent: its Fréchet derivative is a weak derivative
bounded by the Lipschitz constant. -/
theorem _root_.LipschitzWith.memWkpLoc_one [FiniteDimensional ℝ F] {K : NNReal} {u : ℂ → F}
    (hu : LipschitzWith K u) : MemWkpLoc p U 1 u :=
  (hu.locallyLipschitz.locallyLipschitzOn.memWkpLoc_one (Ω := ⊤)).mono <| by
    rw [Opens.coe_top]
    exact subset_univ U

/-- A map from the plane into a finite-dimensional space which is differentiable on an open set
`Ω`, with derivative locally Lipschitz on `Ω`, is in the local class `W^{2,p}` on `Ω`, for every
exponent: its first weak derivative is its classical derivative, and its second weak derivative is
the almost-everywhere derivative of that derivative. -/
theorem _root_.DifferentiableOn.memWkpLoc_two_of_locallyLipschitzOn_fderiv [FiniteDimensional ℝ F]
    {Ω : Opens ℂ} {u : ℂ → F} (hu : DifferentiableOn ℝ u Ω)
    (hDu : LocallyLipschitzOn Ω (fderiv ℝ u)) : MemWkpLoc p Ω 2 u := by
  have hC1 : ContDiffOn ℝ 1 u Ω := (contDiffOn_succ_iff_fderiv_of_isOpen Ω.isOpen).2
    ⟨hu, by simp, contDiffOn_zero.2 hDu.continuousOn⟩
  exact memWkpLoc_succ_iff_of_isOpen.2
    ⟨hu.continuousOn.memLpLoc, fderiv ℝ u, hC1.hasWeakFDerivOn_fderiv, hDu.memWkpLoc_one⟩

end TauCeti
