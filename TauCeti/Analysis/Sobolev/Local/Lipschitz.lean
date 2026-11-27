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

A locally Lipschitz map from an open subset of a finite-dimensional real normed space into a
finite-dimensional real normed space belongs to the local class `W^{1,p}` for every exponent
(`LocallyLipschitzOn.memWkpLoc_one`). By Rademacher's theorem its Fréchet derivative is a weak
derivative, and on every compact subset it is bounded by a local Lipschitz constant. The same
conclusions hold on arbitrary subsets for locally Lipschitz (`LocallyLipschitz.memWkpLoc_one`) and
globally Lipschitz (`LipschitzWith.memWkpLoc_one`) maps; in particular the norm `x ↦ ‖x‖` lies in
`W^{1,p}` everywhere (`TauCeti.memWkpLoc_one_norm`). Moreover, a differentiable map whose
derivative is locally Lipschitz lies in `W^{2,p}`
(`DifferentiableOn.memWkpLoc_two_of_locallyLipschitzOn_fderiv`): it is `C^{1,1}`, hence `W^{2,∞}`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §4.2.3, Theorem 4.5.
-/

public section

open MeasureTheory TopologicalSpace Filter Set
open scoped Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal}

/-- A locally Lipschitz map on an open subset of a finite-dimensional real normed space into a
finite-dimensional space lies in `W^{1,p}_loc` for every exponent `p`: its Fréchet derivative is
a weak derivative and is bounded on every compact subset by a local Lipschitz constant. -/
theorem _root_.LocallyLipschitzOn.memWkpLoc_one [FiniteDimensional ℝ F] {Ω : Opens E}
    {u : E → F} (hu : LocallyLipschitzOn (Ω : Set E) u) : MemWkpLoc p Ω 1 u := by
  refine hu.continuousOn.memWkpLoc_one_iff.2 ⟨fderiv ℝ u, hu.hasWeakFDerivOn_fderiv,
    memLpLoc_of_forall_eventually_norm_le (measurable_fderiv ℝ u).aestronglyMeasurable
      fun z hz => ?_⟩
  obtain ⟨C, s, hs, hC⟩ := hu hz
  rw [Ω.isOpen.nhdsWithin_eq hz] at hs
  obtain ⟨t, hts, hto, hzt⟩ := mem_nhds_iff.1 hs
  refine ⟨C, Eventually.mono (hto.mem_nhds hzt) fun w hw => ?_⟩
  exact norm_fderiv_le_of_lipschitzOn ℝ (hto.mem_nhds hw) (hC.mono hts)

/-- A locally Lipschitz map from a finite-dimensional real normed space into a finite-dimensional
space lies in `W^{1,p}_loc` on every subset, for every exponent `p`. -/
theorem _root_.LocallyLipschitz.memWkpLoc_one [FiniteDimensional ℝ F] {U : Set E} {u : E → F}
    (hu : LocallyLipschitz u) : MemWkpLoc p U 1 u :=
  (hu.locallyLipschitzOn (s := (⊤ : Opens E))).memWkpLoc_one.mono
    ((Set.subset_univ U).trans_eq Opens.coe_top.symm)

/-- A globally Lipschitz map from a finite-dimensional real normed space into a finite-dimensional
space is in the local class `W^{1,p}` on every set, for every exponent: its Fréchet derivative is
a weak derivative bounded by the Lipschitz constant. -/
theorem _root_.LipschitzWith.memWkpLoc_one [FiniteDimensional ℝ F] {U : Set E} {K : NNReal}
    {u : E → F} (hu : LipschitzWith K u) : MemWkpLoc p U 1 u :=
  hu.locallyLipschitz.memWkpLoc_one

/-- The norm `x ↦ ‖x‖` lies in the local class `W^{1,p}` on every set of any
finite-dimensional real normed space, for every exponent: it is `1`-Lipschitz and requires no
inner product. -/
theorem memWkpLoc_one_norm {U : Set E} :
    MemWkpLoc p U 1 (fun x : E => ‖x‖) :=
  lipschitzWith_one_norm.memWkpLoc_one

/-- A map from a finite-dimensional real normed space into a finite-dimensional space which is
differentiable on an open set `Ω`, with derivative locally Lipschitz on `Ω`, is in the local class
`W^{2,p}` on `Ω`, for every exponent: its first weak derivative is its classical derivative, and
its second weak derivative is the almost-everywhere derivative of that derivative. -/
theorem _root_.DifferentiableOn.memWkpLoc_two_of_locallyLipschitzOn_fderiv [FiniteDimensional ℝ F]
    {Ω : Opens E} {u : E → F} (hu : DifferentiableOn ℝ u Ω)
    (hDu : LocallyLipschitzOn (Ω : Set E) (fderiv ℝ u)) : MemWkpLoc p Ω 2 u := by
  have hC1 : ContDiffOn ℝ 1 u Ω := (contDiffOn_succ_iff_fderiv_of_isOpen Ω.isOpen).2
    ⟨hu, by simp, contDiffOn_zero.2 hDu.continuousOn⟩
  exact memWkpLoc_succ_iff_of_isOpen.2
    ⟨hu.continuousOn.memLpLoc, fderiv ℝ u, hC1.hasWeakFDerivOn_fderiv, hDu.memWkpLoc_one⟩

end TauCeti
