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
# Locally Lipschitz maps are in every local `W^{1,p}` class

A map between finite-dimensional real normed spaces that is locally Lipschitz on an open set `Ω`
lies in `TauCeti.MemW1pLoc p Ω` for every exponent `p`, including `∞`
(`LocallyLipschitzOn.memW1pLoc`). By Rademacher's theorem its Fréchet derivative exists almost
everywhere on `Ω` and is a weak derivative (`LocallyLipschitzOn.hasWeakFDerivOn_fderiv`), and on
every compact subset of `Ω` it is bounded by a local Lipschitz constant. Finite dimensionality of
the target is genuinely needed: `t ↦ 1_{[0, t]}` from `ℝ` into `L¹(0, 1)` is `1`-Lipschitz yet has
no Bochner weak derivative.

Globally Lipschitz maps lie in `MemW1pLoc p Ω` on every open set (`LipschitzWith.memW1pLoc`), and on
the plane they lie in `MemWkpLoc p U 1` on every subset `U ⊆ ℂ` (`LipschitzWith.memWkpLoc_one`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* W. P. Ziemer, *Weakly Differentiable Functions*, Theorem 2.2.1.
-/

public section

open MeasureTheory TopologicalSpace Filter

namespace TauCeti

section MemW1pLoc

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {p : ENNReal} {Ω : Opens E}

/-- A locally Lipschitz map on `Ω` between finite-dimensional real normed spaces lies in
`MemW1pLoc p Ω` for every exponent `p`, with weak derivative `fderiv ℝ u`. -/
theorem _root_.LocallyLipschitzOn.memW1pLoc {u : E → F} (hu : LocallyLipschitzOn Ω u) :
    MemW1pLoc p Ω u := by
  refine memW1pLoc_iff.2 ⟨hu.continuousOn.memLpLoc, fderiv ℝ u, hu.hasWeakFDerivOn_fderiv,
    memLpLoc_iff.2 fun K hKΩ hK => ?_⟩
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨C, hC⟩ := (hu.mono hWΩ).exists_lipschitzOnWith_of_compact hWc
  have hCW : LipschitzOnWith C u W := hC.mono subset_closure
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  refine MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact norm_fderiv_le_of_lipschitzOn ℝ (hWo.mem_nhds (hKW hx)) hCW

/-- A globally Lipschitz map between finite-dimensional real normed spaces lies in `MemW1pLoc p Ω`
on every open set and for every exponent `p`. -/
theorem _root_.LipschitzWith.memW1pLoc {K : NNReal} {u : E → F} (hu : LipschitzWith K u) :
    MemW1pLoc p Ω u :=
  hu.locallyLipschitz.locallyLipschitzOn.memW1pLoc

end MemW1pLoc

/-- A globally Lipschitz map from the plane into a finite-dimensional space is in the local
class `W^{1,p}` on every set, for every exponent: its Fréchet derivative is a weak derivative
bounded by the Lipschitz constant. -/
theorem _root_.LipschitzWith.memWkpLoc_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {p : ENNReal} {U : Set ℂ} {K : NNReal} {u : ℂ → F}
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
