/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Local Sobolev classes under changes of chart

Let `M` be a `C¹` manifold without boundary modelled on `ℂ`. A transition map `φ.symm.trans ψ`
between two charts of the maximal `C¹` atlas of `M` is a `C¹` diffeomorphism between open planar
sets, so composing with it preserves the local Sobolev classes `TauCeti.MemWkpLoc` of order at most
one, by the planar change of variables `TauCeti.MemWkpLoc.comp_contDiffOn_diffeo`.

## Main results

* `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas`: changes of chart preserve the local
  classes of order at most one.
-/

public section

open Set
open scoped Manifold ENNReal

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {k : ℕ}

/-- **Changes of chart preserve the local classes of order at most one.** For charts `φ` and `ψ`
of the maximal `C¹` atlas of `M` and a map `u` in `MemWkpLoc p U k` with `k ≤ 1`, the map
`u ∘ ψ ∘ φ.symm` lies in the local class on the set of points of the source of the chart transition
`φ.symm.trans ψ` that it maps into `U`. -/
theorem MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas (hk : k ≤ 1)
    {φ ψ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M)
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M) {U : Set ℂ} {u : ℂ → F}
    (hu : MemWkpLoc p U k u) :
    MemWkpLoc p ((φ.symm.trans ψ).source ∩ φ.symm.trans ψ ⁻¹' U) k
      (fun y ↦ u (ψ (φ.symm y))) := by
  -- The chart transition has an invertible derivative on its source.
  have hdet : ∀ y ∈ (φ.symm.trans ψ).source ∩ φ.symm.trans ψ ⁻¹' U,
      (fderiv ℝ (φ.symm.trans ψ) y).det ≠ 0 := fun y hy ↦ by
    obtain ⟨L, hL⟩ := exists_hasFDerivAt_symm_trans one_ne_zero hφ hψ hy.1
    rw [hL.fderiv]
    exact L.toLinearEquiv.isUnit_det'.ne_zero
  -- As a function, the chart transition is `ψ ∘ φ.symm` (`OpenPartialHomeomorph.coe_trans`).
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] using
    hu.comp_contDiffOn_diffeo hk (φ.symm.trans ψ).open_source
      (contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ)
      ((φ.symm.trans ψ).injOn.mono inter_subset_left) hdet inter_subset_left fun y hy ↦ hy.2

end TauCeti
