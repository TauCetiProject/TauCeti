/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables.Higher
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Local Sobolev classes of every order under changes of chart

Let `M` be a `Cⁿ` manifold without boundary modelled on `ℂ`. A transition map `φ.symm.trans ψ`
between two charts of the maximal `Cⁿ` atlas of `M` is a `Cⁿ` map with invertible derivative on its
open source, so composing with it preserves the local Sobolev classes `TauCeti.MemWkpLoc` of every
order `1 ≤ k ≤ n`, for `1 ≤ p < ∞` and maps into a finite-dimensional space, by the planar change
of variables of every order `TauCeti.MemWkpLoc.comp_contDiffOn`. Orders `k ≤ 1` on the maximal
`C¹` atlas are `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas`.

## Main results

* `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas_of_le`: changes of chart in the maximal
  `Cⁿ` atlas preserve the local classes of every order `1 ≤ k ≤ n`.
-/

public section

open Set TopologicalSpace
open scoped Manifold ENNReal

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {p : ℝ≥0∞} {k : ℕ} {n : WithTop ℕ∞}

/-- **Changes of chart preserve the local classes of every order.** Let `1 ≤ p < ∞` and
`1 ≤ k ≤ n`. For charts `φ` and `ψ` of the maximal `Cⁿ` atlas of `M` and a map `u` into a
finite-dimensional space in `MemWkpLoc p U k` on an open set `U`, the map `u ∘ ψ ∘ φ.symm` lies in
the local class on the set of points of the source of the chart transition `φ.symm.trans ψ` that it
maps into `U`. -/
theorem MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas_of_le [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hk : 1 ≤ k) (hkn : (k : WithTop ℕ∞) ≤ n)
    {φ ψ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) n M)
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) n M) {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F}
    (hu : MemWkpLoc p U k u) :
    MemWkpLoc p ((φ.symm.trans ψ).source ∩ φ.symm.trans ψ ⁻¹' U) k
      (fun y ↦ u (ψ (φ.symm y))) := by
  have hn : n ≠ 0 := (lt_of_lt_of_le (by exact_mod_cast hk) hkn).ne'
  -- The chart transition has an invertible derivative on its source.
  have hdet : ∀ y ∈ (φ.symm.trans ψ).source ∩ φ.symm.trans ψ ⁻¹' U,
      (fderiv ℝ (φ.symm.trans ψ) y).det ≠ 0 := fun y hy ↦ by
    obtain ⟨L, hL⟩ := exists_hasFDerivAt_symm_trans hn hφ hψ hy.1
    rw [hL.fderiv]
    exact L.toLinearEquiv.isUnit_det'.ne_zero
  -- As a function, the chart transition is `ψ ∘ φ.symm` (`OpenPartialHomeomorph.coe_trans`).
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, Opens.coe_mk] using
    hu.comp_contDiffOn (U := ⟨_, (φ.symm.trans ψ).isOpen_inter_preimage hU⟩) (V := ⟨U, hU⟩) hp hk
      (((contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ).of_le hkn).mono inter_subset_left)
      hdet fun y hy ↦ hy.2

end TauCeti
