/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables.Higher
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Local Sobolev classes under changes of chart

Let `M` be a `C¹` manifold without boundary modelled on `ℂ`. A transition map `φ.symm.trans ψ`
between two charts of the maximal `C¹` atlas of `M` is a `C¹` diffeomorphism between open planar
sets, so composing with it preserves the local Sobolev classes `TauCeti.MemWkpLoc` of order at most
one, by the planar change of variables `TauCeti.MemWkpLoc.comp_contDiffOn_diffeo`.

On a `Cⁿ` manifold, `n ≠ 0`, a transition map between two charts of the maximal `Cⁿ` atlas is a
`Cⁿ` map with invertible derivative on its open source, so composing with it also preserves the
local classes on open sets of every order `k ≤ n`, for `1 ≤ p < ∞` and maps into a
finite-dimensional space, by the planar change of variables of every order
`TauCeti.MemWkpLoc.comp_contDiffOn`.

## Main results

* `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas`: changes of chart preserve the local
  classes of order at most one.
* `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas_of_le`: changes of chart in the maximal
  `Cⁿ` atlas preserve the local classes on open sets of every order `k ≤ n`, provided `k ≤ 1` or
  `1 ≤ p < ∞`.
-/

public section

open Set TopologicalSpace
open scoped Manifold ENNReal

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {k : ℕ} {n : WithTop ℕ∞}

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

/-- **Changes of chart preserve the local classes of every order.** Let `n ≠ 0` and `k ≤ n`, and
let either `k ≤ 1` or `1 ≤ p < ∞`. For charts `φ` and `ψ` of the maximal `Cⁿ` atlas of `M` and a
map `u` into a finite-dimensional space in `MemWkpLoc p U k` on an open set `U`, the map
`u ∘ ψ ∘ φ.symm` lies in the local class on the set of points of the source of the chart transition
`φ.symm.trans ψ` that it maps into `U`. Orders `k ≤ 1` reduce to
`TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas`, which needs neither the openness of `U`
nor the finite dimension. -/
theorem MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas_of_le [FiniteDimensional ℝ F]
    {φ ψ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) n M)
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) n M) {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F}
    (hu : MemWkpLoc p U k u) (hkp : k ≤ 1 ∨ 1 ≤ p ∧ p ≠ ⊤) (hn : n ≠ 0)
    (hkn : (k : WithTop ℕ∞) ≤ n) :
    MemWkpLoc p ((φ.symm.trans ψ).source ∩ φ.symm.trans ψ ⁻¹' U) k
      (fun y ↦ u (ψ (φ.symm y))) := by
  rcases le_or_gt k 1 with hk | hk
  · have h₁ := IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ, ℂ)) (M := M)
      (ENat.one_le_iff_ne_zero_withTop.2 hn)
    exact hu.comp_symm_trans_of_mem_maximalAtlas hk (h₁ hφ) (h₁ hψ)
  obtain ⟨hp₁, hp⟩ := hkp.resolve_left hk.not_ge
  have : Fact (1 ≤ p) := ⟨hp₁⟩
  -- The chart transition has an invertible derivative on its source.
  have hdet : ∀ y ∈ (φ.symm.trans ψ).source ∩ φ.symm.trans ψ ⁻¹' U,
      (fderiv ℝ (φ.symm.trans ψ) y).det ≠ 0 := fun y hy ↦ by
    obtain ⟨L, hL⟩ := exists_hasFDerivAt_symm_trans hn hφ hψ hy.1
    rw [hL.fderiv]
    exact L.toLinearEquiv.isUnit_det'.ne_zero
  -- As a function, the chart transition is `ψ ∘ φ.symm` (`OpenPartialHomeomorph.coe_trans`).
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, Opens.coe_mk] using
    hu.comp_contDiffOn (U := ⟨_, (φ.symm.trans ψ).isOpen_inter_preimage hU⟩) (V := ⟨U, hU⟩) hp
      hk.le
      (((contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ).of_le hkn).mono inter_subset_left)
      hdet fun y hy ↦ hy.2

end TauCeti
