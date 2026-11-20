/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables.Higher
import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.CoordChange

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

Weak derivatives transform under changes of chart by the chain rule. On the source side, a
transition map between charts of the maximal `C¹` atlas of a manifold modelled on a
finite-dimensional inner product space is a `C¹` diffeomorphism, so the chain rule
`TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo` applies. On the target side, the change of
extended charts of a boundaryless manifold is `C¹`, so the chain rule
`TauCeti.HasWeakFDerivOn.contDiffOn_comp` applies to a continuous coordinate expression, and the
derivative of the change of chart is the tangent coordinate change.

## Main results

* `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas`: changes of chart preserve the local
  classes of order at most one.
* `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas_of_le`: changes of chart in the maximal
  `Cⁿ` atlas preserve the local classes on open sets of every order `k ≤ n`, provided `k ≤ 1` or
  `1 ≤ p < ∞`.
* `TauCeti.HasWeakFDerivOn.comp_symm_trans_of_mem_maximalAtlas`: a weak derivative read through a
  change of chart of the source.
* `TauCeti.HasWeakFDerivOn.extCoordChange_comp`: a weak derivative of a coordinate expression in an
  extended chart, followed by the tangent coordinate change, is a weak derivative of the coordinate
  expression in another extended chart.
-/

public section

open Set TopologicalSpace MeasureTheory
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
  -- As a function, the chart transition is `ψ ∘ φ.symm` (`OpenPartialHomeomorph.coe_trans`).
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] using
    hu.comp_contDiffOn_diffeo hk (φ.symm.trans ψ).open_source
      (contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ)
      ((φ.symm.trans ψ).injOn.mono inter_subset_left)
      (fun y hy ↦ det_fderiv_symm_trans_ne_zero one_ne_zero hφ hψ hy.1) inter_subset_left
      fun y hy ↦ hy.2

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
  -- As a function, the chart transition is `ψ ∘ φ.symm` (`OpenPartialHomeomorph.coe_trans`).
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, Opens.coe_mk] using
    hu.comp_contDiffOn (U := ⟨_, (φ.symm.trans ψ).isOpen_inter_preimage hU⟩) (V := ⟨U, hU⟩) hp
      hk.le
      (((contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ).of_le hkn).mono inter_subset_left)
      (fun y hy ↦ det_fderiv_symm_trans_ne_zero hn hφ hψ hy.1) fun y hy ↦ hy.2

section WeakDerivSource

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω U : Opens E}

/-- **Weak derivatives under changes of chart of the source.** For charts `φ` and `ψ` of the
maximal `C¹` atlas of a manifold modelled on a finite-dimensional inner product space `E` and a weak
derivative `D` of `g` on `Ω`, the map `g ∘ ψ ∘ φ.symm` has the weak derivative
`y ↦ D (ψ (φ.symm y)) ∘ d(ψ ∘ φ.symm)_y` on every open set `U` in the source of the chart
transition `φ.symm.trans ψ` that `ψ ∘ φ.symm` maps into `Ω`. -/
theorem HasWeakFDerivOn.comp_symm_trans_of_mem_maximalAtlas
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] {φ ψ : OpenPartialHomeomorph N E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 N) (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 N)
    {g : E → F} {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω g D)
    (hU : (U : Set E) ⊆ (φ.symm.trans ψ).source) (hmaps : MapsTo (ψ ∘ φ.symm) U Ω) :
    HasWeakFDerivOn μ U (g ∘ ψ ∘ φ.symm) fun y ↦
      D (ψ (φ.symm y)) ∘L fderiv ℝ (ψ ∘ φ.symm) y := by
  -- As a function, the chart transition is `ψ ∘ φ.symm` (`OpenPartialHomeomorph.coe_trans`).
  have h := hD.comp_contDiffOn_diffeo ((contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ).mono hU)
    ((φ.symm.trans ψ).injOn.mono hU)
    (fun y hy ↦ det_fderiv_symm_trans_ne_zero one_ne_zero hφ hψ (hU hy))
    (by rwa [OpenPartialHomeomorph.coe_trans])
  rwa [OpenPartialHomeomorph.coe_trans] at h

end WeakDerivSource

section WeakDerivTarget

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]

/-- **Weak derivatives under changes of extended chart of the target.** Let `v : E → N` take values
in the sources of the charts at `b` and `y` on `Ω`, with `extChartAt I b ∘ v` continuous there. If
`D` is a weak derivative of `extChartAt I b ∘ v` on `Ω`, then `D` followed by the tangent
coordinate change from `b` to `y` is a weak derivative of `extChartAt I y ∘ v` on `Ω`. -/
theorem HasWeakFDerivOn.extCoordChange_comp {b y : N} {v : E → N} {D : E → E →L[ℝ] G}
    (hD : HasWeakFDerivOn μ Ω (extChartAt I b ∘ v) D) (hv : ContinuousOn (extChartAt I b ∘ v) Ω)
    (hvΩ : ∀ z ∈ Ω, v z ∈ (chartAt H b).source ∩ (chartAt H y).source) :
    HasWeakFDerivOn μ Ω (extChartAt I y ∘ v) fun z ↦ tangentCoordChange I b y (v z) ∘L D z := by
  have hb : ∀ z ∈ Ω, v z ∈ (extChartAt I b).source := fun z hz ↦ by
    simpa using (hvΩ z hz).1
  have hO : IsOpen ((extChartAt I b).symm ≫ extChartAt I y).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact (continuousOn_extChartAt_symm b).isOpen_inter_preimage (isOpen_extChartAt_target b)
      (isOpen_extChartAt_source y)
  have h := hD.contDiffOn_comp hv hO (contDiffOn_ext_coord_change y b) fun z hz ↦ by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine ⟨(extChartAt I b).map_source (hb z hz), ?_⟩
    rw [mem_preimage, Function.comp_apply, (extChartAt I b).left_inv (hb z hz), extChartAt_source]
    exact (hvΩ z hz).2
  refine (h.congr_ae ?_).congr_ae_deriv ?_ <;>
    refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun z hz ↦ ?_ <;>
    beta_reduce
  · simp only [Function.comp_apply, (extChartAt I b).left_inv (hb z hz)]
  · rw [Manifold.tangentCoordChange_eq_fderiv, Function.comp_apply]

end WeakDerivTarget

end TauCeti
