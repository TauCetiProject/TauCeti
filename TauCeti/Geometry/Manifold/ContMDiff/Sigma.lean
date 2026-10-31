/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import TauCeti.Geometry.Manifold.Instances.Sigma

/-!
# Smooth maps on disjoint unions of manifolds

The disjoint union `Σ i, M i` of manifolds on a common model is charted by lifting the charts of
each component along the open embedding `Sigma.mk i` (`ChartedSpace.sigma`). Read in these charts,
a map out of the disjoint union is, near a point of the component `M i`, the same as its restriction
to `M i`. Smoothness of maps out of and into a disjoint union is therefore checked componentwise.
This is the indexed form of Mathlib's lemmas for the binary disjoint union `M ⊕ M'`
(`ContMDiff.inl`, `ContMDiff.sumElim`, `ContMDiff.sumMap`).

## Main results

* `contMDiff_sigmaMk`: the inclusion of a component is `C^n`.
* `contMDiffAt_sigma_iff`, `contMDiff_sigma_iff`: a map out of a disjoint union is `C^n` exactly
  when its restriction to each component is.
* `ContMDiff.sigmaMap`: a family of `C^n` maps between components induces a `C^n` map of
  disjoint unions.
-/

public section

open Set Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'}
  {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}

namespace TauCeti

/-- The extended chart of a disjoint union at `⟨i, x⟩` agrees on the copy of `M i` with the
extended chart of `M i` at `x`. -/
@[mfld_simps]
theorem extChartAt_sigmaMk_apply {i : ι} {x y : M i} :
    extChartAt I (⟨i, x⟩ : Σ i, M i) ⟨i, y⟩ = extChartAt I x y := by
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    ChartedSpace.sigma_chartAt_mk_apply]

/-- The inverse of the extended chart of a disjoint union at `⟨i, x⟩` is the inverse of the
extended chart of `M i` at `x`, followed by the inclusion of `M i`. -/
theorem extChartAt_sigmaMk_symm {i : ι} {x : M i} :
    ⇑(extChartAt I (⟨i, x⟩ : Σ i, M i)).symm = Sigma.mk i ∘ (extChartAt I x).symm := by
  have : Nonempty H := nonempty_of_chartedSpace x
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, ChartedSpace.sigma_chartAt,
    OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_assoc]

/-- **Restriction to a component.** A map out of a disjoint union is `C^n` at a point of the
component `M i` exactly when its restriction to `M i` is `C^n` there. -/
theorem contMDiffAt_sigma_iff {f : (Σ i, M i) → N} {i : ι} {x : M i} :
    ContMDiffAt I J n f ⟨i, x⟩ ↔ ContMDiffAt I J n (f ∘ Sigma.mk i) x := by
  rw [contMDiffAt_iff, contMDiffAt_iff, IsOpenEmbedding.sigmaMk.continuousAt_iff,
    extChartAt_sigmaMk_symm, extChartAt_sigmaMk_apply]
  rfl

/-- A map out of a disjoint union is `C^n` exactly when its restriction to each component is. -/
theorem contMDiff_sigma_iff {f : (Σ i, M i) → N} :
    ContMDiff I J n f ↔ ∀ i, ContMDiff I J n (f ∘ Sigma.mk i) :=
  ⟨fun h i x ↦ contMDiffAt_sigma_iff.mp (h ⟨i, x⟩),
    fun h ⟨i, x⟩ ↦ contMDiffAt_sigma_iff.mpr (h i x)⟩

/-- The inclusion of a component into a disjoint union is `C^n`: read in charts it is the
identity. -/
theorem contMDiff_sigmaMk (i : ι) : ContMDiff I I n (Sigma.mk i : M i → Σ i, M i) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_sigmaMk.continuousAt, contDiffWithinAt_id.congr_of_eventuallyEq ?_ ?_⟩
  · have : I.symm ⁻¹' (chartAt H x).target ∩ range I ∈ 𝓝[range I] (extChartAt I x x) := by
      rw [← I.image_eq (chartAt H x).target]
      exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source _ x)
    filter_upwards [this] with y hy
    simp only [Function.comp_apply, extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, id]
    rw [ChartedSpace.sigma_chartAt_mk_apply, (chartAt H x).right_inv hy.1, I.right_inv hy.2]
  · simp

end TauCeti

/-- **Maps of disjoint unions.** A family of `C^n` maps `g i : M i → M' (f i)` induces a `C^n` map
`Sigma.map f g` of disjoint unions. -/
theorem ContMDiff.sigmaMap {ι' : Type*} {M' : ι' → Type*} [∀ i, TopologicalSpace (M' i)]
    [∀ i, ChartedSpace H' (M' i)] {f : ι → ι'} {g : ∀ i, M i → M' (f i)}
    (hg : ∀ i, ContMDiff I J n (g i)) : ContMDiff I J n (Sigma.map f g) :=
  TauCeti.contMDiff_sigma_iff.mpr fun i ↦ (TauCeti.contMDiff_sigmaMk (f i)).comp (hg i)
