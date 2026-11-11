/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph

/-!
# Recharting a manifold along a linear equivalence of model spaces

Let `M` be a manifold modelled on a normed space `F` and let `L : F ≃L[𝕜] E` be a continuous
linear equivalence. Composing every chart of `M` with `L` gives a second charted space structure
`L.chartedSpace M` on `M`, modelled on `E` (`ContinuousLinearEquiv.chartedSpace`), whose preferred
chart at `x` is `chartAt F x ≫ₕ L` (`ContinuousLinearEquiv.chartAt_chartedSpace`). It is a `C^n`
manifold whenever the original structure is (`ContinuousLinearEquiv.isManifold_chartedSpace`),
and the identity of `M` is a `C^n` map in both directions between the two structures, with
derivatives `L.symm` and `L` (`ContinuousLinearEquiv.mfderiv_id_chartedSpace`,
`ContinuousLinearEquiv.mfderiv_id_chartedSpace_symm`).

This lets a construction stated for manifolds modelled on one particular space, such as a
Euclidean space, be applied to a manifold modelled on any space of the same dimension, while
keeping its original atlas: the two structures carry different model types, so they coexist on
`M` as separate instances.

## Main definitions

* `ContinuousLinearEquiv.chartedSpace L M`: the charts of `M` composed with `L`.

## Main results

* `ContinuousLinearEquiv.isManifold_chartedSpace`: recharting preserves `C^n` manifolds.
* `ContinuousLinearEquiv.contMDiff_id_chartedSpace`,
  `ContinuousLinearEquiv.contMDiff_id_chartedSpace_symm`: the identity is smooth in both
  directions.
* `ContinuousLinearEquiv.mfderiv_id_chartedSpace`,
  `ContinuousLinearEquiv.mfderiv_id_chartedSpace_symm`: its derivatives are `L.symm` and `L`.
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (L : F ≃L[𝕜] E)

/-- `L` as a smooth diffeomorphism of the model spaces, of any order. -/
private def modelDiffeomorph (n : ℕ∞ω) : F ≃ₘ^n⟮𝓘(𝕜, F), 𝓘(𝕜, E)⟯ E where
  toEquiv := L.toEquiv
  contMDiff_toFun := L.contDiff.contMDiff
  contMDiff_invFun := L.symm.contDiff.contMDiff

variable (M : Type*) [TopologicalSpace M] [ChartedSpace F M]

/-- **Recharting along a linear equivalence.** The charted space structure on `M` modelled on
`E` whose charts are the charts of `M` composed with `L : F ≃L[𝕜] E`. -/
@[instance_reducible]
def chartedSpace : ChartedSpace E M :=
  letI := (L.modelDiffeomorph ⊤).toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace
    (by simp)
  ChartedSpace.comp E F M

/-- The preferred chart of the recharted structure at `x` is the preferred chart of `M` at `x`
followed by `L`. -/
theorem chartAt_chartedSpace (x : M) :
    (letI := L.chartedSpace M; chartAt E x) =
      chartAt F x ≫ₕ L.toHomeomorph.toOpenPartialHomeomorph :=
  (rfl)

variable {M}

/-- The preferred chart of the recharted structure at `x` is `L ∘ chartAt F x`. -/
theorem coe_chartAt_chartedSpace (x : M) :
    ⇑(letI := L.chartedSpace M; chartAt E x) = L ∘ chartAt F x :=
  (rfl)

/-- The inverse of the preferred chart of the recharted structure at `x` is
`(chartAt F x).symm ∘ L.symm`. -/
theorem coe_chartAt_chartedSpace_symm (x : M) :
    ⇑(letI := L.chartedSpace M; chartAt E x).symm = (chartAt F x).symm ∘ L.symm :=
  (rfl)

/-- The target of the preferred chart of the recharted structure at `x` is the preimage under
`L.symm` of the target of the preferred chart of `M` at `x`. -/
theorem target_chartAt_chartedSpace (x : M) :
    (letI := L.chartedSpace M; chartAt E x).target = L.symm ⁻¹' (chartAt F x).target := by
  simp [chartAt_chartedSpace]

/-- The source of the preferred chart of the recharted structure at `x` is the source of the
preferred chart of `M` at `x`. -/
theorem source_chartAt_chartedSpace (x : M) :
    (letI := L.chartedSpace M; chartAt E x).source = (chartAt F x).source := by
  simp [chartAt_chartedSpace]

/-- **Recharting preserves manifolds.** If `M` is a `C^n` manifold modelled on `F`, then its
recharting along `L` is a `C^n` manifold modelled on `E`. -/
theorem isManifold_chartedSpace {n : ℕ∞ω} [IsManifold 𝓘(𝕜, F) n M] :
    letI := L.chartedSpace M
    IsManifold 𝓘(𝕜, E) n M := by
  have h := (L.modelDiffeomorph n).isManifold_chartedSpaceComp M
  exact h

/-- In the preferred charts at `x`, the identity from the recharted structure to the original one
is `L.symm` near `chartAt E x x`. -/
private theorem writtenInExtChartAt_id_eventuallyEq (x : M) :
    (letI := L.chartedSpace M
     writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, F) x (id : M → M)) =ᶠ[𝓝 (L (chartAt F x x))] L.symm := by
  let := L.chartedSpace M
  have hmem : L.symm ⁻¹' (chartAt F x).target ∈ 𝓝 (L (chartAt F x x)) :=
    L.symm.continuous.continuousAt.preimage_mem_nhds (by
      simpa using (chartAt F x).open_target.mem_nhds (mem_chart_target F x))
  filter_upwards [hmem] with y hy
  simp [writtenInExtChartAt, coe_chartAt_chartedSpace_symm, (chartAt F x).right_inv hy]

/-- In the preferred charts at `x`, the identity from the original structure to the recharted one
is `L` near `chartAt F x x`. -/
private theorem writtenInExtChartAt_id_symm_eventuallyEq (x : M) :
    (letI := L.chartedSpace M
     writtenInExtChartAt 𝓘(𝕜, F) 𝓘(𝕜, E) x (id : M → M)) =ᶠ[𝓝 (chartAt F x x)] L := by
  let := L.chartedSpace M
  filter_upwards [(chartAt F x).open_target.mem_nhds (mem_chart_target F x)] with y hy
  simp [writtenInExtChartAt, coe_chartAt_chartedSpace, (chartAt F x).right_inv hy]

/-- The identity of `M`, from its recharting along `L` to its original structure, is `C^n`. -/
theorem contMDiff_id_chartedSpace {n : ℕ∞ω} :
    letI := L.chartedSpace M
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n (id : M → M) := by
  let := L.chartedSpace M
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  simp only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
  have h := writtenInExtChartAt_id_eventuallyEq L x
  exact (L.symm.contDiff.contDiffAt.congr_of_eventuallyEq h)

/-- The identity of `M`, from its original structure to its recharting along `L`, is `C^n`. -/
theorem contMDiff_id_chartedSpace_symm {n : ℕ∞ω} :
    letI := L.chartedSpace M
    ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, E) n (id : M → M) := by
  let := L.chartedSpace M
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  simp only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
  have h := writtenInExtChartAt_id_symm_eventuallyEq L x
  exact (L.contDiff.contDiffAt.congr_of_eventuallyEq h)

/-- The derivative of the identity of `M`, from its recharting along `L` to its original
structure, is `L.symm`. -/
theorem mfderiv_id_chartedSpace (x : M) :
    (letI := L.chartedSpace M
     mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) (id : M → M) x) = (L.symm : E →L[𝕜] F) := by
  let := L.chartedSpace M
  rw [((contMDiff_id_chartedSpace L (n := 1)).mdifferentiableAt one_ne_zero).mfderiv]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  exact (writtenInExtChartAt_id_eventuallyEq L x).fderiv_eq.trans L.symm.fderiv

/-- The derivative of the identity of `M`, from its original structure to its recharting along
`L`, is `L`. -/
theorem mfderiv_id_chartedSpace_symm (x : M) :
    (letI := L.chartedSpace M
     mfderiv 𝓘(𝕜, F) 𝓘(𝕜, E) (id : M → M) x) = (L : F →L[𝕜] E) := by
  let := L.chartedSpace M
  rw [((contMDiff_id_chartedSpace_symm L (n := 1)).mdifferentiableAt one_ne_zero).mfderiv]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  exact (writtenInExtChartAt_id_symm_eventuallyEq L x).fderiv_eq.trans L.fderiv

section Comp

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- A map out of `M` is differentiable for the recharted structure exactly when it is
differentiable for the original one. -/
theorem mdifferentiableAt_chartedSpace_left_iff {f : M → N} {x : M} :
    (letI := L.chartedSpace M; MDifferentiableAt 𝓘(𝕜, E) I' f x) ↔
      MDifferentiableAt 𝓘(𝕜, F) I' f x := by
  let := L.chartedSpace M
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact hf.comp (I' := 𝓘(𝕜, E)) x
      ((contMDiff_id_chartedSpace_symm L (n := 1)).mdifferentiableAt one_ne_zero)
  · exact hf.comp (I' := 𝓘(𝕜, F)) x
      ((contMDiff_id_chartedSpace L (n := 1)).mdifferentiableAt one_ne_zero)

/-- The derivative of a map out of `M` for the recharted structure is its derivative for the
original structure composed with `L.symm`. -/
theorem mfderiv_chartedSpace_left {f : M → N} {x : M} (hf : MDifferentiableAt 𝓘(𝕜, F) I' f x) :
    (letI := L.chartedSpace M; mfderiv 𝓘(𝕜, E) I' f x) =
      (mfderiv 𝓘(𝕜, F) I' f x).comp (L.symm : E →L[𝕜] F) := by
  let := L.chartedSpace M
  have h := mfderiv_comp (I' := 𝓘(𝕜, F)) x hf
    ((contMDiff_id_chartedSpace L (n := 1)).mdifferentiableAt one_ne_zero)
  rw [Function.comp_id, mfderiv_id_chartedSpace] at h
  exact h

/-- A map into `M` is differentiable for the recharted structure exactly when it is
differentiable for the original one. -/
theorem mdifferentiableAt_chartedSpace_right_iff {g : N → M} {y : N} :
    (letI := L.chartedSpace M; MDifferentiableAt I' 𝓘(𝕜, E) g y) ↔
      MDifferentiableAt I' 𝓘(𝕜, F) g y := by
  let := L.chartedSpace M
  refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
  · exact ((contMDiff_id_chartedSpace L (n := 1)).mdifferentiableAt one_ne_zero).comp
      (I' := 𝓘(𝕜, E)) y hg
  · exact ((contMDiff_id_chartedSpace_symm L (n := 1)).mdifferentiableAt one_ne_zero).comp
      (I' := 𝓘(𝕜, F)) y hg

/-- The derivative of a map into `M` for the recharted structure is `L` composed with its
derivative for the original structure. -/
theorem mfderiv_chartedSpace_right {g : N → M} {y : N} (hg : MDifferentiableAt I' 𝓘(𝕜, F) g y) :
    (letI := L.chartedSpace M; mfderiv I' 𝓘(𝕜, E) g y) =
      (L : F →L[𝕜] E).comp (mfderiv I' 𝓘(𝕜, F) g y) := by
  let := L.chartedSpace M
  have h := mfderiv_comp (I' := 𝓘(𝕜, F)) (g := (id : M → M)) y
    ((contMDiff_id_chartedSpace_symm L (n := 1)).mdifferentiableAt one_ne_zero) hg
  rw [Function.id_comp, mfderiv_id_chartedSpace_symm] at h
  exact h

end Comp

end ContinuousLinearEquiv
