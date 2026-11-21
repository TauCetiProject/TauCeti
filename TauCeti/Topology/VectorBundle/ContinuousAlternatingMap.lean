/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import Mathlib.Topology.VectorBundle.Hom
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Composition in alternating-bundle coordinates

Precomposing a fibrewise alternating map with a fibrewise linear map commutes with passing
into bundle coordinates wherever the intermediate trivialization is valid. This identity
allows regularity of pullbacks to be checked on fixed model fibres, without choosing norms
on the original fibres.

In degree one, the identification `ContinuousAlternatingMap.ofSubsingleton` of linear maps with
alternating maps of one variable also commutes with passing into coordinates, with no base-set
hypothesis. This compares regularity of degree-one forms with regularity of sections of the
bundle of fibrewise linear maps.

When the codomain is a fixed space, a fibre alternating map read in the trivialization at `x₀`
is precomposed with the inverse, at its base point, of the trivialization of the domain bundle at
`x₀` (`FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd`). This holds everywhere,
with no base-set hypothesis.

In top degree (`Fintype.card ι = Module.finrank 𝕜 F`), pulling back any scalar-valued top-degree
continuous alternating form in a fibre of a finite-rank vector bundle along a fibre endomorphism
multiplies the form by the endomorphism's determinant
(`TauCeti.bundleTopForm_compContinuousLinearMap_eq_det_smul`).

The coordinate maps are Mathlib's `ContinuousAlternatingMap.inCoordinates` and
`ContinuousLinearMap.inCoordinates`.
-/

public section

open Bundle

namespace ContinuousAlternatingMap

variable {𝕜 ι B₁ B₂ B₃ F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₃]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {V₁ : B₁ → Type*} {V₂ : B₂ → Type*} {V₃ : B₃ → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module 𝕜 (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]

/-- Coordinates of precomposition are precomposition of coordinates. Only the intermediate
fibre must belong to its chosen trivialization's base set. -/
theorem inCoordinates_compContinuousLinearMap {x₀ x : B₁} {y₀ y : B₂} {z₀ z : B₃}
    (φ : V₂ y [⋀^ι]→L[𝕜] V₃ z) (A : V₁ x →L[𝕜] V₂ y)
    (hy : y ∈ (trivializationAt F₂ V₂ y₀).baseSet) :
    inCoordinates F₁ F₃ x₀ x z₀ z (φ.compContinuousLinearMap A) =
      (inCoordinates F₂ F₃ y₀ y z₀ z φ).compContinuousLinearMap
        (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x y₀ y A) := by
  ext v
  simp only [inCoordinates, ContinuousLinearMap.inCoordinates,
    compContinuousLinearMap_apply, ContinuousLinearMap.compContinuousAlternatingMap_coe,
    Function.comp_def, ContinuousLinearMap.coe_comp]
  simp only [Trivialization.symmL_continuousLinearMapAt _ hy]

/-- Coordinates of a fibrewise linear map, viewed as an alternating map of one variable, are the
coordinates of the linear map, viewed in the same way. -/
@[simp]
theorem inCoordinates_ofSubsingleton [Subsingleton ι] (i : ι) {x₀ x : B₁} {y₀ y : B₂}
    (φ : V₁ x →L[𝕜] V₂ y) :
    inCoordinates F₁ F₂ x₀ x y₀ y (ofSubsingleton 𝕜 (V₁ x) (V₂ y) i φ) =
      ofSubsingleton 𝕜 F₁ F₂ i (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x y₀ y φ) := by
  ext v
  simp [inCoordinates, ContinuousLinearMap.inCoordinates]

end ContinuousAlternatingMap

namespace FiberBundle

variable {𝕜 ι B F₁ F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [TopologicalSpace B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F₁ V)] [FiberBundle F₁ V] [VectorBundle 𝕜 F₁ V]

/-- In the trivialization at `x₀` of the bundle of alternating maps from `V` to a fixed space `F`,
a fibre map `ω` at `x` is precomposed with the inverse, at `x`, of the trivialization of `V` at
`x₀`. -/
@[simp]
theorem trivializationAt_continuousAlternatingMap_apply_snd (x₀ : B) {x : B}
    (ω : V x [⋀^ι]→L[𝕜] F) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F) (fun x ↦ V x [⋀^ι]→L[𝕜] F) x₀ ⟨x, ω⟩).2 =
      ω.compContinuousLinearMap ((trivializationAt F₁ V x₀).symmL 𝕜 x) := by
  ext v
  simp [trivializationAt_continuousAlternatingMap_apply, ContinuousAlternatingMap.inCoordinates]

end FiberBundle

namespace TauCeti

section TopFormBundle

open FiberBundle

variable {𝕜 ι B F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On a finite-rank vector bundle `V` of model rank `Fintype.card ι`, pulling back any scalar
top-degree alternating form in the fibre `V x [⋀^ι]→L[𝕜] 𝕜` along a continuous linear endomorphism
`A : V x →L[𝕜] V x` multiplies the form by `A.det`. -/
theorem bundleTopForm_compContinuousLinearMap_eq_det_smul
    (h : Fintype.card ι = Module.finrank 𝕜 F) {x : B}
    (α : V x [⋀^ι]→L[𝕜] 𝕜) (A : V x →L[𝕜] V x) :
    α.compContinuousLinearMap A = A.det • α := by
  let _ : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x (mem_baseSet_trivializationAt F V x)
  exact α.compContinuousLinearMap_eq_det_smul (h.trans e.toLinearEquiv.symm.finrank_eq) A

end TopFormBundle

end TauCeti
