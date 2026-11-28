/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap

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
with no base-set hypothesis, and yields the corresponding chart compatibility laws for
empty-index maps (`FiberBundle.constOfIsEmptyLIE_symm_trivializationAt_snd`,
`FiberBundle.trivializationAt_constOfIsEmpty_snd`) and paired wedges
(`FiberBundle.trivializationAt_pairedWedge_snd`).

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

/-- Reading an empty-index alternating fibre map in the trivialization at `x₀` and unwrapping it
with `(ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F₁ F ι).symm` recovers its value at `0`. -/
theorem constOfIsEmptyLIE_symm_trivializationAt_snd [IsEmpty ι] (x₀ x : B)
    (φx : V x [⋀^ι]→L[𝕜] F) :
    (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F₁ F ι).symm
      (trivializationAt (F₁ [⋀^ι]→L[𝕜] F) (fun y ↦ V y [⋀^ι]→L[𝕜] F) x₀ ⟨x, φx⟩).2 =
      φx 0 := by
  rw [ContinuousAlternatingMap.constOfIsEmptyLIE_symm_apply,
    trivializationAt_continuousAlternatingMap_apply_snd,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact congrArg φx (Subsingleton.elim _ _)

/-- Reading a constant empty-index alternating fibre map in the trivialization at `x₀` yields the
model constant map `ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F₁ F ι g`. -/
theorem trivializationAt_constOfIsEmpty_snd [IsEmpty ι] (x₀ x : B) (g : F) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F) (fun y ↦ V y [⋀^ι]→L[𝕜] F) x₀
      ⟨x, ContinuousAlternatingMap.constOfIsEmpty 𝕜 (V x) ι g⟩).2 =
      ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F₁ F ι g := by
  ext v
  simp [trivializationAt_continuousAlternatingMap_apply_snd]

/-- Reading the paired wedge of two alternating fibre maps in the trivialization at `x₀` is the
model-fibre `pairedWedgeCLM` applied to their trivialization coordinates. -/
theorem trivializationAt_pairedWedge_snd {F' G₁ G₂ G₃ : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂]
    [NormedAddCommGroup G₃] [NormedSpace ℝ G₃]
    {V' : B → Type*} [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)]
    [∀ x, TopologicalSpace (V' x)] [TopologicalSpace (TotalSpace F' V')]
    [FiberBundle F' V'] [VectorBundle ℝ F' V']
    {k l : ℕ} (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃) (x₀ x : B)
    (α : V' x [⋀^Fin k]→L[ℝ] G₁) (β : V' x [⋀^Fin l]→L[ℝ] G₂) :
    (trivializationAt (F' [⋀^Fin (k + l)]→L[ℝ] G₃)
      (fun y ↦ V' y [⋀^Fin (k + l)]→L[ℝ] G₃) x₀
      ⟨x, ContinuousAlternatingMap.pairedWedge μ μ.continuous₂ α β⟩).2 =
      ContinuousAlternatingMap.pairedWedgeCLM μ
        (trivializationAt (F' [⋀^Fin k]→L[ℝ] G₁) (fun y ↦ V' y [⋀^Fin k]→L[ℝ] G₁) x₀ ⟨x, α⟩).2
        (trivializationAt (F' [⋀^Fin l]→L[ℝ] G₂) (fun y ↦ V' y [⋀^Fin l]→L[ℝ] G₂) x₀ ⟨x, β⟩).2 := by
  ext v
  simp [trivializationAt_continuousAlternatingMap_apply_snd,
    ContinuousAlternatingMap.pairedWedge_compContinuousLinearMap]

end FiberBundle
