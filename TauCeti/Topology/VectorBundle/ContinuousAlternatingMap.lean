/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import TauCeti.Topology.Algebra.Module.Alternating.Curry

/-!
# Composition and coordinates in alternating-bundle trivializations

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

Fibrewise topological currying and paired wedges also commute with passing into bundle
coordinates (`TauCeti.inCoordinates_curryLeftTopological` and `TauCeti.inCoordinates_pairedWedge`).

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

section Coordinates
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {FW FV : Type*}
  [NormedAddCommGroup FW] [NormedSpace 𝕜 FW] [NormedAddCommGroup FV] [NormedSpace 𝕜 FV]
  {M : Type*} [TopologicalSpace M] {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle 𝕜 FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle 𝕜 FV V]
  [∀ x, ContinuousAdd (V x)] [∀ x, ContinuousConstSMul 𝕜 (V x)]

/-- Coordinate expression of `φ.curryLeftTopological w` in a domain trivialization. -/
theorem inCoordinates_curryLeftTopological {k : ℕ} {x₀ y : M}
    (w : W y) (φ : W y [⋀^Fin (k + 1)]→L[𝕜] V y)
    (hy : y ∈ (trivializationAt FW W x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates FW FV x₀ y x₀ y (φ.curryLeftTopological w) =
      (ContinuousAlternatingMap.inCoordinates FW FV x₀ y x₀ y φ).curryLeft
        ((trivializationAt FW W x₀ ⟨y, w⟩).2) := by
  ext v; simp only [ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeftTopological_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Function.comp_apply]
  congr 2; funext i; refine Fin.cases ?_ (fun _ ↦ rfl) i
  simp only [Function.comp_apply, Matrix.cons_val_zero, Trivialization.symmL_apply _ hy,
    (trivializationAt FW W x₀).symm_apply_apply_mk hy]
end Coordinates

section PairedWedgeCoordinates
variable {FW F₁ F₂ F₃ M : Type*} [TopologicalSpace M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {W V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]

/-- Coordinate expression of a fibrewise paired wedge in valid coefficient trivializations. -/
theorem inCoordinates_pairedWedge {k l : ℕ} {x₀ y : M}
    (μ : V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y) (hμ : Continuous (Function.uncurry fun a b ↦ μ a b))
    (φ : W y [⋀^Fin k]→L[ℝ] V₁ y) (ψ : W y [⋀^Fin l]→L[ℝ] V₂ y)
    (h₁ : y ∈ (trivializationAt F₁ V₁ x₀).baseSet) (h₂ : y ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (h₃ : y ∈ (trivializationAt F₃ V₃ x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates FW F₃ x₀ y x₀ y
        (ContinuousAlternatingMap.pairedWedge μ hμ φ ψ) =
      ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x₀ y x₀ y μ)
        (ContinuousAlternatingMap.inCoordinates FW F₁ x₀ y x₀ y φ)
        (ContinuousAlternatingMap.inCoordinates FW F₂ x₀ y x₀ y ψ) := by
  ext v; simp only [ContinuousAlternatingMap.pairedWedgeCLM_apply,
    ContinuousAlternatingMap.inCoordinates, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    ContinuousAlternatingMap.pairedWedge_apply, map_smul, map_sum]
  congr 2; funext σ
  rw [ContinuousLinearMap.map_smul_of_tower, inCoordinates_apply_eq₂ h₁ h₂ h₃]
  simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symm_linearMapAt _ h₁,
    Trivialization.symm_linearMapAt _ h₂, Function.comp_def]
end PairedWedgeCoordinates

end TauCeti
