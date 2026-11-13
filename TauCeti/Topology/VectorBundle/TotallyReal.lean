/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import Mathlib.Topology.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Maximal total reality in vector bundle coordinates

`TauCeti.isMaximalTotallyReal_inCoordinates_iff` shows that reading a frame between vector bundle
fibres and an endomorphism of its target fibre in trivializations does not change maximal total
reality of the image. This lets tangent images at different points be compared in a fixed chart.
-/

public section

open Bundle
open ContinuousLinearMap (inCoordinates)

namespace TauCeti

variable {B₁ B₂ F₁ F₂ : Type*} [TopologicalSpace B₁] [TopologicalSpace B₂]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B₁ → Type*} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁]
  [VectorBundle ℝ F₁ E₁]
  {E₂ : B₂ → Type*} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℝ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₂ E₂]

/-- Reading a frame `A` and an endomorphism `K` of its target fibre in trivializations whose base
sets contain the fibres does not change maximal total reality of the image. -/
theorem isMaximalTotallyReal_inCoordinates_iff {x₀ x : B₁} {y₀ y : B₂}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet) (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet)
    (A : E₁ x →L[ℝ] E₂ y) (K : E₂ y →L[ℝ] E₂ y) :
    IsMaximalTotallyReal (inCoordinates F₂ E₂ F₂ E₂ y₀ y y₀ y K).toLinearMap
        (LinearMap.range (inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y A).toLinearMap) ↔
      IsMaximalTotallyReal K.toLinearMap (LinearMap.range A.toLinearMap) := by
  set e := (trivializationAt F₂ E₂ y₀).continuousLinearEquivAt ℝ y hy
  have hK : inCoordinates F₂ E₂ F₂ E₂ y₀ y y₀ y K =
      (e : E₂ y →L[ℝ] F₂).comp (K.comp (e.symm : F₂ →L[ℝ] E₂ y)) :=
    ContinuousLinearMap.inCoordinates_eq hy hy
  rw [ContinuousLinearMap.range_inCoordinates hx hy]
  refine e.toLinearEquiv.isMaximalTotallyReal_map_iff ?_
  ext v
  rw [hK]
  simp

end TauCeti
