/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Restricting scalars of vector bundles

A vector bundle over a normed field extension is a vector bundle over the smaller field,
using the same fibres, topology, and trivialization atlas. No new bundle carrier or
trivialization is needed: fibrewise linearity restricts scalars, and the transition operators
are the original operators with scalars restricted.

`VectorBundle.restrictScalars` supplies the resulting mixin as a theorem, so callers can
install it locally without making instance search guess a larger scalar field.
`Bundle.Trivialization.coordChangeL_restrictScalars` identifies the transition operators
everywhere, including the identity extension off the overlap. The corresponding comparison
for `continuousLinearMapAt` identifies the fibre coordinates themselves.

The construction uses Mathlib's `LinearMap.isLinearMap_of_compatibleSMul` and
`ContinuousLinearMap.continuous_restrictScalars`, together with the existing vector-bundle
atlas. See Steenrod, *The Topology of Fibre Bundles*, Part I, §§2–3, for the description of
vector bundles through linear coordinate changes.
-/

public section

open Bundle Set

namespace Bundle.Trivialization

section Linearity

variable {R S B F : Type*} [Semiring R] [Semiring S] [TopologicalSpace B]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F] [Module S F]
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  [∀ b, Module S (E b)] [∀ b, LinearMap.CompatibleSMul (E b) F R S]
  [TopologicalSpace (TotalSpace F E)]

variable (R) in
/-- A fibrewise linear trivialization remains linear after restricting scalars. -/
theorem isLinear_restrictScalars (e : Trivialization F (π F E)) [e.IsLinear S] : e.IsLinear R where
  linear _ hb := ((e.linear S hb).mk' _).isLinearMap_of_compatibleSMul R

end Linearity

section Coordinates

variable {R S B F : Type*} [Semiring R] [Semiring S] [TopologicalSpace B]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F] [Module S F]
  [LinearMap.CompatibleSMul F F R S]
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  [∀ b, Module S (E b)] [TopologicalSpace (TotalSpace F E)]

variable (R) (e e' : Trivialization F (π F E))
  [e.IsLinear S] [e'.IsLinear S] [e.IsLinear R] [e'.IsLinear R]

/-- The transition operator over `R` is the restriction of the original
transition operator over `S`. This also holds off the overlap, where both are the identity. -/
@[simp]
theorem coordChangeL_restrictScalars (b : B) :
    (e.coordChangeL S e' b).restrictScalars R = e.coordChangeL R e' b := by
  classical
  ext v
  by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
  · simp only [ContinuousLinearEquiv.restrictScalars_apply, coordChangeL_apply e e' hb]
  · simp [coordChangeL, hb]

end Coordinates

section FibreCoordinates

variable {𝕜 𝕜' B F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, Module 𝕜' (E b)] [∀ b, IsScalarTower 𝕜 𝕜' (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (𝕜) (e : Trivialization F (π F E)) [e.IsLinear 𝕜'] [e.IsLinear 𝕜]

/-- The fibre-coordinate map over the smaller field is the restriction of the
original fibre-coordinate map, including its zero extension off the base set. -/
@[simp]
theorem continuousLinearMapAt_restrictScalars (b : B) :
    (e.continuousLinearMapAt 𝕜' b).restrictScalars 𝕜 =
      e.continuousLinearMapAt 𝕜 b := by
  ext v
  by_cases hb : b ∈ e.baseSet
  · simp [continuousLinearMapAt_apply_of_mem, hb]
  · simp [continuousLinearMapAt, linearMapAt_def_of_notMem, hb]

end FibreCoordinates

end Bundle.Trivialization

variable {𝕜 𝕜' B F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, Module 𝕜' (E b)] [∀ b, IsScalarTower 𝕜 𝕜' (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (𝕜) in
/-- A vector bundle over a normed field extension is a vector bundle over the smaller
field, with the same fibre bundle and trivialization atlas. -/
theorem VectorBundle.restrictScalars (h : VectorBundle 𝕜' F E) : VectorBundle 𝕜 F E := by
  let := h
  let (e : Trivialization F (π F E)) [MemTrivializationAtlas e] : e.IsLinear 𝕜 :=
    e.isLinear_restrictScalars 𝕜 (S := 𝕜')
  refine ⟨fun e _ ↦ inferInstance, fun e e' _ _ ↦ ?_⟩
  exact (ContinuousLinearMap.continuous_restrictScalars 𝕜).comp_continuousOn
    (continuousOn_coordChange 𝕜' e e') |>.congr fun b _ ↦
      ContinuousLinearMap.ext fun v ↦ DFunLike.congr_fun
        (e.coordChangeL_restrictScalars 𝕜 (S := 𝕜') e' b).symm v
