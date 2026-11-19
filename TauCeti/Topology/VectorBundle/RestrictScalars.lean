/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Scalar restriction and linearity upgrades of topological vector bundles

Along a normed field extension `𝕜' ⊆ 𝕜`, scalar restriction `(G →L[𝕜] G) → (G →L[𝕜'] G)` is an
isometry. Consequently, any `VectorBundle 𝕜 G W` restricts to a `VectorBundle 𝕜' G W` sharing the
exact same total-space topology and trivialization atlas (`VectorBundle.restrictScalars`), and
conversely any `VectorBundle 𝕜' G W` whose atlas trivializations are `𝕜`-linear upgrades to a
`VectorBundle 𝕜 G W` (`VectorBundle.ofLinear`).

The fibre coordinates over `𝕜'` are the scalar restrictions of those over `𝕜`, including their
zero extension off the base set (`Bundle.Trivialization.restrictScalars_continuousLinearMapAt`).
-/

public section

noncomputable section

open Bundle FiberBundle

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B]

/-- The fibre-coordinate map of a trivialization over `𝕜'` is the scalar restriction of the
fibre-coordinate map over `𝕜`, including its zero extension off the base set. Only compatibility
of the two scalar actions is needed, not a field extension. -/
@[simp]
theorem restrictScalars_continuousLinearMapAt (𝕜' 𝕜 : Type*)
    [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] {F : Type*} {E : B → Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, LinearMap.CompatibleSMul (E x) F 𝕜' 𝕜]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜'] [e.IsLinear 𝕜] (b : B) :
    (e.continuousLinearMapAt 𝕜 b).restrictScalars 𝕜' = e.continuousLinearMapAt 𝕜' b :=
  DFunLike.coe_injective
    (coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt 𝕜' 𝕜 e b).symm

end Bundle.Trivialization

namespace VectorBundle

variable {B : Type*} [TopologicalSpace B] (𝕜' 𝕜 : Type*)
  [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜' 𝕜]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜' 𝕜 G]
  (W : B → Type*) [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜' (W x)] [∀ x, Module 𝕜 (W x)]
  [TopologicalSpace (TotalSpace G W)] [∀ x, TopologicalSpace (W x)] [FiberBundle G W]

/-- Restrict a `VectorBundle 𝕜 G W` to a `VectorBundle 𝕜' G W` along a normed field extension
`𝕜' ⊆ 𝕜`, keeping the exact same total-space topology and trivialization atlas. -/
theorem restrictScalars [∀ x, IsScalarTower 𝕜' 𝕜 (W x)] [VectorBundle 𝕜 G W] :
    VectorBundle 𝕜' G W where
  trivialization_linear' e _ := Trivialization.isLinear_restrictScalars 𝕜' 𝕜 e
  continuousOn_coordChange' e e' _ _ := by
    let : e.IsLinear 𝕜' := Trivialization.isLinear_restrictScalars 𝕜' 𝕜 e
    let : e'.IsLinear 𝕜' := Trivialization.isLinear_restrictScalars 𝕜' 𝕜 e'
    refine ((ContinuousLinearMap.restrictScalarsIsometry 𝕜 G G 𝕜' ℤ).isometry.continuous
      |>.comp_continuousOn (continuousOn_coordChange 𝕜 e e')).congr fun b _ ↦
      (Trivialization.restrictScalars_coordChangeL 𝕜' 𝕜 e e').symm

/-- Upgrade a `VectorBundle 𝕜' G W` to `VectorBundle 𝕜 G W` along a normed field extension
`𝕜' ⊆ 𝕜` once every trivialization in the atlas is `𝕜`-linear. -/
theorem ofLinear [VectorBundle 𝕜' G W]
    (hlin : ∀ e : Trivialization G (π G W), MemTrivializationAtlas e → e.IsLinear 𝕜) :
    VectorBundle 𝕜 G W where
  trivialization_linear' e he := hlin e he
  continuousOn_coordChange' e e' he he' := by
    let : e.IsLinear 𝕜 := hlin e he
    let : e'.IsLinear 𝕜 := hlin e' he'
    rw [(ContinuousLinearMap.restrictScalarsIsometry 𝕜 G G 𝕜' ℤ
      ).isometry.isUniformEmbedding.isInducing.continuousOn_iff]
    exact (continuousOn_coordChange 𝕜' e e').congr fun b _ ↦
      Trivialization.restrictScalars_coordChangeL 𝕜' 𝕜 e e'

end VectorBundle

end
