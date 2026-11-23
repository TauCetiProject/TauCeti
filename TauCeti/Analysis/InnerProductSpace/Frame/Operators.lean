/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Analysis, synthesis and the frame operator

For a finite family of vectors, the analysis map takes inner products with the family and
the synthesis map forms linear combinations of those vectors. The range of synthesis is
the span of the family. The frame operator is synthesis after analysis.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

variable (𝕜) in
/-- The analysis map `x ↦ (⟪vᵢ, x⟫)ᵢ` of a finite family `v`, from the ambient space to
coefficient space. -/
noncomputable def analysisMap (v : ι → E) : E →ₗ[𝕜] EuclideanSpace 𝕜 ι where
  toFun x := WithLp.toLp 2 fun i ↦ ⟪v i, x⟫_𝕜
  map_add' x y := by ext i; simp [inner_add_right]
  map_smul' c x := by ext i; simp [inner_smul_right]

variable (𝕜) in
/-- The synthesis map `a ↦ ∑ᵢ aᵢ vᵢ` of a finite family `v`, from coefficient space to the ambient
space. -/
noncomputable def synthesisMap (v : ι → E) : EuclideanSpace 𝕜 ι →ₗ[𝕜] E :=
  Fintype.linearCombination 𝕜 v ∘ₗ (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).toLinearMap

/-- The range of synthesis is the span of the finite family. -/
theorem range_synthesisMap (v : ι → E) :
    LinearMap.range (synthesisMap 𝕜 v) = Submodule.span 𝕜 (Set.range v) := by
  rw [synthesisMap, LinearEquiv.range_comp, Fintype.range_linearCombination]

omit [Fintype ι] in
@[simp]
theorem analysisMap_apply (v : ι → E) (x : E) (i : ι) : analysisMap 𝕜 v x i = ⟪v i, x⟫_𝕜 :=
  (rfl)

@[simp]
theorem synthesisMap_apply (v : ι → E) (a : EuclideanSpace 𝕜 ι) :
    synthesisMap 𝕜 v a = ∑ i, a i • v i := by
  simp [synthesisMap, Fintype.linearCombination_apply]

/-- A finite family is linearly independent exactly when its synthesis map is injective. -/
theorem linearIndependent_iff_injective_synthesisMap (v : ι → E) :
    LinearIndependent 𝕜 v ↔ Function.Injective (synthesisMap 𝕜 v) := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination, synthesisMap, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp]

variable (𝕜) in
/-- The frame operator `x ↦ ∑ᵢ ⟪vᵢ, x⟫ vᵢ` of a finite family: synthesis after analysis. -/
noncomputable def frameOperator (v : ι → E) : E →ₗ[𝕜] E :=
  synthesisMap 𝕜 v ∘ₗ analysisMap 𝕜 v

theorem frameOperator_def (v : ι → E) :
    frameOperator 𝕜 v = synthesisMap 𝕜 v ∘ₗ analysisMap 𝕜 v :=
  (rfl)

@[simp]
theorem frameOperator_apply (v : ι → E) (x : E) :
    frameOperator 𝕜 v x = ∑ i, ⟪v i, x⟫_𝕜 • v i := by
  simp [frameOperator_def]

end TauCeti
