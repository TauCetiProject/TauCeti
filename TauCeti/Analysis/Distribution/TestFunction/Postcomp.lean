/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Changing the coefficient space of test functions

A continuous linear equivalence of coefficient spaces induces a continuous linear equivalence
of native test-function spaces. These maps preserve the exact support
and commute with extension to a larger open domain. Continuity uses Mathlib's
`TestFunction.postcompCLM`, hence the native locally convex inductive-limit topology.
-/

public section

namespace TauCeti

open scoped Distributions

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [Algebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 G]
  {Ω Ω' : TopologicalSpace.Opens E} {n : ℕ∞}

/-- A change of coefficient space acts on test functions by pointwise postcomposition. -/
noncomputable def _root_.TestFunction.postcompCLE (e : F ≃L[𝕜] G) :
    𝓓^{n}(Ω, F) ≃L[𝕜] 𝓓^{n}(Ω, G) where
  toLinearEquiv :=
    { toFun := TestFunction.postcompCLM e.toContinuousLinearMap
      invFun := TestFunction.postcompCLM e.symm.toContinuousLinearMap
      left_inv := by intro φ; ext x; simp
      right_inv := by intro φ; ext x; simp
      map_add' := map_add _
      map_smul' := map_smul _ }
  continuous_toFun := (TestFunction.postcompCLM e.toContinuousLinearMap).continuous
  continuous_invFun := (TestFunction.postcompCLM e.symm.toContinuousLinearMap).continuous

@[simp]
theorem _root_.TestFunction.postcompCLE_apply (e : F ≃L[𝕜] G) (φ : 𝓓^{n}(Ω, F)) (x : E) :
    TestFunction.postcompCLE e φ x = e (φ x) := by rfl

@[simp]
theorem _root_.TestFunction.postcompCLE_symm (e : F ≃L[𝕜] G) :
    (TestFunction.postcompCLE (Ω := Ω) (n := n) e).symm = TestFunction.postcompCLE e.symm := by rfl

/-- The underlying continuous linear map is Mathlib's coefficient postcomposition map. -/
@[simp]
theorem _root_.TestFunction.coe_postcompCLE (e : F ≃L[𝕜] G) :
    (TestFunction.postcompCLE (Ω := Ω) (n := n) e :
      𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{n}(Ω, G)) = TestFunction.postcompCLM e.toContinuousLinearMap := by
  rfl

/-- The identity coefficient change acts as the identity on test functions. -/
@[simp]
theorem _root_.TestFunction.postcompCLE_refl :
    TestFunction.postcompCLE (Ω := Ω) (n := n) (ContinuousLinearEquiv.refl 𝕜 F) =
      ContinuousLinearEquiv.refl 𝕜 𝓓^{n}(Ω, F) := by
  ext φ x
  simp

/-- Successive coefficient changes compose as continuous linear equivalences. -/
theorem _root_.TestFunction.postcompCLE_trans {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedSpace 𝕜 H] [IsScalarTower ℝ 𝕜 H]
    (e : F ≃L[𝕜] G) (e' : G ≃L[𝕜] H) :
    TestFunction.postcompCLE (Ω := Ω) (n := n) (e.trans e') =
      (TestFunction.postcompCLE e).trans (TestFunction.postcompCLE e') := by
  ext φ x
  simp

/-- An invertible coefficient change preserves the topological support exactly. -/
@[simp]
theorem _root_.TestFunction.tsupport_postcompCLE (e : F ≃L[𝕜] G) (φ : 𝓓^{n}(Ω, F)) :
    tsupport (TestFunction.postcompCLE e φ) = tsupport φ := by
  simpa only [Function.comp_def, TestFunction.postcompCLE_apply] using
    (tsupport_comp_eq (g := e) (fun {_} ↦ e.map_eq_zero_iff) φ)

/-- Coefficient changes commute with extension and lowering regularity, including the zero-map
case of `monoCLM` when the domains or orders are incompatible. -/
theorem _root_.TestFunction.postcompCLE_monoCLM (e : F ≃L[𝕜] G) {m : ℕ∞}
    (φ : 𝓓^{n}(Ω, F)) :
    TestFunction.postcompCLE e (TestFunction.monoCLM 𝕜 (Ω₂ := Ω') (n₂ := m) φ) =
      TestFunction.monoCLM 𝕜 (Ω₂ := Ω') (n₂ := m) (TestFunction.postcompCLE e φ) := by
  ext x
  by_cases h : m ≤ n ∧ Ω ≤ Ω' <;> simp [h]

end TauCeti
