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

For complex-valued smooth functions supported in a compact set, postcomposition with the real and
imaginary parts `Complex.reCLM` and `Complex.imCLM` gives real-valued ones. This file records how
these parts transform under complex scalars, that they recover a real function viewed as a complex
one through `Complex.ofRealCLM`, and that a complex function is `Re φ + i Im φ`.

Postcomposition with `T` increases the `C^k` seminorms at most by the factor `‖T‖`
(`ContDiffMapSupportedIn.supSeminorm_postcompCLM_le`), and these seminorms do not depend on the
scalar field (`ContDiffMapSupportedIn.supSeminorm_eq_of_scalars`). In particular the real and
imaginary parts do not increase them
(`ContDiffMapSupportedIn.supSeminorm_postcompCLM_le_of_norm_le_one`).
-/

public section

namespace TestFunction

open scoped Distributions

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [Algebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 G]
  {Ω Ω' : TopologicalSpace.Opens E} {n : ℕ∞}

/-- A change of coefficient space acts on test functions by pointwise postcomposition. -/
noncomputable def postcompCLE (e : F ≃L[𝕜] G) :
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
theorem postcompCLE_apply (e : F ≃L[𝕜] G) (φ : 𝓓^{n}(Ω, F)) (x : E) :
    TestFunction.postcompCLE e φ x = e (φ x) := by rfl

@[simp]
theorem postcompCLE_symm (e : F ≃L[𝕜] G) :
    (TestFunction.postcompCLE (Ω := Ω) (n := n) e).symm = TestFunction.postcompCLE e.symm := by rfl

/-- The underlying continuous linear map is Mathlib's coefficient postcomposition map. -/
@[simp]
theorem coe_postcompCLE (e : F ≃L[𝕜] G) :
    (TestFunction.postcompCLE (Ω := Ω) (n := n) e :
      𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{n}(Ω, G)) = TestFunction.postcompCLM e.toContinuousLinearMap := by
  rfl

/-- The identity coefficient change acts as the identity on test functions. -/
@[simp]
theorem postcompCLE_refl :
    TestFunction.postcompCLE (Ω := Ω) (n := n) (ContinuousLinearEquiv.refl 𝕜 F) =
      ContinuousLinearEquiv.refl 𝕜 𝓓^{n}(Ω, F) := by
  ext φ x
  simp

/-- Successive coefficient changes compose as continuous linear equivalences. -/
theorem postcompCLE_trans {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedSpace 𝕜 H] [IsScalarTower ℝ 𝕜 H]
    (e : F ≃L[𝕜] G) (e' : G ≃L[𝕜] H) :
    TestFunction.postcompCLE (Ω := Ω) (n := n) (e.trans e') =
      (TestFunction.postcompCLE e).trans (TestFunction.postcompCLE e') := by
  ext φ x
  simp

/-- An invertible coefficient change preserves the topological support exactly. -/
@[simp]
theorem tsupport_postcompCLE (e : F ≃L[𝕜] G) (φ : 𝓓^{n}(Ω, F)) :
    tsupport (TestFunction.postcompCLE e φ) = tsupport φ := by
  have hcoe : (TestFunction.postcompCLE e φ : E → G) = e ∘ φ := by
    funext x
    exact TestFunction.postcompCLE_apply e φ x
  rw [hcoe]
  exact tsupport_comp_eq (g := e) (fun {_} ↦ e.map_eq_zero_iff) φ

/-- Coefficient changes commute with extension and lowering regularity, including the zero-map
case of `monoCLM` when the domains or orders are incompatible. -/
theorem postcompCLE_monoCLM (e : F ≃L[𝕜] G) {m : ℕ∞}
    (φ : 𝓓^{n}(Ω, F)) :
    TestFunction.postcompCLE e (TestFunction.monoCLM 𝕜 (Ω₂ := Ω') (n₂ := m) φ) =
      TestFunction.monoCLM 𝕜 (Ω₂ := Ω') (n₂ := m) (TestFunction.postcompCLE e φ) := by
  ext x
  by_cases h : m ≤ n ∧ Ω ≤ Ω' <;> simp [h]

end TestFunction

namespace ContDiffMapSupportedIn

open Complex
open scoped Distributions

section Scalars

variable {𝕜 E F F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
  {K K₁ K₂ : TopologicalSpace.Compacts E} {n n₁ n₂ : ℕ∞}

variable (𝕜) in
/-- The `C^k` seminorms do not depend on the scalar field over which they are considered. -/
theorem supSeminorm_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F]
    [SMulCommClass ℝ 𝕜' F] (k : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K k f =
      ContDiffMapSupportedIn.supSeminorm 𝕜' E F n K k f := by
  simp only [ContDiffMapSupportedIn.supSeminorm, Seminorm.finset_sup_apply,
    ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_eq_of_scalars 𝕜 𝕜']

/-- The `C^k` seminorms grow at most by the factor `‖T‖` under postcomposition with `T`. -/
theorem supSeminorm_postcompCLM_le [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (k : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.supSeminorm 𝕜 E F' n K k (postcompCLM T f) ≤
      ‖T‖ * ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K k f :=
  Seminorm.finset_sup_apply_le (by positivity) fun _ hi ↦ (seminorm_postcompLM_le 𝕜 T f).trans
    (by gcongr; exact Seminorm.le_finset_sup_apply hi)

/-- Postcomposition commutes with enlarging the compact set and lowering regularity, including the
zero-map case of `monoCLM` when the compact sets or orders are incompatible. -/
theorem postcompCLM_monoCLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n₁}_{K₁}(E, F)) :
    postcompCLM T (monoCLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) = monoCLM 𝕜 (postcompCLM T f) := by
  ext x
  by_cases h : n₂ ≤ n₁ ∧ K₁ ≤ K₂ <;> simp [h]

end Scalars

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : TopologicalSpace.Compacts E}
  {n : ℕ∞}

theorem postcompCLM_reCLM_smul (c : ℂ) (φ : 𝓓^{n}_{K}(E, ℂ)) :
    postcompCLM (𝕜 := ℝ) reCLM (c • φ) =
      c.re • postcompCLM (𝕜 := ℝ) reCLM φ - c.im • postcompCLM (𝕜 := ℝ) imCLM φ := by
  ext x
  simp

theorem postcompCLM_imCLM_smul (c : ℂ) (φ : 𝓓^{n}_{K}(E, ℂ)) :
    postcompCLM (𝕜 := ℝ) imCLM (c • φ) =
      c.re • postcompCLM (𝕜 := ℝ) imCLM φ + c.im • postcompCLM (𝕜 := ℝ) reCLM φ := by
  ext x
  simp

@[simp]
theorem postcompCLM_reCLM_ofRealCLM (φ : 𝓓^{n}_{K}(E, ℝ)) :
    postcompCLM (𝕜 := ℝ) reCLM (postcompCLM (𝕜 := ℝ) ofRealCLM φ) = φ := by
  ext x
  simp

@[simp]
theorem postcompCLM_imCLM_ofRealCLM (φ : 𝓓^{n}_{K}(E, ℝ)) :
    postcompCLM (𝕜 := ℝ) imCLM (postcompCLM (𝕜 := ℝ) ofRealCLM φ) = 0 := by
  ext x
  simp

/-- A complex function is the sum `Re φ + i Im φ` of its real and imaginary parts. -/
theorem postcompCLM_re_add_I_smul_im (φ : 𝓓^{n}_{K}(E, ℂ)) :
    postcompCLM (𝕜 := ℝ) ofRealCLM (postcompCLM (𝕜 := ℝ) reCLM φ) +
      I • postcompCLM (𝕜 := ℝ) ofRealCLM (postcompCLM (𝕜 := ℝ) imCLM φ) = φ := by
  ext x
  simp [mul_comm I]

/-- Postcomposition with a real-linear map `ℂ →L[ℝ] ℝ` of norm at most one, such as the real and
imaginary parts, does not increase the `C^k` seminorms. -/
theorem supSeminorm_postcompCLM_le_of_norm_le_one {T : ℂ →L[ℝ] ℝ} (hT : ‖T‖ ≤ 1) (k : ℕ)
    (φ : 𝓓^{n}_{K}(E, ℂ)) :
    ContDiffMapSupportedIn.supSeminorm ℝ E ℝ n K k (postcompCLM T φ) ≤
      ContDiffMapSupportedIn.supSeminorm ℂ E ℂ n K k φ :=
  (supSeminorm_postcompCLM_le T k φ).trans <| by
    rw [supSeminorm_eq_of_scalars ℝ ℂ]
    exact mul_le_of_le_one_left (apply_nonneg _ _) hT

end Complex

end ContDiffMapSupportedIn
