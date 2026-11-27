/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.LieAlgebroid.Cohomology
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Lie algebroid and de Rham differentials on the tangent bundle

Smooth differential `k`-forms on a finite-dimensional real manifold `M` identify `ℝ`-linearly with
degree-`k` Chevalley–Eilenberg cochains of the tangent Lie algebroid `LieAlgebroid.tangent I M` via
`TauCeti.LieAlgebroid.tangentCochainEquiv`, intertwining `TauCeti.mextDerivₗ` with `extDeriv`
(`TauCeti.LieAlgebroid.extDeriv_tangentCochainEquiv`).
-/

public section
noncomputable section

open scoped ContDiff

namespace TauCeti.LieAlgebroid

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- Smooth differential `k`-forms identify `ℝ`-linearly with degree-`k` cochains of
`LieAlgebroid.tangent I M`. -/
def tangentCochainEquiv (k : ℕ) : SmoothForm I M ℝ k ≃ₗ[ℝ] (tangent I M).Cochain k where
  toFun := SmoothForm.toContMDiffSection
  invFun := SmoothForm.ofContMDiffSection
  left_inv := SmoothForm.ofContMDiffSection_toContMDiffSection
  right_inv := SmoothForm.toContMDiffSection_ofContMDiffSection
  map_add' := SmoothForm.add_toContMDiffSection
  map_smul' _ _ := by simp

@[simp] theorem tangentCochainEquiv_apply {k : ℕ} (φ : SmoothForm I M ℝ k) :
    tangentCochainEquiv k φ = φ.toContMDiffSection := (rfl)
@[simp] theorem tangentCochainEquiv_symm_apply {k : ℕ} (η : (tangent I M).Cochain k) :
    (tangentCochainEquiv k).symm η = SmoothForm.ofContMDiffSection η := (rfl)

private theorem tangent_extDeriv_zero [T2Space M] (φ : SmoothForm I M ℝ 0) :
    (tangent I M).extDeriv 0 φ.toContMDiffSection = (mextDerivₗ I 0 φ).toContMDiffSection := by
  ext x v
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  have hfn : ⇑((tangent I M).cochainZeroEquiv φ.toContMDiffSection) =
      fun y ↦ (φ : RoughForm I M ℝ 0) y 0 :=
    funext fun y ↦ by simp
  rw [hv, (tangent I M).extDeriv_zero_apply, tangent_anchor_apply,
    SmoothForm.toContMDiffSection_apply, mextDerivₗ_zero_apply, hfn]

private theorem coe_scalarAlternatingEquiv_removeNth [T2Space M] {k : ℕ}
    (φ : SmoothForm I M ℝ (k + 1))
    (V : Fin (k + 2) → ContMDiffSection I E ∞ (TangentSpace I)) (i : Fin (k + 2)) :
    ⇑(ContMDiffSection.scalarAlternatingEquiv φ.toContMDiffSection (i.removeNth V)) =
      fun y ↦ φ.val y (i.removeNth (V · y)) := by
  ext y; simp; rfl

omit [FiniteDimensional ℝ E] in
private theorem tangent_bracket_summand {k : ℕ} (φ : SmoothForm I M ℝ (k + 1))
    (V : Fin (k + 2) → ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (i j : Fin (k + 1)) :
    (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ) + 1) * φ.val x (Matrix.vecCons
        (VectorField.mlieBracket I (V i.castSucc) (V j.succ) x)
        (j.removeNth (i.castSucc.removeNth (V · x)))) =
      -((-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * φ.val x (Matrix.vecCons
        (VectorField.mlieBracket I (V i.castSucc) (V j.succ) x)
        (j.removeNth (i.castSucc.removeNth (V · x))))) := by
  rw [pow_succ, mul_neg, mul_one, neg_mul]

/-- On `LieAlgebroid.tangent I M`, `extDeriv` agrees with the de Rham exterior derivative
`TauCeti.mextDerivₗ`. -/
theorem tangent_extDeriv_toContMDiffSection [T2Space M] {k : ℕ} (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k φ.toContMDiffSection = (mextDerivₗ I k φ).toContMDiffSection := by
  cases k with
  | zero => exact tangent_extDeriv_zero φ
  | succ k =>
    ext x v
    choose V hV using fun i ↦ ContMDiffSection.evalLinearMap_surjective (I := I) (F := E) ∞
      (V := (TangentSpace I : M → Type _)) x (v i)
    have hv : (fun i ↦ V i x) = v := funext fun i ↦ by simpa using hV i
    rw [← hv, (tangent I M).extDeriv_succ_apply_sections,
      (mextDerivₗ I (k + 1) φ).toContMDiffSection_apply, mextDerivₗ_apply,
      TauCeti.mextDeriv_apply_vectorField (φ.mdifferentiableAt x)
        (fun i ↦ (V i).contMDiff.mdifferentiableAt (by simp))]
    simp [coe_scalarAlternatingEquiv_removeNth, tangent_bracket_summand, sub_eq_add_neg,
      Finset.sum_neg_distrib]

/-- `tangentCochainEquiv` intertwines the de Rham exterior derivative `TauCeti.mextDerivₗ` with
`extDeriv` on `LieAlgebroid.tangent I M`. -/
theorem extDeriv_tangentCochainEquiv [T2Space M] {k : ℕ} (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k (tangentCochainEquiv k φ) =
      tangentCochainEquiv (k + 1) (mextDerivₗ I k φ) := tangent_extDeriv_toContMDiffSection φ

end TauCeti.LieAlgebroid
