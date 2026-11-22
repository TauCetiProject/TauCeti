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
# Comparison of Lie algebroid and de Rham cohomology on the tangent bundle

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
  [T2Space M] [IsManifold I ∞ M]

omit [T2Space M] in
/-- Smooth differential `k`-forms identify `ℝ`-linearly with degree-`k` cochains of
`LieAlgebroid.tangent I M`. -/
def tangentCochainEquiv (k : ℕ) : SmoothForm I M ℝ k ≃ₗ[ℝ] (tangent I M).Cochain k where
  toFun := SmoothForm.toContMDiffSection
  invFun := SmoothForm.ofContMDiffSection
  left_inv := SmoothForm.ofContMDiffSection_toContMDiffSection
  right_inv := SmoothForm.toContMDiffSection_ofContMDiffSection
  map_add' := SmoothForm.add_toContMDiffSection
  map_smul' _ _ := by simp

omit [T2Space M] in
@[simp] theorem tangentCochainEquiv_apply {k : ℕ} (φ : SmoothForm I M ℝ k) :
    tangentCochainEquiv k φ = φ.toContMDiffSection := (rfl)
omit [T2Space M] in
@[simp] theorem tangentCochainEquiv_symm_apply {k : ℕ} (η : (tangent I M).Cochain k) :
    (tangentCochainEquiv k).symm η = SmoothForm.ofContMDiffSection η := (rfl)

/-- On `LieAlgebroid.tangent I M`, `extDeriv` agrees with the de Rham exterior derivative
`TauCeti.mextDerivₗ`. -/
theorem tangent_extDeriv_toContMDiffSection {k : ℕ} (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k φ.toContMDiffSection = (mextDerivₗ I k φ).toContMDiffSection := by
  ext x v
  choose V hV using fun i ↦ ContMDiffSection.evalLinearMap_surjective (I := I) (F := E) ∞
    (V := (TangentSpace I : M → Type _)) x (v i)
  have hv : (fun i ↦ V i x) = v := funext fun i ↦ by
    simpa only [ContMDiffSection.evalLinearMap_apply] using hV i
  rw [← hv]; cases k with
  | zero =>
    have htup : (fun i : Fin 1 ↦ V i x) = ![V 0 x] := funext fun i ↦ by fin_cases i; rfl
    rw [htup, (tangent I M).extDeriv_zero_apply_section, anchorDeriv_apply, tangent_anchor_apply,
      SmoothForm.toContMDiffSection_apply, mextDerivₗ_zero_apply]
    congr 2; ext y; simp
  | succ k =>
    rw [(tangent I M).extDeriv_succ_apply_sections,
      (mextDerivₗ I (k + 1) φ).toContMDiffSection_apply x, mextDerivₗ_apply,
      TauCeti.mextDeriv_apply_vectorField (φ.mdifferentiableAt x)
        (fun i ↦ (V i).contMDiff.mdifferentiableAt (by simp)),
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [anchorDeriv_apply, tangent_anchor_apply]; congr 3; ext y
      simp only [ContMDiffSection.scalarAlternatingEquiv_apply, SmoothForm.toContMDiffSection_apply]
      congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [φ.toContMDiffSection_apply x, tangent_bracket_apply, pow_succ, mul_neg, mul_one, neg_smul]

/-- `tangentCochainEquiv` intertwines the de Rham exterior derivative `TauCeti.mextDerivₗ` with
`extDeriv` on `LieAlgebroid.tangent I M`. -/
theorem extDeriv_tangentCochainEquiv {k : ℕ} (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k (tangentCochainEquiv k φ) =
      tangentCochainEquiv (k + 1) (mextDerivₗ I k φ) :=
  tangent_extDeriv_toContMDiffSection φ

end TauCeti.LieAlgebroid
