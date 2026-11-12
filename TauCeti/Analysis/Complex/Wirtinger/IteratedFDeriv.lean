/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# Iterated derivatives of a Wirtinger derivative on the plane

For `g : ℂ → F`, the function `w ↦ ∂g(w) 1` is the image of the real derivative `Dg` under the
fixed real-linear map `φ ↦ (φ 1 - i φ i) / 2` of norm at most one. Consequently its derivative of
order `i` is the derivative of order `i + 1` of `g`, curried on the right and followed by this
map. Derivative bounds for `g` therefore pass to `∂g(·) 1` with constant one.

## Main declarations

* `TauCeti.wirtingerOne`: the map `φ ↦ (φ 1 - i φ i) / 2`, with `‖wirtingerOne‖ ≤ 1`.
* `TauCeti.wirtingerOneCurryRight i`: the map from `(i + 1)`-multilinear maps to `i`-multilinear
  maps obtained by currying on the right and applying `wirtingerOne`; it does not increase norms.
* `TauCeti.wirtingerDeriv_one_eq_comp`: `(fun w ↦ ∂g(w) 1) = wirtingerOne ∘ Dg`.
* `TauCeti.iteratedFDeriv_wirtingerDeriv_one`: for `g` of class `C^{i+1}`,
  `D^i (∂g(·) 1) = wirtingerOneCurryRight i (D^{i+1} g)`.
-/

public noncomputable section

open Complex

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

/-- The complex-linear part of a real-linear map `φ : ℂ → F`, evaluated at `1`:
`φ ↦ (φ 1 - i φ i) / 2`. Applied to `D g x` it gives `∂ g x 1`. -/
def wirtingerOne : (ℂ →L[ℝ] F) →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun φ := (2 : ℂ)⁻¹ • (φ 1 - I • φ (I • 1))
      map_add' φ ψ := by
        simp only [FunLike.coe_add, Pi.add_apply, smul_add, smul_sub]
        abel
      map_smul' a φ := by
        simp only [FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply]
        rw [smul_comm I a, ← smul_sub]
        exact smul_comm _ _ _ }
    1 fun φ ↦ by
      have h1 : ‖-(I • φ (I • 1))‖ ≤ ‖φ‖ := by
        rw [norm_neg, norm_smul, norm_I, one_mul]
        have h := φ.le_opNorm (I • (1 : ℂ))
        rwa [norm_smul, norm_I, norm_one, mul_one, mul_one] at h
      have h2 : ‖φ 1‖ ≤ ‖φ‖ := by simpa using φ.le_opNorm 1
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul, sub_eq_add_neg]
      exact norm_two_inv_smul_add_le h2 h1

@[simp]
theorem wirtingerOne_apply (φ : ℂ →L[ℝ] F) :
    wirtingerOne φ = (2 : ℂ)⁻¹ • (φ 1 - I • φ (I • 1)) :=
  (rfl)

theorem norm_wirtingerOne_le : ‖(wirtingerOne : (ℂ →L[ℝ] F) →L[ℝ] F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The derivative of order `i` of `∂ g (·) 1` in terms of the derivative of order `i + 1` of
`g`: curry on the right, then apply `wirtingerOne`. -/
def wirtingerOneCurryRight (i : ℕ) : (ℂ [×i + 1]→L[ℝ] F) →L[ℝ] (ℂ [×i]→L[ℝ] F) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ ℂ) (ℂ →L[ℝ] F) F
      wirtingerOne).comp
    (continuousMultilinearCurryRightEquiv' ℝ i ℂ F).toContinuousLinearEquiv.toContinuousLinearMap

theorem wirtingerOneCurryRight_apply (i : ℕ) (Φ : ℂ [×i + 1]→L[ℝ] F) :
    wirtingerOneCurryRight i Φ =
      wirtingerOne.compContinuousMultilinearMap (continuousMultilinearCurryRightEquiv' ℝ i ℂ F Φ) :=
  (rfl)

theorem norm_wirtingerOneCurryRight_apply_le (i : ℕ) (Φ : ℂ [×i + 1]→L[ℝ] F) :
    ‖wirtingerOneCurryRight i Φ‖ ≤ ‖Φ‖ := by
  have h := ContinuousLinearMap.norm_compContinuousMultilinearMap_le
    (wirtingerOne : (ℂ →L[ℝ] F) →L[ℝ] F) (continuousMultilinearCurryRightEquiv' ℝ i ℂ F Φ)
  rw [LinearIsometryEquiv.norm_map] at h
  rw [wirtingerOneCurryRight_apply]
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) norm_wirtingerOne_le)

/-- The function `w ↦ ∂ g w 1` is `wirtingerOne` applied to the real derivative of `g`. -/
theorem wirtingerDeriv_one_eq_comp (g : ℂ → F) :
    (fun w ↦ wirtingerDeriv g w 1) = (wirtingerOne : (ℂ →L[ℝ] F) →L[ℝ] F) ∘ fderiv ℝ g := by
  -- The real action is uniquely determined by the compatible complex action.
  cases NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ) (E := F)
  exact funext fun w ↦ by rw [Function.comp_apply, wirtingerOne_apply, wirtingerDeriv_apply]

/-- **The iterated derivatives of `∂ g (·) 1`.** For `g` of class `C^{i+1}`, the derivative of
order `i` of `w ↦ ∂ g w 1` is the image of the derivative of order `i + 1` of `g` under the fixed
map `wirtingerOneCurryRight i`. -/
theorem iteratedFDeriv_wirtingerDeriv_one {g : ℂ → F} {i : ℕ}
    (hg : ContDiff ℝ (i + 1 : ℕ) g) (x : ℂ) :
    iteratedFDeriv ℝ i (fun w ↦ wirtingerDeriv g w 1) x =
      wirtingerOneCurryRight i (iteratedFDeriv ℝ (i + 1) g x) := by
  have hD : ContDiff ℝ i (fderiv ℝ g) := hg.fderiv_right (by push_cast; exact le_rfl)
  rw [wirtingerDeriv_one_eq_comp, wirtingerOne.iteratedFDeriv_comp_left hD.contDiffAt le_rfl,
    iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, wirtingerOneCurryRight_apply,
    LinearIsometryEquiv.apply_symm_apply]

end TauCeti
