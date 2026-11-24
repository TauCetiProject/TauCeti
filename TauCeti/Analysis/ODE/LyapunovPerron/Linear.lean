/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Basic

/-!
# The linear operators of the Lyapunov--Perron equation

The homogeneous term sends the initial parameter to its forward evolution under the linear flow
and is bounded in the sup norm by `K` times the norm of the parameter. The two integral terms act
linearly on a bounded continuous forcing term on the nonnegative time axis. Forward and backward
exponential estimates bound the integral operator in the sup norm by `2 K / α`. Packaging these
terms as continuous linear maps makes the implicit-function argument for smooth stable and
unstable manifolds possible.

The integral and exponential estimates follow Coppel, *Dichotomies in Stability Theory*,
Chapter 5.
-/

public section

open MeasureTheory NormedSpace
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

section Homogeneous

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K α : ℝ≥0} {A P : X →L[ℝ] X}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)

omit [CompleteSpace X] in
include hs in
/-- The homogeneous term of the Lyapunov--Perron equation is bounded by `K ‖ξ‖` in forward
time. -/
private theorem norm_exp_smul_apply_le (ξ : X) (t : ℝ≥0) :
    ‖exp ((t : ℝ) • A) (P ξ)‖ ≤ K * ‖ξ‖ :=
  calc ‖exp ((t : ℝ) • A) (P ξ)‖ ≤ K * Real.exp (-α * t) * ‖ξ‖ := hs t t.property ξ
    _ ≤ K * 1 * ‖ξ‖ := by
      gcongr
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.2 α.coe_nonneg) t.property)
    _ = K * ‖ξ‖ := by ring

/-- The homogeneous term `ξ ↦ (t ↦ exp (t A) (P ξ))` of the Lyapunov--Perron equation, as a
bounded linear map into bounded continuous curves on `[0, ∞)`. -/
def lyapunovPerronHomogeneousCLM : X →L[ℝ] (ℝ≥0 →ᵇ X) :=
  LinearMap.mkContinuous
    { toFun := fun ξ ↦ BoundedContinuousFunction.ofNormedAddCommGroup
        (fun t : ℝ≥0 ↦ exp ((t : ℝ) • A) (P ξ))
        (((differentiable_exp_smul_const ℝ A).continuous.comp NNReal.continuous_coe).clm_apply
          continuous_const)
        (K * ‖ξ‖) (norm_exp_smul_apply_le hs ξ)
      map_add' := fun ξ ζ ↦ by ext t; simp
      map_smul' := fun c ξ ↦ by ext t; simp }
    K fun ξ ↦ BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity)
      (norm_exp_smul_apply_le hs ξ)

/-- The homogeneous term is the decaying linear evolution of the stable coordinate. -/
@[simp]
theorem lyapunovPerronHomogeneousCLM_apply (ξ : X) (t : ℝ≥0) :
    lyapunovPerronHomogeneousCLM hs ξ t = exp ((t : ℝ) • A) (P ξ) :=
  (rfl)

end Homogeneous

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {A P : X →L[ℝ] X} {K α : ℝ≥0}

/-- The integral part of the Lyapunov--Perron equation, acting on bounded continuous curves on
`[0, ∞)`. Its value at `t` is the forward integral of the `P` component minus the improper
backward integral of the remainder `v - P v`. -/
def lyapunovPerronIntegralCLM
    (A P : X →L[ℝ] X)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) : (ℝ≥0 →ᵇ X) →L[ℝ] (ℝ≥0 →ᵇ X) :=
  let F : (ℝ≥0 →ᵇ X) → (ℝ≥0 →ᵇ X) :=
    lyapunovPerronMap A P id hs hu hα LipschitzWith.id 0
  let L : (ℝ≥0 →ᵇ X) →ₗ[ℝ] (ℝ≥0 →ᵇ X) :=
    { toFun := F
      map_add' := by
        intro γ η
        ext t
        simp only [F, lyapunovPerronMap_apply, map_zero, zero_add, id_eq]
        have hc (ζ : ℝ≥0 →ᵇ X) : Continuous fun s : ℝ ↦ ζ s.toNNReal :=
          ζ.continuous.comp continuous_real_toNNReal
        have hb (ζ : ℝ≥0 →ᵇ X) (s : ℝ) : ‖ζ s.toNNReal‖ ≤ ‖ζ‖ :=
          ζ.norm_coe_le_norm _
        have h := lyapunovPerronIntegral_sub hu hα
          (hc (γ + η)) (hb (γ + η)) (hc γ) (hb γ) (t : ℝ)
        have hfun : (fun s : ℝ ↦ (γ + η) s.toNNReal) -
            (fun s : ℝ ↦ γ s.toNNReal) = (fun s : ℝ ↦ η s.toNNReal) := by
          funext s
          simp
        rw [hfun] at h
        simpa only [_root_.add_apply, lyapunovPerronMap_apply,
          map_zero, zero_add, id_eq, add_comm] using eq_add_of_sub_eq h
      map_smul' := by
        intro c γ
        ext t
        simp only [F, lyapunovPerronMap_apply, map_zero, zero_add, id_eq,
          _root_.smul_apply, RingHom.id_apply]
        rw [← lyapunovPerronIntegral_smul]
        rfl }
  L.mkContinuous (2 * K / α) (fun γ ↦ by
    have h : dist (F γ) (F 0) ≤ 2 * K * (1 : ℝ≥0) / α * dist γ 0 :=
      dist_lyapunovPerronMap_le hs hu hα LipschitzWith.id 0 γ 0
    have hzero : F 0 = 0 := L.map_zero
    -- `L` is the linear structure on the function `F`.
    change ‖F γ‖ ≤ 2 * K / α * ‖γ‖
    simpa only [hzero, dist_zero_right, NNReal.coe_one, mul_one] using h)

/-- Evaluation of the bounded linear Lyapunov--Perron integral. -/
@[simp]
theorem lyapunovPerronIntegralCLM_apply
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (γ : ℝ≥0 →ᵇ X) (t : ℝ≥0) :
    lyapunovPerronIntegralCLM A P hs hu hα γ t =
      lyapunovPerronIntegral A P (fun s ↦ γ s.toNNReal) t := by
  simp [lyapunovPerronIntegralCLM, lyapunovPerronMap_apply]

/-- The Lyapunov--Perron integral has sup-operator norm at most `2 K / α`. -/
theorem norm_lyapunovPerronIntegralCLM_le
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) :
    ‖lyapunovPerronIntegralCLM A P hs hu hα‖ ≤ 2 * K / α := by
  unfold lyapunovPerronIntegralCLM
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end ContinuousLinearMap

end
