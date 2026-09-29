/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Basic

/-!
# The Lyapunov--Perron integral as a bounded linear operator

The two integral terms of the Lyapunov--Perron equation act linearly on a bounded continuous
forcing term on the nonnegative time axis. An exponential dichotomy bounds this operator in the
sup norm by `2 K / α`. This is the linear part of the derivative of the Lyapunov--Perron map;
packaging it as a continuous linear map makes the implicit-function argument for smooth stable
and unstable manifolds possible.

The integral and dichotomy estimates follow Coppel, *Dichotomies in Stability Theory*,
Chapter 5.
-/

public section

open MeasureTheory NormedSpace
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {A P : X →L[ℝ] X} {K α : ℝ≥0}

private theorem lyapunovPerronMap_id_apply
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (γ : ℝ≥0 →ᵇ X) (t : ℝ≥0) :
    lyapunovPerronMap A P id hs hu hα LipschitzWith.id 0 γ t =
      lyapunovPerronIntegral A P (fun s ↦ γ s.toNNReal) t := by
  simp [lyapunovPerronMap_apply]

/-- The integral part of the Lyapunov--Perron equation, acting on bounded continuous curves on
`[0, ∞)`. Its value at `t` is the forward integral in the stable directions minus the improper
backward integral in the complementary directions. -/
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
        simp only [F, lyapunovPerronMap_id_apply]
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
        simpa only [BoundedContinuousFunction.add_apply, lyapunovPerronMap_id_apply,
          add_comm] using eq_add_of_sub_eq h
      map_smul' := by
        intro c γ
        ext t
        simp only [F, lyapunovPerronMap_id_apply, BoundedContinuousFunction.smul_apply,
          RingHom.id_apply]
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
  exact lyapunovPerronMap_id_apply hs hu hα γ t

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
