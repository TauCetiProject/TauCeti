/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting
-- Private: the exponential integrals, the splitting of exponentials, and the product rule are used
-- only inside the proofs below.
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# The Lyapunov--Perron fixed point

Let `A` be a bounded operator on a real Banach space `X` and let `P` be a bounded operator such
that the linear flow `exp (t A)` damps `P v` exponentially in forward time and `v - P v`
exponentially in backward time, with constant `K` and rate `α > 0`:

`‖exp (t A) (P v)‖ ≤ K exp (-α t) ‖v‖` for `t ≥ 0`, and
`‖exp (t A) (v - P v)‖ ≤ K exp (α t) ‖v‖` for `t ≤ 0`.

These are the two estimates carried by an exponential dichotomy of `y' = A y`, but nothing below
needs `P` to be idempotent or to commute with `A`: they are used here purely as a forward and a
backward exponential estimate, and `P v` and `v - P v` are not assumed to be the components of a
splitting. For a globally `ε`-Lipschitz nonlinearity `N`, the *Lyapunov--Perron integral equation*

`y t = exp (t A) (P ξ) + ∫₀ᵗ exp ((t - s) A) (P (N (y s))) ds
  - ∫ₜ^∞ exp ((t - s) A) (N (y s) - P (N (y s))) ds`

builds a bounded forward solution of `y' = A y + N y` from the input parameter `ξ`.

This file shows that when `2 K ε < α` the right-hand side is a contraction of the complete space
of bounded continuous functions on `[0, ∞)`. Its unique fixed point
`ContinuousLinearMap.lyapunovPerronSolution` depends Lipschitz-continuously on `ξ` and solves
`y' = A y + N y` on `[0, ∞)`. The converse is *not* proved here: this file does not show that
every bounded forward solution satisfies the integral equation, which needs `P` to be idempotent
and to commute with `A` and is left to a later file. What is proved is the analytic core of the
Lyapunov--Perron proof of the stable-manifold theorem at a hyperbolic equilibrium, where the local
stable manifold is read off from the initial values of these fixed points after the nonlinearity
has been cut off.

## Main declarations

* `ContinuousLinearMap.lyapunovPerronIntegral`: the two integral terms of the equation, for an
  arbitrary forcing term `g`.
* `ContinuousLinearMap.hasDerivAt_lyapunovPerronIntegral`: the integral terms solve the forced
  linear equation `y' = A y + g`.
* `ContinuousLinearMap.norm_lyapunovPerronIntegral_le`: under the forward and backward
  exponential estimates, a forcing term bounded by `M` produces integral terms bounded by
  `2 K M / α` in forward time.
* `ContinuousLinearMap.lyapunovPerronMap`: the Lyapunov--Perron operator on bounded continuous
  functions on `[0, ∞)`.
* `ContinuousLinearMap.contractingWith_lyapunovPerronMap`: it is a contraction when `2 K ε < α`.
* `ContinuousLinearMap.lyapunovPerronSolution`: its unique fixed point.
* `ContinuousLinearMap.lipschitzWith_lyapunovPerronSolution`: the fixed point is Lipschitz in `ξ`.
* `ContinuousLinearMap.isIntegralCurveOn_lyapunovPerronSolution`: the fixed point solves
  `y' = A y + N y` on `[0, ∞)`.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics 629, Springer,
  1978, Chapter 5.
* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  Section 4.3.
-/

public section

open Filter MeasureTheory NormedSpace Set Topology
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The integral terms of the Lyapunov--Perron equation with forcing term `g`:

`∫₀ᵗ exp ((t - s) A) (P (g s)) ds - ∫ₜ^∞ exp ((t - s) A) (g s - P (g s)) ds`.

The first integral propagates the part `P (g s)` of the forcing forward from time `0`; the second
propagates the remaining part `g s - P (g s)` backward from time `∞`. -/
def lyapunovPerronIntegral (A P : X →L[ℝ] X) (g : ℝ → X) (t : ℝ) : X :=
  (∫ s in (0 : ℝ)..t, exp ((t - s) • A) (P (g s))) -
    ∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))

variable [CompleteSpace X]

variable {A P : X →L[ℝ] X} {K α : ℝ≥0} {M : ℝ} {g g₁ g₂ : ℝ → X} {t : ℝ}

section Estimates

variable (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
include hu

omit [CompleteSpace X] in
/-- The pointwise exponential bound on the unstable integrand. -/
private theorem norm_unstable_integrand_le {s : ℝ} (hs : t < s) (hgs : ‖g s‖ ≤ M) :
    ‖exp ((t - s) • A) (g s - P (g s))‖ ≤
      K * M * Real.exp (α * t) * Real.exp (-α * s) := by
  calc ‖exp ((t - s) • A) (g s - P (g s))‖
      ≤ K * Real.exp (α * (t - s)) * ‖g s‖ := hu _ (sub_nonpos.2 hs.le) _
    _ ≤ K * Real.exp (α * (t - s)) * M := by gcongr
    _ = K * M * Real.exp (α * t) * Real.exp (-α * s) := by
      rw [mul_sub, sub_eq_add_neg, Real.exp_add, neg_mul]; ring

/-- Under the backward exponential estimate, a forcing term that is continuous and bounded by `M`
on `(t, ∞)` makes the unstable integrand of the Lyapunov--Perron equation integrable there. -/
theorem integrableOn_lyapunovPerron_unstable (hα : 0 < α) (t : ℝ) (hg : ContinuousOn g (Ioi t))
    (hgM : ∀ s ∈ Ioi t, ‖g s‖ ≤ M) :
    IntegrableOn (fun s ↦ exp ((t - s) • A) (g s - P (g s))) (Ioi t) := by
  have hbound : IntegrableOn (fun s ↦ K * M * Real.exp (α * t) * Real.exp (-α * s)) (Ioi t) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (NNReal.coe_pos.2 hα)) t).const_mul _
  refine hbound.mono' ?_ ?_
  · exact ((((differentiable_exp_smul_const ℝ A).continuous.comp
      (continuous_const.sub continuous_id)).continuousOn.clm_apply
        (hg.sub (P.continuous.comp_continuousOn' hg))).aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact norm_unstable_integrand_le hu hs (hgM s hs)

omit [CompleteSpace X] in
/-- Under the backward exponential estimate, the unstable integral of a forcing term bounded by
`M` on `(t, ∞)` is bounded by `K M / α`. -/
theorem norm_setIntegral_lyapunovPerron_unstable_le (hα : 0 < α) (t : ℝ)
    (hgM : ∀ s ∈ Ioi t, ‖g s‖ ≤ M) :
    ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖ ≤ K * M / α := by
  have hα' : (0 : ℝ) < α := NNReal.coe_pos.2 hα
  have hbound : IntegrableOn (fun s ↦ K * M * Real.exp (α * t) * Real.exp (-α * s)) (Ioi t) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hα') t).const_mul _
  calc ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖
      ≤ ∫ s in Ioi t, K * M * Real.exp (α * t) * Real.exp (-α * s) :=
        norm_integral_le_of_norm_le hbound <| (ae_restrict_mem measurableSet_Ioi).mono
          fun s hs ↦ norm_unstable_integrand_le hu hs (hgM s hs)
    _ = K * M / α := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hα'), neg_div_neg_eq,
        mul_div_assoc', mul_assoc, ← Real.exp_add]
      simp

end Estimates

omit [CompleteSpace X] in
/-- Under the forward exponential estimate, the stable integral of a forcing term bounded by `M`
on `[0, t]` is bounded by `K M / α` in forward time. -/
theorem norm_intervalIntegral_lyapunovPerron_stable_le
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hα : 0 < α) (ht : 0 ≤ t) (hgM : ∀ s ∈ Icc (0 : ℝ) t, ‖g s‖ ≤ M) :
    ‖∫ s in (0 : ℝ)..t, exp ((t - s) • A) (P (g s))‖ ≤ K * M / α := by
  have hα' : (0 : ℝ) < α := NNReal.coe_pos.2 hα
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgM 0 ⟨le_rfl, ht⟩)
  -- Splitting the kernel into a factor depending on `t` and one depending on the integration
  -- variable `s` turns the estimate into an ordinary exponential integral.
  have hsplit (s : ℝ) : Real.exp (-α * (t - s)) = Real.exp (-α * t) * Real.exp (α * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (-α * t) * (Real.exp (α * t) - 1) ≤ 1 := by
    rw [mul_sub, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one]
    linarith [Real.exp_pos (-(α * t))]
  calc ‖∫ s in (0 : ℝ)..t, exp ((t - s) • A) (P (g s))‖
      ≤ ∫ s in (0 : ℝ)..t, K * M * Real.exp (-α * t) * Real.exp (α * s) := by
        have hcont : Continuous fun s : ℝ ↦ K * M * Real.exp (-α * t) * Real.exp (α * s) := by
          fun_prop
        refine intervalIntegral.norm_integral_le_of_norm_le ht (ae_of_all _ fun s hs' ↦ ?_)
          (hcont.intervalIntegrable 0 t)
        calc ‖exp ((t - s) • A) (P (g s))‖
            ≤ K * Real.exp (-α * (t - s)) * ‖g s‖ := hs _ (sub_nonneg.2 hs'.2) _
          _ ≤ K * Real.exp (-α * (t - s)) * M := by gcongr; exact hgM s ⟨hs'.1.le, hs'.2⟩
          _ = K * M * Real.exp (-α * t) * Real.exp (α * s) := by rw [hsplit]; ring
    _ = K * M / α * (Real.exp (-α * t) * (Real.exp (α * t) - 1)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left (fun s ↦ Real.exp s) hα'.ne', integral_exp,
        mul_zero, Real.exp_zero, smul_eq_mul]
      field_simp
    _ ≤ K * M / α * 1 := by gcongr
    _ = K * M / α := mul_one _

omit [CompleteSpace X] in
/-- Under the forward and backward exponential estimates, the integral terms of the
Lyapunov--Perron equation with a forcing term bounded by `M` are bounded by `2 K M / α` in
forward time. -/
theorem norm_lyapunovPerronIntegral_le
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hgM : ∀ s, ‖g s‖ ≤ M) (ht : 0 ≤ t) :
    ‖lyapunovPerronIntegral A P g t‖ ≤ 2 * K * M / α := by
  rw [lyapunovPerronIntegral]
  refine (norm_sub_le _ _).trans ?_
  have h₁ := norm_intervalIntegral_lyapunovPerron_stable_le hs hα ht fun s _ ↦ hgM s
  have h₂ := norm_setIntegral_lyapunovPerron_unstable_le hu hα t fun s _ ↦ hgM s
  calc _ ≤ K * M / α + K * M / α := add_le_add h₁ h₂
    _ = 2 * K * M / α := by ring

section Derivative

variable (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
include hu

/-- The integral terms of the Lyapunov--Perron equation are linear in the forcing term. -/
theorem lyapunovPerronIntegral_sub (hα : 0 < α) (hg₁ : Continuous g₁) (hg₁M : ∀ s, ‖g₁ s‖ ≤ M)
    (hg₂ : Continuous g₂) {M₂ : ℝ} (hg₂M : ∀ s, ‖g₂ s‖ ≤ M₂) (t : ℝ) :
    lyapunovPerronIntegral A P g₁ t - lyapunovPerronIntegral A P g₂ t =
      lyapunovPerronIntegral A P (g₁ - g₂) t := by
  have hstable (s : ℝ) : exp ((t - s) • A) (P ((g₁ - g₂) s)) =
      exp ((t - s) • A) (P (g₁ s)) - exp ((t - s) • A) (P (g₂ s)) := by
    simp only [Pi.sub_apply, map_sub]
  have hunstable (s : ℝ) : exp ((t - s) • A) ((g₁ - g₂) s - P ((g₁ - g₂) s)) =
      exp ((t - s) • A) (g₁ s - P (g₁ s)) - exp ((t - s) • A) (g₂ s - P (g₂ s)) := by
    simp only [Pi.sub_apply, map_sub]
    abel
  have hcont (g : ℝ → X) (hg : Continuous g) :
      Continuous fun s ↦ exp ((t - s) • A) (P (g s)) :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp
      (continuous_const.sub continuous_id)).clm_apply (P.continuous.comp hg)
  simp only [lyapunovPerronIntegral, hstable, hunstable]
  rw [intervalIntegral.integral_sub ((hcont _ hg₁).intervalIntegrable _ _)
    ((hcont _ hg₂).intervalIntegrable _ _),
    integral_sub (integrableOn_lyapunovPerron_unstable hu hα t hg₁.continuousOn fun s _ ↦ hg₁M s)
      (integrableOn_lyapunovPerron_unstable hu hα t hg₂.continuousOn fun s _ ↦ hg₂M s)]
  abel

/-- Under the backward exponential estimate, the integral terms of the Lyapunov--Perron equation
solve the forced linear equation `y' = A y + g`. -/
theorem hasDerivAt_lyapunovPerronIntegral (hα : 0 < α) (hg : Continuous g)
    (hgM : ∀ s, ‖g s‖ ≤ M) (t : ℝ) :
    HasDerivAt (lyapunovPerronIntegral A P g) (A (lyapunovPerronIntegral A P g t) + g t) t := by
  have hexp_apply (u s : ℝ) (v : X) :
      exp (u • A) (exp (s • A) v) = exp ((u + s) • A) v := by
    rw [TauCeti.exp_add_smul, comp_apply]
  -- After pulling `exp (u A)` out of both integrals, the integrands no longer depend on `u`.
  set hp : ℝ → X := fun s ↦ exp ((-s) • A) (P (g s)) with hp_def
  set hq : ℝ → X := fun s ↦ exp ((-s) • A) (g s - P (g s)) with hq_def
  have hp_cont : Continuous hp :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_apply
      (P.continuous.comp hg)
  have hq_cont : Continuous hq :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_apply
      (hg.sub (P.continuous.comp hg))
  have hq_int (u : ℝ) : IntegrableOn hq (Ioi u) := by
    refine ((exp ((-u) • A)).integrable_comp (integrableOn_lyapunovPerron_unstable hu hα u
      hg.continuousOn fun s _ ↦ hgM s)).congr (ae_of_all _ fun s ↦ ?_)
    simp only [hq_def, hexp_apply]
    congr 3
    ring
  have hstable (u : ℝ) : (∫ s in (0 : ℝ)..u, exp ((u - s) • A) (P (g s))) =
      exp (u • A) (∫ s in (0 : ℝ)..u, hp s) := by
    rw [← (exp (u • A)).intervalIntegral_comp_comm (hp_cont.intervalIntegrable _ _)]
    simp only [hp_def, hexp_apply, sub_eq_add_neg]
  have hunstable (u : ℝ) : (∫ s in Ioi u, exp ((u - s) • A) (g s - P (g s))) =
      exp (u • A) ((∫ s in Ioi 0, hq s) - ∫ s in (0 : ℝ)..u, hq s) := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' (hq_int 0) (hq_int u), sub_sub_cancel,
      ← (exp (u • A)).integral_comp_comm (hq_int u)]
    simp only [hq_def, hexp_apply, sub_eq_add_neg]
  have hfun : lyapunovPerronIntegral A P g = fun u ↦
      exp (u • A) (∫ s in (0 : ℝ)..u, hp s) -
        exp (u • A) ((∫ s in Ioi 0, hq s) - ∫ s in (0 : ℝ)..u, hq s) := by
    ext u
    rw [lyapunovPerronIntegral, hstable, hunstable]
  have hexp := hasDerivAt_exp_smul_const' A t
  have hP := hexp.clm_apply (intervalIntegral.integral_hasDerivAt_right
    (hp_cont.intervalIntegrable 0 t) (hp_cont.stronglyMeasurableAtFilter _ _)
    hp_cont.continuousAt)
  have hQ := hexp.clm_apply ((hasDerivAt_const t (∫ s in Ioi 0, hq s)).sub
    (intervalIntegral.integral_hasDerivAt_right (hq_cont.intervalIntegrable 0 t)
      (hq_cont.stronglyMeasurableAtFilter _ _) hq_cont.continuousAt))
  have hpt : exp (t • A) (hp t) = P (g t) := by
    simp only [hp_def, hexp_apply, add_neg_cancel, zero_smul, exp_zero,
      one_apply_eq_self]
  have hqt : exp (t • A) (hq t) = g t - P (g t) := by
    simp only [hq_def, hexp_apply, add_neg_cancel, zero_smul, exp_zero,
      one_apply_eq_self]
  rw [hfun]
  refine (hP.sub hQ).congr_deriv ?_
  simp only [Pi.sub_apply, mul_apply_eq_comp, zero_sub, map_neg, hpt, hqt, map_sub]
  abel

end Derivative

/-- Under the backward exponential estimate, the integral terms of the Lyapunov--Perron equation
are continuous in time. -/
theorem continuous_lyapunovPerronIntegral
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) :
    Continuous (lyapunovPerronIntegral A P g) :=
  continuous_iff_continuousAt.2 fun t ↦
    (hasDerivAt_lyapunovPerronIntegral hu hα hg hgM t).continuousAt

section Contraction

variable {N : X → X} {ε : ℝ≥0}

variable
  (A P : X →L[ℝ] X) (N : X → X)
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hN : LipschitzWith ε N)

/-- The **Lyapunov--Perron operator** of `y' = A y + N y` with input parameter `ξ`, acting on
bounded continuous functions on `[0, ∞)`:

`γ ↦ (t ↦ exp (t A) (P ξ) + lyapunovPerronIntegral A P (N ∘ γ) t)`.

Here `P ξ` is only the parameter in the homogeneous term. Without projection and commutation
hypotheses on `P`, it is not identified with `P (y 0)`. -/
def lyapunovPerronMap (ξ : X) (γ : ℝ≥0 →ᵇ X) : ℝ≥0 →ᵇ X :=
  have hg_continuous : Continuous fun s : ℝ ↦ N (γ s.toNNReal) :=
    ((γ.comp N hN).compContinuous
      ⟨Real.toNNReal, continuous_real_toNNReal⟩).continuous
  have hgM (s : ℝ) : ‖N (γ s.toNNReal)‖ ≤ ‖N 0‖ + ε * ‖γ‖ :=
    ((γ.comp N hN).norm_coe_le_norm s.toNNReal).trans
      (TauCeti.norm_boundedContinuousFunction_comp_le hN γ)
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ≥0 ↦ exp ((t : ℝ) • A) (P ξ) +
      lyapunovPerronIntegral A P (fun s ↦ N (γ s.toNNReal)) t)
    ((((differentiable_exp_smul_const ℝ A).continuous.comp NNReal.continuous_coe).clm_apply
      continuous_const).add
      ((continuous_lyapunovPerronIntegral hu hα hg_continuous hgM).comp
        NNReal.continuous_coe))
    (K * ‖ξ‖ + 2 * K * (‖N 0‖ + ε * ‖γ‖) / α)
    fun t ↦ by
      refine (norm_add_le _ _).trans (add_le_add ?_
        (norm_lyapunovPerronIntegral_le hs hu hα hgM t.2))
      calc ‖exp ((t : ℝ) • A) (P ξ)‖ ≤ K * Real.exp (-α * t) * ‖ξ‖ := hs t t.2 ξ
        _ ≤ K * 1 * ‖ξ‖ := by
          gcongr
          exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.2 α.coe_nonneg) t.2)
        _ = K * ‖ξ‖ := by ring

variable {A P N}

@[simp]
theorem lyapunovPerronMap_apply (ξ : X) (γ : ℝ≥0 →ᵇ X) (t : ℝ≥0) :
    lyapunovPerronMap A P N hs hu hα hN ξ γ t =
      exp ((t : ℝ) • A) (P ξ) + lyapunovPerronIntegral A P (fun s ↦ N (γ s.toNNReal)) t :=
  (rfl)

/-- The Lyapunov--Perron operator is `2 K ε / α`-Lipschitz. -/
theorem dist_lyapunovPerronMap_le (ξ : X) (γ η : ℝ≥0 →ᵇ X) :
    dist (lyapunovPerronMap A P N hs hu hα hN ξ γ) (lyapunovPerronMap A P N hs hu hα hN ξ η) ≤
      2 * K * ε / α * dist γ η := by
  have hcontinuous (ζ : ℝ≥0 →ᵇ X) : Continuous fun s : ℝ ↦ N (ζ s.toNNReal) :=
    ((ζ.comp N hN).compContinuous
      ⟨Real.toNNReal, continuous_real_toNNReal⟩).continuous
  have hbound (ζ : ℝ≥0 →ᵇ X) (s : ℝ) : ‖N (ζ s.toNNReal)‖ ≤ ‖N 0‖ + ε * ‖ζ‖ :=
    ((ζ.comp N hN).norm_coe_le_norm s.toNNReal).trans
      (TauCeti.norm_boundedContinuousFunction_comp_le hN ζ)
  refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun t ↦ ?_
  have hdiff (s : ℝ) : ‖(fun s ↦ N (γ s.toNNReal)) s - (fun s ↦ N (η s.toNNReal)) s‖ ≤
      ε * dist γ η := by
    rw [← dist_eq_norm]
    exact hN.dist_le_mul_of_le (BoundedContinuousFunction.dist_coe_le_dist _)
  rw [lyapunovPerronMap_apply, lyapunovPerronMap_apply, dist_eq_norm, add_sub_add_left_eq_sub,
    lyapunovPerronIntegral_sub hu hα (hcontinuous γ) (hbound γ)
      (hcontinuous η) (hbound η)]
  calc _ ≤ 2 * K * (ε * dist γ η) / α := norm_lyapunovPerronIntegral_le hs hu hα hdiff t.2
    _ = 2 * K * ε / α * dist γ η := by ring

/-- When `2 K ε < α`, the Lyapunov--Perron operator is a contraction. -/
theorem contractingWith_lyapunovPerronMap (hsmall : 2 * K * ε < α) (ξ : X) :
    ContractingWith (2 * K * ε / α) (lyapunovPerronMap A P N hs hu hα hN ξ) :=
  ⟨(div_lt_one hα).2 hsmall, LipschitzWith.of_dist_le_mul fun γ η ↦ by
    simpa using dist_lyapunovPerronMap_le hs hu hα hN ξ γ η⟩

/-- Changing the input parameter moves the Lyapunov--Perron operator by at most `K ‖ξ - ζ‖`. -/
theorem dist_lyapunovPerronMap_lyapunovPerronMap_le (ξ ζ : X) (γ : ℝ≥0 →ᵇ X) :
    dist (lyapunovPerronMap A P N hs hu hα hN ξ γ) (lyapunovPerronMap A P N hs hu hα hN ζ γ) ≤
      K * dist ξ ζ := by
  refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun t ↦ ?_
  rw [lyapunovPerronMap_apply, lyapunovPerronMap_apply, dist_eq_norm, add_sub_add_right_eq_sub,
    ← map_sub, ← map_sub, dist_eq_norm]
  calc _ ≤ K * Real.exp (-α * t) * ‖ξ - ζ‖ := hs t t.2 _
    _ ≤ K * 1 * ‖ξ - ζ‖ := by
      gcongr
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.2 α.coe_nonneg) t.2)
    _ = K * ‖ξ - ζ‖ := by ring

variable (A P N)

/-- The **Lyapunov--Perron solution** with input parameter `ξ`: the unique fixed point of the
Lyapunov--Perron operator, when `2 K ε < α`. -/
def lyapunovPerronSolution (hsmall : 2 * K * ε < α) (ξ : X) : ℝ≥0 →ᵇ X :=
  ContractingWith.fixedPoint _ (contractingWith_lyapunovPerronMap hs hu hα hN hsmall ξ)

variable {A P N} (hsmall : 2 * K * ε < α)

theorem isFixedPt_lyapunovPerronSolution (ξ : X) :
    Function.IsFixedPt (lyapunovPerronMap A P N hs hu hα hN ξ)
      (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ) :=
  ContractingWith.fixedPoint_isFixedPt _

/-- The Lyapunov--Perron solution satisfies the Lyapunov--Perron integral equation. -/
theorem lyapunovPerronSolution_apply (ξ : X) (t : ℝ≥0) :
    lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t =
      exp ((t : ℝ) • A) (P ξ) + lyapunovPerronIntegral A P
        (fun s ↦ N (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ s.toNNReal)) t := by
  conv_lhs => rw [← isFixedPt_lyapunovPerronSolution hs hu hα hN hsmall ξ]
  exact lyapunovPerronMap_apply hs hu hα hN ξ _ t

/-- The Lyapunov--Perron solution is the only bounded continuous solution of the
Lyapunov--Perron integral equation. -/
theorem eq_lyapunovPerronSolution {ξ : X} {γ : ℝ≥0 →ᵇ X}
    (hγ : ∀ t : ℝ≥0, γ t = exp ((t : ℝ) • A) (P ξ) +
      lyapunovPerronIntegral A P (fun s ↦ N (γ s.toNNReal)) t) :
    γ = lyapunovPerronSolution A P N hs hu hα hN hsmall ξ :=
  ContractingWith.fixedPoint_unique _ <| BoundedContinuousFunction.ext fun t ↦ (hγ t).symm

/-- The Lyapunov--Perron solution depends Lipschitz-continuously on the input parameter. -/
theorem lipschitzWith_lyapunovPerronSolution :
    LipschitzWith (K / (1 - 2 * K * ε / α)) (lyapunovPerronSolution A P N hs hu hα hN hsmall) := by
  have hlt : 2 * K * ε / α < 1 := (div_lt_one hα).2 hsmall
  refine LipschitzWith.of_dist_le_mul fun ξ ζ ↦ ?_
  have h := ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'
    (contractingWith_lyapunovPerronMap hs hu hα hN hsmall ξ) _
    (isFixedPt_lyapunovPerronSolution hs hu hα hN hsmall ξ)
    (isFixedPt_lyapunovPerronSolution hs hu hα hN hsmall ζ)
    (dist_lyapunovPerronMap_lyapunovPerronMap_le hs hu hα hN ξ ζ)
  rw [NNReal.coe_div, NNReal.coe_sub hlt.le, NNReal.coe_one]
  calc _ ≤ K * dist ξ ζ / (1 - ((2 * K * ε / α : ℝ≥0) : ℝ)) := h
    _ = _ := by ring

/-- If the nonlinearity vanishes at the origin, the Lyapunov--Perron solution with zero input
parameter is the zero solution. -/
@[simp]
theorem lyapunovPerronSolution_zero (hN0 : N 0 = 0) :
    lyapunovPerronSolution A P N hs hu hα hN hsmall 0 = 0 := by
  refine (eq_lyapunovPerronSolution hs hu hα hN hsmall fun t ↦ ?_).symm
  simp [lyapunovPerronIntegral, hN0]

/-- The Lyapunov--Perron solution solves `y' = A y + N y` on `[0, ∞)`. -/
theorem isIntegralCurveOn_lyapunovPerronSolution (ξ : X) :
    IsIntegralCurveOn (fun t ↦ lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t.toNNReal)
      (fun _ y ↦ A y + N y) (Ici 0) := by
  set γ := lyapunovPerronSolution A P N hs hu hα hN hsmall ξ
  set g : ℝ → X := fun s ↦ N (γ s.toNNReal)
  intro t ht
  have hg_continuous : Continuous g := by
    exact ((γ.comp N hN).compContinuous
      ⟨Real.toNNReal, continuous_real_toNNReal⟩).continuous
  have hg_bound (s : ℝ) : ‖g s‖ ≤ ‖N 0‖ + ε * ‖γ‖ := by
    dsimp only [g]
    exact ((γ.comp N hN).norm_coe_le_norm s.toNNReal).trans
      (TauCeti.norm_boundedContinuousFunction_comp_le hN γ)
  have hφ := ((hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t (P ξ))).add
    (hasDerivAt_lyapunovPerronIntegral hu hα hg_continuous hg_bound t)
  have heq (u : ℝ) (hu' : u ∈ Ici (0 : ℝ)) :
      γ u.toNNReal = exp (u • A) (P ξ) + lyapunovPerronIntegral A P g u := by
    rw [lyapunovPerronSolution_apply hs hu hα hN hsmall, Real.coe_toNNReal u hu']
  refine (hφ.hasDerivWithinAt.congr heq (heq t ht)).congr_deriv ?_
  simp only [g, heq t ht, map_add, map_zero, add_zero, mul_apply_eq_comp]
  abel

end Contraction

end ContinuousLinearMap
