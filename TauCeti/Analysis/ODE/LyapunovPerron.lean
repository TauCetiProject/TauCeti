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
import Mathlib.Analysis.ODE.ExistUnique
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
`y' = A y + N y` on `[0, ∞)`. Conversely, once `P` is idempotent and commutes with `A`, every
solution that stays bounded on `[0, ∞)` is the fixed point whose input parameter is its initial
value. The initial values of the bounded forward solutions are therefore exactly the points `x`
with `lyapunovPerronSolution x 0 = x`; their `P`-component is free and determines the rest
Lipschitz-continuously.

The fixed points also decay: for every rate `β ≥ 0` with `2 K ε < α - β`, two Lyapunov--Perron
solutions approach each other at rate `β`. When `N 0 = 0` every Lyapunov--Perron solution
therefore decays exponentially to the equilibrium `0`, and the bounded forward solutions are
exactly the forward solutions tending to `0`: the initial values above form the stable set of
the equilibrium. This is the analytic core of the Lyapunov--Perron proof of the stable-manifold
theorem at a hyperbolic equilibrium, where the local stable manifold is read off from the initial
values of these fixed points after the nonlinearity has been cut off.

## Main declarations

* `ContinuousLinearMap.lyapunovPerronIntegral`: the two integral terms of the equation, for an
  arbitrary forcing term `g`.
* `ContinuousLinearMap.hasDerivAt_lyapunovPerronIntegral`: the integral terms solve the forced
  linear equation `y' = A y + g`.
* `ContinuousLinearMap.norm_lyapunovPerronIntegral_le_mul_exp`: under the forward and backward
  exponential estimates, a forcing term bounded by `M exp (-β s)`, for `0 ≤ β < α`, produces
  integral terms bounded by `2 K M exp (-β t) / (α - β)` in forward time;
  `ContinuousLinearMap.norm_lyapunovPerronIntegral_le` is the case `β = 0`.
* `ContinuousLinearMap.lyapunovPerronMap`: the Lyapunov--Perron operator on bounded continuous
  functions on `[0, ∞)`.
* `ContinuousLinearMap.contractingWith_lyapunovPerronMap`: it is a contraction when `2 K ε < α`.
* `ContinuousLinearMap.lyapunovPerronSolution`: its unique fixed point.
* `ContinuousLinearMap.lipschitzWith_lyapunovPerronSolution`: the fixed point is Lipschitz in `ξ`.
* `ContinuousLinearMap.isIntegralCurveOn_lyapunovPerronSolution`: the fixed point solves
  `y' = A y + N y` on `[0, ∞)`.
* `ContinuousLinearMap.eqOn_lyapunovPerronSolution_of_isIntegralCurveOn`: when `P` is idempotent
  and commutes with `A`, every bounded forward solution is a Lyapunov--Perron solution.
* `ContinuousLinearMap.exists_isIntegralCurveOn_bounded_iff`: the initial values of bounded
  forward solutions are the fixed points of `ξ ↦ lyapunovPerronSolution ξ 0`.
* `ContinuousLinearMap.apply_lyapunovPerronSolution_zero`: the `P`-component of that initial value
  is `P ξ`.
* `ContinuousLinearMap.lyapunovPerronSolution_lyapunovPerronSolution_zero`: restarting a
  Lyapunov--Perron solution from its initial value reproduces it.
* `ContinuousLinearMap.norm_lyapunovPerronSolution_sub_le`: Lyapunov--Perron solutions approach
  each other exponentially, at every rate `β ≥ 0` with `2 K ε < α - β`.
* `ContinuousLinearMap.norm_lyapunovPerronSolution_le`,
  `ContinuousLinearMap.tendsto_lyapunovPerronSolution`: when `N 0 = 0`, Lyapunov--Perron
  solutions decay exponentially to `0`.
* `ContinuousLinearMap.norm_le_of_isIntegralCurveOn_of_bounded`: bounded forward solutions decay
  exponentially to `0`.
* `ContinuousLinearMap.exists_isIntegralCurveOn_tendsto_iff`: the initial values of forward
  solutions tending to `0` are the fixed points of `ξ ↦ lyapunovPerronSolution ξ 0`.

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
`M exp (-β s)` on `(t, ∞)` is bounded by `K M exp (-β t) / (α + β)`, provided `α + β > 0`. -/
theorem norm_setIntegral_lyapunovPerron_unstable_le_mul_exp {β : ℝ} (hαβ : 0 < α + β) (t : ℝ)
    (hgM : ∀ s ∈ Ioi t, ‖g s‖ ≤ M * Real.exp (-β * s)) :
    ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖ ≤
      K * M / (α + β) * Real.exp (-β * t) := by
  have hbound : IntegrableOn
      (fun s ↦ K * M * Real.exp (α * t) * Real.exp (-(α + β) * s)) (Ioi t) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hαβ) t).const_mul _
  calc ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖
      ≤ ∫ s in Ioi t, K * M * Real.exp (α * t) * Real.exp (-(α + β) * s) := by
        refine norm_integral_le_of_norm_le hbound <| (ae_restrict_mem measurableSet_Ioi).mono
          fun s hs ↦ ?_
        calc ‖exp ((t - s) • A) (g s - P (g s))‖
            ≤ K * Real.exp (α * (t - s)) * ‖g s‖ := hu _ (sub_nonpos.2 (le_of_lt hs)) _
          _ ≤ K * Real.exp (α * (t - s)) * (M * Real.exp (-β * s)) := by gcongr; exact hgM s hs
          _ = K * M * Real.exp (α * t) * Real.exp (-(α + β) * s) := by
            have hsplit : Real.exp (α * (t - s)) * Real.exp (-β * s) =
                Real.exp (α * t) * Real.exp (-(α + β) * s) := by
              rw [← Real.exp_add, ← Real.exp_add]
              ring_nf
            linear_combination (K * M : ℝ) * hsplit
    _ = K * M / (α + β) * Real.exp (-β * t) := by
      have hsplit : Real.exp (α * t) * Real.exp (-(α + β) * t) = Real.exp (-β * t) := by
        rw [← Real.exp_add]
        ring_nf
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hαβ), neg_div_neg_eq,
        ← hsplit]
      ring

omit [CompleteSpace X] in
/-- Under the backward exponential estimate, the unstable integral of a forcing term bounded by
`M` on `(t, ∞)` is bounded by `K M / α`. -/
theorem norm_setIntegral_lyapunovPerron_unstable_le (hα : 0 < α) (t : ℝ)
    (hgM : ∀ s ∈ Ioi t, ‖g s‖ ≤ M) :
    ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖ ≤ K * M / α := by
  simpa using norm_setIntegral_lyapunovPerron_unstable_le_mul_exp hu (β := 0)
    (by simpa using hα) t (by simpa using hgM)

end Estimates

omit [CompleteSpace X] in
/-- Under the forward exponential estimate, the stable integral of a forcing term bounded by
`M exp (-β s)` on `[0, t]` is bounded by `K M exp (-β t) / (α - β)` in forward time, provided
`β < α`. -/
theorem norm_intervalIntegral_lyapunovPerron_stable_le_mul_exp
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    {β : ℝ} (hβα : β < α) (ht : 0 ≤ t)
    (hgM : ∀ s ∈ Icc (0 : ℝ) t, ‖g s‖ ≤ M * Real.exp (-β * s)) :
    ‖∫ s in (0 : ℝ)..t, exp ((t - s) • A) (P (g s))‖ ≤
      K * M / (α - β) * Real.exp (-β * t) := by
  have hαβ : (0 : ℝ) < α - β := sub_pos.2 hβα
  have hM : 0 ≤ M := by
    simpa using (norm_nonneg _).trans (hgM 0 ⟨le_rfl, ht⟩)
  -- Splitting the kernel into a factor depending on `t` and one depending on the integration
  -- variable `s` turns the estimate into an ordinary exponential integral.
  have hsplit (s : ℝ) : Real.exp (-α * (t - s)) * Real.exp (-β * s) =
      Real.exp (-α * t) * Real.exp ((α - β) * s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hexp : Real.exp (-α * t) * (Real.exp ((α - β) * t) - 1) ≤ Real.exp (-β * t) := by
    rw [mul_sub, ← Real.exp_add, mul_one]
    ring_nf
    linarith [Real.exp_pos (-(α * t))]
  calc ‖∫ s in (0 : ℝ)..t, exp ((t - s) • A) (P (g s))‖
      ≤ ∫ s in (0 : ℝ)..t, K * M * Real.exp (-α * t) * Real.exp ((α - β) * s) := by
        have hcont : Continuous fun s : ℝ ↦
            K * M * Real.exp (-α * t) * Real.exp ((α - β) * s) := by
          fun_prop
        refine intervalIntegral.norm_integral_le_of_norm_le ht (ae_of_all _ fun s hs' ↦ ?_)
          (hcont.intervalIntegrable 0 t)
        calc ‖exp ((t - s) • A) (P (g s))‖
            ≤ K * Real.exp (-α * (t - s)) * ‖g s‖ := hs _ (sub_nonneg.2 hs'.2) _
          _ ≤ K * Real.exp (-α * (t - s)) * (M * Real.exp (-β * s)) := by
            gcongr; exact hgM s ⟨hs'.1.le, hs'.2⟩
          _ = K * M * Real.exp (-α * t) * Real.exp ((α - β) * s) := by
            linear_combination (K * M : ℝ) * hsplit s
    _ = K * M / (α - β) * (Real.exp (-α * t) * (Real.exp ((α - β) * t) - 1)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left (fun s ↦ Real.exp s) hαβ.ne', integral_exp,
        mul_zero, Real.exp_zero, smul_eq_mul]
      field_simp
    _ ≤ K * M / (α - β) * Real.exp (-β * t) := by gcongr

omit [CompleteSpace X] in
/-- Under the forward exponential estimate, the stable integral of a forcing term bounded by `M`
on `[0, t]` is bounded by `K M / α` in forward time. -/
theorem norm_intervalIntegral_lyapunovPerron_stable_le
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hα : 0 < α) (ht : 0 ≤ t) (hgM : ∀ s ∈ Icc (0 : ℝ) t, ‖g s‖ ≤ M) :
    ‖∫ s in (0 : ℝ)..t, exp ((t - s) • A) (P (g s))‖ ≤ K * M / α := by
  simpa using norm_intervalIntegral_lyapunovPerron_stable_le_mul_exp hs (β := 0)
    (by simpa using hα) ht (by simpa using hgM)

omit [CompleteSpace X] in
/-- Under the forward and backward exponential estimates, the integral terms of the
Lyapunov--Perron equation with a forcing term bounded by `M exp (-β s)` in forward time are
bounded by `2 K M exp (-β t) / (α - β)` in forward time, for a rate `0 ≤ β < α`. -/
theorem norm_lyapunovPerronIntegral_le_mul_exp
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    {β : ℝ} (hβ : 0 ≤ β) (hβα : β < α) (hgM : ∀ s, 0 ≤ s → ‖g s‖ ≤ M * Real.exp (-β * s))
    (ht : 0 ≤ t) :
    ‖lyapunovPerronIntegral A P g t‖ ≤ 2 * K * M / (α - β) * Real.exp (-β * t) := by
  have hαβ : (0 : ℝ) < α - β := sub_pos.2 hβα
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hgM 0 le_rfl)
  rw [lyapunovPerronIntegral]
  refine (norm_sub_le _ _).trans ?_
  have h₁ := norm_intervalIntegral_lyapunovPerron_stable_le_mul_exp hs hβα ht
    fun s hs ↦ hgM s hs.1
  have h₂ := norm_setIntegral_lyapunovPerron_unstable_le_mul_exp hu (by linarith) t
    fun s hs ↦ hgM s (ht.trans (le_of_lt hs))
  -- The unstable integral decays with the better constant `1 / (α + β) ≤ 1 / (α - β)`.
  have h₃ : K * M / (α + β) * Real.exp (-β * t) ≤ K * M / (α - β) * Real.exp (-β * t) := by
    gcongr
    linarith
  calc _ ≤ K * M / (α - β) * Real.exp (-β * t) + K * M / (α - β) * Real.exp (-β * t) :=
        add_le_add h₁ (h₂.trans h₃)
    _ = 2 * K * M / (α - β) * Real.exp (-β * t) := by ring

omit [CompleteSpace X] in
/-- Under the forward and backward exponential estimates, the integral terms of the
Lyapunov--Perron equation with a forcing term bounded by `M` are bounded by `2 K M / α` in
forward time. -/
theorem norm_lyapunovPerronIntegral_le
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hgM : ∀ s, ‖g s‖ ≤ M) (ht : 0 ≤ t) :
    ‖lyapunovPerronIntegral A P g t‖ ≤ 2 * K * M / α := by
  simpa using norm_lyapunovPerronIntegral_le_mul_exp hs hu le_rfl (β := 0)
    (by simpa using hα) (by simpa using fun s _ ↦ hgM s) ht

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

/-- When `P` is idempotent and commutes with `A`, the integral terms of the Lyapunov--Perron
equation have vanishing `P`-component at time `0`: there only the backward integral of the parts
`g s - P (g s)` survives. -/
theorem apply_lyapunovPerronIntegral_zero
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hP : IsIdempotentElem P) (hAP : Commute A P) (hg : ContinuousOn g (Ioi 0))
    (hgM : ∀ s ∈ Ioi (0 : ℝ), ‖g s‖ ≤ M) :
    P (lyapunovPerronIntegral A P g 0) = 0 := by
  rw [lyapunovPerronIntegral, intervalIntegral.integral_same, zero_sub, map_neg,
    ← P.integral_comp_comm (integrableOn_lyapunovPerron_unstable hu hα 0 hg hgM), neg_eq_zero]
  refine integral_eq_zero_of_ae (ae_of_all _ fun s ↦ ?_)
  dsimp only [Pi.zero_apply]
  rw [← mul_apply_eq_comp, ((hAP.symm.smul_right _).exp_right).eq, mul_apply_eq_comp, map_sub,
    ← mul_apply_eq_comp P P, hP.eq, sub_self, map_zero]

/-- Under the backward exponential estimate, a vector `v` with `P v = 0` whose forward orbit
`t ↦ exp (t A) v` stays bounded is zero, provided `P` commutes with `A`.

This is the linear uniqueness statement behind the converse of the Lyapunov--Perron
construction: the component of a forward solution not seen by `P` cannot stay bounded unless it
vanishes. -/
theorem eq_zero_of_norm_exp_smul_apply_le
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hAP : Commute A P) {v : X} (hv : P v = 0) {C : ℝ}
    (hC : ∀ t : ℝ, 0 ≤ t → ‖exp (t • A) v‖ ≤ C) : v = 0 := by
  have hα' : (0 : ℝ) < α := NNReal.coe_pos.2 hα
  -- Pulling `exp (t A) v` back by `exp (-t A)` bounds `‖v‖` by `K C exp (-α t)` for all `t ≥ 0`.
  have hbound (t : ℝ) (ht : 0 ≤ t) : ‖v‖ ≤ K * C * Real.exp (-(α * t)) := by
    have hPexp : P (exp (t • A) v) = 0 := by
      rw [← mul_apply_eq_comp P, ((hAP.symm.smul_right t).exp_right).eq, mul_apply_eq_comp,
        hv, map_zero]
    have hback : exp ((-t) • A) (exp (t • A) v - P (exp (t • A) v)) = v := by
      rw [hPexp, sub_zero, ← comp_apply, ← TauCeti.exp_add_smul, neg_add_cancel, zero_smul,
        exp_zero, one_apply_eq_self]
    calc ‖v‖ = ‖exp ((-t) • A) (exp (t • A) v - P (exp (t • A) v))‖ := by rw [hback]
      _ ≤ K * Real.exp (α * -t) * ‖exp (t • A) v‖ := hu (-t) (neg_nonpos.2 ht) _
      _ ≤ K * Real.exp (α * -t) * C := by gcongr; exact hC t ht
      _ = K * C * Real.exp (-(α * t)) := by rw [mul_neg]; ring
  have hlim : Tendsto (fun t : ℝ ↦ K * C * Real.exp (-(α * t))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hα')).const_mul ((K : ℝ) * C)
  exact norm_le_zero_iff.1 <| ge_of_tendsto hlim <|
    (eventually_ge_atTop 0).mono fun t ht ↦ hbound t ht

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

section BoundedSolutions

/-! ### Bounded forward solutions are Lyapunov--Perron solutions

When `P` is idempotent and commutes with `A`, every bounded forward solution of
`y' = A y + N y` is the Lyapunov--Perron solution with input parameter its initial value. The
initial values of the bounded forward solutions are therefore exactly the fixed points of
`ξ ↦ lyapunovPerronSolution ξ 0`: the graph, over the range of `P`, of a Lipschitz map into the
kernel of `P`. -/

/-- When `P` is idempotent, the Lyapunov--Perron solution depends only on the `P`-component of
its input parameter. -/
@[simp]
theorem lyapunovPerronSolution_map (hP : IsIdempotentElem P) (ξ : X) :
    lyapunovPerronSolution A P N hs hu hα hN hsmall (P ξ) =
      lyapunovPerronSolution A P N hs hu hα hN hsmall ξ := by
  refine (eq_lyapunovPerronSolution hs hu hα hN hsmall fun t ↦ ?_).symm
  rw [← mul_apply_eq_comp P, hP.eq, lyapunovPerronSolution_apply]

/-- When `P` is idempotent and commutes with `A`, the `P`-component of the initial value of a
Lyapunov--Perron solution is the `P`-component of its input parameter. -/
@[simp]
theorem apply_lyapunovPerronSolution_zero (hP : IsIdempotentElem P) (hAP : Commute A P)
    (ξ : X) : P (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ 0) = P ξ := by
  set γ := lyapunovPerronSolution A P N hs hu hα hN hsmall ξ
  set g : ℝ → X := fun s ↦ N (γ s.toNNReal)
  have hg : Continuous g :=
    ((γ.comp N hN).compContinuous ⟨Real.toNNReal, continuous_real_toNNReal⟩).continuous
  have hgM (s : ℝ) : ‖g s‖ ≤ ‖N 0‖ + ε * ‖γ‖ :=
    ((γ.comp N hN).norm_coe_le_norm s.toNNReal).trans
      (TauCeti.norm_boundedContinuousFunction_comp_le hN γ)
  rw [lyapunovPerronSolution_apply, NNReal.coe_zero, map_add,
    apply_lyapunovPerronIntegral_zero hu hα hP hAP hg.continuousOn fun s _ ↦ hgM s, add_zero,
    zero_smul, exp_zero, one_apply_eq_self, ← mul_apply_eq_comp P, hP.eq]

/-- When `P` is idempotent and commutes with `A`, restarting a Lyapunov--Perron solution from its
own initial value reproduces it. Hence every initial value `lyapunovPerronSolution ξ 0` is a fixed
point of `x ↦ lyapunovPerronSolution x 0`, and the `P`-component `P ξ` can be prescribed
arbitrarily. -/
@[simp]
theorem lyapunovPerronSolution_lyapunovPerronSolution_zero (hP : IsIdempotentElem P)
    (hAP : Commute A P) (ξ : X) :
    lyapunovPerronSolution A P N hs hu hα hN hsmall
        (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ 0) =
      lyapunovPerronSolution A P N hs hu hα hN hsmall ξ := by
  rw [← lyapunovPerronSolution_map hs hu hα hN hsmall hP, apply_lyapunovPerronSolution_zero hs hu
    hα hN hsmall hP hAP, lyapunovPerronSolution_map hs hu hα hN hsmall hP]

/-- **Bounded forward solutions are Lyapunov--Perron solutions.** When `P` is idempotent and
commutes with `A`, every solution of `y' = A y + N y` on `[0, ∞)` that stays bounded there agrees
on `[0, ∞)` with the Lyapunov--Perron solution whose input parameter is its initial value. -/
theorem eqOn_lyapunovPerronSolution_of_isIntegralCurveOn (hP : IsIdempotentElem P)
    (hAP : Commute A P) {y : ℝ → X} (hy : IsIntegralCurveOn y (fun _ y ↦ A y + N y) (Ici 0))
    {B : ℝ} (hB : ∀ t ∈ Ici (0 : ℝ), ‖y t‖ ≤ B) :
    EqOn y (fun t ↦ lyapunovPerronSolution A P N hs hu hα hN hsmall (y 0) t.toNNReal)
      (Ici 0) := by
  have hy_cont : ContinuousOn y (Ici 0) := hy.continuousOn
  -- The restriction of `y` to `[0, ∞)`, as a bounded continuous function.
  let γ : ℝ≥0 →ᵇ X := BoundedContinuousFunction.ofNormedAddCommGroup (fun t : ℝ≥0 ↦ y t)
    (hy_cont.comp_continuous NNReal.continuous_coe fun t ↦ t.2) B fun t ↦ hB t t.2
  have hγ (t : ℝ) (ht : 0 ≤ t) : γ t.toNNReal = y t := by
    simp [γ, Real.coe_toNNReal t ht]
  set g : ℝ → X := fun s ↦ N (γ s.toNNReal)
  have hg : Continuous g :=
    ((γ.comp N hN).compContinuous ⟨Real.toNNReal, continuous_real_toNNReal⟩).continuous
  have hgM (s : ℝ) : ‖g s‖ ≤ ‖N 0‖ + ε * ‖γ‖ :=
    ((γ.comp N hN).norm_coe_le_norm s.toNNReal).trans
      (TauCeti.norm_boundedContinuousFunction_comp_le hN γ)
  -- `w` is the right-hand side of the Lyapunov--Perron equation along `y`; the difference
  -- `z = y - w` solves the linear equation `z' = A z` on `[0, ∞)`.
  set w : ℝ → X := fun t ↦ exp (t • A) (P (y 0)) + lyapunovPerronIntegral A P g t
  have hw (t : ℝ) : HasDerivAt w (A (w t) + g t) t := by
    refine (((hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t (P (y 0)))).add
      (hasDerivAt_lyapunovPerronIntegral hu hα hg hgM t)).congr_deriv ?_
    simp only [w, map_add, map_zero, add_zero, mul_apply_eq_comp]
    abel
  set z : ℝ → X := fun t ↦ y t - w t
  have hz (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : HasDerivWithinAt z (A (z t)) (Ici t) t := by
    refine ((hy t ht).mono (Ici_subset_Ici.2 ht)).sub (hw t).hasDerivWithinAt |>.congr_deriv ?_
    simp only [z, g, hγ t ht, map_sub]
    abel
  -- By uniqueness for the linear equation, `z t = exp (t A) (z 0)`.
  have hz_exp (t : ℝ) (ht : 0 ≤ t) : z t = exp (t • A) (z 0) := by
    have hw_cont : Continuous w := continuous_iff_continuousAt.2 fun t ↦ (hw t).continuousAt
    refine ODE_solution_unique_of_mem_Icc_right (v := fun _ x ↦ A x) (s := fun _ ↦ univ)
      (K := ‖A‖₊) (fun _ _ ↦ A.lipschitzWith.lipschitzOnWith)
      ((hy_cont.sub hw_cont.continuousOn).mono Icc_subset_Ici_self)
      (fun t ht ↦ hz t ht.1) (fun _ _ ↦ mem_univ _)
      (((differentiable_exp_smul_const ℝ A).continuous.clm_apply continuous_const).continuousOn)
      (fun t _ ↦ ((hasDerivAt_exp_smul_const' A t).clm_apply
        (hasDerivAt_const t (z 0))).hasDerivWithinAt.congr_deriv (by simp [mul_apply_eq_comp]))
      (fun _ _ ↦ mem_univ _) (by simp [z]) ⟨ht, le_rfl⟩
  -- `z 0` has vanishing `P`-component and a bounded forward orbit, so it is zero.
  have hz0 : z 0 = 0 := by
    refine eq_zero_of_norm_exp_smul_apply_le hu hα hAP ?_ (C := B + (K * ‖y 0‖ +
      2 * K * (‖N 0‖ + ε * ‖γ‖) / α)) fun t ht ↦ ?_
    · have hint := apply_lyapunovPerronIntegral_zero hu hα hP hAP hg.continuousOn
        fun s _ ↦ hgM s
      simp only [z, w, zero_smul, exp_zero, one_apply_eq_self, map_sub, map_add, hint, add_zero,
        ← mul_apply_eq_comp P P, hP.eq, sub_self]
    · rw [← hz_exp t ht]
      refine (norm_sub_le _ _).trans (add_le_add (hB t ht) ((norm_add_le _ _).trans
        (add_le_add ?_ (norm_lyapunovPerronIntegral_le hs hu hα hgM ht))))
      calc ‖exp (t • A) (P (y 0))‖ ≤ K * Real.exp (-α * t) * ‖y 0‖ := hs t ht _
        _ ≤ K * 1 * ‖y 0‖ := by
          gcongr
          exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.2 α.coe_nonneg) ht)
        _ = K * ‖y 0‖ := by ring
  have hsol : γ = lyapunovPerronSolution A P N hs hu hα hN hsmall (y 0) := by
    refine eq_lyapunovPerronSolution hs hu hα hN hsmall fun t ↦ ?_
    have h := hz_exp t t.2
    rw [hz0, map_zero] at h
    have hγt : γ t = y t := by simpa using hγ t t.2
    exact hγt.trans (sub_eq_zero.1 h)
  intro t ht
  rw [← hsol]
  exact (hγ t ht).symm

/-- **The Lyapunov--Perron description of bounded forward solutions.** When `P` is idempotent and
commutes with `A`, a point is the initial value of a solution of `y' = A y + N y` that stays
bounded on `[0, ∞)` exactly when it is the initial value of the Lyapunov--Perron solution with
itself as input parameter. -/
theorem exists_isIntegralCurveOn_bounded_iff (hP : IsIdempotentElem P) (hAP : Commute A P)
    (x : X) :
    (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ y ↦ A y + N y) (Ici 0) ∧ y 0 = x ∧
      ∃ B, ∀ t ∈ Ici (0 : ℝ), ‖y t‖ ≤ B) ↔
      lyapunovPerronSolution A P N hs hu hα hN hsmall x 0 = x := by
  constructor
  · rintro ⟨y, hy, rfl, B, hB⟩
    have h := eqOn_lyapunovPerronSolution_of_isIntegralCurveOn hs hu hα hN hsmall hP hAP hy hB
      (mem_Ici.2 le_rfl)
    simp only [Real.toNNReal_zero] at h
    exact h.symm
  · intro hx
    set γ := lyapunovPerronSolution A P N hs hu hα hN hsmall x
    refine ⟨fun t ↦ γ t.toNNReal, isIntegralCurveOn_lyapunovPerronSolution hs hu hα hN hsmall x,
      by simpa using hx, ‖γ‖, fun t _ ↦ γ.norm_coe_le_norm _⟩

end BoundedSolutions

section Decay

/-! ### Exponential decay of Lyapunov--Perron solutions

For every rate `β ≥ 0` in the spectral gap left by the nonlinearity, `2 K ε < α - β`, the
Lyapunov--Perron solutions approach each other at rate `β`. When `N 0 = 0` the solution with
input parameter `0` is the zero solution, so all Lyapunov--Perron solutions decay exponentially,
and the bounded forward solutions are exactly the forward solutions tending to the equilibrium
`0`. -/

/-- The weighted form of `dist_lyapunovPerronMap_le`: if two curves stay within
`R exp (-β t)` of each other in forward time, for a rate `0 ≤ β < α`, then their images under
the Lyapunov--Perron operators with input parameters `ξ` and `ζ` stay within
`(K ‖ξ - ζ‖ + 2 K ε R / (α - β)) exp (-β t)` of each other. -/
theorem norm_lyapunovPerronMap_sub_le_mul_exp {β : ℝ} (hβ : 0 ≤ β) (hβα : β < α) (ξ ζ : X)
    {γ η : ℝ≥0 →ᵇ X} {R : ℝ} (hγη : ∀ t : ℝ≥0, ‖γ t - η t‖ ≤ R * Real.exp (-β * t))
    (t : ℝ≥0) :
    ‖lyapunovPerronMap A P N hs hu hα hN ξ γ t - lyapunovPerronMap A P N hs hu hα hN ζ η t‖ ≤
      (K * ‖ξ - ζ‖ + 2 * K * ε * R / (α - β)) * Real.exp (-β * t) := by
  have hcont (θ : ℝ≥0 →ᵇ X) : Continuous fun s : ℝ ↦ N (θ s.toNNReal) :=
    ((θ.comp N hN).compContinuous ⟨Real.toNNReal, continuous_real_toNNReal⟩).continuous
  have hbound (θ : ℝ≥0 →ᵇ X) (s : ℝ) : ‖N (θ s.toNNReal)‖ ≤ ‖N 0‖ + ε * ‖θ‖ :=
    ((θ.comp N hN).norm_coe_le_norm s.toNNReal).trans
      (TauCeti.norm_boundedContinuousFunction_comp_le hN θ)
  have hdiff (s : ℝ) (hs0 : 0 ≤ s) :
      ‖((fun s : ℝ ↦ N (γ s.toNNReal)) - fun s : ℝ ↦ N (η s.toNNReal)) s‖ ≤
        ε * R * Real.exp (-β * s) := by
    rw [Pi.sub_apply, ← dist_eq_norm, mul_assoc]
    refine hN.dist_le_mul_of_le ?_
    rw [dist_eq_norm]
    simpa [Real.coe_toNNReal s hs0] using hγη s.toNNReal
  have hlin : ‖exp ((t : ℝ) • A) (P (ξ - ζ))‖ ≤ K * ‖ξ - ζ‖ * Real.exp (-β * t) := by
    calc _ ≤ K * Real.exp (-α * t) * ‖ξ - ζ‖ := hs t t.2 _
      _ ≤ K * Real.exp (-β * t) * ‖ξ - ζ‖ := by gcongr
      _ = K * ‖ξ - ζ‖ * Real.exp (-β * t) := by ring
  rw [lyapunovPerronMap_apply, lyapunovPerronMap_apply, add_sub_add_comm, ← map_sub, ← map_sub,
    lyapunovPerronIntegral_sub hu hα (hcont γ) (hbound γ) (hcont η) (hbound η)]
  calc _ ≤ K * ‖ξ - ζ‖ * Real.exp (-β * t) + 2 * K * (ε * R) / (α - β) * Real.exp (-β * t) :=
        (norm_add_le _ _).trans
          (add_le_add hlin (norm_lyapunovPerronIntegral_le_mul_exp hs hu hβ hβα hdiff t.2))
    _ = _ := by ring

/-- **Exponential decay of the difference of Lyapunov--Perron solutions.** For a rate `β ≥ 0`
with `2 K ε < α - β`, two Lyapunov--Perron solutions approach each other at rate `β`, with a
constant proportional to the distance between their input parameters. -/
theorem norm_lyapunovPerronSolution_sub_le {β : ℝ} (hβ : 0 ≤ β) (hβα : 2 * K * ε < α - β)
    (ξ ζ : X) (t : ℝ≥0) :
    ‖lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t -
        lyapunovPerronSolution A P N hs hu hα hN hsmall ζ t‖ ≤
      K / (1 - 2 * K * ε / (α - β)) * Real.exp (-β * t) * ‖ξ - ζ‖ := by
  have hKε : (0 : ℝ) ≤ 2 * K * ε := by positivity
  have hαβ : (0 : ℝ) < α - β := hKε.trans_lt hβα
  have hq : 0 < 1 - 2 * K * ε / (α - β) := sub_pos.2 ((div_lt_one hαβ).2 hβα)
  set R : ℝ := K / (1 - 2 * K * ε / (α - β)) * ‖ξ - ζ‖
  have hR : K * ‖ξ - ζ‖ + 2 * K * ε * R / (α - β) = R := by
    have h : R * (1 - 2 * K * ε / (α - β)) = K * ‖ξ - ζ‖ := by
      rw [mul_right_comm, div_mul_cancel₀ _ hq.ne']
    linear_combination -h
  set y := lyapunovPerronSolution A P N hs hu hα hN hsmall ζ
  -- The curves within `R exp (-β t)` of `y` form a closed set, which the Lyapunov--Perron
  -- operator with input parameter `ξ` maps to itself because `y` is a fixed point for `ζ`.
  set S : Set (ℝ≥0 →ᵇ X) := {γ | ∀ t : ℝ≥0, ‖γ t - y t‖ ≤ R * Real.exp (-β * t)}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun t ↦ isClosed_le
      ((continuous_eval_const t).sub continuous_const).norm continuous_const
  have hyS : y ∈ S := fun t ↦ by
    rw [sub_self, norm_zero]
    positivity
  have hmaps : MapsTo (lyapunovPerronMap A P N hs hu hα hN ξ) S S := fun γ hγ t ↦ by
    have h := norm_lyapunovPerronMap_sub_le_mul_exp hs hu hα hN hβ (by linarith) ξ ζ hγ t
    rwa [hR, isFixedPt_lyapunovPerronSolution hs hu hα hN hsmall ζ] at h
  -- Hence the fixed point for `ξ`, the limit of the iterates of `y`, lies in the set.
  have hfix : lyapunovPerronSolution A P N hs hu hα hN hsmall ξ ∈ S := by
    have hf := contractingWith_lyapunovPerronMap hs hu hα hN hsmall ξ
    rw [ContractingWith.fixedPoint_unique hf (isFixedPt_lyapunovPerronSolution hs hu hα hN
      hsmall ξ)]
    exact hS.mem_of_tendsto (hf.tendsto_iterate_fixedPoint y)
      (Eventually.of_forall fun n ↦ hmaps.iterate n hyS)
  calc _ ≤ R * Real.exp (-β * t) := hfix t
    _ = _ := by ring

/-- **Exponential decay of Lyapunov--Perron solutions.** If the nonlinearity vanishes at the
origin, then for a rate `β ≥ 0` with `2 K ε < α - β` every Lyapunov--Perron solution decays to
`0` at rate `β`. -/
theorem norm_lyapunovPerronSolution_le (hN0 : N 0 = 0) {β : ℝ} (hβ : 0 ≤ β)
    (hβα : 2 * K * ε < α - β) (ξ : X) (t : ℝ≥0) :
    ‖lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t‖ ≤
      K / (1 - 2 * K * ε / (α - β)) * Real.exp (-β * t) * ‖ξ‖ := by
  simpa [hN0] using norm_lyapunovPerronSolution_sub_le hs hu hα hN hsmall hβ hβα ξ 0 t

/-- If the nonlinearity vanishes at the origin, every Lyapunov--Perron solution tends to `0`
in forward time. -/
theorem tendsto_lyapunovPerronSolution (hN0 : N 0 = 0) (ξ : X) :
    Tendsto (fun t : ℝ ↦ lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t.toNNReal) atTop
      (𝓝 0) := by
  -- Any rate strictly inside the gap `α - 2 K ε` works; take half of it.
  set β : ℝ := (α - 2 * K * ε) / 2
  have hgap : (2 * K * ε : ℝ) < α := by exact_mod_cast hsmall
  have hβ : 0 ≤ β := by simp only [β]; linarith
  have hβα : 2 * K * ε < (α : ℝ) - β := by simp only [β]; linarith
  have hβpos : 0 < β := by simp only [β]; linarith
  set C : ℝ := K / (1 - 2 * K * ε / (α - β)) * ‖ξ‖
  have hlim : Tendsto (fun t : ℝ ↦ C * Real.exp (-β * t)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hβpos)).const_mul C
  refine squeeze_zero_norm' ((eventually_ge_atTop 0).mono fun t ht ↦ ?_) hlim
  have h := norm_lyapunovPerronSolution_le hs hu hα hN hsmall hN0 hβ hβα ξ t.toNNReal
  rw [Real.coe_toNNReal t ht] at h
  simpa only [C, mul_right_comm _ (Real.exp _)] using h

include hs hu hα hN hsmall in
/-- **Bounded forward solutions decay exponentially.** When the nonlinearity vanishes at the
origin and `P` is idempotent and commutes with `A`, every solution of `y' = A y + N y` that stays
bounded on `[0, ∞)` decays to `0` there at every rate `β ≥ 0` with `2 K ε < α - β`. -/
theorem norm_le_of_isIntegralCurveOn_of_bounded (hN0 : N 0 = 0) (hP : IsIdempotentElem P)
    (hAP : Commute A P) {β : ℝ} (hβ : 0 ≤ β) (hβα : 2 * K * ε < α - β) {y : ℝ → X}
    (hy : IsIntegralCurveOn y (fun _ y ↦ A y + N y) (Ici 0)) {B : ℝ}
    (hB : ∀ t ∈ Ici (0 : ℝ), ‖y t‖ ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖y t‖ ≤ K / (1 - 2 * K * ε / (α - β)) * Real.exp (-β * t) * ‖y 0‖ := by
  have h := norm_lyapunovPerronSolution_le hs hu hα hN hsmall hN0 hβ hβα (y 0) t.toNNReal
  have hyt : y t = lyapunovPerronSolution A P N hs hu hα hN hsmall (y 0) t.toNNReal :=
    eqOn_lyapunovPerronSolution_of_isIntegralCurveOn hs hu hα hN hsmall hP hAP hy hB (mem_Ici.2 ht)
  rwa [Real.coe_toNNReal t ht, ← hyt] at h

/-- **The Lyapunov--Perron description of the stable set.** When the nonlinearity vanishes at
the origin and `P` is idempotent and commutes with `A`, a point is the initial value of a
solution of `y' = A y + N y` on `[0, ∞)` tending to the equilibrium `0` exactly when it is the
initial value of the Lyapunov--Perron solution with itself as input parameter. -/
theorem exists_isIntegralCurveOn_tendsto_iff (hN0 : N 0 = 0) (hP : IsIdempotentElem P)
    (hAP : Commute A P) (x : X) :
    (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ y ↦ A y + N y) (Ici 0) ∧ y 0 = x ∧
      Tendsto y atTop (𝓝 0)) ↔
      lyapunovPerronSolution A P N hs hu hα hN hsmall x 0 = x := by
  constructor
  · rintro ⟨y, hy, hy0, hlim⟩
    refine (exists_isIntegralCurveOn_bounded_iff hs hu hα hN hsmall hP hAP x).1
      ⟨y, hy, hy0, ?_⟩
    -- A curve tending to `0` is eventually within `1` of it, and it is bounded on the compact
    -- interval before that.
    have hone : ∀ᶠ t in atTop, ‖y t‖ ≤ 1 :=
      hlim.norm.eventually (ge_mem_nhds (by rw [norm_zero]; exact zero_lt_one))
    obtain ⟨T, hT⟩ := eventually_atTop.1 hone
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hy.continuousOn.mono (Icc_subset_Ici_self : Icc (0 : ℝ) (max T 0) ⊆ Ici 0))
    refine ⟨max C 1, fun t ht ↦ ?_⟩
    rcases le_total t (max T 0) with htT | htT
    · exact (hC t ⟨ht, htT⟩).trans (le_max_left _ _)
    · exact (hT t ((le_max_left _ _).trans htT)).trans (le_max_right _ _)
  · intro hx
    exact ⟨fun t ↦ lyapunovPerronSolution A P N hs hu hα hN hsmall x t.toNNReal,
      isIntegralCurveOn_lyapunovPerronSolution hs hu hα hN hsmall x, by simpa using hx,
      tendsto_lyapunovPerronSolution hs hu hα hN hsmall hN0 x⟩

end Decay

end Contraction

end ContinuousLinearMap
