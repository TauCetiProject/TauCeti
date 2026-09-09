/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Analysis.Calculus.Morse.Linearization
-- Private: the mean value inequality, monotonicity from the sign of a derivative, the fundamental
-- theorem of calculus and the norm comparison for the gradient are used only inside proofs; no
-- declaration below exposes their APIs.
import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponential convergence of a negative gradient trajectory

A negative gradient trajectory that converges to a **nondegenerate** critical point `p` converges
to it at an exponential rate:

`‖γ t - p‖ ≤ C * exp (-μ * t)` for large `t`,

and the same holds for the energy `f (γ t) - f p`. This is the asymptotic input the moduli spaces
of Morse and Floer theory are built on: it is what puts a trajectory running between two critical
points into the weighted Sobolev spaces on which the linearized operator `d/ds + A(s)` is Fredholm,
and it is what makes the ends of a trajectory converge fast enough for the broken-trajectory
compactness and gluing arguments of Lane M of the analytic Heegaard Floer roadmap.

## The argument

Everything rests on the **Morse form of Łojasiewicz's gradient inequality**, with the optimal
exponent `1/2`: near a nondegenerate critical point,

`lam * |f x - f p| ≤ ‖∇ f x‖ ^ 2`.

Both halves of it come from the linearization `TauCeti.hessianOperator` of the gradient. Since the
Hessian operator is invertible, the gradient is bounded below by a multiple of the distance to `p`
(`TauCeti.IsNondegenerateCriticalPoint.exists_mul_norm_sub_le_norm_gradient`); since it vanishes at
`p` and is bounded above by a multiple of that distance, the mean value inequality bounds the
energy by the *square* of the distance
(`TauCeti.IsNondegenerateCriticalPoint.exists_sub_le_mul_norm_sub_sq`). Comparing the two gives the
inequality (`TauCeti.IsNondegenerateCriticalPoint.exists_mul_sub_le_norm_gradient_sq`).

Along the trajectory the energy `g t = f (γ t) - f p` is nonnegative — `f ∘ γ` is antitone and
tends to `f p` — and satisfies `g' = -‖∇ f (γ t)‖ ^ 2 ≤ -lam * g`, so `g` decays like
`exp (-lam * t)`.

That decay does not by itself bound `‖γ t - p‖`: the energy vanishes on the cone where the
Hessian quadratic form does, and that cone meets every neighbourhood of `p` as soon as the Morse
index is neither `0` nor maximal. The distance is instead recovered from the *length* of the
trajectory. On a time interval of length one the energy identity
`TauCeti.IsIntegralCurveOn.integral_norm_gradient_sq_eq_sub` computes `∫ ‖∇ f (γ s)‖ ^ 2`, and the
elementary bound `v ≤ (α * v ^ 2 + 1 / α) / 2`, optimized in `α`, converts it into a bound for
`∫ ‖∇ f (γ s)‖ = ∫ ‖γ' s‖`, hence for `‖γ (t + 1) - γ t‖`, by the square root of the energy.
Summing the resulting geometric series over the times `t, t + 1, t + 2, …` and passing to the limit
bounds `‖γ t - p‖` by a multiple of `sqrt (g t)`, which decays like `exp (-lam * t / 2)`.

## Main results

* `TauCeti.IsNondegenerateCriticalPoint.exists_mul_sub_le_norm_gradient_sq`: **the Morse form of
  Łojasiewicz's gradient inequality**, with exponent `1/2`.
* `TauCeti.IsIntegralCurveOn.exists_sub_le_mul_exp_atTop`: the energy along a trajectory
  converging to a nondegenerate critical point decays exponentially.
* `TauCeti.IsIntegralCurveOn.exists_norm_sub_le_mul_exp_atTop`: **the trajectory itself
  converges exponentially fast**.
* `TauCeti.IsIntegralCurveOn.exists_norm_sub_le_mul_exp_atBot`: the backward-time statement,
  obtained from the forward one by reversing time and negating the function.
* `TauCeti.IsIntegralCurveOn.isBigO_exp_atTop`: the forward statement in `IsBigO` form.

## References

* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 2.
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2, where the exponential convergence of
  trajectories is what places them in the weighted Sobolev spaces of the Fredholm theory.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Asymptotics Filter InnerProductSpace MeasureTheory Metric Set
open scoped Gradient Interval Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {p : E} {a : ℝ}

/-! ### The Morse form of Łojasiewicz's gradient inequality -/

namespace IsNondegenerateCriticalPoint

/-- Near a nondegenerate critical point the gradient is bounded below by a multiple of the
distance to that point: the Hessian operator is invertible, hence bounded below, and the gradient
differs from it by a term of smaller order. -/
theorem exists_mul_norm_sub_le_norm_gradient (h : IsNondegenerateCriticalPoint f p) :
    ∃ c > 0, ∀ᶠ x in 𝓝 p, c * ‖x - p‖ ≤ ‖∇ f x‖ := by
  obtain ⟨A, hA⟩ := h.isInvertible_hessianOperator
  set M : ℝ := ‖(A.symm : E →L[ℝ] E)‖ + 1 with hMdef
  have hMpos : 0 < M := by positivity
  have hlow : ∀ v : E, ‖v‖ ≤ M * ‖hessianOperator f p v‖ := by
    intro v
    have h1 : ‖v‖ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖(A : E →L[ℝ] E) v‖ := by
      conv_lhs => rw [← A.symm_apply_apply v]
      exact (A.symm : E →L[ℝ] E).le_opNorm _
    rw [← hA]
    nlinarith [norm_nonneg ((A : E →L[ℝ] E) v)]
  have h2M : (0 : ℝ) < 2 * M := by positivity
  refine ⟨(2 * M)⁻¹, by positivity, ?_⟩
  filter_upwards [h.neg_gradient_sub_linearization_isLittleO.def
    (show (0 : ℝ) < (2 * M)⁻¹ by positivity)] with x hx
  set R : ℝ := ‖(-∇ f) x + hessianOperator f p (x - p)‖ with hRdef
  have hR : 2 * M * R ≤ ‖x - p‖ := by
    calc 2 * M * R ≤ 2 * M * ((2 * M)⁻¹ * ‖x - p‖) := mul_le_mul_of_nonneg_left hx h2M.le
      _ = ‖x - p‖ := by field_simp
  have h1 : ‖x - p‖ ≤ M * ‖hessianOperator f p (x - p)‖ := hlow _
  have h2 : ‖hessianOperator f p (x - p)‖ ≤ R + ‖∇ f x‖ := by
    calc ‖hessianOperator f p (x - p)‖
        = ‖((-∇ f) x + hessianOperator f p (x - p)) - (-∇ f) x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖(-∇ f) x + hessianOperator f p (x - p)‖ + ‖(-∇ f) x‖ := norm_sub_le _ _
      _ = R + ‖∇ f x‖ := by simp [hRdef]
  have h3 : M * ‖hessianOperator f p (x - p)‖ ≤ M * (R + ‖∇ f x‖) :=
    mul_le_mul_of_nonneg_left h2 hMpos.le
  rw [inv_mul_le_iff₀ h2M]
  nlinarith

/-- Near a nondegenerate critical point the gradient is bounded above by a multiple of the
distance to that point: it vanishes at the point and is differentiable there. -/
theorem exists_norm_gradient_le_mul_norm_sub (h : IsNondegenerateCriticalPoint f p) :
    ∃ C > 0, ∀ᶠ x in 𝓝 p, ‖∇ f x‖ ≤ C * ‖x - p‖ := by
  refine ⟨‖hessianOperator f p‖ + 1, by positivity, ?_⟩
  filter_upwards [h.neg_gradient_sub_linearization_isLittleO.def one_pos] with x hx
  rw [one_mul] at hx
  have h2 : ‖hessianOperator f p (x - p)‖ ≤ ‖hessianOperator f p‖ * ‖x - p‖ :=
    (hessianOperator f p).le_opNorm _
  have h1 : ‖∇ f x‖ ≤ ‖(-∇ f) x + hessianOperator f p (x - p)‖
      + ‖hessianOperator f p (x - p)‖ := by
    calc ‖∇ f x‖ = ‖(-∇ f) x‖ := by simp
      _ = ‖((-∇ f) x + hessianOperator f p (x - p)) - hessianOperator f p (x - p)‖ := by
          rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  nlinarith

/-- Near a nondegenerate critical point the absolute energy difference `|f x - f p|` is bounded by
a multiple of the squared distance to that point. This is the mean value inequality applied along
the segment from `p` to `x`, on which the gradient is bounded by a multiple of `‖x - p‖`. -/
theorem exists_sub_le_mul_norm_sub_sq (h : IsNondegenerateCriticalPoint f p) :
    ∃ C > 0, ∀ᶠ x in 𝓝 p, |f x - f p| ≤ C * ‖x - p‖ ^ 2 := by
  obtain ⟨C, hC, hgrad⟩ := h.exists_norm_gradient_le_mul_norm_sub
  have hdiff : ∀ᶠ x in 𝓝 p, DifferentiableAt ℝ f x := by
    filter_upwards [h.contDiffAt.eventually (by simp)] with x hx
    exact hx.differentiableAt (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hgrad.and hdiff)
  refine ⟨C, hC, Metric.eventually_nhds_iff.2 ⟨r, hr, fun {x} hx ↦ ?_⟩⟩
  have hxr : ‖x - p‖ < r := by rwa [← dist_eq_norm]
  have hsub : Metric.closedBall p ‖x - p‖ ⊆ Metric.ball p r := fun y hy ↦
    lt_of_le_of_lt (Metric.mem_closedBall.1 hy) hxr
  have hkey : ‖f x - f p‖ ≤ C * ‖x - p‖ * ‖x - p‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (s := Metric.closedBall p ‖x - p‖) (f' := fun y ↦ fderiv ℝ f y)
      (fun y hy ↦ ?_) (fun y hy ↦ ?_) (convex_closedBall p ‖x - p‖) ?_ ?_
    · exact ((hball (hsub hy)).2).hasFDerivAt.hasFDerivWithinAt
    · rw [← norm_gradient_eq_norm_fderiv]
      refine ((hball (hsub hy)).1).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
      have hy' := Metric.mem_closedBall.1 hy
      rwa [dist_eq_norm] at hy'
    · exact Metric.mem_closedBall_self (norm_nonneg _)
    · simp [Metric.mem_closedBall, dist_eq_norm]
  calc |f x - f p| = ‖f x - f p‖ := by rw [Real.norm_eq_abs]
    _ ≤ C * ‖x - p‖ * ‖x - p‖ := hkey
    _ = C * ‖x - p‖ ^ 2 := by ring

/-- **The Morse form of Łojasiewicz's gradient inequality.** Near a nondegenerate critical point
the absolute energy difference is bounded by a multiple of the squared norm of the gradient;
equivalently the
Łojasiewicz inequality holds there with the optimal exponent `1 / 2`. For a merely smooth function
no such inequality is available, and a gradient trajectory can spiral forever without converging. -/
theorem exists_mul_sub_le_norm_gradient_sq (h : IsNondegenerateCriticalPoint f p) :
    ∃ lam > 0, ∀ᶠ x in 𝓝 p, lam * |f x - f p| ≤ ‖∇ f x‖ ^ 2 := by
  obtain ⟨c, hc, h1⟩ := h.exists_mul_norm_sub_le_norm_gradient
  obtain ⟨C, hC, h2⟩ := h.exists_sub_le_mul_norm_sub_sq
  refine ⟨c ^ 2 / C, by positivity, ?_⟩
  filter_upwards [h1, h2] with x hx1 hx2
  have h3 : (c * ‖x - p‖) ^ 2 ≤ ‖∇ f x‖ ^ 2 := pow_le_pow_left₀ (by positivity) hx1 2
  calc c ^ 2 / C * |f x - f p| ≤ c ^ 2 / C * (C * ‖x - p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hx2 (by positivity)
    _ = (c * ‖x - p‖) ^ 2 := by field_simp
    _ ≤ ‖∇ f x‖ ^ 2 := h3

end IsNondegenerateCriticalPoint

/-! ### Decay along a trajectory -/

namespace IsIntegralCurveOn

variable {T lam : ℝ}

/-- **Exponential decay of the energy.** If along a trajectory the energy is nonnegative and
satisfies Łojasiewicz's inequality with constant `lam`, then it decays like `exp (-lam * t)`,
because the derivative of `t ↦ (f (γ t) - f p) * exp (lam * t)` is nonpositive. -/
private theorem energy_le_mul_exp
    (hderiv : ∀ t ∈ Ici T, HasDerivAt γ (-∇ f (γ t)) t)
    (hdiff : ∀ t ∈ Ici T, DifferentiableAt ℝ f (γ t))
    (hloj : ∀ t ∈ Ici T, lam * (f (γ t) - f p) ≤ ‖∇ f (γ t)‖ ^ 2)
    {t : ℝ} (ht : T ≤ t) :
    f (γ t) - f p ≤ (f (γ T) - f p) * Real.exp (-(lam * (t - T))) := by
  set g : ℝ → ℝ := fun s ↦ (f (γ s) - f p) * Real.exp (lam * s)
  set g' : ℝ → ℝ := fun s ↦
    (-‖∇ f (γ s)‖ ^ 2 + lam * (f (γ s) - f p)) * Real.exp (lam * s) with hg'
  have hgderiv : ∀ s ∈ Ici T, HasDerivAt g (g' s) s := by
    intro s hs
    have h1 : HasDerivAt (fun u ↦ f (γ u) - f p) (-‖∇ f (γ s)‖ ^ 2) s := by
      have hc := (hdiff s hs).hasFDerivAt.comp_hasDerivAt s (hderiv s hs)
      have h1' : HasDerivAt (fun u ↦ f (γ u)) (-‖∇ f (γ s)‖ ^ 2) s := by
        refine hc.congr_deriv ?_
        rw [map_neg, ← inner_gradient_left, real_inner_self_eq_norm_sq]
      exact h1'.sub_const _
    have h2 : HasDerivAt (fun u : ℝ ↦ Real.exp (lam * u)) (Real.exp (lam * s) * lam) s := by
      have hmul : HasDerivAt (fun u : ℝ ↦ lam * u) lam s := by
        simpa using (hasDerivAt_id s).const_mul lam
      simpa using hmul.exp
    refine (h1.mul h2).congr_deriv ?_
    rw [hg']
    ring
  have hanti : AntitoneOn g (Ici T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Ici T)
      (fun s hs ↦ (hgderiv s hs).continuousAt.continuousWithinAt) (fun s hs ↦ ?_) (fun s hs ↦ ?_)
    · exact (hgderiv s (interior_subset hs)).hasDerivWithinAt
    · have hlj := hloj s (interior_subset hs)
      have hexp : (0 : ℝ) < Real.exp (lam * s) := Real.exp_pos _
      rw [hg']
      nlinarith
  have hle : g t ≤ g T := hanti (le_refl T) ht ht
  have hexp : Real.exp (-(lam * (t - T))) = Real.exp (lam * T) * Real.exp (-(lam * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hone : (f (γ t) - f p) * Real.exp (lam * t) * Real.exp (-(lam * t)) = f (γ t) - f p := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  calc f (γ t) - f p = (f (γ t) - f p) * Real.exp (lam * t) * Real.exp (-(lam * t)) := hone.symm
    _ ≤ (f (γ T) - f p) * Real.exp (lam * T) * Real.exp (-(lam * t)) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ = (f (γ T) - f p) * (Real.exp (lam * T) * Real.exp (-(lam * t))) := by ring

/-- **The unit-time step estimate.** Over a time interval of length one the trajectory moves by at
most `(α * energy + 1 / α) / 2`, for every `α > 0`. The distance travelled is at most the integral
of `‖∇ f (γ s)‖`, and the elementary inequality `v ≤ (α * v ^ 2 + 1 / α) / 2` turns the energy
identity for `∫ ‖∇ f (γ s)‖ ^ 2` into a bound for it. -/
private theorem norm_sub_add_one_le
    (hderiv : ∀ s ∈ Ici T, HasDerivAt γ (-∇ f (γ s)) s)
    (hdiff : ∀ s ∈ Ici T, DifferentiableAt ℝ f (γ s))
    (hcont : ContinuousOn (fun s ↦ ∇ f (γ s)) (Ici T))
    (hge : ∀ s ∈ Ici T, f p ≤ f (γ s))
    {t : ℝ} (ht : T ≤ t) {α : ℝ} (hα : 0 < α) :
    ‖γ (t + 1) - γ t‖ ≤ (α * (f (γ t) - f p) + 1 / α) / 2 := by
  have htt : t ≤ t + 1 := by linarith
  have hsub : [[t, t + 1]] ⊆ Ici T := by
    rw [uIcc_of_le htt]
    exact fun s hs ↦ le_trans ht hs.1
  have hcontv : ContinuousOn (fun s ↦ ∇ f (γ s)) [[t, t + 1]] := hcont.mono hsub
  have hcontn : ContinuousOn (fun s ↦ ‖∇ f (γ s)‖) [[t, t + 1]] := hcontv.norm
  have hint1 : IntervalIntegrable (fun s ↦ ‖∇ f (γ s)‖) volume t (t + 1) :=
    hcontn.intervalIntegrable
  have hint2 : IntervalIntegrable (fun s ↦ ‖∇ f (γ s)‖ ^ 2) volume t (t + 1) :=
    (hcontn.pow 2).intervalIntegrable
  have hintv : IntervalIntegrable (fun s ↦ -∇ f (γ s)) volume t (t + 1) :=
    hcontv.neg.intervalIntegrable
  have hint3 : IntervalIntegrable (fun s ↦ (α * ‖∇ f (γ s)‖ ^ 2 + 1 / α) / 2) volume t (t + 1) :=
    ((hint2.const_mul α).add intervalIntegrable_const).div_const 2
  have hFTC : ∫ s in t..(t + 1), -∇ f (γ s) = γ (t + 1) - γ t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs ↦ hderiv s (hsub hs)) hintv
  have step1 : ‖γ (t + 1) - γ t‖ ≤ ∫ s in t..(t + 1), ‖∇ f (γ s)‖ := by
    rw [← hFTC]
    calc ‖∫ s in t..(t + 1), -∇ f (γ s)‖ ≤ ∫ s in t..(t + 1), ‖-∇ f (γ s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm htt
      _ = ∫ s in t..(t + 1), ‖∇ f (γ s)‖ := by simp
  have hinv : α * (1 / α) = 1 := by field_simp
  have step2 : (∫ s in t..(t + 1), ‖∇ f (γ s)‖)
      ≤ ∫ s in t..(t + 1), (α * ‖∇ f (γ s)‖ ^ 2 + 1 / α) / 2 := by
    refine intervalIntegral.integral_mono_on htt hint1 hint3 fun s _ ↦ ?_
    nlinarith [sq_nonneg (α * ‖∇ f (γ s)‖ - 1), norm_nonneg (∇ f (γ s)), hα, hinv]
  have step3 : (∫ s in t..(t + 1), (α * ‖∇ f (γ s)‖ ^ 2 + 1 / α) / 2)
      = (α * (∫ s in t..(t + 1), ‖∇ f (γ s)‖ ^ 2) + 1 / α) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint2.const_mul α)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp
  have hcurve : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici T) :=
    fun s hs ↦ (hderiv s hs).hasDerivWithinAt
  have step4 : (∫ s in t..(t + 1), ‖∇ f (γ s)‖ ^ 2) = f (γ t) - f (γ (t + 1)) :=
    integral_norm_gradient_sq_eq_sub hcurve hsub (fun s hs ↦ hdiff s (hsub hs)) hint2
  have hge1 : f p ≤ f (γ (t + 1)) := hge (t + 1) (le_trans ht htt)
  have hfinal : α * (f (γ t) - f (γ (t + 1))) ≤ α * (f (γ t) - f p) :=
    mul_le_mul_of_nonneg_left (by linarith) hα.le
  calc ‖γ (t + 1) - γ t‖ ≤ ∫ s in t..(t + 1), ‖∇ f (γ s)‖ := step1
    _ ≤ ∫ s in t..(t + 1), (α * ‖∇ f (γ s)‖ ^ 2 + 1 / α) / 2 := step2
    _ = (α * (f (γ t) - f (γ (t + 1))) + 1 / α) / 2 := by rw [step3, step4]
    _ ≤ (α * (f (γ t) - f p) + 1 / α) / 2 := by linarith

/-! ### The main theorems -/

/-- The data extracted from the hypotheses of the exponential-convergence theorems: a time `T`
after which the trajectory is confined to a neighbourhood of `p` on which Łojasiewicz's inequality
holds, together with everything the two estimates above ask for. -/
private theorem exists_time_of_tendsto
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ lam > 0, ∃ T, a < T ∧
      (∀ t ∈ Ici T, HasDerivAt γ (-∇ f (γ t)) t) ∧
      (∀ t ∈ Ici T, DifferentiableAt ℝ f (γ t)) ∧
      ContinuousOn (fun s ↦ ∇ f (γ s)) (Ici T) ∧
      (∀ t ∈ Ici T, lam * (f (γ t) - f p) ≤ ‖∇ f (γ t)‖ ^ 2) ∧
      (∀ t ∈ Ici T, f p ≤ f (γ t)) := by
  obtain ⟨lam, hlam, hloj⟩ := hp.exists_mul_sub_le_norm_gradient_sq
  have hloj' : ∀ᶠ x in 𝓝 p, lam * (f x - f p) ≤ ‖∇ f x‖ ^ 2 := by
    filter_upwards [hloj] with x hx
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) hlam.le).trans hx
  have hC2 : ∀ᶠ x in 𝓝 p, ContDiffAt ℝ 2 f x := hp.contDiffAt.eventually (by simp)
  have hev : ∀ᶠ t in atTop,
      (lam * (f (γ t) - f p) ≤ ‖∇ f (γ t)‖ ^ 2 ∧ ContDiffAt ℝ 2 f (γ t)) ∧ a < t :=
    (hconv.eventually (hloj'.and hC2)).and (eventually_gt_atTop a)
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  have hTa : a < T := (hT T le_rfl).2
  have hderiv : ∀ t ∈ Ici T, HasDerivAt γ (-∇ f (γ t)) t := by
    intro t ht
    have hta : a < t := lt_of_lt_of_le hTa ht
    exact (hγ t hta.le).hasDerivAt (Ici_mem_nhds hta)
  have hdiff : ∀ t ∈ Ici T, DifferentiableAt ℝ f (γ t) := fun t ht ↦
    ((hT t ht).1.2).differentiableAt (by simp)
  have hgradfun : (∇ f : E → E) = fun y ↦ (toDual ℝ E).symm (fderiv ℝ f y) := by
    funext y
    exact (toDual ℝ E).eq_symm_apply.2 toDual_gradient
  have hcont : ContinuousOn (fun s ↦ ∇ f (γ s)) (Ici T) := by
    intro s hs
    have hgs : ContinuousAt (∇ f) (γ s) := by
      rw [hgradfun]
      exact ((toDual ℝ E).symm.continuous.continuousAt).comp
        (((hT s hs).1.2).continuousAt_fderiv (by simp))
    exact (hgs.comp (hderiv s hs).continuousAt).continuousWithinAt
  have hcurve : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici T) :=
    fun s hs ↦ (hderiv s hs).hasDerivWithinAt
  have hanti : AntitoneOn (f ∘ γ) (Ici T) :=
    antitoneOn_comp_neg_gradient hcurve (convex_Ici T) hdiff
  have htend : Tendsto (fun t ↦ f (γ t)) atTop (𝓝 (f p)) :=
    (hp.contDiffAt.continuousAt).tendsto.comp hconv
  have hge : ∀ t ∈ Ici T, f p ≤ f (γ t) := by
    intro t ht
    refine le_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop t] with s hs
    exact hanti ht (le_trans ht hs) hs
  exact ⟨lam, hlam, T, hTa, hderiv, hdiff, hcont, fun t ht ↦ (hT t ht).1.1, hge⟩

/-- **The energy along a trajectory converging to a nondegenerate critical point decays
exponentially.** -/
theorem exists_sub_le_mul_exp_atTop (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop, f (γ t) - f p ≤ C * Real.exp (-(μ * t)) := by
  obtain ⟨lam, hlam, T, _, hderiv, hdiff, _, hloj, _⟩ := exists_time_of_tendsto hγ hp hconv
  refine ⟨lam, hlam, (|f (γ T) - f p| + 1) * Real.exp (lam * T), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  have hmain := energy_le_mul_exp hderiv hdiff hloj ht
  have hbound : f (γ T) - f p ≤ |f (γ T) - f p| + 1 := by
    have := le_abs_self (f (γ T) - f p)
    linarith
  have hexp : Real.exp (-(lam * (t - T))) = Real.exp (lam * T) * Real.exp (-(lam * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc f (γ t) - f p ≤ (f (γ T) - f p) * Real.exp (-(lam * (t - T))) := hmain
    _ ≤ (|f (γ T) - f p| + 1) * Real.exp (-(lam * (t - T))) :=
        mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ = (|f (γ T) - f p| + 1) * Real.exp (lam * T) * Real.exp (-(lam * t)) := by
        rw [hexp]; ring

/-- **A negative gradient trajectory converging to a nondegenerate critical point converges to it
exponentially fast.** The rate is half the Łojasiewicz constant of the critical point, which for a
nondegenerate critical point is controlled by the Hessian. -/
theorem exists_norm_sub_le_mul_exp_atTop (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop, ‖γ t - p‖ ≤ C * Real.exp (-(μ * t)) := by
  obtain ⟨lam, hlam, T, _, hderiv, hdiff, hcont, hloj, hge⟩ := exists_time_of_tendsto hγ hp hconv
  set G : ℝ := f (γ T) - f p + 1 with hGdef
  have hG : 0 < G := by
    have := hge T (le_refl T)
    simp only [hGdef]
    linarith
  set q : ℝ := Real.sqrt G
  have hq0 : 0 < q := Real.sqrt_pos.2 hG
  have hqne : q ≠ 0 := hq0.ne'
  have hqq : q * q = G := Real.mul_self_sqrt hG.le
  -- the energy is dominated by `G * exp (-lam * (t - T))`
  have hdecay : ∀ t ∈ Ici T, f (γ t) - f p ≤ G * Real.exp (-(lam * (t - T))) := by
    intro t ht
    refine (energy_le_mul_exp hderiv hdiff hloj ht).trans ?_
    exact mul_le_mul_of_nonneg_right (by simp [hGdef]) (Real.exp_pos _).le
  -- the trajectory moves by at most `sqrt (energy)` in unit time
  have hstep : ∀ t ∈ Ici T, ‖γ (t + 1) - γ t‖ ≤ q * Real.exp (-(lam / 2 * (t - T))) := by
    intro t ht
    set e : ℝ := Real.exp (lam / 2 * (t - T)) with hedef
    have hepos : (0 : ℝ) < e := Real.exp_pos _
    have hene : e ≠ 0 := hepos.ne'
    have hee : (e * e)⁻¹ = Real.exp (-(lam * (t - T))) := by
      rw [hedef, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      ring
    have hexpneg2 : Real.exp (-(lam / 2 * (t - T))) = e⁻¹ := by
      rw [hedef, Real.exp_neg]
    have hα : (0 : ℝ) < e / q := by positivity
    refine (norm_sub_add_one_le hderiv hdiff hcont hge ht hα).trans ?_
    have h1 : e / q * (f (γ t) - f p) ≤ q / e := by
      have hd := hdecay t ht
      rw [← hee] at hd
      calc e / q * (f (γ t) - f p) ≤ e / q * (G * (e * e)⁻¹) :=
            mul_le_mul_of_nonneg_left hd hα.le
        _ = q / e := by rw [← hqq]; field_simp
    have h2 : 1 / (e / q) = q / e := by field_simp
    rw [hexpneg2, h2]
    have h3 : q / e = q * e⁻¹ := by field_simp
    rw [h3] at h1 ⊢
    linarith
  -- summing the geometric series over the times `t, t + 1, t + 2, …`
  set r : ℝ := Real.exp (-(lam / 2)) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have hone : (0 : ℝ) < 1 - r := by linarith
  have htel : ∀ (n : ℕ) (t : ℝ), T ≤ t →
      ‖γ (t + n) - γ t‖ ≤ q * Real.exp (-(lam / 2 * (t - T))) * ((1 - r ^ n) / (1 - r)) := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ n ih =>
      intro t ht
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have hmem : t + (n : ℝ) ∈ Ici T := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        simp only [mem_Ici] at ht ⊢
        linarith
      have hexpn : Real.exp (-(lam / 2 * (t + (n : ℝ) - T)))
          = Real.exp (-(lam / 2 * (t - T))) * r ^ n := by
        rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      have hstep' : ‖γ (t + (n : ℝ) + 1) - γ (t + n)‖
          ≤ q * Real.exp (-(lam / 2 * (t - T))) * r ^ n := by
        refine (hstep _ hmem).trans_eq ?_
        rw [hexpn, mul_assoc]
      have hIH := ih t ht
      have hsum : ‖γ (t + ((n : ℝ) + 1)) - γ t‖
          ≤ ‖γ (t + (n : ℝ) + 1) - γ (t + n)‖ + ‖γ (t + n) - γ t‖ := by
        have heq : t + ((n : ℝ) + 1) = t + (n : ℝ) + 1 := by ring
        rw [heq, ← sub_add_sub_cancel (γ (t + (n : ℝ) + 1)) (γ (t + (n : ℝ))) (γ t)]
        exact norm_add_le _ _
      have hcalc : q * Real.exp (-(lam / 2 * (t - T))) * r ^ n
          + q * Real.exp (-(lam / 2 * (t - T))) * ((1 - r ^ n) / (1 - r))
          = q * Real.exp (-(lam / 2 * (t - T))) * ((1 - r ^ (n + 1)) / (1 - r)) := by
        field_simp
        ring
      rw [hcast]
      calc ‖γ (t + ((n : ℝ) + 1)) - γ t‖
          ≤ ‖γ (t + (n : ℝ) + 1) - γ (t + n)‖ + ‖γ (t + n) - γ t‖ := hsum
        _ ≤ q * Real.exp (-(lam / 2 * (t - T))) * r ^ n
            + q * Real.exp (-(lam / 2 * (t - T))) * ((1 - r ^ n) / (1 - r)) :=
            add_le_add hstep' hIH
        _ = _ := hcalc
  have hlimit : ∀ t ∈ Ici T,
      ‖γ t - p‖ ≤ q * Real.exp (-(lam / 2 * (t - T))) / (1 - r) := by
    intro t ht
    have htend : Tendsto (fun n : ℕ ↦ γ (t + n)) atTop (𝓝 p) :=
      hconv.comp (tendsto_atTop_add_const_left atTop t tendsto_natCast_atTop_atTop)
    have hnorm : Tendsto (fun n : ℕ ↦ ‖γ (t + n) - γ t‖) atTop (𝓝 ‖p - γ t‖) :=
      (htend.sub_const (γ t)).norm
    have hbd : ‖p - γ t‖ ≤ q * Real.exp (-(lam / 2 * (t - T))) / (1 - r) := by
      refine le_of_tendsto hnorm (Filter.Eventually.of_forall fun n ↦ ?_)
      refine (htel n t ht).trans ?_
      have hA : (0 : ℝ) ≤ q * Real.exp (-(lam / 2 * (t - T))) := by positivity
      have hrn : (0 : ℝ) ≤ r ^ n := by positivity
      have hle1 : (1 : ℝ) - r ^ n ≤ 1 := by linarith
      calc q * Real.exp (-(lam / 2 * (t - T))) * ((1 - r ^ n) / (1 - r))
          ≤ q * Real.exp (-(lam / 2 * (t - T))) * (1 / (1 - r)) := by
            refine mul_le_mul_of_nonneg_left ?_ hA
            gcongr
        _ = q * Real.exp (-(lam / 2 * (t - T))) / (1 - r) := by ring
    rwa [norm_sub_rev] at hbd
  refine ⟨lam / 2, by linarith, q * Real.exp (lam / 2 * T) / (1 - r), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  refine (hlimit t ht).trans_eq ?_
  have hexp : Real.exp (-(lam / 2 * (t - T)))
      = Real.exp (lam / 2 * T) * Real.exp (-(lam / 2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- **The backward-time form.** A negative gradient trajectory converging to a nondegenerate
critical point as `t → -∞` converges to it exponentially fast. Reversing time turns the trajectory
into a negative gradient trajectory of `-f`, whose critical point at `p` is again nondegenerate. -/
theorem exists_norm_sub_le_mul_exp_atBot (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atBot (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atBot, ‖γ t - p‖ ≤ C * Real.exp (μ * t) := by
  have hmaps : MapsTo (fun t : ℝ ↦ -t) (Ici (-a)) (Iic a) := by
    intro s hs
    simp only [mem_Ici] at hs
    simp only [mem_Iic]
    linarith
  have hrev : IsIntegralCurveOn (fun t ↦ γ (-t)) (fun _ x ↦ -∇ (-f) x) (Ici (-a)) := by
    intro t ht
    have hneg : HasDerivWithinAt (fun t : ℝ ↦ -t) (-1) (Ici (-a)) t :=
      ((hasDerivAt_id t).neg).hasDerivWithinAt
    have hcomp := (hγ (-t) (hmaps ht)).scomp t hneg hmaps
    simpa [Function.comp_def, gradient_neg] using hcomp
  have hconv' : Tendsto (fun t ↦ γ (-t)) atTop (𝓝 p) := hconv.comp tendsto_neg_atTop_atBot
  obtain ⟨μ, hμ, C, hC, hbound⟩ := exists_norm_sub_le_mul_exp_atTop hrev hp.neg hconv'
  refine ⟨μ, hμ, C, hC, ?_⟩
  filter_upwards [tendsto_neg_atBot_atTop.eventually hbound] with t ht
  simpa using ht

/-- The exponential convergence of a trajectory to a nondegenerate critical point, in `IsBigO`
form. -/
theorem isBigO_exp_atTop (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ μ > 0, (fun t ↦ γ t - p) =O[atTop] fun t ↦ Real.exp (-(μ * t)) := by
  obtain ⟨μ, hμ, C, _, hbound⟩ := exists_norm_sub_le_mul_exp_atTop hγ hp hconv
  refine ⟨μ, hμ, IsBigO.of_bound C ?_⟩
  filter_upwards [hbound] with t ht
  rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

end IsIntegralCurveOn

end TauCeti
