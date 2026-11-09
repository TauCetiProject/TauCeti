/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Analysis.Calculus.Morse.Linearization
-- Private: Grönwall's inequality, the fundamental theorem of calculus, reparametrization of an
-- integral curve, and scalar multiplication of the gradient are used only inside proofs; no
-- declaration below exposes their APIs.
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.Transform
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
compactness and gluing arguments that assemble the Morse and Floer complexes.

## The argument

Everything rests on the **Morse form of Łojasiewicz's gradient inequality**, with the optimal
exponent `1/2`: near a nondegenerate critical point,

`lam * |f x - f p| ≤ ‖∇ f x‖ ^ 2`.

Both halves of it come from the linearization `TauCeti.hessianOperator` of the gradient. Since the
Hessian operator is invertible, the gradient is bounded below by a multiple of the distance to `p`
(`TauCeti.IsNondegenerateCriticalPoint.exists_mul_norm_sub_le_norm_gradient`); since it vanishes at
`p` and is bounded above by a multiple of that distance, the mean value inequality bounds the
energy by the *square* of the distance (`ContDiffAt.exists_abs_sub_le_mul_norm_sub_sq`, which needs
no nondegeneracy). Comparing the two gives the inequality
(`TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_gradient_sq`).

Along the trajectory the energy `g t = f (γ t) - f p` is nonnegative — `f ∘ γ` is antitone and
tends to `f p` — and satisfies `g' = -‖∇ f (γ t)‖ ^ 2 ≤ -lam * g`, so `g` decays like
`exp (-lam * t)`.

That decay does not by itself bound `‖γ t - p‖`: an indefinite quadratic approximation has null
directions, so the energy difference does not uniformly control the squared distance to `p`. The
distance is instead recovered from the *length* of the trajectory. On a time interval of length
one the energy identity
`IsIntegralCurveOn.integral_norm_gradient_sq_eq_sub` computes `∫ ‖∇ f (γ s)‖ ^ 2`, and the
elementary bound `v ≤ (α * v ^ 2 + 1 / α) / 2`, optimized in `α`, converts it into a bound for
`∫ ‖∇ f (γ s)‖ = ∫ ‖γ' s‖`, hence for `‖γ (t + 1) - γ t‖`, by the square root of the energy.
Summing the resulting geometric series over the times `t, t + 1, t + 2, …` and passing to the limit
bounds `‖γ t - p‖` by a multiple of `sqrt (g t)`, which decays like `exp (-lam * t / 2)`.

## Main results

* `TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_gradient_sq`: **the Morse form
  of Łojasiewicz's gradient inequality**, with exponent `1/2`.
* `IsIntegralCurveOn.exists_sub_le_mul_exp_atTop`: the energy along a trajectory
  converging to a nondegenerate critical point decays exponentially.
* `IsIntegralCurveOn.exists_norm_sub_le_mul_exp_atTop`: **the trajectory itself
  converges exponentially fast**.
* `IsIntegralCurveOn.exists_norm_gradient_le_mul_exp_atTop` and
  `IsIntegralCurveOn.exists_norm_deriv_le_mul_exp_atTop`: the gradient and velocity decay
  exponentially.
* The corresponding `atBot` theorems give backward-time energy, position, gradient, and velocity
  decay by reversing time and negating the function.

## References

* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 2.
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2, where the exponential convergence of
  trajectories is what places them in the weighted Sobolev spaces of the Fredholm theory.
-/

public section

open Filter InnerProductSpace MeasureTheory Metric Set TauCeti
open scoped Gradient Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {p : E} {a : ℝ}

/-! ### Decay along a trajectory -/

namespace IsIntegralCurveOn

variable {T lam : ℝ}

/-- Along a negative gradient trajectory the energy `f (γ t) - f p` has derivative
`-‖∇ f (γ t)‖ ^ 2`. -/
private theorem hasDerivAt_energy {t : ℝ} (hderiv : HasDerivAt γ (-∇ f (γ t)) t)
    (hdiff : DifferentiableAt ℝ f (γ t)) :
    HasDerivAt (fun s ↦ f (γ s) - f p) (-‖∇ f (γ t)‖ ^ 2) t := by
  refine ((hdiff.hasFDerivAt.comp_hasDerivAt t hderiv).congr_deriv ?_).sub_const _
  rw [map_neg, ← inner_gradient_left, real_inner_self_eq_norm_sq]

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
  have hint2 : IntervalIntegrable (fun s ↦ ‖∇ f (γ s)‖ ^ 2) volume t (t + 1) :=
    (hcontv.norm.pow 2).intervalIntegrable
  have hFTC : ∫ s in t..(t + 1), -∇ f (γ s) = γ (t + 1) - γ t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs ↦ hderiv s (hsub hs))
      hcontv.neg.intervalIntegrable
  have hE : (∫ s in t..(t + 1), ‖∇ f (γ s)‖ ^ 2) = f (γ t) - f (γ (t + 1)) :=
    integral_norm_gradient_sq_eq_sub (fun s hs ↦ (hderiv s hs).hasDerivWithinAt) hsub
      (fun s hs ↦ hdiff s (hsub hs))
  have hge1 : f p ≤ f (γ (t + 1)) := hge (t + 1) (le_trans ht htt)
  calc ‖γ (t + 1) - γ t‖ ≤ ∫ s in t..(t + 1), ‖∇ f (γ s)‖ := by
        rw [← hFTC]
        simpa using intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun s ↦ -∇ f (γ s)) htt
    _ ≤ ∫ s in t..(t + 1), (α * ‖∇ f (γ s)‖ ^ 2 + 1 / α) / 2 := by
        refine intervalIntegral.integral_mono_on htt hcontv.norm.intervalIntegrable
          (((hint2.const_mul α).add intervalIntegrable_const).div_const 2) fun s _ ↦ ?_
        have hyoung := two_mul_le_add_mul_sq (a := ‖∇ f (γ s)‖) (b := 1) hα
        norm_num [one_div] at hyoung ⊢
        linarith
    _ = (α * (f (γ t) - f (γ (t + 1))) + 1 / α) / 2 := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint2.const_mul α)
          intervalIntegrable_const, intervalIntegral.integral_const_mul, hE]
        simp
    _ ≤ (α * (f (γ t) - f p) + 1 / α) / 2 := by nlinarith

/-! ### The main theorems -/

/-- **The unit-time step is at most the square root of the energy.** If the energy decays like
`q ^ 2 * exp (-(lam * (t - T)))` after time `T`, then the trajectory moves in unit time by at most
`q * exp (-(lam / 2 * (t - T)))`; this is `norm_sub_add_one_le` with
`α = exp (lam / 2 * (t - T)) / q`. -/
private theorem norm_sub_add_one_le_mul_exp
    (hderiv : ∀ s ∈ Ici T, HasDerivAt γ (-∇ f (γ s)) s)
    (hdiff : ∀ s ∈ Ici T, DifferentiableAt ℝ f (γ s))
    (hcont : ContinuousOn (fun s ↦ ∇ f (γ s)) (Ici T))
    (hge : ∀ s ∈ Ici T, f p ≤ f (γ s)) {q : ℝ} (hq : 0 < q)
    (hdecay : ∀ t ∈ Ici T, f (γ t) - f p ≤ q * q * Real.exp (-(lam * (t - T)))) :
    ∀ t ∈ Ici T, ‖γ (t + 1) - γ t‖ ≤ q * Real.exp (-(lam / 2 * (t - T))) := by
  intro t ht
  set e : ℝ := Real.exp (lam / 2 * (t - T)) with hedef
  have hepos : (0 : ℝ) < e := Real.exp_pos _
  have hee : (e * e)⁻¹ = Real.exp (-(lam * (t - T))) := by
    rw [hedef, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have hα : (0 : ℝ) < e / q := by positivity
  refine (norm_sub_add_one_le hderiv hdiff hcont hge ht hα).trans ?_
  have h1 : e / q * (f (γ t) - f p) ≤ q / e := by
    have hd := hdecay t ht
    rw [← hee] at hd
    calc e / q * (f (γ t) - f p) ≤ e / q * (q * q * (e * e)⁻¹) :=
          mul_le_mul_of_nonneg_left hd hα.le
      _ = q / e := by field_simp
  rw [Real.exp_neg, ← hedef, one_div_div]
  rw [div_eq_mul_inv q e] at h1 ⊢
  linarith

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
  obtain ⟨lam, hlam, hloj⟩ := hp.exists_mul_abs_sub_le_norm_gradient_sq
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
  exact ⟨lam, hlam, exists_le_mul_exp_atTop_of_hasDerivAt_le_neg_mul (lam := lam)
    (fun s hs ↦ hasDerivAt_energy (hderiv s hs) (hdiff s hs)) fun s hs ↦ by linarith [hloj s hs]⟩

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
  have hdecay : ∀ t ∈ Ici T, f (γ t) - f p ≤ q * q * Real.exp (-(lam * (t - T))) := by
    intro t ht
    refine (le_mul_exp_of_hasDerivAt_le_neg_mul (lam := lam)
      (fun s hs ↦ hasDerivAt_energy (hderiv s hs) (hdiff s hs))
      (fun s hs ↦ by linarith [hloj s hs]) ht).trans ?_
    rw [hqq]
    exact mul_le_mul_of_nonneg_right (by simp [hGdef]) (Real.exp_pos _).le
  have hstep := norm_sub_add_one_le_mul_exp hderiv hdiff hcont hge hq0 hdecay
  -- summing the geometric series over the times `t, t + 1, t + 2, …`
  set r : ℝ := Real.exp (-(lam / 2)) with hrdef
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have hone : (0 : ℝ) < 1 - r := by linarith
  have hlimit : ∀ t ∈ Ici T,
      ‖γ t - p‖ ≤ q * Real.exp (-(lam / 2 * (t - T))) / (1 - r) := by
    intro t ht
    have h := dist_le_of_le_geometric_of_tendsto₀ (f := fun n : ℕ ↦ γ (t + n)) r
      (q * Real.exp (-(lam / 2 * (t - T)))) hr1 (fun n ↦ ?_)
      (hconv.comp (tendsto_atTop_add_const_left atTop t tendsto_natCast_atTop_atTop))
    · simpa [dist_eq_norm] using h
    · have hmem : t + (n : ℝ) ∈ Ici T := by
        simp only [mem_Ici] at ht ⊢
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [dist_comm, dist_eq_norm, Nat.cast_succ, ← add_assoc]
      refine (hstep _ hmem).trans_eq ?_
      rw [hrdef, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      ring
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

/-- **The gradient along a trajectory converging to a nondegenerate critical point decays
exponentially.** -/
theorem exists_norm_gradient_le_mul_exp_atTop
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop, ‖∇ f (γ t)‖ ≤ C * Real.exp (-(μ * t)) := by
  obtain ⟨μ, hμ, C, hC, hpos⟩ := exists_norm_sub_le_mul_exp_atTop hγ hp hconv
  obtain ⟨D, hD, hgrad⟩ := hp.contDiffAt.exists_norm_gradient_le_mul_norm_sub
    hp.gradient_eq_zero
  refine ⟨μ, hμ, D * C, mul_pos hD hC, ?_⟩
  filter_upwards [hpos, hconv.eventually hgrad] with t ht hgradt
  calc ‖∇ f (γ t)‖ ≤ D * ‖γ t - p‖ := hgradt
    _ ≤ D * (C * Real.exp (-(μ * t))) := mul_le_mul_of_nonneg_left ht hD.le
    _ = D * C * Real.exp (-(μ * t)) := by ring

/-- **The velocity of a trajectory converging to a nondegenerate critical point decays
exponentially.** -/
theorem exists_norm_deriv_le_mul_exp_atTop
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop, ‖deriv γ t‖ ≤ C * Real.exp (-(μ * t)) := by
  obtain ⟨μ, hμ, C, hC, hbound⟩ :=
    exists_norm_gradient_le_mul_exp_atTop hγ hp hconv
  refine ⟨μ, hμ, C, hC, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop a] with t ht hta
  have hderiv := (hγ t hta.le).hasDerivAt (Ici_mem_nhds hta)
  rw [hderiv.deriv, norm_neg]
  exact ht

/-- Reversing time turns a negative gradient trajectory for `f` on `Iic a` into a negative
gradient trajectory for `-f` on `Ici (-a)`. -/
private theorem comp_neg_isIntegralCurveOn_neg
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic a)) :
    IsIntegralCurveOn (fun t ↦ γ (-t)) (fun _ x ↦ -∇ (-f) x) (Ici (-a)) := by
  have hgrad_neg : ∀ y : E, ∇ (-f) y = -∇ f y := fun y ↦ gradient_neg
  have hdomain : {t : ℝ | t * (-1) ∈ Iic a} = Ici (-a) := by
    ext t
    simp only [mem_ofPred_eq, mem_Iic, mem_Ici, mul_neg, mul_one, neg_le]
  have hfield : ((-1 : ℝ) • (fun _ : ℝ ↦ fun x ↦ -∇ f x)) ∘ (fun t : ℝ ↦ t * (-1)) =
      (fun _ : ℝ ↦ fun x ↦ -∇ (-f) x) := by
    funext t y
    simp only [Function.comp_apply, neg_one_smul, Pi.neg_apply, hgrad_neg, neg_neg]
  have hcomp : γ ∘ (fun t : ℝ ↦ t * (-1)) = fun t ↦ γ (-t) := by
    funext t
    simp
  rw [← hcomp, ← hdomain, ← hfield]
  exact hγ.comp_mul (-1)

/-- **The energy along a backward trajectory converging to a nondegenerate critical point decays
exponentially.** -/
theorem exists_sub_le_mul_exp_atBot (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atBot (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atBot, f p - f (γ t) ≤ C * Real.exp (μ * t) := by
  have hrev := comp_neg_isIntegralCurveOn_neg hγ
  have hconv' : Tendsto (fun t ↦ γ (-t)) atTop (𝓝 p) := hconv.comp tendsto_neg_atTop_atBot
  obtain ⟨μ, hμ, C, hC, hbound⟩ := exists_sub_le_mul_exp_atTop hrev hp.neg hconv'
  refine ⟨μ, hμ, C, hC, ?_⟩
  filter_upwards [tendsto_neg_atBot_atTop.eventually hbound] with t ht
  simpa [sub_eq_add_neg, add_comm] using ht

/-- **The backward-time form.** A negative gradient trajectory converging to a nondegenerate
critical point as `t → -∞` converges to it exponentially fast. Reversing time turns the trajectory
into a negative gradient trajectory of `-f`, whose critical point at `p` is again nondegenerate. -/
theorem exists_norm_sub_le_mul_exp_atBot (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atBot (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atBot, ‖γ t - p‖ ≤ C * Real.exp (μ * t) := by
  have hrev := comp_neg_isIntegralCurveOn_neg hγ
  have hconv' : Tendsto (fun t ↦ γ (-t)) atTop (𝓝 p) := hconv.comp tendsto_neg_atTop_atBot
  obtain ⟨μ, hμ, C, hC, hbound⟩ := exists_norm_sub_le_mul_exp_atTop hrev hp.neg hconv'
  refine ⟨μ, hμ, C, hC, ?_⟩
  filter_upwards [tendsto_neg_atBot_atTop.eventually hbound] with t ht
  simpa using ht

/-- **The gradient along a backward trajectory converging to a nondegenerate critical point
decays exponentially.** -/
theorem exists_norm_gradient_le_mul_exp_atBot
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atBot (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atBot, ‖∇ f (γ t)‖ ≤ C * Real.exp (μ * t) := by
  obtain ⟨μ, hμ, C, hC, hpos⟩ := exists_norm_sub_le_mul_exp_atBot hγ hp hconv
  obtain ⟨D, hD, hgrad⟩ := hp.contDiffAt.exists_norm_gradient_le_mul_norm_sub
    hp.gradient_eq_zero
  refine ⟨μ, hμ, D * C, mul_pos hD hC, ?_⟩
  filter_upwards [hpos, hconv.eventually hgrad] with t ht hgradt
  calc ‖∇ f (γ t)‖ ≤ D * ‖γ t - p‖ := hgradt
    _ ≤ D * (C * Real.exp (μ * t)) := mul_le_mul_of_nonneg_left ht hD.le
    _ = D * C * Real.exp (μ * t) := by ring

/-- **The velocity of a backward trajectory converging to a nondegenerate critical point decays
exponentially.** -/
theorem exists_norm_deriv_le_mul_exp_atBot
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic a))
    (hp : IsNondegenerateCriticalPoint f p) (hconv : Tendsto γ atBot (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atBot, ‖deriv γ t‖ ≤ C * Real.exp (μ * t) := by
  obtain ⟨μ, hμ, C, hC, hbound⟩ :=
    exists_norm_gradient_le_mul_exp_atBot hγ hp hconv
  refine ⟨μ, hμ, C, hC, ?_⟩
  filter_upwards [hbound, eventually_lt_atBot a] with t ht hta
  have hderiv := (hγ t hta.le).hasDerivAt (Iic_mem_nhds hta)
  rw [hderiv.deriv, norm_neg]
  exact ht

end IsIntegralCurveOn
