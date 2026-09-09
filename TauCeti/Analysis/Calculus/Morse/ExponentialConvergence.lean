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
import Mathlib.Analysis.ODE.Gronwall
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
`TauCeti.IsIntegralCurveOn.integral_norm_gradient_sq_eq_sub` computes `∫ ‖∇ f (γ s)‖ ^ 2`, and the
elementary bound `v ≤ (α * v ^ 2 + 1 / α) / 2`, optimized in `α`, converts it into a bound for
`∫ ‖∇ f (γ s)‖ = ∫ ‖γ' s‖`, hence for `‖γ (t + 1) - γ t‖`, by the square root of the energy.
Summing the resulting geometric series over the times `t, t + 1, t + 2, …` and passing to the limit
bounds `‖γ t - p‖` by a multiple of `sqrt (g t)`, which decays like `exp (-lam * t / 2)`.

## Main results

* `TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_gradient_sq`: **the Morse form
  of Łojasiewicz's gradient inequality**, with exponent `1/2`.
* `TauCeti.IsIntegralCurveOn.exists_sub_le_mul_exp_atTop`: the energy along a trajectory
  converging to a nondegenerate critical point decays exponentially.
* `TauCeti.IsIntegralCurveOn.exists_norm_sub_le_mul_exp_atTop`: **the trajectory itself
  converges exponentially fast**.
* `TauCeti.IsIntegralCurveOn.exists_norm_gradient_le_mul_exp_atTop` and
  `TauCeti.IsIntegralCurveOn.exists_norm_deriv_le_mul_exp_atTop`: the gradient and velocity decay
  exponentially.
* The corresponding `atBot` theorems give backward-time energy, position, gradient, and velocity
  decay by reversing time and negating the function.

## References

* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 2.
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2, where the exponential convergence of
  trajectories is what places them in the weighted Sobolev spaces of the Fredholm theory.
-/

public section

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped Gradient Interval Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {p : E} {a : ℝ}

/-! ### Decay along a trajectory -/

namespace IsIntegralCurveOn

variable {T lam : ℝ}

/-- **Exponential decay of the energy.** If along a trajectory the energy is nonnegative and
satisfies Łojasiewicz's inequality with constant `lam`, then it decays like `exp (-lam * t)`,
by Grönwall's inequality. -/
private theorem energy_le_mul_exp
    (hderiv : ∀ t ∈ Ici T, HasDerivAt γ (-∇ f (γ t)) t)
    (hdiff : ∀ t ∈ Ici T, DifferentiableAt ℝ f (γ t))
    (hloj : ∀ t ∈ Ici T, lam * (f (γ t) - f p) ≤ ‖∇ f (γ t)‖ ^ 2)
    {t : ℝ} (ht : T ≤ t) :
    f (γ t) - f p ≤ (f (γ T) - f p) * Real.exp (-(lam * (t - T))) := by
  let g : ℝ → ℝ := fun s ↦ f (γ s) - f p
  let g' : ℝ → ℝ := fun s ↦ -‖∇ f (γ s)‖ ^ 2
  have hgderiv : ∀ s ∈ Ici T, HasDerivAt g (g' s) s := by
    intro s hs
    have hc := (hdiff s hs).hasFDerivAt.comp_hasDerivAt s (hderiv s hs)
    have hcomp : HasDerivAt (fun u ↦ f (γ u)) (-‖∇ f (γ s)‖ ^ 2) s := by
      refine hc.congr_deriv ?_
      rw [map_neg, ← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact hcomp.sub_const _
  have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
    (f := g) (f' := g') (δ := g T) (K := -lam) (ε := 0) (a := T) (b := t)
    (fun s hs ↦ (hgderiv s (mem_Ici.2 hs.1)).continuousAt.continuousWithinAt)
    (fun s hs r hr ↦
      (hgderiv s (mem_Ici.2 hs.1)).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun s hs ↦ by
      have hlj := hloj s (mem_Ici.2 hs.1)
      dsimp [g, g']
      linarith)
    t ⟨ht, le_rfl⟩
  simpa only [g, gronwallBound_ε0, neg_mul] using hgronwall

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
  have step2 : (∫ s in t..(t + 1), ‖∇ f (γ s)‖)
      ≤ ∫ s in t..(t + 1), (α * ‖∇ f (γ s)‖ ^ 2 + 1 / α) / 2 := by
    refine intervalIntegral.integral_mono_on htt hint1 hint3 fun s _ ↦ ?_
    have hyoung := two_mul_le_add_mul_sq (a := ‖∇ f (γ s)‖) (b := 1) hα
    norm_num [one_div] at hyoung ⊢
    linarith
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
  have hgrad_neg : ∀ y : E, ∇ (-f) y = -∇ f y := fun y ↦ by
    simpa using (gradient_const_smul (𝕜 := ℝ) (F := E) (f := f) (x := y) (-1))
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

end TauCeti
