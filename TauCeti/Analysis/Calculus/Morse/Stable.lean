/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.MonotoneConvergence
public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Dynamics.Flow.Stable
-- Private: used only to recognize a differentiable curve with zero derivative as constant.
import Mathlib.Analysis.Calculus.MeanValue
-- Private: monotonicity from the derivative, the derivative of the norm and the gradient of `-f`
-- in the energy-barrier argument.
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.Gradient

/-!
# Stable and unstable sets of a negative gradient flow

This file specializes stable and unstable sets to a flow whose trajectories solve the negative
gradient equation.  Along such a flow the defining function is antitone.  Consequently, a point
in the stable set of `q` has value at least `f q`, while a point in the unstable set of `p` has
value at most `f p`.

The intersection `unstableSet φ p ∩ stableSet φ q` is the set underlying the parametrized Morse
trajectories from `p` to `q`.  It is empty unless `f q ≤ f p`; when `p ≠ q`, the inequality is
strict.  In particular a negative gradient flow has no nonconstant homoclinic trajectories.

Reversing time turns a negative gradient flow of `f` into one of `-f`, exchanging the stable and
unstable sets.  An energy barrier confines trajectories: if `‖∇ f‖ ≥ c` on an annulus about `x`,
a trajectory converging to `x` cannot cross the annulus unless it starts at least `c` times the
width of the annulus above `f x`.  This is what makes the stable set agree, near a nondegenerate
critical point, with the set of trajectories confined to a small ball, and hence what makes it an
embedded submanifold (`TauCeti.Analysis.Calculus.Morse.GlobalChart`).

## Main declarations

* `Flow.IsNegativeGradient.value_le_of_mem_stableSet`: stable-set points lie above the
  limiting critical value.
* `Flow.IsNegativeGradient.value_ge_of_mem_unstableSet`: unstable-set points lie below
  the limiting critical value.
* `Flow.IsNegativeGradient.value_le_of_mem_unstableSet_inter_stableSet`: a connecting
  trajectory goes from a weakly higher critical value to a lower one.
* `Flow.IsNegativeGradient.value_lt_of_mem_unstableSet_inter_stableSet`: the inequality is
  strict for distinct endpoints.
* `Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet`: there are no
  nonconstant homoclinic trajectories.
* `Flow.IsNegativeGradient.reverse`: the reversed flow is a negative gradient flow of `-f`.
* `Flow.IsNegativeGradient.dist_le_of_mem_stableSet` and
  `Flow.IsNegativeGradient.dist_le_of_mem_unstableSet`: the energy barrier confining stable and
  unstable trajectories that start low enough near their limit.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function InnerProductSpace Set Topology
open scoped Gradient

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q x : E}

/-- A point in the stable set of `p` has value at least `f p`.  Only differentiability along the
chosen orbit and continuity at its limiting point are required. -/
theorem IsNegativeGradient.value_le_of_mem_stableSet (hφ : IsNegativeGradient φ f)
    (hx : x ∈ stableSet φ p) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) :
    f p ≤ f x := by
  have hlim : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_stableSet.mp hx)
  simpa only [_root_.Flow.map_zero_apply] using (hφ.orbit_antitone x hf).le_of_tendsto hlim 0

/-- A point in the unstable set of `p` has value at most `f p`.  Only differentiability along the
chosen orbit and continuity at its limiting point are required. -/
theorem IsNegativeGradient.value_ge_of_mem_unstableSet (hφ : IsNegativeGradient φ f)
    (hx : x ∈ unstableSet φ p) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) :
    f x ≤ f p := by
  have hlim : Tendsto (fun t ↦ f (φ t x)) atBot (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_unstableSet.mp hx)
  simpa only [_root_.Flow.map_zero_apply] using (hφ.orbit_antitone x hf).ge_of_tendsto hlim 0

/-- If an orbit converges to `p` in backward time and to `q` in forward time, then `f q ≤ f p`. -/
theorem IsNegativeGradient.value_le_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    f q ≤ f p :=
  (hφ.value_le_of_mem_stableSet hx.2 hf hfq).trans
    (hφ.value_ge_of_mem_unstableSet hx.1 hf hfp)

/-- An orbit on which `f` is constant is constant: any two of its points coincide. -/
private theorem IsNegativeGradient.orbit_eq_of_const_value (hφ : IsNegativeGradient φ f)
    (hf : ∀ t, DifferentiableAt ℝ f (φ t x)) (hc : ∀ t, f (φ t x) = f x) (t u : ℝ) :
    φ t x = φ u x := by
  let γ : ℝ → E := fun v ↦ φ v x
  have hγ : IsIntegralCurve γ (fun _ y ↦ -∇ f y) := hφ.isIntegralCurve x
  apply is_const_of_deriv_eq_zero (fun v ↦ (hγ v).differentiableAt) _ t u
  intro v
  have hgrad : ∇ f (γ v) = 0 :=
    TauCeti.IsIntegralCurve.gradient_eq_zero_of_eventually_const_value hγ (hf v)
      (Eventually.of_forall hc)
  rw [(hγ v).deriv]
  simp only [hgrad, neg_zero]

/-- If an orbit's values converge to the same constant in both forward and backward time, then the
orbit is constant: every time map fixes its initial point. -/
private theorem IsNegativeGradient.orbit_eq_self_of_tendsto_const_value
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    {c : ℝ} (hbot : Tendsto (fun t ↦ f (φ t x)) atBot (𝓝 c))
    (htop : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 c)) :
    ∀ t, φ t x = x := by
  have hanti := hφ.orbit_antitone x hf
  have hvalue : ∀ t, f (φ t x) = f x := fun t ↦ by
    simpa only [_root_.Flow.map_zero_apply] using le_antisymm
      ((hanti.ge_of_tendsto hbot t).trans (hanti.le_of_tendsto htop 0))
      ((hanti.ge_of_tendsto hbot 0).trans (hanti.le_of_tendsto htop t))
  intro t
  simpa only [_root_.Flow.map_zero_apply] using
    hφ.orbit_eq_of_const_value hf hvalue t 0

/-- A connecting orbit whose two endpoint values agree lies on the constant orbit through the
shared endpoint: `x = p` and `p = q`. -/
theorem IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet_of_value_eq
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) (hpq : f p = f q) :
    x = p ∧ p = q := by
  have horbit := hφ.orbit_eq_self_of_tendsto_const_value hf
    (hfp.tendsto.comp (mem_unstableSet.mp hx.1))
    (by simpa only [hpq, Function.comp_def] using
      hfq.tendsto.comp (mem_stableSet.mp hx.2))
  have hxbot : Tendsto (fun _ : ℝ ↦ x) atBot (𝓝 p) := by
    simpa only [horbit] using mem_unstableSet.mp hx.1
  have hxtop : Tendsto (fun _ : ℝ ↦ x) atTop (𝓝 q) := by
    simpa only [horbit] using mem_stableSet.mp hx.2
  have hpx : x = p := tendsto_nhds_unique tendsto_const_nhds hxbot
  have hxq : x = q := tendsto_nhds_unique tendsto_const_nhds hxtop
  exact ⟨hpx, hpx ▸ hxq⟩

/-- A negative gradient connecting orbit between distinct endpoints strictly lowers the defining
function. -/
theorem IsNegativeGradient.value_lt_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q) (hpq : p ≠ q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    f q < f p := by
  refine lt_of_le_of_ne
    (hφ.value_le_of_mem_unstableSet_inter_stableSet hf hfp hfq hx) ?_
  intro hvalue
  exact hpq
    (hφ.eq_of_mem_unstableSet_inter_stableSet_of_value_eq hf hfp hfq hx
      hvalue.symm).2

/-- A point lying in both the stable and unstable set of the same endpoint lies on the constant
orbit of that endpoint.  Thus a negative gradient flow has no nonconstant homoclinic orbit. -/
theorem IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ p) :
    x = p :=
  (hφ.eq_of_mem_unstableSet_inter_stableSet_of_value_eq hf hfp hfp hx rfl).1

variable {z : E}

/-- Reversing time turns a negative gradient flow of `f` into a negative gradient flow of `-f`. -/
theorem IsNegativeGradient.reverse (hφ : IsNegativeGradient φ f) :
    IsNegativeGradient φ.reverse (-f) := by
  refine isNegativeGradient_iff.2 fun z t ↦ ?_
  have hgrad : ∇ (-f) (φ (-t) z) = -∇ f (φ (-t) z) := by
    simpa using TauCeti.gradient_const_smul (-1 : ℝ) (f := f) (x := φ (-t) z)
  have hd := (hφ.isIntegralCurve z (-t)).scomp t (hasDerivAt_neg t)
  simpa [Function.comp_def, hgrad] using hd

/-- Along a negative gradient trajectory, `f + c * dist (·) x` is antitone on a time interval
in whose interior the trajectory avoids `x` and `c ≤ ‖∇ f‖`: there the value of `f` drops at
least `c` times as fast as the trajectory can move away from `x`. -/
private theorem antitoneOn_add_mul_dist {γ : ℝ → E}
    (hγ : IsIntegralCurve γ (fun _ w ↦ -∇ f w)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    {c a b : ℝ} (hc : 0 ≤ c) (hann : ∀ τ ∈ Ioo a b, γ τ ≠ x ∧ c ≤ ‖∇ f (γ τ)‖) :
    AntitoneOn (fun τ ↦ f (γ τ) + c * dist (γ τ) x) (Icc a b) := by
  simp only [dist_eq_norm]
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (f' := fun τ ↦ -‖∇ f (γ τ)‖ ^ 2 + c * fderiv ℝ (‖·‖) (γ τ - x) (-∇ f (γ τ)))
  · exact ((continuous_iff_continuousAt.2 fun τ ↦
      (hf τ).continuousAt.comp hγ.continuous.continuousAt).add
        (continuous_const.mul ((hγ.continuous.sub continuous_const).norm))).continuousOn
  · intro τ hτ
    rw [interior_Icc] at hτ
    have hnorm : HasDerivAt (fun σ ↦ ‖γ σ - x‖)
        (fderiv ℝ (‖·‖) (γ τ - x) (-∇ f (γ τ))) τ :=
      ((contDiffAt_norm ℝ (sub_ne_zero.2 (hann τ hτ).1)).differentiableAt
        one_ne_zero).hasFDerivAt.comp_hasDerivAt τ ((hγ τ).sub_const x)
    exact ((TauCeti.IsIntegralCurve.hasDerivAt_comp_neg_gradient hγ (hf τ)).add
      (hnorm.const_mul c)).hasDerivWithinAt
  · intro τ hτ
    rw [interior_Icc] at hτ
    -- The derivative of the norm has operator norm at most one.
    have hL : fderiv ℝ (‖·‖) (γ τ - x) (-∇ f (γ τ)) ≤ ‖∇ f (γ τ)‖ :=
      calc fderiv ℝ (‖·‖) (γ τ - x) (-∇ f (γ τ))
          ≤ ‖fderiv ℝ (‖·‖) (γ τ - x)‖ * ‖-∇ f (γ τ)‖ :=
            (Real.le_norm_self _).trans (ContinuousLinearMap.le_opNorm _ _)
        _ ≤ 1 * ‖-∇ f (γ τ)‖ := by
            gcongr
            simpa using norm_fderiv_le_of_lipschitz ℝ (f := fun v : E ↦ ‖v‖)
              (x₀ := γ τ - x) lipschitzWith_one_norm
        _ = ‖∇ f (γ τ)‖ := by rw [one_mul, norm_neg]
    nlinarith [norm_nonneg (∇ f (γ τ)), (hann τ hτ).2]

/-- **An energy barrier confines stable trajectories.** Suppose that `‖∇ f‖ ≥ c` on the open
annulus `s < dist w x < r`. A trajectory of a negative gradient flow converging to `x` that
starts within distance `s` of `x` at a value below `f x + c * (r - s)` never leaves the closed
ball of radius `r` about `x`: to cross the annulus it would have to lose at least `c * (r - s)` of
`f`, more than it has to spare above its limiting value. -/
theorem IsNegativeGradient.dist_le_of_mem_stableSet (hφ : IsNegativeGradient φ f)
    (hz : z ∈ stableSet φ x) (hf : ∀ t, DifferentiableAt ℝ f (φ t z)) (hfx : ContinuousAt f x)
    {s r c : ℝ} (hc : 0 ≤ c) (hgrad : ∀ w, s < dist w x → dist w x < r → c ≤ ‖∇ f w‖)
    (hzs : dist z x ≤ s) (hfz : f z < f x + c * (r - s)) {t : ℝ} (ht : 0 ≤ t) :
    dist (φ t z) x ≤ r := by
  set γ : ℝ → E := fun τ ↦ φ τ z with hγdef
  have hγ : IsIntegralCurve γ (fun _ w ↦ -∇ f w) := hφ.isIntegralCurve z
  have hcontD : Continuous fun τ ↦ dist (γ τ) x := hγ.continuous.dist continuous_const
  have hγ0 : γ 0 = z := φ.map_zero_apply z
  -- Along the orbit, `f` decreases towards its limiting value `f x`.
  have hlow : ∀ τ, f x ≤ f (γ τ) := fun τ ↦
    hφ.value_le_of_mem_stableSet (isInvariant_stableSet φ x τ hz)
      (fun t' ↦ by simpa only [hγdef, ← _root_.Flow.map_add] using hf (t' + τ)) hfx
  by_contra! hcon
  -- `b` is the first time at which the trajectory reaches distance `r`.
  set A : Set ℝ := {τ ∈ Icc 0 t | r ≤ dist (γ τ) x}
  have hAbdd : BddBelow A := ⟨0, fun τ hτ ↦ hτ.1.1⟩
  have hbA : sInf A ∈ A :=
    (isClosed_Icc.inter (isClosed_le continuous_const hcontD)).csInf_mem
      ⟨t, ⟨ht, le_rfl⟩, hcon.le⟩ hAbdd
  set b := sInf A
  have hbefore : ∀ τ, 0 ≤ τ → τ < b → dist (γ τ) x < r := fun τ h0 hτ ↦ by
    by_contra! hh
    exact (not_le.2 hτ) (csInf_le hAbdd ⟨⟨h0, hτ.le.trans hbA.1.2⟩, hh⟩)
  -- `a` is the last time before `b` at which the trajectory is within distance `s`.
  set B : Set ℝ := {τ ∈ Icc 0 b | dist (γ τ) x ≤ s}
  have hBbdd : BddAbove B := ⟨b, fun τ hτ ↦ hτ.1.2⟩
  have haB : sSup B ∈ B :=
    (isClosed_Icc.inter (isClosed_le hcontD continuous_const)).csSup_mem
      ⟨0, ⟨le_rfl, hbA.1.1⟩, by rw [Set.mem_ofPred_eq, hγ0]; exact hzs⟩ hBbdd
  set a := sSup B
  have hafter : ∀ τ, a < τ → τ ≤ b → s < dist (γ τ) x := fun τ hτ hτb ↦ by
    by_contra! hh
    exact (not_le.2 hτ) (le_csSup hBbdd ⟨⟨haB.1.1.trans hτ.le, hτb⟩, hh⟩)
  -- Between `a` and `b` the trajectory crosses the annulus, losing `c * (r - s)` of `f`.
  have hs0 : 0 ≤ s := dist_nonneg.trans hzs
  have hF := antitoneOn_add_mul_dist hγ hf hc (x := x) (fun τ hτ ↦
    ⟨fun hEq ↦ by linarith [hafter τ hτ.1 hτ.2.le, dist_eq_zero.2 hEq],
      hgrad _ (hafter τ hτ.1 hτ.2.le) (hbefore τ (haB.1.1.trans hτ.1.le) hτ.2)⟩)
    ⟨le_rfl, haB.1.2⟩ ⟨haB.1.2, le_rfl⟩ haB.1.2
  have hfa : f (γ a) ≤ f z := by
    rw [← hγ0]
    exact hφ.orbit_antitone z hf haB.1.1
  have hcb : c * r ≤ c * dist (γ b) x := mul_le_mul_of_nonneg_left hbA.2 hc
  have hca : c * dist (γ a) x ≤ c * s := mul_le_mul_of_nonneg_left haB.2 hc
  linarith [hlow b]

/-- **An energy barrier confines unstable trajectories.** The backward-time counterpart of
`Flow.IsNegativeGradient.dist_le_of_mem_stableSet`: if `‖∇ f‖ ≥ c` on the open annulus
`s < dist w x < r`, a trajectory converging to `x` in backward time that starts within distance
`s` of `x` at a value above `f x - c * (r - s)` stays in the closed ball of radius `r` about `x`
at all nonpositive times. -/
theorem IsNegativeGradient.dist_le_of_mem_unstableSet (hφ : IsNegativeGradient φ f)
    (hz : z ∈ unstableSet φ x) (hf : ∀ t, DifferentiableAt ℝ f (φ t z)) (hfx : ContinuousAt f x)
    {s r c : ℝ} (hc : 0 ≤ c) (hgrad : ∀ w, s < dist w x → dist w x < r → c ≤ ‖∇ f w‖)
    (hzs : dist z x ≤ s) (hfz : f x - c * (r - s) < f z) {t : ℝ} (ht : t ≤ 0) :
    dist (φ t z) x ≤ r := by
  have hneg (w : E) : ∇ (-f) w = -∇ f w := by
    simpa using TauCeti.gradient_const_smul (-1 : ℝ) (f := f) (x := w)
  simpa only [_root_.Flow.reverse_apply, neg_neg] using
    hφ.reverse.dist_le_of_mem_stableSet (by rwa [stableSet_reverse])
      (fun t ↦ by simpa only [_root_.Flow.reverse_apply] using (hf (-t)).neg) hfx.neg hc
      (fun w h₁ h₂ ↦ by simpa only [hneg, norm_neg] using hgrad w h₁ h₂) hzs
      (by simp only [Pi.neg_apply]; linarith) (neg_nonneg.2 ht)

end Flow
