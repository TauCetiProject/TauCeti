/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Comparison
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Viscosity solutions of the Monge–Ampère equation

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` and `f : E → ℝ`.
Besides the Aleksandrov (measure) sense `MA_u = f dx` of the Monge–Ampère equation
`det D²u = f`, a convex function `u` can solve it in the *viscosity* sense, which tests the
equation against `C²` convex functions touching `u` at a point:

* `u` is a **viscosity subsolution** if, whenever a convex function `φ` of class `C²` near
  `x₀ ∈ Ω` touches `u` from above at `x₀` (`u - φ` has a local maximum at `x₀`), then
  `f x₀ ≤ det D²φ(x₀)`;
* `u` is a **viscosity supersolution** if, whenever such a `φ` touches `u` from below at `x₀`
  (`u - φ` has a local minimum at `x₀`), then `det D²φ(x₀) ≤ f x₀`;
* `u` is a **viscosity solution** if it is both.

Here `D²φ(x₀)` is the derivative of the gradient `∇ φ` at `x₀`, an endomorphism of `E`. The test
functions are required to be convex only near `x₀`, so the class of test functions is at least as
large as that of convex `C²` functions on `Ω`.

Aleksandrov solutions are viscosity solutions. If `u` is convex on `Ω`, `f` is continuous on `Ω`,
and `f dx ≤ MA_u`, then `u` is a viscosity subsolution; if `MA_u ≤ f dx` and `f ≥ 0`, it is a
viscosity supersolution. The proof compares `u` with a quadratic perturbation
`ψ = φ + (t / 2) ‖x - x₀‖² + c` of a test function on a small ball around `x₀`. If the viscosity
inequality failed at `x₀`, then for a suitable small `t` the Hessian `D²φ + t` of `ψ` is positive
and its determinant lies strictly on the wrong side of `f` near `x₀`, so `ψ` is convex there and
its Monge–Ampère measure `det (D²φ + t) dx` compares with `MA_u`. The constant `c` makes `ψ` lie
strictly on one side of `u` on the boundary sphere and strictly on the other side at the centre,
which contradicts the comparison principle
(`TauCeti.le_of_mongeAmpereMeasure_le_of_le_frontier`).

For a convex function of class `C²` the viscosity sense agrees with the classical one: it is a
viscosity solution exactly when `det D²u = f` at every point of `Ω`. One direction tests the
equation with `φ = u`; the other goes through the Aleksandrov measure `MA_u = det (D²u) dx`.

## Main definitions

* `TauCeti.IsMongeAmpereViscositySubsolution Ω u f`,
  `TauCeti.IsMongeAmpereViscositySupersolution Ω u f` and
  `TauCeti.IsMongeAmpereViscositySolution Ω u f`: viscosity sub-, super- and solutions of
  `det D²u = f` on `Ω`.

## Main statements

* `TauCeti.IsMongeAmpereViscositySubsolution.mono`, `.mono_rhs` and their supersolution and
  solution counterparts: the predicates restrict to subsets of `Ω`, and sub- (super-) solutions
  stay so for smaller (larger) right-hand sides;
* `TauCeti.isMongeAmpereViscositySubsolution_of_withDensity_le_mongeAmpereMeasure` and
  `TauCeti.isMongeAmpereViscositySupersolution_of_mongeAmpereMeasure_le_withDensity`: Aleksandrov
  sub- and supersolutions with continuous right-hand side (and `f ≥ 0` for supersolutions) are
  viscosity sub- and supersolutions;
* `TauCeti.isMongeAmpereViscositySolution_of_mongeAmpereMeasure_eq`: **an Aleksandrov solution of
  `MA_u = f dx` with `f ≥ 0` continuous is a viscosity solution**;
* `TauCeti.isMongeAmpereViscositySolution_iff_forall_det_eq`: a convex `C²` function is a
  viscosity solution exactly when it is a classical solution.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.3.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, Chapter 2.
-/

public section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric Module
open scoped Topology ENNReal Gradient

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `u` is a **viscosity subsolution** of the Monge–Ampère equation `det D²u = f` on `Ω`: whenever
a function `φ`, of class `C²` at `x₀ ∈ Ω` and convex on a neighbourhood of `x₀`, touches `u` from
above at `x₀` (that is, `u - φ` has a local maximum at `x₀`), the Hessian of `φ` satisfies
`f x₀ ≤ det D²φ(x₀)`. The Hessian is the derivative of the gradient `∇ φ` at `x₀`. -/
structure IsMongeAmpereViscositySubsolution (Ω : Set E) (u f : E → ℝ) : Prop where
  /-- The viscosity inequality `f x₀ ≤ det D²φ(x₀)` for a convex `C²` test function `φ`
  touching `u` from above at `x₀`. -/
  le_det ⦃x₀ : E⦄ (hx₀ : x₀ ∈ Ω) ⦃φ : E → ℝ⦄ (hφ : ContDiffAt ℝ 2 φ x₀)
    (hφc : ∃ s ∈ 𝓝 x₀, ConvexOn ℝ s φ) (hmax : IsLocalMax (fun x => u x - φ x) x₀) :
    f x₀ ≤ (fderiv ℝ (∇ φ) x₀).det

/-- `u` is a **viscosity supersolution** of the Monge–Ampère equation `det D²u = f` on `Ω`:
whenever a function `φ`, of class `C²` at `x₀ ∈ Ω` and convex on a neighbourhood of `x₀`, touches
`u` from below at `x₀` (that is, `u - φ` has a local minimum at `x₀`), the Hessian of `φ`
satisfies `det D²φ(x₀) ≤ f x₀`. The Hessian is the derivative of the gradient `∇ φ` at `x₀`. -/
structure IsMongeAmpereViscositySupersolution (Ω : Set E) (u f : E → ℝ) : Prop where
  /-- The viscosity inequality `det D²φ(x₀) ≤ f x₀` for a convex `C²` test function `φ`
  touching `u` from below at `x₀`. -/
  det_le ⦃x₀ : E⦄ (hx₀ : x₀ ∈ Ω) ⦃φ : E → ℝ⦄ (hφ : ContDiffAt ℝ 2 φ x₀)
    (hφc : ∃ s ∈ 𝓝 x₀, ConvexOn ℝ s φ) (hmin : IsLocalMin (fun x => u x - φ x) x₀) :
    (fderiv ℝ (∇ φ) x₀).det ≤ f x₀

/-- `u` is a **viscosity solution** of the Monge–Ampère equation `det D²u = f` on `Ω`: it is both a
viscosity subsolution and a viscosity supersolution. -/
structure IsMongeAmpereViscositySolution (Ω : Set E) (u f : E → ℝ) : Prop
    extends IsMongeAmpereViscositySubsolution Ω u f, IsMongeAmpereViscositySupersolution Ω u f

namespace IsMongeAmpereViscositySubsolution

variable {Ω Ω' : Set E} {u f f' : E → ℝ}

/-- A viscosity subsolution on `Ω` is a viscosity subsolution on every subset of `Ω`. -/
theorem mono (h : IsMongeAmpereViscositySubsolution Ω u f) (hΩ' : Ω' ⊆ Ω) :
    IsMongeAmpereViscositySubsolution Ω' u f :=
  ⟨fun _ hx₀ _ hφ hφc hmax => h.le_det (hΩ' hx₀) hφ hφc hmax⟩

/-- A viscosity subsolution of `det D²u = f` is a viscosity subsolution of `det D²u = f'` for every
`f' ≤ f` on `Ω`. -/
theorem mono_rhs (h : IsMongeAmpereViscositySubsolution Ω u f) (hf : ∀ x ∈ Ω, f' x ≤ f x) :
    IsMongeAmpereViscositySubsolution Ω u f' :=
  ⟨fun _ hx₀ _ hφ hφc hmax => (hf _ hx₀).trans (h.le_det hx₀ hφ hφc hmax)⟩

end IsMongeAmpereViscositySubsolution

namespace IsMongeAmpereViscositySupersolution

variable {Ω Ω' : Set E} {u f f' : E → ℝ}

/-- A viscosity supersolution on `Ω` is a viscosity supersolution on every subset of `Ω`. -/
theorem mono (h : IsMongeAmpereViscositySupersolution Ω u f) (hΩ' : Ω' ⊆ Ω) :
    IsMongeAmpereViscositySupersolution Ω' u f :=
  ⟨fun _ hx₀ _ hφ hφc hmin => h.det_le (hΩ' hx₀) hφ hφc hmin⟩

/-- A viscosity supersolution of `det D²u = f` is a viscosity supersolution of `det D²u = f'` for
every `f' ≥ f` on `Ω`. -/
theorem mono_rhs (h : IsMongeAmpereViscositySupersolution Ω u f) (hf : ∀ x ∈ Ω, f x ≤ f' x) :
    IsMongeAmpereViscositySupersolution Ω u f' :=
  ⟨fun _ hx₀ _ hφ hφc hmin => (h.det_le hx₀ hφ hφc hmin).trans (hf _ hx₀)⟩

end IsMongeAmpereViscositySupersolution

/-- A viscosity solution on `Ω` is a viscosity solution on every subset of `Ω`. -/
theorem IsMongeAmpereViscositySolution.mono {Ω Ω' : Set E} {u f : E → ℝ}
    (h : IsMongeAmpereViscositySolution Ω u f) (hΩ' : Ω' ⊆ Ω) :
    IsMongeAmpereViscositySolution Ω' u f :=
  { toIsMongeAmpereViscositySubsolution := h.toIsMongeAmpereViscositySubsolution.mono hΩ'
    toIsMongeAmpereViscositySupersolution := h.toIsMongeAmpereViscositySupersolution.mono hΩ' }

end Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Set E} {u f : E → ℝ}

omit [FiniteDimensional ℝ E] in
/-- `det (A + t • id) → det A` as `t → 0`. -/
private theorem tendsto_det_add_smul_id (A : E →L[ℝ] E) :
    Tendsto (fun t : ℝ => (A + t • ContinuousLinearMap.id ℝ E).det) (𝓝 0) (𝓝 A.det) := by
  have : Continuous fun t : ℝ => (A + t • ContinuousLinearMap.id ℝ E).det :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  simpa using this.tendsto 0

section Measure

variable [MeasurableSpace E] [BorelSpace E] [DecidablePred (· ∈ Ω)] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- **The quadratic perturbation of a test function.** Let `φ` be differentiable with
differentiable gradient on `ball x₀ R`, and suppose that `D²φ + t` is a positive operator there.
For `r < R`, the function `ψ = φ + (t / 2) ‖· - x₀‖² + c` is convex on `ball x₀ r`, continuous
on its closure, and its Monge–Ampère measure there is `det (D²φ + t) dx`. -/
private theorem convexOn_mongeAmpereMeasure_add_mul_norm_sq {φ : E → ℝ} {x₀ : E} {t R r : ℝ}
    (c : ℝ) (hrR : r < R) (hd : ∀ x ∈ ball x₀ R, DifferentiableAt ℝ φ x)
    (hd' : ∀ x ∈ ball x₀ R, DifferentiableAt ℝ (∇ φ) x)
    (hpos : ∀ x ∈ ball x₀ R, ∀ v,
      0 ≤ inner ℝ ((fderiv ℝ (∇ φ) x + t • ContinuousLinearMap.id ℝ E) v) v)
    [DecidablePred (· ∈ ball x₀ r)] :
    ConvexOn ℝ (ball x₀ r) (fun x => φ x + t / 2 * ‖x - x₀‖ ^ 2 + c) ∧
      ContinuousOn (fun x => φ x + t / 2 * ‖x - x₀‖ ^ 2 + c) (closedBall x₀ r) ∧
      mongeAmpereMeasure μ
          (fun x => if x ∈ ball x₀ r then ((φ x + t / 2 * ‖x - x₀‖ ^ 2 + c : ℝ) : EReal) else ⊤) =
        (μ.restrict (ball x₀ r)).withDensity
          fun x => ENNReal.ofReal (fderiv ℝ (∇ φ) x + t • ContinuousLinearMap.id ℝ E).det := by
  set ψ := fun x => φ x + t / 2 * ‖x - x₀‖ ^ 2 + c
  have hrB : ball x₀ r ⊆ ball x₀ R := ball_subset_ball hrR.le
  -- On `ball x₀ R`, `ψ` has gradient `∇ φ + t (· - x₀)` and Hessian `D²φ + t`.
  have hgrad : ∀ x ∈ ball x₀ R, HasGradientAt ψ (∇ φ x + t • (x - x₀)) x := fun x hx => by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (((hd x hx).hasFDerivAt.add
      ((HasFDerivAt.norm_sq ((hasFDerivAt_id x).sub_const x₀)).const_mul (t / 2))).add_const
      c).congr_fderiv ?_
    ext v
    simp only [map_add, map_smul, InnerProductSpace.toDual_apply_apply, inner_gradient_left,
      _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul,
      Nat.cast_ofNat, id_eq]
    ring
  have hψd : ∀ x ∈ ball x₀ R, DifferentiableAt ℝ ψ x := fun x hx => (hgrad x hx).differentiableAt
  have hH : ∀ x ∈ ball x₀ R,
      HasFDerivAt (∇ ψ) (fderiv ℝ (∇ φ) x + t • ContinuousLinearMap.id ℝ E) x := fun x hx => by
    have hloc : ∇ ψ =ᶠ[𝓝 x] fun y => ∇ φ y + t • (y - x₀) :=
      eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy => (hgrad y hy).gradient
    refine HasFDerivAt.congr_of_eventuallyEq ?_ hloc
    exact (hd' x hx).hasFDerivAt.add (((hasFDerivAt_id x).sub_const x₀).const_smul t)
  have hconv : ConvexOn ℝ (ball x₀ r) ψ :=
    convexOn_of_hasFDerivAt_gradient (convex_ball x₀ r) isOpen_ball
      (fun x hx => hψd x (hrB hx)) (fun x hx => hH x (hrB hx)) fun x hx => hpos x (hrB hx)
  refine ⟨hconv, fun x hx =>
    (hψd x (closedBall_subset_ball hrR hx)).continuousAt.continuousWithinAt, ?_⟩
  rw [mongeAmpereMeasure_ite_eq_withDensity_det μ isOpen_ball hconv
    (fun x hx => (hψd x (hrB hx)).differentiableWithinAt)
    (fun x hx => (hH x (hrB hx)).differentiableAt.differentiableWithinAt)]
  exact withDensity_congr_ae (ae_restrict_of_forall_mem measurableSet_ball fun x hx => by
    simp only [(hH x (hrB hx)).fderiv])

/-- **The comparison principle on a ball, in contradiction form.** Two convex functions `v` and
`w` on `ball x₀ r`, continuous on its closure, with `MA_v ≤ MA_w` and `w ≤ v` on the sphere cannot
satisfy `v x₀ < w x₀`. -/
private theorem false_of_mongeAmpereMeasure_le_of_le_sphere [Nontrivial E] {v w : E → ℝ}
    {x₀ : E} {r : ℝ} (hr : 0 < r) [DecidablePred (· ∈ ball x₀ r)]
    (hv : ConvexOn ℝ (ball x₀ r) v) (hw : ConvexOn ℝ (ball x₀ r) w)
    (hvc : ContinuousOn v (closedBall x₀ r)) (hwc : ContinuousOn w (closedBall x₀ r))
    (hMA : mongeAmpereMeasure μ (fun x => if x ∈ ball x₀ r then (v x : EReal) else ⊤) ≤
      mongeAmpereMeasure μ (fun x => if x ∈ ball x₀ r then (w x : EReal) else ⊤))
    (hsph : ∀ x ∈ sphere x₀ r, w x ≤ v x) (hx₀ : v x₀ < w x₀) : False := by
  rw [← closure_ball x₀ hr.ne'] at hvc hwc
  rw [← frontier_ball x₀ hr.ne'] at hsph
  exact hx₀.not_ge (le_of_mongeAmpereMeasure_le_of_le_frontier μ isOpen_ball isBounded_ball hv hw
    hvc hwc hMA hsph (mem_ball_self hr))

/-- **Aleksandrov subsolutions are viscosity subsolutions.** Let `u` be convex on an open set `Ω`
of a real inner product space of finite dimension `n ≥ 1`, and let `f` be continuous on `Ω`. If
the Aleksandrov Monge–Ampère measure of `u` (extended by `⊤` off `Ω`, with respect to an additive
Haar measure `μ`) dominates `f dμ` on `Ω`, then `u` is a viscosity subsolution of `det D²u = f`
on `Ω`. -/
theorem isMongeAmpereViscositySubsolution_of_withDensity_le_mongeAmpereMeasure [Nontrivial E]
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) (hf : ContinuousOn f Ω)
    (hMA : (μ.restrict Ω).withDensity (fun x => ENNReal.ofReal (f x)) ≤
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤)) :
    IsMongeAmpereViscositySubsolution Ω u f := by
  classical
  refine ⟨fun x₀ hx₀ φ hφ hφc hmax => ?_⟩
  by_contra! hlt
  obtain ⟨s, hs, hφs⟩ := hφc
  set A := fderiv ℝ (∇ φ) x₀
  set I := ContinuousLinearMap.id ℝ E
  -- Choose `t > 0` with `det (A + t) < f x₀`.
  obtain ⟨t, htA, ht⟩ : ∃ t : ℝ, (A + t • I).det < f x₀ ∧ 0 < t :=
    ((((tendsto_det_add_smul_id A).eventually (gt_mem_nhds hlt)).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  -- Choose `R > 0` such that on `ball x₀ R`: `x ∈ Ω`, `φ` is convex near `x`,
  -- `u - φ ≤ u x₀ - φ x₀`, `φ` and `∇ φ` are differentiable, and `det (D²φ + t) < f`.
  have hev : ∀ᶠ x in 𝓝 x₀, x ∈ Ω ∧ x ∈ interior s ∧ u x - φ x ≤ u x₀ - φ x₀ ∧
      DifferentiableAt ℝ φ x ∧ DifferentiableAt ℝ (∇ φ) x ∧
      (fderiv ℝ (∇ φ) x + t • I).det < f x := by
    filter_upwards [hΩ.eventually_mem hx₀,
      isOpen_interior.eventually_mem (mem_interior_iff_mem_nhds.2 hs), hmax,
      hφ.eventually (by simp), hφ.eventually_differentiableAt_gradient le_rfl,
      (ContinuousLinearMap.continuous_det.continuousAt.comp
        ((hφ.continuousAt_fderiv_gradient le_rfl).add continuousAt_const)).eventually_lt
        (hf.continuousAt (hΩ.mem_nhds hx₀)) htA] with x hxΩ hxs hxmax hxφ hxd hxdet
    exact ⟨hxΩ, hxs, hxmax, hxφ.differentiableAt two_ne_zero, hxd, hxdet⟩
  obtain ⟨R, hR, hRsub⟩ := Metric.eventually_nhds_iff_ball.1 hev
  simp only [imp_and, forall_and] at hRsub
  obtain ⟨hRΩ, hRs, hRmax, hRφ, hRd, hRdet⟩ := hRsub
  set r := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hBΩ : closedBall x₀ r ⊆ Ω := fun x hx => hRΩ x (closedBall_subset_ball hrR hx)
  have hbΩ : ball x₀ r ⊆ Ω := ball_subset_closedBall.trans hBΩ
  -- The barrier `ψ = φ + (t / 2) ‖· - x₀‖² + c` is convex on `ball x₀ r`, since `D²φ` is positive.
  set c := u x₀ - φ x₀ - t * r ^ 2 / 4 with hc
  obtain ⟨hψc, hψcont, hψMA⟩ := convexOn_mongeAmpereMeasure_add_mul_norm_sq μ c hrR hRφ hRd
    fun x hx v => by
      have hpos := hφs.isPositive_of_hasFDerivAt_gradient
        (mem_interior_iff_mem_nhds.1 (hRs x hx)) (eventually_of_mem (isOpen_ball.mem_nhds hx) hRφ)
        (hRd x hx).hasFDerivAt
      have := hpos.re_inner_nonneg_left v
      simp only [ContinuousLinearMap.coe_coe, RCLike.re_to_real] at this
      simp only [_root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      exact add_nonneg this (mul_nonneg ht.le (sq_nonneg _))
  -- `MA_ψ = det (D²φ + t) dx ≤ f dx ≤ MA_u` on `ball x₀ r`.
  have hMAB : mongeAmpereMeasure μ
        (fun x => if x ∈ ball x₀ r then ((φ x + t / 2 * ‖x - x₀‖ ^ 2 + c : ℝ) : EReal) else ⊤) ≤
      mongeAmpereMeasure μ (fun x => if x ∈ ball x₀ r then (u x : EReal) else ⊤) := by
    rw [hψMA, mongeAmpereMeasure_ite_eq_restrict μ hΩ isOpen_ball (convex_ball x₀ r) hbΩ hu
      AbsolutelyContinuous.rfl]
    calc (μ.restrict (ball x₀ r)).withDensity
          (fun x => ENNReal.ofReal (fderiv ℝ (∇ φ) x + t • I).det)
        ≤ (μ.restrict (ball x₀ r)).withDensity fun x => ENNReal.ofReal (f x) :=
          withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun x hx =>
            ENNReal.ofReal_le_ofReal (hRdet x (ball_subset_ball hrR.le hx)).le)
      _ = ((μ.restrict Ω).withDensity fun x => ENNReal.ofReal (f x)).restrict (ball x₀ r) := by
          rw [restrict_withDensity measurableSet_ball, restrict_restrict_of_subset hbΩ]
      _ ≤ _ := Measure.restrict_mono subset_rfl hMA
  -- `u < ψ` on the sphere and `ψ < u` at the centre, contradicting the comparison principle.
  refine false_of_mongeAmpereMeasure_le_of_le_sphere μ hr hψc (hu.subset hbΩ (convex_ball x₀ r))
    hψcont ((hu.continuousOn hΩ).mono hBΩ) hMAB (fun x hx => ?_) ?_
  · have := hRmax x (sphere_subset_ball hrR hx)
    rw [mem_sphere_iff_norm.1 hx, hc]
    nlinarith [mul_pos ht (pow_pos hr 2)]
  · simp only [sub_self, norm_zero, hc]
    nlinarith [mul_pos ht (pow_pos hr 2)]

/-- **Aleksandrov supersolutions are viscosity supersolutions.** Let `u` be convex on an open set
`Ω` of a real inner product space of finite dimension `n ≥ 1`, and let `f ≥ 0` be continuous on
`Ω`. If the Aleksandrov Monge–Ampère measure of `u` (extended by `⊤` off `Ω`, with respect to an
additive Haar measure `μ`) is at most `f dμ`, then `u` is a viscosity supersolution of
`det D²u = f` on `Ω`. -/
theorem isMongeAmpereViscositySupersolution_of_mongeAmpereMeasure_le_withDensity [Nontrivial E]
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) (hf : ContinuousOn f Ω) (hf₀ : ∀ x ∈ Ω, 0 ≤ f x)
    (hMA : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) ≤
      (μ.restrict Ω).withDensity (fun x => ENNReal.ofReal (f x))) :
    IsMongeAmpereViscositySupersolution Ω u f := by
  classical
  refine ⟨fun x₀ hx₀ φ hφ hφc hmin => ?_⟩
  by_contra! hlt
  obtain ⟨s, hs, hφs⟩ := hφc
  have hcont := hφ.continuousAt_fderiv_gradient le_rfl
  have hφd : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ φ x :=
    (hφ.eventually (by simp)).mono fun x hx => hx.differentiableAt two_ne_zero
  have hφd' := hφ.eventually_differentiableAt_gradient le_rfl
  set A := fderiv ℝ (∇ φ) x₀
  set I := ContinuousLinearMap.id ℝ E
  -- `A` is positive with `det A > f x₀ ≥ 0`, so it is coercive: `κ ‖v‖² ≤ ⟪A v, v⟫`.
  have hApos : (A : E →ₗ[ℝ] E).IsPositive :=
    hφs.isPositive_of_hasFDerivAt_gradient hs hφd hφd'.self_of_nhds.hasFDerivAt
  have hker : LinearMap.ker (A : E →ₗ[ℝ] E) = ⊥ := by
    by_contra h
    have : A.det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.2 h
    linarith [hf₀ x₀ hx₀]
  obtain ⟨κ, hκ, hA⟩ := hApos.exists_pos_mul_norm_sq_le_re_inner hker
  simp only [ContinuousLinearMap.coe_coe, RCLike.re_to_real] at hA
  -- Choose `-κ / 2 < t < 0` with `f x₀ < det (A + t)`.
  obtain ⟨t, ⟨htA, htκ⟩, ht⟩ : ∃ t : ℝ, (f x₀ < (A + t • I).det ∧ -(κ / 2) < t) ∧ t < 0 :=
    (((((tendsto_det_add_smul_id A).eventually (lt_mem_nhds hlt)).and
      (lt_mem_nhds (by linarith))).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Iio (0 : ℝ)))).exists
  -- Choose `R > 0` such that on `ball x₀ R`: `x ∈ Ω`, `u - φ ≥ u x₀ - φ x₀`, `φ` and `∇ φ` are
  -- differentiable, `‖D²φ - A‖ < κ / 2`, and `f < det (D²φ + t)`.
  have hev : ∀ᶠ x in 𝓝 x₀, x ∈ Ω ∧ u x₀ - φ x₀ ≤ u x - φ x ∧
      DifferentiableAt ℝ φ x ∧ DifferentiableAt ℝ (∇ φ) x ∧
      fderiv ℝ (∇ φ) x ∈ ball A (κ / 2) ∧ f x < (fderiv ℝ (∇ φ) x + t • I).det := by
    filter_upwards [hΩ.eventually_mem hx₀, hmin, hφd, hφd',
      hcont.eventually (ball_mem_nhds A (half_pos hκ)),
      (hf.continuousAt (hΩ.mem_nhds hx₀)).eventually_lt
        (ContinuousLinearMap.continuous_det.continuousAt.comp (hcont.add continuousAt_const)) htA]
      with x hxΩ hxmin hxφ hxd hxA hxdet
    exact ⟨hxΩ, hxmin, hxφ, hxd, hxA, hxdet⟩
  obtain ⟨R, hR, hRsub⟩ := Metric.eventually_nhds_iff_ball.1 hev
  simp only [imp_and, forall_and] at hRsub
  obtain ⟨hRΩ, hRmin, hRφ, hRd, hRA, hRdet⟩ := hRsub
  set r := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hBΩ : closedBall x₀ r ⊆ Ω := fun x hx => hRΩ x (closedBall_subset_ball hrR hx)
  have hbΩ : ball x₀ r ⊆ Ω := ball_subset_closedBall.trans hBΩ
  -- The barrier `ψ = φ + (t / 2) ‖· - x₀‖² + c` is convex on `ball x₀ r`, by coercivity of `A`.
  set c := u x₀ - φ x₀ - t * r ^ 2 / 4 with hc
  obtain ⟨hψc, hψcont, hψMA⟩ := convexOn_mongeAmpereMeasure_add_mul_norm_sq μ c hrR hRφ hRd
    fun x hx v => by
      -- `⟪(D²φ x + t) v, v⟫ ≥ (κ - ‖D²φ x - A‖ + t) ‖v‖² ≥ 0`.
      set B := fderiv ℝ (∇ φ) x - A
      have hB : ‖B‖ < κ / 2 := by simpa [B, dist_eq_norm] using hRA x hx
      have h₁ : -(‖B‖ * ‖v‖ ^ 2) ≤ inner ℝ (B v) v := by
        nlinarith [abs_le.1 (abs_real_inner_le_norm (B v) v), B.le_opNorm v, norm_nonneg v]
      have h₂ : inner ℝ ((fderiv ℝ (∇ φ) x + t • I) v) v =
          inner ℝ (A v) v + inner ℝ (B v) v + t * ‖v‖ ^ 2 := by
        simp only [B, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
          ContinuousLinearMap.id_apply, inner_add_left, inner_sub_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq, I]
        ring
      rw [h₂]
      nlinarith [hA v, sq_nonneg ‖v‖]
  -- `MA_u ≤ f dx ≤ det (D²φ + t) dx = MA_ψ` on `ball x₀ r`.
  have hMAB : mongeAmpereMeasure μ (fun x => if x ∈ ball x₀ r then (u x : EReal) else ⊤) ≤
      mongeAmpereMeasure μ
        (fun x => if x ∈ ball x₀ r then ((φ x + t / 2 * ‖x - x₀‖ ^ 2 + c : ℝ) : EReal) else ⊤) := by
    rw [hψMA, mongeAmpereMeasure_ite_eq_restrict μ hΩ isOpen_ball (convex_ball x₀ r) hbΩ hu
      AbsolutelyContinuous.rfl]
    calc (mongeAmpereMeasure μ fun x => if x ∈ Ω then (u x : EReal) else ⊤).restrict (ball x₀ r)
        ≤ ((μ.restrict Ω).withDensity fun x => ENNReal.ofReal (f x)).restrict (ball x₀ r) :=
          Measure.restrict_mono subset_rfl hMA
      _ = (μ.restrict (ball x₀ r)).withDensity fun x => ENNReal.ofReal (f x) := by
          rw [restrict_withDensity measurableSet_ball, restrict_restrict_of_subset hbΩ]
      _ ≤ _ :=
          withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun x hx =>
            ENNReal.ofReal_le_ofReal (hRdet x (ball_subset_ball hrR.le hx)).le)
  -- `ψ < u` on the sphere and `u < ψ` at the centre, contradicting the comparison principle.
  refine false_of_mongeAmpereMeasure_le_of_le_sphere μ hr (hu.subset hbΩ (convex_ball x₀ r)) hψc
    ((hu.continuousOn hΩ).mono hBΩ) hψcont hMAB (fun x hx => ?_) ?_
  · have := hRmin x (sphere_subset_ball hrR hx)
    rw [mem_sphere_iff_norm.1 hx, hc]
    nlinarith [mul_neg_of_neg_of_pos ht (pow_pos hr 2)]
  · simp only [sub_self, norm_zero, hc]
    nlinarith [mul_neg_of_neg_of_pos ht (pow_pos hr 2)]

/-- **Aleksandrov solutions are viscosity solutions.** Let `u` be convex on an open set `Ω` of a
real inner product space of finite dimension `n ≥ 1`, and let `f ≥ 0` be continuous on `Ω`. If
`u` solves the Monge–Ampère equation `MA_u = f dμ` in the sense of Aleksandrov (for the
Monge–Ampère measure of `u` extended by `⊤` off `Ω`, with respect to an additive Haar measure
`μ`), then `u` is a viscosity solution of `det D²u = f` on `Ω`. -/
theorem isMongeAmpereViscositySolution_of_mongeAmpereMeasure_eq [Nontrivial E] (hΩ : IsOpen Ω)
    (hu : ConvexOn ℝ Ω u) (hf : ContinuousOn f Ω) (hf₀ : ∀ x ∈ Ω, 0 ≤ f x)
    (hMA : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) =
      (μ.restrict Ω).withDensity (fun x => ENNReal.ofReal (f x))) :
    IsMongeAmpereViscositySolution Ω u f :=
  { toIsMongeAmpereViscositySubsolution :=
      isMongeAmpereViscositySubsolution_of_withDensity_le_mongeAmpereMeasure μ hΩ hu hf hMA.ge
    toIsMongeAmpereViscositySupersolution :=
      isMongeAmpereViscositySupersolution_of_mongeAmpereMeasure_le_withDensity μ hΩ hu hf hf₀
        hMA.le }

end Measure

/-- **Classical and viscosity solutions agree for `C²` convex functions.** Let `u` be convex and
of class `C²` on an open set `Ω` of a real inner product space of finite dimension `n ≥ 1`. Then
`u` is a viscosity solution of `det D²u = f` on `Ω` exactly when `det D²u(x) = f x` at every
`x ∈ Ω`. -/
theorem isMongeAmpereViscositySolution_iff_forall_det_eq [Nontrivial E] (hΩ : IsOpen Ω)
    (hu : ConvexOn ℝ Ω u) (hu₂ : ContDiffOn ℝ 2 u Ω) :
    IsMongeAmpereViscositySolution Ω u f ↔ ∀ x ∈ Ω, (fderiv ℝ (∇ u) x).det = f x := by
  have hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x := fun x hx => hu₂.contDiffAt (hΩ.mem_nhds hx)
  refine ⟨fun h x hx => le_antisymm ?_ ?_, fun hdet => ?_⟩
  · -- Test the supersolution property with `φ = u`.
    exact h.det_le hx (hreg x hx) ⟨Ω, hΩ.mem_nhds hx, hu⟩ (by simpa using isLocalMin_const)
  · -- Test the subsolution property with `φ = u`.
    exact h.le_det hx (hreg x hx) ⟨Ω, hΩ.mem_nhds hx, hu⟩ (by simpa using isLocalMax_const)
  -- Conversely, `MA_u = det (D²u) dx = f dx`, and `f = det D²u ≥ 0` is continuous on `Ω`.
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hd : ∀ x ∈ Ω, DifferentiableAt ℝ u x ∧ DifferentiableAt ℝ (∇ u) x := fun x hx =>
    ⟨(hreg x hx).differentiableAt two_ne_zero,
      ((hreg x hx).eventually_differentiableAt_gradient le_rfl).self_of_nhds⟩
  have hMA := mongeAmpereMeasure_ite_eq_withDensity_det addHaar hΩ hu
    (fun x hx => (hd x hx).1.differentiableWithinAt)
    (fun x hx => (hd x hx).2.differentiableWithinAt)
  refine isMongeAmpereViscositySolution_of_mongeAmpereMeasure_eq addHaar hΩ hu ?_ ?_
    (hMA.trans (withDensity_congr_ae (ae_restrict_of_forall_mem hΩ.measurableSet
      fun x hx => by simp only [hdet x hx])))
  · refine ContinuousOn.congr (fun x hx => ?_) fun x hx => (hdet x hx).symm
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hreg x hx).continuousAt_fderiv_gradient le_rfl)).continuousWithinAt
  · intro x hx
    rw [← hdet x hx]
    exact (hu.isPositive_of_hasFDerivAt_gradient (hΩ.mem_nhds hx)
      (eventually_of_mem (hΩ.mem_nhds hx) fun y hy => (hd y hy).1)
      (hd x hx).2.hasFDerivAt).det_nonneg

end TauCeti
