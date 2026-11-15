/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.MeasureTheory.Integral.Cosh
import TauCeti.Analysis.ODE.Nonautonomous

/-!
# The global solution of a globally Lipschitz autonomous ODE

Picard--Lindelöf solves `γ' = v ∘ γ` only on a small time interval, because a solution can escape
to infinity in finite time. When the vector field is *globally* Lipschitz no such escape happens,
and through every initial point there is exactly one solution defined on all of `ℝ`. This file
presents it as `ODE.globalSolution`, specialized at initial time `0` from the nonautonomous
weighted Picard contraction in `TauCeti.Analysis.ODE.Nonautonomous`.

## Main declarations

* `ODE.globalSolution`: the solution of `γ' = v ∘ γ` with `γ 0 = x` on all of `ℝ`.
* `ODE.globalSolution_eq_integral`: it satisfies the integral equation of the initial value
  problem.
* `ODE.globalSolution_zero` and `ODE.hasDerivAt_globalSolution`: it is a solution.
* `ODE.eq_globalSolution`: every global solution with the same initial value is equal to it.
* `ODE.globalSolution_congr`: it does not depend on the chosen Lipschitz bound.
* `ODE.globalSolution_add`: the flow law, following the solution for two successive times.
* `ODE.globalSolution_neg`: reversing time solves the negated field.
* `ODE.dist_globalSolution_le`: two solutions drift apart at most exponentially.
* `ODE.continuous_globalSolution`: joint continuity in time and initial condition.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The global solution of a globally Lipschitz autonomous ODE.** For a Lipschitz vector field
`v` on a Banach space, `ODE.globalSolution v hv x` is the unique curve `γ : ℝ → E` defined on the
whole line with `γ 0 = x` and `γ' t = v (γ t)` for every `t`. -/
noncomputable def globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) : ℝ → E :=
  nonautonomousSolution (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv) 0 x

/-- The global solution satisfies the integral equation of the initial value problem. -/
theorem globalSolution_eq_integral (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    globalSolution v hv x t = x + ∫ s in (0 : ℝ)..t, v (globalSolution v hv x s) :=
  nonautonomousSolution_eq_integral (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv) 0 x t

/-- The global solution starts at the prescribed initial point. -/
@[simp]
theorem globalSolution_zero (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) :
    globalSolution v hv x 0 = x :=
  nonautonomousSolution_self (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv) 0 x

/-- The global solution is continuous. -/
theorem continuous_globalSolution_apply (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) :
    Continuous (globalSolution v hv x) :=
  continuous_nonautonomousSolution_apply (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv) 0 x

/-- **The global solution solves the differential equation** at every time. -/
theorem hasDerivAt_globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    HasDerivAt (globalSolution v hv x) (v (globalSolution v hv x t)) t :=
  hasDerivAt_nonautonomousSolution (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv) 0 x t

/-- The global solution is an integral curve of `v`, read as a time-independent vector field. -/
theorem isIntegralCurve_globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) :
    IsIntegralCurve (globalSolution v hv x) fun _ y ↦ v y :=
  isIntegralCurve_nonautonomousSolution (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv) 0 x

/-- **Uniqueness.** Any curve defined on the whole line that solves `γ' = v ∘ γ` is the global
solution through its own initial value. -/
theorem eq_globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) : γ = globalSolution v hv (γ 0) :=
  eq_nonautonomousSolution (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv) hγ 0

/-- **Independence of the Lipschitz bound.** Two Lipschitz witnesses for the same vector field,
with possibly different constants, produce the same global solution. -/
theorem globalSolution_congr (v : E → E) {K K' : ℝ≥0} (hv : LipschitzWith K v)
    (hv' : LipschitzWith K' v) (x : E) : globalSolution v hv x = globalSolution v hv' x :=
  congrFun (congrFun (nonautonomousSolution_congr (fun _ ↦ v) (fun _ ↦ continuous_const)
    (fun _ ↦ hv) (fun _ ↦ hv')) 0) x

/-- **The flow law.** Following the global solution from `x` for the time `t + s` is the same as
following it from `x` for the time `t` and then, from where it has arrived, for the time `s`: both
curves solve the equation on the whole line and start at the same point. -/
theorem globalSolution_add (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) (t s : ℝ) :
    globalSolution v hv x (t + s) = globalSolution v hv (globalSolution v hv x t) s := by
  have hγ : IsIntegralCurve (fun r : ℝ ↦ globalSolution v hv x (t + r)) fun _ y ↦ v y := by
    simpa [Function.comp_def, add_comm] using (isIntegralCurve_globalSolution v hv x).comp_add t
  simpa using congrFun (eq_globalSolution v hv hγ) s

/-- **Reversing time** turns the global solution of `v` into the global solution of `-v`. -/
theorem globalSolution_neg (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    globalSolution v hv x (-t) = globalSolution (fun z ↦ -v z) hv.neg x t := by
  have hγ : IsIntegralCurve (fun s : ℝ ↦ globalSolution v hv x (-s))
      (fun _ z ↦ -v z) := by
    simpa only [Function.comp_def, Pi.smul_def, mul_neg_one, neg_one_smul, Pi.neg_def] using
      (isIntegralCurve_globalSolution v hv x).comp_mul (-1)
  simpa using congrFun (eq_globalSolution (fun z ↦ -v z) hv.neg hγ) t

/-- **Continuous dependence on the initial condition.** Two global solutions drift apart at most
exponentially, at the rate given by the Lipschitz constant of the vector field, in both time
directions. -/
theorem dist_globalSolution_le (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x y : E) (t : ℝ) :
    dist (globalSolution v hv x t) (globalSolution v hv y t) ≤ dist x y * Real.exp (K * |t|) := by
  simpa [globalSolution] using
    dist_nonautonomousSolution_le (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv) 0 x y t

/-- **Joint continuity** of the global solution in time and initial condition. -/
theorem continuous_globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) :
    Continuous fun p : ℝ × E ↦ globalSolution v hv p.2 p.1 :=
  (continuous_nonautonomousSolution (fun _ ↦ v) (fun _ ↦ continuous_const) (fun _ ↦ hv)).comp
    (continuous_const.prodMk (continuous_snd.prodMk continuous_fst))

end ODE
