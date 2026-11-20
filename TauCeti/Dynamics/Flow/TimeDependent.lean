/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.GlobalSolution
public import TauCeti.Analysis.ODE.Nonautonomous
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Global flows of time-dependent vector fields

A time-dependent vector field `v : ℝ → E → E` can be made autonomous on `ℝ × E` by
adjoining the clock equation `t' = 1`.  If this suspended vector field is globally Lipschitz,
then `v` is continuous in time at each point and uniformly Lipschitz in space, so
`ODE.nonautonomousSolution` defines its global evolution map from an initial time `s` to a
final time `t`, and `globalSolution_timeDependentSuspension` identifies this evolution with the
autonomous global solution of the suspended field from `TauCeti.Analysis.ODE.GlobalSolution`.

The resulting map starts at the prescribed point, solves the original time-dependent equation, is
jointly continuous in both times and the initial point, and satisfies the two-time composition law.
It is also the unique global solution with a given value at a given time.  These properties are the
nonautonomous replacement for the group law of an ordinary `Flow`.

## Main declarations

* `TauCeti.timeDependentSuspension`: the autonomous field `(t, x) ↦ (1, v t x)`.
* `TauCeti.timeDependentFlow`: the global evolution map of a time-dependent field whose
  suspension is globally Lipschitz, specializing `ODE.nonautonomousSolution`.
* `TauCeti.timeDependentFlow_eq_nonautonomousSolution`: agreement with
  `ODE.nonautonomousSolution` for any continuity and spatial Lipschitz witnesses.
* `TauCeti.globalSolution_timeDependentSuspension`: identification with the autonomous global
  solution of the suspended field.
* `TauCeti.hasDerivAt_timeDependentFlow`: the evolution solves `x' = v(t, x)`.
* `TauCeti.timeDependentFlow_trans`: evolution through an intermediate time composes.
* `TauCeti.timeDependentFlow_eq_integral`: the integral equation from time `s` to time `t`.
* `TauCeti.eq_timeDependentFlow`: uniqueness for global solutions with prescribed initial time.
-/

public section

open Function
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The autonomous suspension of a time-dependent vector field: its first component advances the
clock at unit speed and its second component is the original field. -/
def timeDependentSuspension (v : ℝ → E → E) : ℝ × E → ℝ × E :=
  fun p ↦ (1, v p.1 p.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
@[simp]
theorem timeDependentSuspension_apply (v : ℝ → E → E) (t : ℝ) (x : E) :
    timeDependentSuspension v (t, x) = (1, v t x) :=
  by rw [timeDependentSuspension]

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem continuous_of_lipschitzWith_timeDependentSuspension (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (x : E) :
    Continuous (v · x) :=
  continuous_snd.comp (hv.continuous.comp (continuous_id.prodMk continuous_const))

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem lipschitzWith_of_lipschitzWith_timeDependentSuspension (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (t : ℝ) :
    LipschitzWith K (v t) := fun x y ↦ by
  simpa [timeDependentSuspension, Prod.edist_eq] using hv (t, x) (t, y)

/-- The global **time-dependent flow** of `v`.  The value `timeDependentFlow v hv s t x` is the
value at time `t` of the solution which equals `x` at time `s`, obtained by specializing
`ODE.nonautonomousSolution` to a field whose suspension is globally Lipschitz. -/
noncomputable def timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) (x : E) : E :=
  ODE.nonautonomousSolution v
    (continuous_of_lipschitzWith_timeDependentSuspension v hv)
    (lipschitzWith_of_lipschitzWith_timeDependentSuspension v hv) s x t

/-- The time-dependent flow agrees with `ODE.nonautonomousSolution` for any continuity and
spatial Lipschitz witnesses of `v`. -/
theorem timeDependentFlow_eq_nonautonomousSolution (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v))
    (hvc : ∀ x, Continuous (v · x)) {K' : ℝ≥0} (hv' : ∀ t, LipschitzWith K' (v t))
    (s t : ℝ) (x : E) :
    timeDependentFlow v hv s t x = ODE.nonautonomousSolution v hvc hv' s x t := by
  rw [timeDependentFlow, ODE.nonautonomousSolution_congr v hvc _ hv']

/-- A time-dependent flow starts at its prescribed initial point. -/
@[simp]
theorem timeDependentFlow_self (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s : ℝ) (x : E) :
    timeDependentFlow v hv s s x = x :=
  ODE.nonautonomousSolution_self v _ _ s x

/-- The time-dependent flow solves the original nonautonomous differential equation. -/
theorem hasDerivAt_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) (x : E) :
    HasDerivAt (fun u ↦ timeDependentFlow v hv s u x)
      (v t (timeDependentFlow v hv s t x)) t :=
  ODE.hasDerivAt_nonautonomousSolution v _ _ s x t

/-- The suspended global solution consists of the current time and the time-dependent flow. -/
theorem globalSolution_timeDependentSuspension (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) (x : E) :
    ODE.globalSolution (timeDependentSuspension v) hv (s, x) (t - s) =
      (t, timeDependentFlow v hv s t x) := by
  let γ : ℝ → ℝ × E := fun u ↦ (s + u, timeDependentFlow v hv s (s + u) x)
  have hγ (u : ℝ) : HasDerivAt γ (timeDependentSuspension v (γ u)) u := by
    have htime : HasDerivAt (fun q : ℝ ↦ s + q) 1 u := (hasDerivAt_id u).const_add s
    have hflow := (hasDerivAt_timeDependentFlow v hv s (s + u) x).comp_const_add s u
    simpa only [γ, timeDependentSuspension_apply] using htime.prodMk hflow
  have heq := congrFun (ODE.eq_globalSolution (timeDependentSuspension v) hv hγ) (t - s)
  have hzero : γ 0 = (s, x) := by simp [γ]
  rw [hzero] at heq
  simpa [γ] using heq.symm

/-- Time-dependent evolution through an intermediate time is the same as direct evolution. -/
@[simp]
theorem timeDependentFlow_trans (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (r s t : ℝ) (x : E) :
    timeDependentFlow v hv s t (timeDependentFlow v hv r s x) =
      timeDependentFlow v hv r t x :=
  ODE.nonautonomousSolution_trans v _ _ r s t x

/-- The evolution from `t` back to `s` is a left inverse of the evolution from `s` to `t`. -/
theorem leftInverse_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) :
    LeftInverse (timeDependentFlow v hv t s) (timeDependentFlow v hv s t) :=
  fun _ ↦ by simp

/-- The evolution from `t` back to `s` is a right inverse of the evolution from `s` to `t`. -/
theorem rightInverse_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) :
    RightInverse (timeDependentFlow v hv t s) (timeDependentFlow v hv s t) :=
  fun _ ↦ by simp

/-- Each time map of the time-dependent flow is bijective. -/
theorem bijective_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) :
    Bijective (timeDependentFlow v hv s t) :=
  ⟨(leftInverse_timeDependentFlow v hv s t).injective,
    (rightInverse_timeDependentFlow v hv s t).surjective⟩

/-- The time-dependent flow is jointly continuous in the initial time, final time, and point. -/
theorem continuous_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) :
    Continuous fun p : (ℝ × ℝ) × E ↦ timeDependentFlow v hv p.1.1 p.1.2 p.2 :=
  (ODE.continuous_nonautonomousSolution v _ _).comp
    (by fun_prop : Continuous fun p : (ℝ × ℝ) × E ↦ (p.1.1, p.2, p.1.2))

/-- The construction does not depend on the chosen Lipschitz bound for the suspended field. -/
theorem timeDependentFlow_congr (v : ℝ → E → E) {K K' : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v))
    (hv' : LipschitzWith K' (timeDependentSuspension v)) :
    timeDependentFlow v hv = timeDependentFlow v hv' := by
  funext s t x
  exact congrFun (congrFun (congrFun (ODE.nonautonomousSolution_congr v _ _ _) s) x) t

/-- **The integral equation of the time-dependent flow**:
`φ(s, t) x = x + ∫ₛᵗ v(u, φ(s, u) x) du`. -/
theorem timeDependentFlow_eq_integral (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) (x : E) :
    timeDependentFlow v hv s t x =
      x + ∫ u in s..t, v u (timeDependentFlow v hv s u x) :=
  ODE.nonautonomousSolution_eq_integral v _ _ s x t

/-- **Uniqueness of the time-dependent flow.** A global solution of `y' = v(t, y)` is the
time-dependent flow through its value at any chosen initial time. -/
theorem eq_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) {y : ℝ → E}
    (hy : ∀ t, HasDerivAt y (v t (y t)) t) (s t : ℝ) :
    y t = timeDependentFlow v hv s t (y s) :=
  congrFun (ODE.eq_nonautonomousSolution v _ _ hy s) t

end TauCeti

end
