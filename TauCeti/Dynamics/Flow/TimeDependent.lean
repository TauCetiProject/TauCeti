/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.GlobalSolution
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Global flows of time-dependent vector fields

A time-dependent vector field `v : ℝ → E → E` can be made autonomous on `ℝ × E` by
adjoining the clock equation `t' = 1`.  If this suspended vector field is globally Lipschitz,
its global autonomous solution defines the evolution map from an initial time `s` to a final
time `t`.

This file carries out that construction.  The resulting map starts at the prescribed point,
solves the original time-dependent equation, is jointly continuous in both times and the initial
point, and satisfies the two-time composition law.  It is also the unique global solution with a
given value at a given time.  These properties are the nonautonomous replacement for the group
law of an ordinary `Flow`.

## Main declarations

* `TauCeti.timeDependentSuspension`: the autonomous field `(t, x) ↦ (1, v t x)`.
* `TauCeti.timeDependentFlow`: the global evolution map of a time-dependent field whose
  suspension is globally Lipschitz.
* `TauCeti.hasDerivAt_timeDependentFlow`: the evolution solves `x' = v(t, x)`.
* `TauCeti.timeDependentFlow_trans`: evolution through an intermediate time composes.
* `TauCeti.timeDependentFlow_eq_integral`: the integral equation from time `s` to time `t`.
* `TauCeti.eq_timeDependentFlow`: uniqueness for global solutions with prescribed initial time.

The construction uses the global autonomous Picard--Lindelöf solution from
`TauCeti.Analysis.ODE.GlobalSolution`.
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

/-- The time coordinate of the suspended global solution advances at unit speed. -/
private theorem fst_globalSolution_timeDependentSuspension (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s : ℝ) (x : E) (r : ℝ) :
    (ODE.globalSolution (timeDependentSuspension v) hv (s, x) r).1 = s + r := by
  let γ : ℝ → ℝ × E := ODE.globalSolution (timeDependentSuspension v) hv (s, x)
  have hderiv (u : ℝ) : HasDerivAt (fun q ↦ (γ q).1 - q) 0 u := by
    have hγ := ODE.hasDerivAt_globalSolution (timeDependentSuspension v) hv (s, x) u
    have hfst : HasDerivAt (fun q ↦ (γ q).1) 1 u := by
      convert (hγ.hasFDerivAt.fst).hasDerivAt using 1
      all_goals simp [timeDependentSuspension]
    convert hfst.sub (hasDerivAt_id' u) using 1
    all_goals simp
  have hconst := is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
    (fun u ↦ (hderiv u).deriv) r 0
  simpa [γ, add_comm, sub_eq_iff_eq_add] using hconst

/-- The global **time-dependent flow** of `v`.  The value `timeDependentFlow v hv s t x` is the
value at time `t` of the solution which equals `x` at time `s`.  Global existence follows by
applying the autonomous global-solution theorem to the suspended field on `ℝ × E`. -/
noncomputable def timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) (x : E) : E :=
  (ODE.globalSolution (timeDependentSuspension v) hv (s, x) (t - s)).2

/-- The suspended global solution consists of the current time and the time-dependent flow. -/
theorem globalSolution_timeDependentSuspension (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) (x : E) :
    ODE.globalSolution (timeDependentSuspension v) hv (s, x) (t - s) =
      (t, timeDependentFlow v hv s t x) := by
  apply Prod.ext
  · rw [fst_globalSolution_timeDependentSuspension]
    ring
  · rfl

/-- A time-dependent flow starts at its prescribed initial point. -/
@[simp]
theorem timeDependentFlow_self (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s : ℝ) (x : E) :
    timeDependentFlow v hv s s x = x := by
  simp [timeDependentFlow]

/-- The time-dependent flow solves the original nonautonomous differential equation. -/
theorem hasDerivAt_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) (x : E) :
    HasDerivAt (fun u ↦ timeDependentFlow v hv s u x)
      (v t (timeDependentFlow v hv s t x)) t := by
  let Γ : ℝ → ℝ × E := ODE.globalSolution (timeDependentSuspension v) hv (s, x)
  have hΓ := ODE.hasDerivAt_globalSolution (timeDependentSuspension v) hv (s, x) (t - s)
  have hsnd : HasDerivAt (fun q ↦ (Γ q).2) (v t (timeDependentFlow v hv s t x))
      (t - s) := by
    convert (hΓ.hasFDerivAt.snd).hasDerivAt using 1
    all_goals simp [globalSolution_timeDependentSuspension, timeDependentSuspension]
  have hcomp := hsnd.comp_sub_const t s
  convert hcomp using 1
  all_goals simp only [Γ, timeDependentFlow]

/-- Time-dependent evolution through an intermediate time is the same as direct evolution. -/
@[simp]
theorem timeDependentFlow_trans (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (r s t : ℝ) (x : E) :
    timeDependentFlow v hv s t (timeDependentFlow v hv r s x) =
      timeDependentFlow v hv r t x := by
  have h := ODE.globalSolution_add (timeDependentSuspension v) hv (r, x) (s - r) (t - s)
  rw [globalSolution_timeDependentSuspension v hv r s x,
    globalSolution_timeDependentSuspension v hv s t] at h
  have hsum : s - r + (t - s) = t - r := by ring
  rw [hsum, globalSolution_timeDependentSuspension v hv r t x] at h
  simpa only using (congrArg Prod.snd h).symm

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
    Continuous fun p : (ℝ × ℝ) × E ↦ timeDependentFlow v hv p.1.1 p.1.2 p.2 := by
  unfold timeDependentFlow
  have hm : Continuous fun p : (ℝ × ℝ) × E ↦
      (p.1.2 - p.1.1, (p.1.1, p.2)) := by fun_prop
  have h := (ODE.continuous_globalSolution (timeDependentSuspension v) hv).comp hm
  convert continuous_snd.comp h using 1
  funext p
  rfl

/-- The construction does not depend on the chosen Lipschitz bound for the suspended field. -/
theorem timeDependentFlow_congr (v : ℝ → E → E) {K K' : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v))
    (hv' : LipschitzWith K' (timeDependentSuspension v)) :
    timeDependentFlow v hv = timeDependentFlow v hv' := by
  funext s t x
  exact congrArg Prod.snd
    (congrFun (ODE.globalSolution_congr (timeDependentSuspension v) hv hv' (s, x)) (t - s))

/-- **The integral equation of the time-dependent flow**:
`φ(s, t) x = x + ∫ₛᵗ v(u, φ(s, u) x) du`. -/
theorem timeDependentFlow_eq_integral (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) (x : E) :
    timeDependentFlow v hv s t x =
      x + ∫ u in s..t, v u (timeDependentFlow v hv s u x) := by
  have hcont : Continuous fun u ↦ v u (timeDependentFlow v hv s u x) := by
    have hv' : Continuous fun p : ℝ × E ↦ v p.1 p.2 :=
      continuous_snd.comp hv.continuous
    exact hv'.comp (continuous_id.prodMk ((continuous_timeDependentFlow v hv).comp
      (by fun_prop : Continuous fun u : ℝ ↦ ((s, u), x))))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_timeDependentFlow v hv s u x) (hcont.intervalIntegrable s t)]
  simp

/-- **Uniqueness of the time-dependent flow.** A global solution of `y' = v(t, y)` is the
time-dependent flow through its value at any chosen initial time. -/
theorem eq_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) {y : ℝ → E}
    (hy : ∀ t, HasDerivAt y (v t (y t)) t) (s t : ℝ) :
    y t = timeDependentFlow v hv s t (y s) := by
  let γ : ℝ → ℝ × E := fun u ↦ (s + u, y (s + u))
  have hγ (u : ℝ) : HasDerivAt γ (timeDependentSuspension v (γ u)) u := by
    have htime : HasDerivAt (fun q : ℝ ↦ s + q) 1 u := (hasDerivAt_id u).const_add s
    have hy' : HasDerivAt (fun q : ℝ ↦ y (s + q)) (v (s + u) (y (s + u))) u :=
      (hy (s + u)).comp_const_add s u
    simpa only [γ, timeDependentSuspension_apply] using htime.prodMk hy'
  have heq := ODE.eq_globalSolution (timeDependentSuspension v) hv hγ
  have hat := congrFun heq (t - s)
  have hzero : γ 0 = (s, y s) := by simp [γ]
  rw [hzero] at hat
  rw [globalSolution_timeDependentSuspension v hv s t (y s)] at hat
  have harg : s + (t - s) = t := by ring
  simpa only [γ, harg] using congrArg Prod.snd hat

end TauCeti

end
