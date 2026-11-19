/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.GlobalSolution
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
* `TauCeti.lipschitzWith_timeDependentSuspension`: a jointly Lipschitz field has a Lipschitz
  suspension.
* `TauCeti.timeDependentFlow`: the global evolution map of a time-dependent field whose
  suspension is globally Lipschitz.
* `TauCeti.hasDerivAt_timeDependentFlow`: the evolution solves `x' = v(t, x)`.
* `TauCeti.timeDependentFlow_trans`: evolution through an intermediate time composes.
* `TauCeti.timeDependentFlow_eq_integral`: the integral equation from time `s` to time `t`.
* `TauCeti.eq_timeDependentFlow`: uniqueness for global solutions with prescribed initial time.
* `TauCeti.timeDependentFlow_add_const`: the flow of a translation-invariant field commutes with
  the translation.
* `TauCeti.timeDependentFlow_snd_eq_of_snd_eq`: the flow of a field on a product `E × F`
  tangent to a slice `E × {c}` preserves that slice.
* `TauCeti.timeDependentFlow_snd_mem_Icc`: the flow of a field on `E × ℝ` tangent to the slices
  `E × {a}` and `E × {b}` preserves the band `E × [a, b]`.

The construction uses the global autonomous Picard--Lindelöf solution from
`TauCeti.Analysis.ODE.GlobalSolution`.
-/

public section

open Function Set
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
/-- The suspension of a time-dependent field is Lipschitz with the joint Lipschitz constant of
the field in time and space. -/
theorem lipschitzWith_timeDependentSuspension {v : ℝ → E → E} {K : ℝ≥0}
    (hv : LipschitzWith K fun p : ℝ × E ↦ v p.1 p.2) :
    LipschitzWith K (timeDependentSuspension v) :=
  LipschitzWith.of_dist_le_mul fun p q ↦ by
    simpa [timeDependentSuspension, Prod.dist_eq] using hv.dist_le_mul p q

/-- The time coordinate of the suspended global solution advances at unit speed. -/
private theorem fst_globalSolution_timeDependentSuspension (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s : ℝ) (x : E) (r : ℝ) :
    (ODE.globalSolution (timeDependentSuspension v) hv (s, x) r).1 = s + r := by
  let γ : ℝ → ℝ × E := ODE.globalSolution (timeDependentSuspension v) hv (s, x)
  have hderiv (u : ℝ) : HasDerivAt (fun q ↦ (γ q).1 - q) 0 u := by
    have hγ := ODE.hasDerivAt_globalSolution (timeDependentSuspension v) hv (s, x) u
    have hfst : HasDerivAt (fun q ↦ (γ q).1) 1 u := by
      convert (hγ.hasFDerivAt.fst).hasDerivAt using 1
      simp [timeDependentSuspension]
    convert hfst.sub (hasDerivAt_id' u) using 1
    simp
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
    simp [globalSolution_timeDependentSuspension, timeDependentSuspension]
  have hcomp := hsnd.comp_sub_const t s
  convert hcomp using 1
  simp only [Γ, timeDependentFlow]

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

/-- If a time-dependent field is invariant under the translation by `c`, its flow commutes with
that translation. -/
theorem timeDependentFlow_add_const (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) {c : E}
    (hc : ∀ t x, v t (x + c) = v t x) (s t : ℝ) (x : E) :
    timeDependentFlow v hv s t (x + c) = timeDependentFlow v hv s t x + c := by
  have h := eq_timeDependentFlow v hv (y := fun u ↦ timeDependentFlow v hv s u x + c)
    (fun u ↦ by simpa only [hc] using (hasDerivAt_timeDependentFlow v hv s u x).add_const c) s t
  simpa using h.symm

/-! ### Fields on a product tangent to slices -/

section Slice

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K : ℝ≥0}

/-- The time-dependent flow of a field on a product `E × F` whose second component vanishes on
the slice `E × {c}` preserves that slice. -/
theorem timeDependentFlow_snd_eq_of_snd_eq {v : ℝ → E × F → E × F}
    (hv : LipschitzWith K (timeDependentSuspension v)) {c : F} (hc : ∀ t x, (v t (x, c)).2 = 0)
    (s t : ℝ) {p : E × F} (hp : p.2 = c) : (timeDependentFlow v hv s t p).2 = c := by
  set φ : ℝ → E × F := fun u ↦ timeDependentFlow v hv s u p with hφ
  -- The height of the orbit and the constant `c` solve the same scalar equation.
  have hLip (u : ℝ) : LipschitzOnWith K (fun z ↦ (v u ((φ u).1, z)).2) univ := by
    refine (LipschitzWith.of_dist_le_mul fun z z' ↦ ?_).lipschitzOnWith
    have h := hv.dist_le_mul (u, ((φ u).1, z)) (u, ((φ u).1, z'))
    simp only [timeDependentSuspension_apply, Prod.dist_eq, dist_self] at h
    simp only [max_eq_right dist_nonneg] at h
    exact (le_max_right _ _).trans (le_max_right _ _ |>.trans h)
  have hf (u : ℝ) : HasDerivAt (fun u ↦ (φ u).2) ((v u ((φ u).1, (φ u).2)).2) u :=
    by simpa using ((hasDerivAt_timeDependentFlow v hv s u p).hasFDerivAt.snd).hasDerivAt
  have h := ODE_solution_unique_univ (v := fun u z ↦ (v u ((φ u).1, z)).2) (s := fun _ ↦ univ)
    (f := fun u ↦ (φ u).2) (g := fun _ ↦ c) (t₀ := s) hLip (fun u ↦ ⟨hf u, trivial⟩)
    (fun u ↦ ⟨by simpa only [hc] using hasDerivAt_const u c, trivial⟩) (by simpa [hφ] using hp)
  exact congrFun h t

/-- The time-dependent flow of a field on `E × ℝ` whose second component vanishes on the slices
`E × {a}` and `E × {b}` preserves the band `E × [a, b]`. -/
theorem timeDependentFlow_snd_mem_Icc {v : ℝ → E × ℝ → E × ℝ}
    (hv : LipschitzWith K (timeDependentSuspension v))
    {a b : ℝ} (ha : ∀ t x, (v t (x, a)).2 = 0) (hb : ∀ t x, (v t (x, b)).2 = 0) (s t : ℝ)
    {p : E × ℝ} (hp : p.2 ∈ Icc a b) :
    (timeDependentFlow v hv s t p).2 ∈ Icc a b := by
  -- If the orbit meets a boundary line at some time, it stays on it at every time.
  have hline (c : ℝ) (hc : ∀ t x, (v t (x, c)).2 = 0) (u : ℝ)
      (hu : (timeDependentFlow v hv s u p).2 = c) : (timeDependentFlow v hv s t p).2 = c := by
    rw [← timeDependentFlow_trans v hv s u t]
    exact timeDependentFlow_snd_eq_of_snd_eq hv hc u t hu
  have hz : ContinuousOn (fun u ↦ (timeDependentFlow v hv s u p).2) (uIcc s t) :=
    (continuous_snd.comp ((continuous_timeDependentFlow v hv).comp
      (by fun_prop : Continuous fun u : ℝ ↦ ((s, u), p)))).continuousOn
  have hs : (timeDependentFlow v hv s s p).2 = p.2 := by simp
  refine ⟨le_of_not_gt fun hlt ↦ ?_, le_of_not_gt fun hlt ↦ ?_⟩
  · obtain ⟨u, -, hu⟩ := intermediate_value_uIcc hz
      (mem_uIcc.2 (Or.inr ⟨hlt.le, hs ▸ hp.1⟩))
    exact hlt.ne (hline a ha u hu)
  · obtain ⟨u, -, hu⟩ := intermediate_value_uIcc hz
      (mem_uIcc.2 (Or.inl ⟨hs ▸ hp.2, hlt.le⟩))
    exact hlt.ne' (hline b hb u hu)

end Slice

end TauCeti

end
