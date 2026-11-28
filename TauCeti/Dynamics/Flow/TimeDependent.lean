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
import Mathlib.Analysis.ODE.ExistUnique
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
* `TauCeti.lipschitzWith_timeDependentSuspension`: a jointly Lipschitz field has a Lipschitz
  suspension.
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
* `TauCeti.timeDependentFlow_add_const`: the flow of a translation-invariant field commutes with
  the translation.
* `TauCeti.timeDependentFlow_snd_eq_of_snd_eq`: the flow of a field on a product `E × F`
  tangent to a slice `E × {c}` preserves that slice.
* `TauCeti.timeDependentFlow_snd_mem_Icc`: the flow of a field on `E × ℝ` tangent to the slices
  `E × {a}` and `E × {b}` preserves the band `E × [a, b]`.
* `TauCeti.timeDependentFlow_freeze`: for a family of fields `v u` depending on a parameter `u`,
  the flow of `(x, u) ↦ (v u t x, 0)` on `E × F` moves `x` by the flow of `v u` and keeps `u`.
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
private theorem continuous_of_lipschitzWith_timeDependentSuspension (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (x : E) :
    Continuous (v · x) :=
  continuous_snd.comp (hv.continuous.comp (continuous_id.prodMk continuous_const))

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem lipschitzWith_of_lipschitzWith_timeDependentSuspension (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (t : ℝ) :
    LipschitzWith K (v t) := fun x y ↦ by
  simpa [timeDependentSuspension, Prod.edist_eq] using hv (t, x) (t, y)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The suspension of a time-dependent field is Lipschitz with the joint Lipschitz constant of
the field in time and space. -/
theorem lipschitzWith_timeDependentSuspension {v : ℝ → E → E} {K : ℝ≥0}
    (hv : LipschitzWith K fun p : ℝ × E ↦ v p.1 p.2) :
    LipschitzWith K (timeDependentSuspension v) :=
  LipschitzWith.of_dist_le_mul fun p q ↦ by
    simpa [timeDependentSuspension, Prod.dist_eq] using hv.dist_le_mul p q

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

/-! ### Fields depending on a parameter -/

section Parameter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K : ℝ≥0}
  {v : F → ℝ → E → E}

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- For a family of time-dependent fields `v u` which is jointly Lipschitz in the parameter `u`,
the time and the point, each field `v u` has a Lipschitz suspension, with the same constant. -/
theorem lipschitzWith_timeDependentSuspension_of_parametric
    (hv : LipschitzWith K fun q : F × ℝ × E ↦ v q.1 q.2.1 q.2.2) (u : F) :
    LipschitzWith K (timeDependentSuspension (v u)) := by
  refine lipschitzWith_timeDependentSuspension (LipschitzWith.of_dist_le_mul fun a b ↦ ?_)
  have h := hv.dist_le_mul (u, a) (u, b)
  simp only [Prod.dist_eq (x := (u, a)) (y := (u, b)), dist_self,
    max_eq_right dist_nonneg] at h
  exact h

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- For a family of time-dependent fields `v u` which is jointly Lipschitz in the parameter `u`,
the time and the point, the field `(x, u) ↦ (v u t x, 0)` on `E × F`, which moves `x` along `v u`
and freezes the parameter, has a Lipschitz suspension, with the same constant. -/
theorem lipschitzWith_timeDependentSuspension_freeze
    (hv : LipschitzWith K fun q : F × ℝ × E ↦ v q.1 q.2.1 q.2.2) :
    LipschitzWith K (timeDependentSuspension fun t (q : E × F) ↦ (v q.2 t q.1, (0 : F))) := by
  refine lipschitzWith_timeDependentSuspension (LipschitzWith.of_dist_le_mul fun a b ↦ ?_)
  have h := hv.dist_le_mul (a.2.2, a.1, a.2.1) (b.2.2, b.1, b.2.1)
  simp only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
  exact max_le (le_max_of_le_right (le_max_right _ _))
    (max_le (le_max_left _ _) (le_max_of_le_right (le_max_left _ _)))

/-- **Flowing with a frozen parameter.** For a family of time-dependent fields `v u` which is
jointly Lipschitz in the parameter `u`, the time and the point, the flow of the field
`(x, u) ↦ (v u t x, 0)` on `E × F` keeps the parameter `u` and moves `x` by the flow of `v u`.
So the flows of the fields `v u` inherit from this single flow their joint regularity in the
parameter. -/
theorem timeDependentFlow_freeze (hv : LipschitzWith K fun q : F × ℝ × E ↦ v q.1 q.2.1 q.2.2)
    (s t : ℝ) (x : E) (u : F) :
    timeDependentFlow (fun t (q : E × F) ↦ (v q.2 t q.1, (0 : F)))
        (lipschitzWith_timeDependentSuspension_freeze hv) s t (x, u) =
      (timeDependentFlow (v u) (lipschitzWith_timeDependentSuspension_of_parametric hv u) s t x,
        u) := by
  set Φ := timeDependentFlow (fun t (q : E × F) ↦ (v q.2 t q.1, (0 : F)))
    (lipschitzWith_timeDependentSuspension_freeze hv) with hΦ
  have hsnd (τ : ℝ) : (Φ s τ (x, u)).2 = u :=
    timeDependentFlow_snd_eq_of_snd_eq _ (fun _ _ ↦ rfl) s τ rfl
  -- The first component of an orbit of `Φ` is an orbit of `v u`, by uniqueness of solutions.
  have hy (τ : ℝ) : HasDerivAt (fun τ ↦ (Φ s τ (x, u)).1) (v u τ (Φ s τ (x, u)).1) τ := by
    have h := (hasDerivAt_timeDependentFlow (fun t (q : E × F) ↦ (v q.2 t q.1, (0 : F)))
      (lipschitzWith_timeDependentSuspension_freeze hv) s τ (x, u)).hasFDerivAt.fst.hasDerivAt
    rw [← hΦ] at h
    simpa [hsnd] using h
  have h :=
    eq_timeDependentFlow (v u) (lipschitzWith_timeDependentSuspension_of_parametric hv u) hy s t
  rw [hΦ, timeDependentFlow_self, ← hΦ] at h
  exact Prod.ext h (hsnd t)

end Parameter

end TauCeti

end
