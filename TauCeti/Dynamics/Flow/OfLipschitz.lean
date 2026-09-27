/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.Analysis.ODE.GlobalSolution

/-!
# The flow of a globally Lipschitz vector field

A vector field whose solutions may blow up in finite time generates no flow: the group law
`φ (t₁ + t₂) = φ t₁ ∘ φ t₂` needs solutions defined for all time. A globally Lipschitz vector
field on a Banach space has them, by `ODE.globalSolution`, and this file assembles them into a
`Flow ℝ E`.

The group law is uniqueness of solutions applied to the time-translated orbit, the identity law is
the initial condition, and the joint continuity required by `Flow` is
`ODE.continuous_globalSolution`.

## Main declarations

* `TauCeti.flowOfLipschitz`: the flow of a globally Lipschitz vector field on a Banach space.
* `TauCeti.hasDerivAt_flowOfLipschitz` and `TauCeti.isIntegralCurve_flowOfLipschitz`: its
  orbits solve the differential equation.
* `TauCeti.eq_flowOfLipschitz`: every global solution is an orbit of the flow.
* `TauCeti.eq_flowOfLipschitz_of_isIntegralCurveOn`: the corresponding uniqueness statement for a
  solution on any time set containing the interval between zero and the chosen time.
* `TauCeti.flowOfLipschitz_congr`: it does not depend on the chosen Lipschitz bound.
* `TauCeti.forall_flowOfLipschitz_eq_self_iff`: the rest points of the flow are the zeros of the
  vector field.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : E → E} {K : ℝ≥0}

/-- **The flow of a globally Lipschitz vector field** on a Banach space: the time-`t` map sends an
initial point to the value at time `t` of the unique global solution of `γ' = v ∘ γ` through it. -/
noncomputable def flowOfLipschitz (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) : Flow ℝ E where
  toFun t x := ODE.globalSolution v hv x t
  cont' := ODE.continuous_globalSolution v hv
  map_add' t₁ t₂ x := by
    simpa [add_comm] using ODE.globalSolution_add v hv x t₂ t₁
  map_zero' x := ODE.globalSolution_zero v hv x

@[simp]
theorem flowOfLipschitz_apply (hv : LipschitzWith K v) (t : ℝ) (x : E) :
    flowOfLipschitz v hv t x = ODE.globalSolution v hv x t := (rfl)

/-- **Independence of the Lipschitz bound.** Two Lipschitz witnesses for the same vector field,
with possibly different constants, produce the same flow. -/
theorem flowOfLipschitz_congr {K' : ℝ≥0} (hv : LipschitzWith K v) (hv' : LipschitzWith K' v) :
    flowOfLipschitz v hv = flowOfLipschitz v hv' :=
  Flow.ext fun t x ↦ congrFun (ODE.globalSolution_congr v hv hv' x) t

/-- Every orbit of the flow solves the differential equation. -/
theorem hasDerivAt_flowOfLipschitz (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ flowOfLipschitz v hv t x) (v (flowOfLipschitz v hv t x)) t :=
  ODE.hasDerivAt_globalSolution v hv x t

/-- Every orbit of the flow is an integral curve of the vector field. -/
theorem isIntegralCurve_flowOfLipschitz (hv : LipschitzWith K v) (x : E) :
    IsIntegralCurve (fun t ↦ flowOfLipschitz v hv t x) fun _ y ↦ v y :=
  ODE.isIntegralCurve_globalSolution v hv x

/-- **Every global solution is an orbit** of the flow, namely the one through its initial value. -/
theorem eq_flowOfLipschitz (hv : LipschitzWith K v) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (t : ℝ) : γ t = flowOfLipschitz v hv t (γ 0) :=
  congrFun (ODE.eq_globalSolution v hv hγ) t

/-- **Uniqueness on a time set.** An integral curve on a set containing the interval between zero
and `t` agrees at `t` with the globally Lipschitz flow through its value at zero. -/
theorem eq_flowOfLipschitz_of_isIntegralCurveOn (hv : LipschitzWith K v) {γ : ℝ → E}
    {s : Set ℝ} (hγ : IsIntegralCurveOn γ (fun _ y ↦ v y) s) {t : ℝ}
    (hst : uIcc 0 t ⊆ s) :
    γ t = flowOfLipschitz v hv t (γ 0) := by
  have hγ' := hγ.mono hst
  let η : ℝ → E := fun s ↦ flowOfLipschitz v hv s (γ 0)
  have hη : IsIntegralCurve η (fun _ y ↦ v y) := isIntegralCurve_flowOfLipschitz hv (γ 0)
  have hinit : γ 0 = η 0 := by simp only [η, _root_.Flow.map_zero_apply]
  rcases le_total 0 t with ht | ht
  · rw [uIcc_of_le ht] at hγ'
    have heq := ODE_solution_unique (a := 0) (b := t) (v := fun _ y ↦ v y)
      (fun _ ↦ hv) hγ'.continuousOn
      (fun s hs ↦ (hγ' s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs))
      hη.continuous.continuousOn (fun s _ ↦ (hη s).hasDerivWithinAt) hinit
    exact heq ⟨ht, le_rfl⟩
  · rw [uIcc_of_ge ht] at hγ'
    have heq := ODE_solution_unique_of_mem_Icc_left (a := t) (b := 0)
      (v := fun _ y ↦ v y) (s := fun _ ↦ univ) (K := K)
      (fun _ _ ↦ hv.lipschitzOnWith) hγ'.continuousOn
      (fun s hs ↦ (hγ' s ⟨hs.1.le, hs.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem hs))
      (fun _ _ ↦ mem_univ _) hη.continuous.continuousOn
      (fun s _ ↦ (hη s).hasDerivWithinAt) (fun _ _ ↦ mem_univ _) hinit
    exact heq ⟨le_rfl, ht⟩

/-- **The rest points of the flow are the zeros of the vector field.** -/
theorem forall_flowOfLipschitz_eq_self_iff (hv : LipschitzWith K v) (x : E) :
    (∀ t, flowOfLipschitz v hv t x = x) ↔ v x = 0 := by
  refine ⟨fun h ↦ ?_, fun h t ↦ ?_⟩
  · have h1 : HasDerivAt (fun t ↦ flowOfLipschitz v hv t x)
        (v (flowOfLipschitz v hv 0 x)) 0 :=
      hasDerivAt_flowOfLipschitz hv x 0
    have h2 : HasDerivAt (fun t : ℝ ↦ flowOfLipschitz v hv t x) 0 0 :=
      (hasDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq (.of_forall h)
    have h3 := h1.unique h2
    rwa [h 0] at h3
  · have hconst : ∀ s : ℝ, HasDerivAt (fun _ : ℝ ↦ x) (v ((fun _ : ℝ ↦ x) s)) s := fun s ↦ by
      simpa [h] using hasDerivAt_const s x
    simpa using (eq_flowOfLipschitz hv hconst t).symm

end TauCeti
