/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.TimeDependent
public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Time-dependent Hamiltonian flows on symplectic vector spaces

For a time-dependent Hamiltonian `H : ℝ → V → ℝ`, the associated nonautonomous vector
field is `X_H(t, x) = X_{H_t}(x)`, with the convention
`ω(X_H(t, x), v) = fderiv ℝ (H t) x v`; when `H t` is differentiable at `x`, this is its
differential there.  Suspending this field by the clock equation and assuming that the resulting
field on `ℝ × V` is globally Lipschitz produces a global two-time Hamiltonian evolution.

The flow solves the evolution equation for this `fderiv`-defined vector field, starts at the
prescribed point, is jointly continuous, and satisfies the composition law through intermediate
times. If `H` is jointly `C²`, every evolution map preserves the symplectic form on tangent vectors.
For an autonomous Hamiltonian the construction recovers the existing Hamiltonian flow at elapsed
time `t - s`; the required Lipschitz hypothesis on the suspension follows directly from the one on
the autonomous Hamiltonian vector field.

## Main declarations

* `TauCeti.SymplecticForm.timeDependentHamiltonianSuspension`: the suspended Hamiltonian field.
* `TauCeti.SymplecticForm.timeDependentHamiltonianFlow`: its global two-time evolution.
* `TauCeti.SymplecticForm.hasDerivAt_timeDependentHamiltonianFlow`: the evolution equation.
* `TauCeti.SymplecticForm.eq_timeDependentHamiltonianFlow`: uniqueness of solutions.
* `TauCeti.SymplecticForm.hamiltonianVectorField_eq_inverse_spatialFDeriv`: the fixed-time
  Hamiltonian field in terms of the spatial Jacobian of `H`.
* `TauCeti.SymplecticForm.contDiff_timeDependentHamiltonianSuspension`: smoothness of the
  suspended Hamiltonian field.
* `TauCeti.SymplecticForm.apply_fderiv_timeDependentHamiltonianFlow`: time-dependent Hamiltonian
  evolution preserves the symplectic form.
* `TauCeti.SymplecticForm.apply_fderiv_timeDependentHamiltonianFlow_of_contDiff_suspension`: the
  same under a `C¹` suspended field and `C²` fixed-time Hamiltonians.
* `TauCeti.SymplecticForm.timeDependentHamiltonianFlow_const`: recovery of the autonomous flow.

See McDuff--Salamon, *Introduction to Symplectic Topology*, the discussion of time-dependent
Hamiltonian vector fields and flows.
-/

public section

open Function
open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The autonomous suspension of the time-dependent Hamiltonian vector field: the clock advances
at speed one and the spatial component is `X_{H_t}`. -/
noncomputable def timeDependentHamiltonianSuspension (omega : SymplecticForm V)
    (H : ℝ → V → ℝ) :
    ℝ × V → ℝ × V :=
  timeDependentSuspension fun t x ↦ omega.hamiltonianVectorField (H t) x

/-- The Hamiltonian suspension is the generic time-dependent suspension of the Hamiltonian
vector field. -/
theorem timeDependentHamiltonianSuspension_eq (omega : SymplecticForm V) (H : ℝ → V → ℝ) :
    omega.timeDependentHamiltonianSuspension H =
      timeDependentSuspension fun t x ↦ omega.hamiltonianVectorField (H t) x := (rfl)

@[simp]
theorem timeDependentHamiltonianSuspension_apply (omega : SymplecticForm V)
    (H : ℝ → V → ℝ) (t : ℝ) (x : V) :
    omega.timeDependentHamiltonianSuspension H (t, x) =
      (1, omega.hamiltonianVectorField (H t) x) :=
  by rw [timeDependentHamiltonianSuspension, timeDependentSuspension_apply]

/-- The global time-dependent Hamiltonian evolution from time `s` to time `t`. -/
noncomputable def timeDependentHamiltonianFlow (omega : SymplecticForm V) (H : ℝ → V → ℝ)
    {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (s t : ℝ) (x : V) : V :=
  timeDependentFlow (fun u y ↦ omega.hamiltonianVectorField (H u) y) hX s t x

/-- The time-dependent Hamiltonian evolution is the time-dependent flow of the Hamiltonian
vector field. -/
theorem timeDependentHamiltonianFlow_eq (omega : SymplecticForm V) (H : ℝ → V → ℝ)
    {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H)) :
    omega.timeDependentHamiltonianFlow H hX =
      timeDependentFlow (fun u y ↦ omega.hamiltonianVectorField (H u) y)
        (omega.timeDependentHamiltonianSuspension_eq H ▸ hX) := (rfl)

/-- The time-dependent Hamiltonian evolution starts at its prescribed point. -/
@[simp]
theorem timeDependentHamiltonianFlow_self (omega : SymplecticForm V) (H : ℝ → V → ℝ)
    {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (s : ℝ) (x : V) :
    omega.timeDependentHamiltonianFlow H hX s s x = x :=
  timeDependentFlow_self _ hX s x

/-- Time-dependent Hamiltonian evolution through an intermediate time composes. -/
@[simp]
theorem timeDependentHamiltonianFlow_trans (omega : SymplecticForm V) (H : ℝ → V → ℝ)
    {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (r s t : ℝ) (x : V) :
    omega.timeDependentHamiltonianFlow H hX s t
        (omega.timeDependentHamiltonianFlow H hX r s x) =
      omega.timeDependentHamiltonianFlow H hX r t x :=
  timeDependentFlow_trans _ hX r s t x

/-- Each time map of the time-dependent Hamiltonian evolution is bijective. -/
theorem bijective_timeDependentHamiltonianFlow (omega : SymplecticForm V) (H : ℝ → V → ℝ)
    {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H)) (s t : ℝ) :
    Bijective (omega.timeDependentHamiltonianFlow H hX s t) :=
  bijective_timeDependentFlow _ hX s t

/-- The time-dependent Hamiltonian evolution is jointly continuous in both times and the point. -/
theorem continuous_timeDependentHamiltonianFlow (omega : SymplecticForm V)
    (H : ℝ → V → ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H)) :
    Continuous fun p : (ℝ × ℝ) × V ↦
      omega.timeDependentHamiltonianFlow H hX p.1.1 p.1.2 p.2 :=
  continuous_timeDependentFlow _ hX

/-- At a point where `H` is jointly differentiable, the Hamiltonian vector field of the
fixed-time Hamiltonian `H t` is the contraction-dual of the spatial Jacobian of `H`. -/
theorem hamiltonianVectorField_eq_inverse_spatialFDeriv (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {t : ℝ} {x : V} (hH : DifferentiableAt ℝ (Function.uncurry H) (t, x)) :
    omega.hamiltonianVectorField (H t) x =
      omega.toBilinForm.toContinuousBilinearMap.inverse
        (spatialFDeriv (Function.uncurry H) x t) := by
  rw [eq_comm, eq_hamiltonianVectorField_iff, ← fderiv_timeSlice hH]
  exact fun w ↦ congrArg (fun L : V →L[ℝ] ℝ ↦ L w)
    (omega.isInvertible_toContinuousBilinearMap.self_apply_inverse _)

/-- A jointly `C^(n+2)` time-dependent Hamiltonian has a `C^(n+1)` suspended Hamiltonian vector
field. -/
theorem contDiff_timeDependentHamiltonianSuspension (omega : SymplecticForm V) (n : ℕ)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ (n + 2) (Function.uncurry H)) :
    ContDiff ℝ (n + 1) (omega.timeDependentHamiltonianSuspension H) := by
  have hfun : omega.timeDependentHamiltonianSuspension H = fun p : ℝ × V ↦
      ((1 : ℝ), omega.toBilinForm.toContinuousBilinearMap.inverse
        ((fderiv ℝ (Function.uncurry H) p).comp (ContinuousLinearMap.inr ℝ ℝ V))) := by
    funext ⟨t, x⟩
    rw [timeDependentHamiltonianSuspension_apply,
      omega.hamiltonianVectorField_eq_inverse_spatialFDeriv (hH.differentiable (by simp) (t, x)),
      spatialFDeriv_def]
  rw [hfun]
  exact contDiff_const.prodMk (omega.toBilinForm.toContinuousBilinearMap.inverse.contDiff.comp
    ((hH.fderiv_right (m := n + 1) (by norm_cast)).clm_comp contDiff_const))

/-- Each evolution map of a time-dependent Hamiltonian preserves the symplectic form on tangent
vectors, provided the suspended Hamiltonian field is `C¹` and each fixed-time Hamiltonian is
`C²`. -/
theorem apply_fderiv_timeDependentHamiltonianFlow_of_contDiff_suspension
    (omega : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (hSusp : ContDiff ℝ 1 (omega.timeDependentHamiltonianSuspension H))
    (hslice : ∀ r, ContDiff ℝ 2 (H r)) (s t : ℝ) (x u v : V) :
    omega (fderiv ℝ (omega.timeDependentHamiltonianFlow H hX s t) x u)
        (fderiv ℝ (omega.timeDependentHamiltonianFlow H hX s t) x v) = omega u v := by
  rw [omega.timeDependentHamiltonianFlow_eq H hX]
  set φ := timeDependentFlow (fun a y ↦ omega.hamiltonianVectorField (H a) y) hX s
  have hvs : ContDiff ℝ 1 fun p : ℝ × V ↦ omega.hamiltonianVectorField (H p.1) p.2 := by
    convert hSusp.snd using 1
    funext ⟨r, y⟩
    simp
  have hd (r : ℝ) : HasDerivAt
      (fun q ↦ omega (fderiv ℝ (φ q) x u) (fderiv ℝ (φ q) x v)) 0 r := by
    have hφ := hasDerivAt_fderiv_timeDependentFlow hX hvs s r x
    have hu := hφ.clm_apply (hasDerivAt_const r u)
    have hv := hφ.clm_apply (hasDerivAt_const r v)
    have hp := omega.toBilinForm.toContinuousBilinearMap.hasDerivAt_of_bilinear
      (fun _ ↦ hu) (fun _ ↦ hv)
    simp only [LinearMap.toContinuousBilinearMap_apply, ContinuousLinearMap.comp_apply, map_zero,
      add_zero] at hp
    convert hp using 1
    simpa only [add_comm] using (omega.apply_fderiv_hamiltonianVectorField_add
      (hslice r).contDiffAt (fderiv ℝ (φ r) x u) (fderiv ℝ (φ r) x v)).symm
  have hc := is_const_of_deriv_eq_zero (fun r ↦ (hd r).differentiableAt)
    (fun r ↦ (hd r).deriv) t s
  have hself : φ s = id := funext fun y ↦ timeDependentFlow_self _ hX s y
  simpa only [hself, fderiv_id, ContinuousLinearMap.id_apply] using hc

/-- Each evolution map of a jointly `C²` time-dependent Hamiltonian preserves the symplectic
form on tangent vectors. -/
@[simp]
theorem apply_fderiv_timeDependentHamiltonianFlow (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (s t : ℝ) (x u v : V) :
    omega (fderiv ℝ (omega.timeDependentHamiltonianFlow H hX s t) x u)
        (fderiv ℝ (omega.timeDependentHamiltonianFlow H hX s t) x v) = omega u v :=
  omega.apply_fderiv_timeDependentHamiltonianFlow_of_contDiff_suspension hX
    (omega.contDiff_timeDependentHamiltonianSuspension 0 hH)
    (fun r ↦ hH.comp (contDiff_prodMk_right r)) s t x u v

/-- The construction does not depend on the chosen Lipschitz bound for the suspended Hamiltonian
vector field. -/
theorem timeDependentHamiltonianFlow_congr (omega : SymplecticForm V) (H : ℝ → V → ℝ)
    {K K' : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (hX' : LipschitzWith K' (omega.timeDependentHamiltonianSuspension H)) :
    omega.timeDependentHamiltonianFlow H hX = omega.timeDependentHamiltonianFlow H hX' :=
  timeDependentFlow_congr _ hX hX'

/-- Orbits solve the evolution equation for the `fderiv`-defined Hamiltonian vector field. -/
theorem hasDerivAt_timeDependentHamiltonianFlow (omega : SymplecticForm V)
    (H : ℝ → V → ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (s t : ℝ) (x : V) :
    HasDerivAt (fun u ↦ omega.timeDependentHamiltonianFlow H hX s u x)
      (omega.hamiltonianVectorField (H t)
        (omega.timeDependentHamiltonianFlow H hX s t x)) t :=
  hasDerivAt_timeDependentFlow _ hX s t x

/-- **Uniqueness of the time-dependent Hamiltonian evolution.** A global solution of
`y' = X_{H_t}(y)` is the time-dependent Hamiltonian evolution through its value at any chosen
initial time. -/
theorem eq_timeDependentHamiltonianFlow (omega : SymplecticForm V) (H : ℝ → V → ℝ)
    {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H)) {y : ℝ → V}
    (hy : ∀ t, HasDerivAt y (omega.hamiltonianVectorField (H t) (y t)) t) (s t : ℝ) :
    y t = omega.timeDependentHamiltonianFlow H hX s t (y s) :=
  eq_timeDependentFlow _ hX hy s t

/-- A Lipschitz autonomous Hamiltonian vector field has a Lipschitz time suspension. -/
theorem lipschitzWith_timeDependentHamiltonianSuspension_const (omega : SymplecticForm V)
    (H : V → ℝ) {K : ℝ≥0} (hX : LipschitzWith K (omega.hamiltonianVectorField H)) :
    LipschitzWith K (omega.timeDependentHamiltonianSuspension fun _ ↦ H) := by
  have hK : (0 : ℝ≥0) ≤ K := bot_le
  have h : LipschitzWith K (fun p : ℝ × V ↦
      ((1 : ℝ), omega.hamiltonianVectorField H p.2)) := by
    simpa only [max_eq_right hK, Function.comp_apply, mul_one] using
      (LipschitzWith.const (α := ℝ × V) (1 : ℝ)).prodMk
        (hX.comp LipschitzWith.prod_snd)
  convert h using 1
  funext ⟨t, x⟩
  simp

/-- For an autonomous Hamiltonian, the time-dependent evolution is the ordinary Hamiltonian flow
at the elapsed time `t - s`. -/
theorem timeDependentHamiltonianFlow_const (omega : SymplecticForm V) (H : V → ℝ)
    {K : ℝ≥0} (hX : LipschitzWith K (omega.hamiltonianVectorField H)) (s t : ℝ) (x : V) :
    omega.timeDependentHamiltonianFlow (fun _ ↦ H)
        (omega.lipschitzWith_timeDependentHamiltonianSuspension_const H hX) s t x =
      omega.hamiltonianFlow H hX (t - s) x := by
  symm
  simpa using omega.eq_timeDependentHamiltonianFlow (fun _ ↦ H)
    (omega.lipschitzWith_timeDependentHamiltonianSuspension_const H hX)
      (y := fun u ↦ omega.hamiltonianFlow H hX (u - s) x)
      (fun u ↦ (omega.hasDerivAt_hamiltonianFlow H hX x (u - s)).comp_sub_const u s) s t

end TauCeti.SymplecticForm

end
