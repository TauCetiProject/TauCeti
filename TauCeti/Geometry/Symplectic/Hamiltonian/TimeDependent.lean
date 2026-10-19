/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.TimeDependent
public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow

/-!
# Time-dependent Hamiltonian flows on symplectic vector spaces

For a time-dependent Hamiltonian `H : ℝ → V → ℝ`, the associated nonautonomous vector
field is `X_H(t, x) = X_{H_t}(x)`, with the convention
`ω(X_H(t, x), v) = fderiv ℝ (H t) x v`; when `H t` is differentiable at `x`, this is its
differential there.  Suspending this field by the clock equation and assuming that the resulting
field on `ℝ × V` is globally Lipschitz produces a global two-time Hamiltonian evolution.

The flow solves the evolution equation for this `fderiv`-defined vector field, starts at the
prescribed point, is jointly continuous, and satisfies the composition law through intermediate
times.  For an autonomous Hamiltonian it recovers the existing Hamiltonian flow at elapsed time
`t - s`; the required Lipschitz hypothesis on the suspension follows directly from the one on the
autonomous Hamiltonian vector field.

## Main declarations

* `TauCeti.SymplecticForm.timeDependentHamiltonianSuspension`: the suspended Hamiltonian field.
* `TauCeti.SymplecticForm.timeDependentHamiltonianFlow`: its global two-time evolution.
* `TauCeti.SymplecticForm.hasDerivAt_timeDependentHamiltonianFlow`: the evolution equation.
* `TauCeti.SymplecticForm.timeDependentHamiltonianFlow_const`: recovery of the autonomous flow.

See McDuff--Salamon, *Introduction to Symplectic Topology*, the discussion of time-dependent
Hamiltonian vector fields and flows.
-/

public section

open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The autonomous suspension of the time-dependent Hamiltonian vector field: the clock advances
at speed one and the spatial component is `X_{H_t}`. -/
noncomputable def timeDependentHamiltonianSuspension (omega : SymplecticForm V)
    (H : ℝ → V → ℝ) :
    ℝ × V → ℝ × V :=
  timeDependentSuspension fun t x ↦ omega.hamiltonianVectorField (H t) x

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

/-- The time-dependent Hamiltonian evolution is jointly continuous in both times and the point. -/
theorem continuous_timeDependentHamiltonianFlow (omega : SymplecticForm V)
    (H : ℝ → V → ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H)) :
    Continuous fun p : (ℝ × ℝ) × V ↦
      omega.timeDependentHamiltonianFlow H hX p.1.1 p.1.2 p.2 :=
  continuous_timeDependentFlow _ hX

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
  have heq := eq_timeDependentFlow _
    (omega.lipschitzWith_timeDependentHamiltonianSuspension_const H hX)
      (y := fun u ↦ omega.hamiltonianFlow H hX (u - s) x)
      (fun u ↦ (omega.hasDerivAt_hamiltonianFlow H hX x (u - s)).comp_sub_const u s) s t
  simpa [timeDependentHamiltonianFlow] using heq

end TauCeti.SymplecticForm

end
