/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.TimeDependent
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Dynamics.FixedPoints.Defs

/-!
# Periodic solutions of time-dependent vector fields

For a time-periodic vector field, simultaneous translation of the initial and final times by a
period leaves its evolution unchanged. Consequently a trajectory is periodic exactly when its
initial point is fixed by the return map. Evaluation at the initial time gives an equivalence
between periodic solutions of the differential equation and fixed points of that map.

The results apply to Banach spaces whenever the suspended field is globally Lipschitz, the
hypothesis of `TauCeti.timeDependentFlow`. In particular they apply to the time-dependent
Hamiltonian evolution by taking `v t x = omega.hamiltonianVectorField (H t) x`. The period is an
arbitrary real number; taking it to be one gives the parametrized periodic trajectories used in
Hamiltonian dynamics. No minimal-period or nondegeneracy assertion is made.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, the discussion of time-dependent
  Hamiltonian flows and their periodic orbits.
-/

public section

open Function
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : ℝ → E → E} {K : ℝ≥0}
  (hv : LipschitzWith K (timeDependentSuspension v)) {T : ℝ}

/-- Simultaneously translating both times by a period of the field preserves the evolution. -/
theorem timeDependentFlow_add_period (hT : Periodic v T) (s t : ℝ) (x : E) :
    timeDependentFlow v hv (s + T) (t + T) x = timeDependentFlow v hv s t x := by
  have hsol (u : ℝ) :
      HasDerivAt (fun r ↦ timeDependentFlow v hv (s + T) (r + T) x)
        (v u (timeDependentFlow v hv (s + T) (u + T) x)) u := by
    simpa only [hT u] using
      (hasDerivAt_timeDependentFlow v hv (s + T) (u + T) x).comp_add_const u T
  simpa only [timeDependentFlow_self] using eq_timeDependentFlow v hv hsol s t

/-- For a time-periodic field, evolving for a period and then to time `t` gives the value at
`t + T` of the original trajectory. -/
theorem timeDependentFlow_add_period_right (hT : Periodic v T) (s t : ℝ) (x : E) :
    timeDependentFlow v hv s (t + T) x =
      timeDependentFlow v hv s t (timeDependentFlow v hv s (s + T) x) := by
  rw [← timeDependentFlow_add_period hv hT s t]
  exact (timeDependentFlow_trans v hv s (s + T) (t + T) x).symm

/-- A trajectory of a time-periodic field is periodic precisely when its initial point is a
fixed point of the return map. This includes the zero period. -/
theorem periodic_timeDependentFlow_iff (hT : Periodic v T) (s : ℝ) (x : E) :
    Periodic (fun t ↦ timeDependentFlow v hv s t x) T ↔
      IsFixedPt (timeDependentFlow v hv s (s + T)) x := by
  constructor
  · intro h
    simpa only [timeDependentFlow_self, IsFixedPt] using h s
  · intro h t
    dsimp only
    rw [timeDependentFlow_add_period_right hv hT, h.eq]

include hv in
/-- A global solution of a time-periodic differential equation is periodic if and only if it
returns to its initial value after one period of the field. -/
theorem periodic_iff_return_of_hasDerivAt (hT : Periodic v T) {y : ℝ → E}
    (hy : ∀ t, HasDerivAt y (v t (y t)) t) (s : ℝ) :
    Periodic y T ↔ y (s + T) = y s := by
  have heq : y = fun t ↦ timeDependentFlow v hv s t (y s) :=
    funext (eq_timeDependentFlow v hv hy s)
  rw [heq, periodic_timeDependentFlow_iff hv hT]
  simp only [timeDependentFlow_self, IsFixedPt]

/-- Parametrized periodic global solutions correspond to fixed points of the return map.
The forward map evaluates at the initial time, and the inverse follows the evolution.
Periodicity is written pointwise to keep the evaluation simp lemmas in normal form. -/
noncomputable def periodicSolutionEquivFixedPoints (hT : Periodic v T) (s : ℝ) :
    {y : ℝ → E // (∀ t, HasDerivAt y (v t (y t)) t) ∧ ∀ t, y (t + T) = y t} ≃
      fixedPoints (timeDependentFlow v hv s (s + T)) where
  toFun y := ⟨y.1 s, by
    rw [mem_fixedPoints, ← periodic_timeDependentFlow_iff hv hT]
    have heq : (fun t ↦ timeDependentFlow v hv s t (y.1 s)) = y.1 :=
      (funext (eq_timeDependentFlow v hv y.2.1 s)).symm
    rw [heq]
    exact y.2.2⟩
  invFun x := ⟨fun t ↦ timeDependentFlow v hv s t x,
    (fun t ↦ hasDerivAt_timeDependentFlow v hv s t x),
    (periodic_timeDependentFlow_iff hv hT s x).2 x.2⟩
  left_inv y := Subtype.ext (funext (eq_timeDependentFlow v hv y.2.1 s)).symm
  right_inv x := Subtype.ext (timeDependentFlow_self v hv s x)

/-- The correspondence from periodic solutions to fixed points evaluates at the initial time. -/
@[simp]
theorem periodicSolutionEquivFixedPoints_apply (hT : Periodic v T) (s : ℝ)
    (y : {y : ℝ → E // (∀ t, HasDerivAt y (v t (y t)) t) ∧ ∀ t, y (t + T) = y t}) :
    (periodicSolutionEquivFixedPoints hv hT s y : E) = y.1 s :=
  (rfl)

/-- The periodic solution associated to a fixed point is its evolution trajectory. -/
@[simp]
theorem periodicSolutionEquivFixedPoints_symm_apply (hT : Periodic v T) (s : ℝ)
    (x : fixedPoints (timeDependentFlow v hv s (s + T))) (t : ℝ) :
    ((periodicSolutionEquivFixedPoints hv hT s).symm x).val t =
      timeDependentFlow v hv s t x :=
  (rfl)

end TauCeti
