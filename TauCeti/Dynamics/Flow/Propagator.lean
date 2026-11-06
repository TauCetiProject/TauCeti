/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
public import TauCeti.Dynamics.Flow.Periodic
public import TauCeti.Dynamics.Flow.Variational

/-!
# The linearized time-dependent flow is a propagator

Let `v` be a jointly `C¹` time-dependent vector field on a Banach space `E` whose suspension is
globally Lipschitz, and let `φ(s, t)` be its flow (`TauCeti.timeDependentFlow`). Along the
trajectory of `x` starting at time `s`, the linearized field

`S(u) = D(v_{s + u})(φ(s, s + u) x)`

is a continuous path of bounded operators (`TauCeti.continuous_fderiv_comp_timeDependentFlow`).
The variational equation `TauCeti.hasDerivAt_fderiv_timeDependentFlow` says that
`u ↦ Dφ(s, s + u)(x)` solves `Ψ' = S Ψ` with `Ψ(0) = 1`. By uniqueness of solutions of linear
equations it is therefore the left Dyson series of `S`, the propagator of the linearized equation
`w' = S(u) w` (`TauCeti.fderiv_timeDependentFlow_eq_dysonSeriesLeft`):

`Dφ(s, s + t)(x) = dysonSeriesLeft S t`.

If `v` has period `T` in time and `x` is a fixed point of the return map `φ(s, s + T)`, then the
trajectory and hence `S` have period `T` (`TauCeti.periodic_fderiv_comp_timeDependentFlow`), and the
derivative of the return map at `x` is the value of the propagator after one period. A vector is
fixed by this derivative exactly when the corresponding solution `u ↦ dysonSeriesLeft S u w` of the
linearized equation has period `T` (`TauCeti.periodic_dysonSeriesLeft_apply_iff`). This is the
form in which nondegeneracy of a periodic orbit is compared with the kernel of a linearized
operator on periodic loops.

## Main results

* `TauCeti.fderiv_timeDependentFlow_eq_dysonSeriesLeft`: the derivative of the flow is the
  propagator of the linearized equation along the trajectory.
* `TauCeti.periodic_fderiv_comp_timeDependentFlow`: along a periodic trajectory of a periodic
  field, the linearized field is periodic.

## References

* P. Hartman, *Ordinary Differential Equations*, 2nd ed., SIAM, 2002, Chapter V, Theorem 3.1
  (differentiability of solutions with respect to initial conditions and the variational
  equation).
-/

public section

open Function
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : ℝ → E → E} {K : ℝ≥0} (hv : LipschitzWith K (timeDependentSuspension v))

/-- Along a periodic trajectory of a field of the same period, the linearized field
`u ↦ D(v_{s + u})(φ(s, s + u) x)` is periodic. -/
theorem periodic_fderiv_comp_timeDependentFlow {T : ℝ} (hT : Periodic v T) (s : ℝ) {x : E}
    (hx : IsFixedPt (timeDependentFlow v hv s (s + T)) x) :
    Periodic (fun u ↦ fderiv ℝ (v (s + u)) (timeDependentFlow v hv s (s + u) x)) T := by
  have hper := (periodic_timeDependentFlow_iff hv hT s x).2 hx
  intro u
  dsimp only
  rw [← add_assoc, hT (s + u), show timeDependentFlow v hv s (s + u + T) x = _ from hper (s + u)]

variable (hvs : ContDiff ℝ 1 fun p : ℝ × E ↦ v p.1 p.2)
include hvs

/-- The linearized field `u ↦ D(v_{s + u})(φ(s, s + u) x)` along a trajectory of a jointly `C¹`
field is continuous. -/
theorem continuous_fderiv_comp_timeDependentFlow (s : ℝ) (x : E) :
    Continuous fun u ↦ fderiv ℝ (v (s + u)) (timeDependentFlow v hv s (s + u) x) := by
  have hγ : Continuous fun u ↦ timeDependentFlow v hv s (s + u) x :=
    continuous_iff_continuousAt.2 fun u ↦
      ((hasDerivAt_timeDependentFlow v hv s (s + u) x).comp_const_add s u).continuousAt
  have hf : ContDiff ℝ 1 (uncurry fun u y ↦ v (s + u) y) :=
    hvs.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
  exact (hf.fderiv (contDiff_zero.2 hγ) le_rfl).continuous

/-- **The derivative of the flow is the propagator of the linearized equation.** For a jointly
`C¹` time-dependent field with globally Lipschitz suspension, the derivative of the flow from time
`s` to time `s + t` at `x` is the left Dyson series, at time `t`, of the linearized field
`u ↦ D(v_{s + u})(φ(s, s + u) x)` along the trajectory of `x`. -/
theorem fderiv_timeDependentFlow_eq_dysonSeriesLeft (s t : ℝ) (x : E) :
    fderiv ℝ (timeDependentFlow v hv s (s + t)) x =
      dysonSeriesLeft (fun u ↦ fderiv ℝ (v (s + u)) (timeDependentFlow v hv s (s + u) x)) t := by
  have hf (u : ℝ) : HasDerivAt (fun u ↦ fderiv ℝ (timeDependentFlow v hv s (s + u)) x)
      (fderiv ℝ (v (s + u)) (timeDependentFlow v hv s (s + u) x) *
        fderiv ℝ (timeDependentFlow v hv s (s + u)) x) u :=
    (hasDerivAt_fderiv_timeDependentFlow hv hvs s (s + u) x).comp_const_add s u
  have hself : timeDependentFlow v hv s (s + 0) = id :=
    funext fun y ↦ by rw [add_zero, timeDependentFlow_self, id]
  rw [eq_dysonSeriesLeft_mul (continuous_fderiv_comp_timeDependentFlow hv hvs s x) hf t, hself,
    fderiv_id, ContinuousLinearMap.one_def.symm, mul_one]

end TauCeti
