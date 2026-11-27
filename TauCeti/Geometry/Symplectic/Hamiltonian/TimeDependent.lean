/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.TimeDependent
public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
public import TauCeti.Analysis.Calculus.ParametricFDeriv
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Dynamics.Flow.Periodic.Basic

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
* `TauCeti.SymplecticForm.differentiable_timeDependentHamiltonianFlow` and
  `TauCeti.SymplecticForm.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft`: the evolution
  maps are differentiable, and along an orbit `x` the derivative of the evolution is the
  propagator `TauCeti.dysonSeriesLeft` of the linearized equation `ζ' = dX_{H_t}(x(t)) ζ`.
* `TauCeti.SymplecticForm.apply_dysonSeriesLeft_fderiv_hamiltonianVectorField`: the propagator
  of the linearized Hamiltonian equation along any continuous path is symplectic.
* `TauCeti.SymplecticForm.timeDependentHamiltonianFlow_const`: recovery of the autonomous flow.
* `TauCeti.SymplecticForm.hasDerivAt_apply_of_hasDerivAt_hamiltonianVectorField`: a
  time-dependent function `F` changes along a solution at the rate `∂_t F + {F_t, H_t}`; in
  particular (`..._self`) the energy changes at the rate `∂_t H`.
* `TauCeti.SymplecticForm.forall_apply_timeDependentHamiltonianFlow_eq_iff`: a differentiable
  `F` is conserved by the evolution exactly when `∂_t F + {F_t, H_t} = 0`.
* `TauCeti.SymplecticForm.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg`: reversing
  time turns a solution of `y' = X_{-G}(y)` into a solution of `x' = X_G(x)`; for instance a
  solution for the reversed Hamiltonian `-H_{-t}` into a solution for `H_t`
  (`TauCeti.SymplecticForm.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse`).
* `TauCeti.SymplecticForm.exists_pos_forall_eq_of_isNondegenerateFixedPt` and
  `TauCeti.SymplecticForm.eq_zero_of_dysonSeriesLeft_apply_eq_self`: a one-periodic orbit `x` with
  `x(0)` a nondegenerate fixed point of the time-one map is isolated among the one-periodic orbits,
  and the return map `Ψ(1)` of its linearized equation fixes no nonzero vector. The `_reverse`
  variants state the same for the reversed Hamiltonian `-H_{-t}`, whose one-periodic orbits are
  those of `H_t` traversed backwards.
* `TauCeti.SymplecticForm.finite_setOf_periodic_hasDerivAt_of_isNondegenerateFixedPt`: if all
  one-periodic orbits with values in a compact set are nondegenerate, there are finitely many.

See McDuff--Salamon, *Introduction to Symplectic Topology*, the discussion of time-dependent
Hamiltonian vector fields and flows.
-/

public section

open Function
open scoped NNReal Manifold

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
        (spatialFDeriv (𝕜 := ℝ) (Function.uncurry H) x t) := by
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
  have hvs : ContDiff ℝ 1 fun p : ℝ × V ↦ omega.hamiltonianVectorField (H p.1) p.2 := by
    convert hSusp.snd using 1
    funext ⟨r, y⟩
    simp
  rw [fderiv_timeDependentFlow_eq_dysonSeriesLeft _ hvs]
  refine apply_dysonSeriesLeft_apply_dysonSeriesLeft ?_ omega.toBilinForm.toContinuousBilinearMap
    (fun r ↦ omega.apply_fderiv_hamiltonianVectorField_add (hslice (s + r)).contDiffAt) (t - s) u v
  exact (ContDiff.fderiv (f := fun a y ↦ omega.hamiltonianVectorField (H a) y) hvs
    (contDiff_zero.2 ((continuous_timeDependentFlow _ _).comp
      (by fun_prop : Continuous fun r : ℝ ↦ ((s, r), x)))) le_rfl).continuous.comp
    (continuous_const.add continuous_id)

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

/-- Each evolution map of a jointly `C²` time-dependent Hamiltonian is differentiable. -/
theorem differentiable_timeDependentHamiltonianFlow (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (s t : ℝ) :
    Differentiable ℝ (omega.timeDependentHamiltonianFlow H hX s t) := by
  rw [omega.timeDependentHamiltonianFlow_eq H hX]
  exact differentiable_timeDependentFlow _
    (omega.contDiff_hamiltonianVectorField_uncurry (n := 1) hH) s t

/-- **The linearized evolution along an orbit.** Let `x` be an orbit of a jointly `C²`
time-dependent Hamiltonian `H` whose suspended vector field is globally Lipschitz,
`x' = X_{H_t}(x)`. Then the derivative at `x(s)` of the evolution from time `s` to time `t` is
the propagator from `0` to `t - s` of the linearized Hamiltonian equation `ζ' = S_r ζ` along `x`,
with `S_r = dX_{H_{s + r}}(x(s + r))`. For a one-periodic orbit and `s = 0`, the return map
`Ψ(1)` of `ζ' = dX_{H_r}(x(r)) ζ` is thus the derivative of the time-one map at its fixed point
`x(0)`. -/
theorem fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (omega.hamiltonianVectorField (H t) (x t)) t) (s t : ℝ) :
    fderiv ℝ (omega.timeDependentHamiltonianFlow H hX s t) (x s) =
      dysonSeriesLeft
        (fun r ↦ fderiv ℝ (omega.hamiltonianVectorField (H (s + r))) (x (s + r))) (t - s) := by
  have horbit (r : ℝ) := (omega.eq_timeDependentHamiltonianFlow H hX hx s r).symm
  rw [timeDependentHamiltonianFlow_eq] at horbit ⊢
  rw [fderiv_timeDependentFlow_eq_dysonSeriesLeft _
    (omega.contDiff_hamiltonianVectorField_uncurry (n := 1) hH)]
  simp only [horbit]

/-- **The propagator of the linearized Hamiltonian equation is symplectic.** Along a continuous
path `x` and for a jointly `C²` time-dependent Hamiltonian, the propagator of `ζ' = S_r ζ`, with
`S_r = dX_{H_{s + r}}(x(s + r))`, preserves `ω`. By
`fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft`, along an orbit this propagator is the
derivative of the evolution. -/
theorem apply_dysonSeriesLeft_fderiv_hamiltonianVectorField (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H)) {x : ℝ → V} (hx : Continuous x)
    (s t : ℝ) (u v : V) :
    omega (dysonSeriesLeft
        (fun r ↦ fderiv ℝ (omega.hamiltonianVectorField (H (s + r))) (x (s + r))) t u)
      (dysonSeriesLeft
        (fun r ↦ fderiv ℝ (omega.hamiltonianVectorField (H (s + r))) (x (s + r))) t v) =
      omega u v :=
  apply_dysonSeriesLeft_apply_dysonSeriesLeft
    ((omega.continuous_fderiv_hamiltonianVectorField_comp hH hx).comp
      (continuous_const.add continuous_id)) omega.toBilinForm.toContinuousBilinearMap
    (fun r ↦ omega.apply_fderiv_hamiltonianVectorField_add
      (hH.comp (contDiff_prodMk_right (s + r))).contDiffAt) t u v

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

/-- **The derivative of a time-dependent function along a solution.** If `x` solves the
nonautonomous equation `x' = X_{H_t}(x)` at `t` and `F` is differentiable at `(t, x t)`, then
`d/dt F(t, x(t)) = ∂_t F(t, x(t)) + {F_t, H_t}(x(t))`. -/
theorem hasDerivAt_apply_of_hasDerivAt_hamiltonianVectorField (omega : SymplecticForm V)
    {F H : ℝ → V → ℝ} {x : ℝ → V} {t : ℝ} (hF : DifferentiableAt ℝ (uncurry F) (t, x t))
    (hx : HasDerivAt x (omega.hamiltonianVectorField (H t) (x t)) t) :
    HasDerivAt (fun s ↦ F s (x s))
      (timeFDeriv (uncurry F) t (x t) + omega.poissonBracket (F t) (H t) (x t)) t := by
  have hspatial : spatialFDeriv (uncurry F) (x t) t = fderiv ℝ (F t) (x t) :=
    (fderiv_timeSlice hF).symm
  rw [poissonBracket_eq_fderiv, ← hspatial]
  exact hasDerivAt_comp_prodMk (F := uncurry F) hF hx

/-- **The energy changes at the rate `∂_t H`.** Along a solution `x` of the nonautonomous
equation `x' = X_{H_t}(x)`, `d/dt H(t, x(t)) = ∂_t H(t, x(t))`. -/
theorem hasDerivAt_apply_of_hasDerivAt_hamiltonianVectorField_self (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {x : ℝ → V} {t : ℝ}
    (hH : DifferentiableAt ℝ (uncurry H) (t, x t))
    (hx : HasDerivAt x (omega.hamiltonianVectorField (H t) (x t)) t) :
    HasDerivAt (fun s ↦ H s (x s)) (timeFDeriv (uncurry H) t (x t)) t := by
  simpa using omega.hasDerivAt_apply_of_hasDerivAt_hamiltonianVectorField hH hx

/-- **Time reversal of Hamiltonian trajectories.** If `y` solves `y' = X_{-G}(y)` at `-t`, then
`t ↦ y(-t)` solves `x' = X_G(x)` at `t`: both the time and the Hamiltonian vector field change
sign. Taking `G = H_t` at each time, reversing time turns a solution for the reversed Hamiltonian
`-H_{-t}` into a solution for `H_t`. -/
theorem hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg (omega : SymplecticForm V)
    {G : V → ℝ} {y : ℝ → V} {t : ℝ}
    (hy : HasDerivAt y (omega.hamiltonianVectorField (-G) (y (-t))) (-t)) :
    HasDerivAt (fun s ↦ y (-s)) (omega.hamiltonianVectorField G (y (-t))) t := by
  have h := hy.scomp t (hasDerivAt_neg t)
  rw [hamiltonianVectorField_neg, neg_one_smul, neg_neg] at h
  exact h

/-- **Time reversal of Hamiltonian orbits.** Reversing time, `t ↦ x(-t)`, turns an orbit `x` of
the reversed Hamiltonian `-H_{-t}` into an orbit of `H_t`. -/
theorem hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse
    (omega : SymplecticForm V) {H : ℝ → V → ℝ} {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (omega.hamiltonianVectorField (fun y ↦ -H (-t) y) (x t)) t) (t : ℝ) :
    HasDerivAt (fun s ↦ x (-s)) (omega.hamiltonianVectorField (H t) (x (-t))) t :=
  omega.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg
    (by simpa only [neg_neg, Pi.neg_def] using hx (-t))

/-- **Conserved quantities of a time-dependent Hamiltonian.** For a time-dependent Hamiltonian
whose suspended vector field is Lipschitz, a differentiable time-dependent function `F` is constant
along its evolution, `F(t, Φ_{s,t} x) = F(s, x)`, exactly when `∂_t F + {F_t, H_t} = 0`. -/
theorem forall_apply_timeDependentHamiltonianFlow_eq_iff (omega : SymplecticForm V)
    {F H : ℝ → V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (hF : Differentiable ℝ (uncurry F)) :
    (∀ s t x, F t (omega.timeDependentHamiltonianFlow H hX s t x) = F s x) ↔
      ∀ t x, timeFDeriv (uncurry F) t x + omega.poissonBracket (F t) (H t) x = 0 := by
  have hderiv : ∀ s t x, HasDerivAt (fun u ↦ F u (omega.timeDependentHamiltonianFlow H hX s u x))
      (timeFDeriv (uncurry F) t (omega.timeDependentHamiltonianFlow H hX s t x) +
        omega.poissonBracket (F t) (H t) (omega.timeDependentHamiltonianFlow H hX s t x)) t :=
    fun s t x ↦ omega.hasDerivAt_apply_of_hasDerivAt_hamiltonianVectorField (hF _)
      (omega.hasDerivAt_timeDependentHamiltonianFlow H hX s t x)
  constructor
  · intro h t x
    -- The function `u ↦ F(u, Φ_{t,u} x)` is constant, so its derivative at `u = t` vanishes.
    have hconst : (fun u ↦ F u (omega.timeDependentHamiltonianFlow H hX t u x)) = fun _ ↦ F t x :=
      funext fun u ↦ h t u x
    have h0 := hderiv t t x
    rw [hconst, timeDependentHamiltonianFlow_self] at h0
    exact h0.unique (hasDerivAt_const t (F t x))
  · intro h s t x
    have hzero : ∀ u,
        HasDerivAt (fun u ↦ F u (omega.timeDependentHamiltonianFlow H hX s u x)) 0 u :=
      fun u ↦ (h u _) ▸ hderiv s u x
    rw [is_const_of_deriv_eq_zero (fun u ↦ (hzero u).differentiableAt)
      (fun u ↦ (hzero u).deriv) t s, timeDependentHamiltonianFlow_self]

section Nondegenerate

/-! ### Nondegenerate one-periodic orbits -/

/-- **Nondegenerate orbits are isolated.** A one-periodic orbit `x` of `H` such that `x(0)` is a
nondegenerate fixed point of the time-one map is isolated among the one-periodic orbits of `H`. -/
theorem exists_pos_forall_eq_of_isNondegenerateFixedPt (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    {x : ℝ → V} (hx : ∀ t, HasDerivAt x (omega.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (omega.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (omega.hamiltonianVectorField (H t) (y t)) t) →
      dist (y 0) (x 0) < ε → y = x := by
  have hiso := hnd.eventually_not_isFixedPt
  rw [timeDependentHamiltonianFlow_eq, ← zero_add (1 : ℝ)] at hiso
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_periodic_eq_of_eventually_not_isFixedPt _ hx hiso
  exact ⟨ε, hε, fun y hyper hy hyx ↦ h y hy hyper hyx⟩

/-- **Nondegenerate orbits of the reversed Hamiltonian are isolated.** A one-periodic orbit `x` of
the reversed Hamiltonian `-H_{-t}`, such that `x(0)` is a nondegenerate fixed point of the time-one
map of `H`, is isolated among the one-periodic orbits of `-H_{-t}`. -/
theorem exists_pos_forall_eq_of_isNondegenerateFixedPt_reverse (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    {x : ℝ → V} (hx : ∀ t, HasDerivAt x (omega.hamiltonianVectorField (fun y ↦ -H (-t) y) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (omega.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (omega.hamiltonianVectorField (fun z ↦ -H (-t) z) (y t)) t) →
      dist (y 0) (x 0) < ε → y = x := by
  obtain ⟨ε, hε, h⟩ := omega.exists_pos_forall_eq_of_isNondegenerateFixedPt hX
    (omega.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse hx)
    (by simpa only [neg_zero] using hnd)
  refine ⟨ε, hε, fun y hyper hy hyx ↦ funext fun t ↦ ?_⟩
  have hxy := congrFun (h _ hyper.comp_neg
    (omega.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse hy)
    (by simpa only [neg_zero] using hyx)) (-t)
  simpa only [neg_neg] using hxy

/-- **Finitely many nondegenerate orbits in a compact set.** If every one-periodic orbit of `H`
with values in a compact set `C` starts at a nondegenerate fixed point of the time-one map, then
there are only finitely many one-periodic orbits with values in `C`. -/
theorem finite_setOf_periodic_hasDerivAt_of_isNondegenerateFixedPt (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    {C : Set V} (hC : IsCompact C)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (omega.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ C) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (omega.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (omega.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ C}.Finite := by
  set O := {x : ℝ → V | Periodic x 1 ∧
    (∀ t, HasDerivAt x (omega.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ C}
  have hflow (t : ℝ) : Continuous fun p : V ↦ omega.timeDependentHamiltonianFlow H hX 0 t p :=
    (omega.continuous_timeDependentHamiltonianFlow H hX).comp
      (continuous_const.prodMk continuous_id : Continuous fun p : V ↦ (((0 : ℝ), t), p))
  -- An orbit is the flow through its initial point, so it is determined by that point.
  have hinj : Set.InjOn (fun x : ℝ → V ↦ x 0) O := fun x hx y hy hxy ↦ funext fun t ↦ by
    rw [omega.eq_timeDependentHamiltonianFlow H hX hx.2.1 0 t,
      omega.eq_timeDependentHamiltonianFlow H hX hy.2.1 0 t]
    exact congrArg _ hxy
  refine Set.Finite.of_finite_image ?_ hinj
  refine IsCompact.finite_of_isNondegenerateFixedPt (I := 𝓘(ℝ, V))
    (f := omega.timeDependentHamiltonianFlow H hX 0 1)
    (hC.of_isClosed_subset (isClosed_of_closure_subset fun p hp ↦ ?_) ?_) ?_
  · -- A limit of initial points of orbits in `C` starts an orbit in `C`: the orbits converge
    -- pointwise to the flow line through the limit.
    obtain ⟨q, hqO, hq⟩ := mem_closure_iff_seq_limit.1 hp
    choose x hx hxq using hqO
    have hlim (t : ℝ) : Filter.Tendsto (fun n ↦ x n t) Filter.atTop
        (nhds (omega.timeDependentHamiltonianFlow H hX 0 t p)) := by
      have h := ((hflow t).tendsto p).comp hq
      refine h.congr fun n ↦ ?_
      simp only [Function.comp_apply, ← hxq n]
      exact (omega.eq_timeDependentHamiltonianFlow H hX (hx n).2.1 0 t).symm
    refine ⟨fun t ↦ omega.timeDependentHamiltonianFlow H hX 0 t p, ⟨fun t ↦ ?_, fun t ↦
      omega.hasDerivAt_timeDependentHamiltonianFlow H hX 0 t p, fun t ↦
      hC.isClosed.mem_of_tendsto (hlim t) (.of_forall fun n ↦ (hx n).2.2 t)⟩,
      omega.timeDependentHamiltonianFlow_self H hX 0 p⟩
    exact tendsto_nhds_unique ((hlim (t + 1)).congr fun n ↦ (hx n).1 t) (hlim t)
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2.2 0
  · rintro _ ⟨x, hx, rfl⟩
    exact hnd x hx.1 hx.2.1 hx.2.2

/-- **The return map at a nondegenerate orbit fixes no nonzero vector.** Let `x` be an orbit of
a jointly `C²` time-dependent Hamiltonian `H` whose suspended vector field is globally Lipschitz,
with `x(0)` a nondegenerate fixed point of the time-one map. Then the return map `Ψ(1)` of the
linearized Hamiltonian equation `ζ' = S_t ζ`, with `S_t = dX_{H_t}(x(t))`, fixes no nonzero
vector: it is the derivative of the time-one map at `x(0)`
(`fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft`). -/
theorem eq_zero_of_dysonSeriesLeft_apply_eq_self (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (omega.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (omega.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {v : V}
    (hv : dysonSeriesLeft (fun t ↦ fderiv ℝ (omega.hamiltonianVectorField (H t)) (x t)) 1 v = v) :
    v = 0 := by
  refine hnd.eq_zero_of_mfderiv_apply_eq ?_
  rw [(omega.differentiable_timeDependentHamiltonianFlow hX hH 0 1 (x 0)).hasFDerivAt
      |>.hasMFDerivAt.mfderiv,
    omega.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft hX hH hx 0 1]
  simp only [zero_add, sub_zero]
  exact hv

/-- **The return map at a nondegenerate orbit of the reversed Hamiltonian fixes no nonzero
vector.** Let `x` be a
one-periodic orbit of the reversed Hamiltonian `-H_{-t}` of a one-periodic, jointly `C²`
Hamiltonian `H` whose suspended vector field is globally Lipschitz, such that `x(0)` is a
nondegenerate fixed point of the time-one map of `H`. Then the return map of the linearized
equation of `-H_{-t}` along `x` fixes no nonzero vector. Its linearization is
`S'_t = -S_{-t}`, where `S_t` is that of `H` along the orbit `t ↦ x(-t)`, so `t ↦ ζ(-t)` turns a
periodic solution of `ζ' = S'_t ζ` into one of `ζ' = S_t ζ`. -/
theorem eq_zero_of_dysonSeriesLeft_reverse_apply_eq_self (omega : SymplecticForm V)
    {H : ℝ → V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (omega.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V} (hxp : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (omega.hamiltonianVectorField (fun y ↦ -H (-t) y) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (omega.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {v : V} (hv : dysonSeriesLeft
      (fun t ↦ fderiv ℝ (omega.hamiltonianVectorField (fun y ↦ -H (-t) y)) (x t)) 1 v = v) :
    v = 0 := by
  have hy := omega.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse hx
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (omega.hamiltonianVectorField (H t)) (x (-t))
  set S' : ℝ → V →L[ℝ] V :=
    fun t ↦ fderiv ℝ (omega.hamiltonianVectorField (fun y ↦ -H (-t) y)) (x t)
  have hSc : Continuous S := omega.continuous_fderiv_hamiltonianVectorField_comp hH
    (continuous_iff_continuousAt.2 fun t ↦ (hy t).continuousAt)
  -- The linearization of the reversed Hamiltonian is `S'_t = -S_{-t}`.
  have hS' (t : ℝ) : S' t = -S (-t) := by
    have hX' : omega.hamiltonianVectorField (fun y ↦ -H (-t) y) =
        fun y ↦ -omega.hamiltonianVectorField (H (-t)) y :=
      funext fun y ↦ by simpa only [Pi.neg_def] using omega.hamiltonianVectorField_neg (H (-t)) y
    simp only [S', S, hX', fderiv_fun_neg, neg_neg]
  have hS'c : Continuous S' := by
    rw [show S' = fun t ↦ -S (-t) from funext hS']
    exact (hSc.comp continuous_neg).neg
  have hS'p : Periodic S' 1 := fun t ↦ by
    simp only [S', hxp t, neg_add, ← sub_eq_add_neg, hHp.sub_eq]
  -- The periodic solution `t ↦ Ψ'(t) v` of `ζ' = S'_t ζ`, run backwards, is a periodic solution
  -- of `ζ' = S_t ζ` starting at `v`.
  set ζ : ℝ → V := fun t ↦ dysonSeriesLeft S' (-t) v
  have hζ (t : ℝ) : HasDerivAt ζ (S t (ζ t)) t := by
    have h := (hasDerivAt_dysonSeriesLeft_apply hS'c v (-t)).scomp t (hasDerivAt_neg t)
    rw [hS', neg_neg, neg_one_smul, neg_apply, neg_neg] at h
    exact h
  have hζp : Periodic ζ 1 := ((periodic_dysonSeriesLeft_apply_iff hS'c hS'p v).2 hv).comp_neg
  have hζ0 : ζ 0 = v := by simp [ζ, dysonSeriesLeft_zero]
  refine omega.eq_zero_of_dysonSeriesLeft_apply_eq_self hX hH hy
    (by simpa only [neg_zero] using hnd) ?_
  rw [← hζ0, ← eq_dysonSeriesLeft_apply hSc hζ, ← zero_add (1 : ℝ), hζp 0]

end Nondegenerate

end TauCeti.SymplecticForm

end
