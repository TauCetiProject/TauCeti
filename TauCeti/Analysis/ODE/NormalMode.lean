/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Normal-mode solutions of `u'' = A u`

Let `A` be a bounded linear operator on a real normed space `E`, for instance the linearized
force operator of a system of springs divided by the masses. A *normal mode* of the equation
`u'' = A u` is an eigenvector `x` of `A` for an eigenvalue `-ω²`, `ω ≥ 0`; along such a vector the
equation decouples into the scalar oscillator `f'' = -ω² f`. The motion with initial position
`x` and initial velocity `y`, both in this eigenspace, is

`normalModeMotion ω x y t = cos (ω t) • x + (t sinc (ω t)) • y`,

which is `cos (ω t) • x + (sin (ω t) / ω) • y` when `ω ≠ 0` and the uniform motion `x + t • y`
when `ω = 0`, so that zero modes need no separate treatment.

The solutions of `u'' = A u` are determined by their initial position and velocity
(`TauCeti.eq_of_hasDerivAt_of_hasDerivAt_apply`), since the equation is the first-order linear
system `(u, u')' = (u', A u)` on `E × E`. Consequently, if the initial data are sums of
eigenvectors, the solution is the corresponding superposition of normal-mode motions
(`TauCeti.eq_sum_normalModeMotion`), with angular frequencies `ω`.

## Main definitions

* `TauCeti.normalModeMotion ω x y`: the motion `t ↦ cos (ω t) • x + (t sinc (ω t)) • y`.

## Main results

* `TauCeti.hasDerivAt_normalModeMotion`: the velocity of `normalModeMotion ω x y` is
  `normalModeMotion ω y (-(ω ^ 2) • x)`.
* `TauCeti.hasDerivAt_normalModeMotion_of_apply_eq`: for eigenvectors `x`, `y` of `A` with
  eigenvalue `-ω²`, the acceleration of `normalModeMotion ω x y` is `A` applied to it.
* `TauCeti.eq_of_hasDerivAt_of_hasDerivAt_apply`: uniqueness for `u'' = A u`.
* `TauCeti.eq_sum_normalModeMotion`: the solution with initial data a sum of eigenvectors is the
  superposition of the normal-mode motions.

## References

* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 6.2.
-/

public section

namespace TauCeti

open Real

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The **normal-mode motion** of angular frequency `ω` with initial position `x` and initial
velocity `y`: `t ↦ cos (ω t) • x + (t sinc (ω t)) • y`. For `ω ≠ 0` this is
`cos (ω t) • x + (sin (ω t) / ω) • y` (`TauCeti.normalModeMotion_of_ne_zero`), and for `ω = 0` it
is the uniform motion `x + t • y` (`TauCeti.normalModeMotion_zero_left`). When `x` and `y` are
eigenvectors of `A` for `-ω²` it solves `u'' = A u`
(`TauCeti.hasDerivAt_normalModeMotion_of_apply_eq`). -/
noncomputable def normalModeMotion (ω : ℝ) (x y : E) (t : ℝ) : E :=
  cos (ω * t) • x + (t * sinc (ω * t)) • y

theorem normalModeMotion_def (ω : ℝ) (x y : E) (t : ℝ) :
    normalModeMotion ω x y t = cos (ω * t) • x + (t * sinc (ω * t)) • y :=
  (rfl)

/-- At angular frequency `0` the normal-mode motion is the uniform motion `x + t • y`. -/
@[simp]
theorem normalModeMotion_zero_left (x y : E) (t : ℝ) : normalModeMotion 0 x y t = x + t • y := by
  simp [normalModeMotion_def]

theorem normalModeMotion_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) (x y : E) (t : ℝ) :
    normalModeMotion ω x y t = cos (ω * t) • x + (sin (ω * t) / ω) • y := by
  rw [normalModeMotion_def, mul_sinc_mul_of_ne_zero hω]

/-- The normal-mode motion starts at its initial position `x`. -/
@[simp]
theorem normalModeMotion_apply_zero (ω : ℝ) (x y : E) : normalModeMotion ω x y 0 = x := by
  simp [normalModeMotion_def]

/-- The normal-mode motion does not depend on the sign of the angular frequency. -/
@[simp]
theorem normalModeMotion_neg_left (ω : ℝ) (x y : E) (t : ℝ) :
    normalModeMotion (-ω) x y t = normalModeMotion ω x y t := by
  simp [normalModeMotion_def]

theorem normalModeMotion_add (ω : ℝ) (x y x' y' : E) (t : ℝ) :
    normalModeMotion ω (x + x') (y + y') t = normalModeMotion ω x y t + normalModeMotion ω x' y' t
    := by
  simp only [normalModeMotion_def, smul_add]
  abel

theorem normalModeMotion_smul (ω c : ℝ) (x y : E) (t : ℝ) :
    normalModeMotion ω (c • x) (c • y) t = c • normalModeMotion ω x y t := by
  simp only [normalModeMotion_def, smul_add, smul_comm c]

/-- A linear map commutes with the normal-mode motion. -/
theorem map_normalModeMotion {F G : Type*} [AddCommGroup F] [Module ℝ F] [FunLike G E F]
    [LinearMapClass G ℝ E F] (L : G) (ω : ℝ) (x y : E) (t : ℝ) :
    L (normalModeMotion ω x y t) = normalModeMotion ω (L x) (L y) t := by
  simp [normalModeMotion_def]

end Module

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The velocity of the normal-mode motion with initial data `(x, y)` is the normal-mode motion
with initial data `(y, -ω² x)`. -/
theorem hasDerivAt_normalModeMotion (ω : ℝ) (x y : E) (t : ℝ) :
    HasDerivAt (normalModeMotion ω x y) (normalModeMotion ω y (-(ω ^ 2) • x) t) t := by
  have hcos : HasDerivAt (fun s ↦ cos (ω * s)) (-(ω * sin (ω * t))) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul ω).cos
  have hfun : normalModeMotion ω x y = fun s ↦ cos (ω * s) • x + (s * sinc (ω * s)) • y :=
    funext (normalModeMotion_def ω x y)
  rw [hfun]
  convert (hcos.smul_const x).fun_add ((hasDerivAt_mul_sinc_mul ω t).smul_const y) using 1
  rw [normalModeMotion_def, ← mul_sinc (ω * t)]
  module

/-- If `x` and `y` are eigenvectors of `A` for the eigenvalue `-ω²`, the acceleration of the
normal-mode motion `normalModeMotion ω x y` is `A` applied to its position: it solves
`u'' = A u`, with velocity given by `TauCeti.hasDerivAt_normalModeMotion`. -/
theorem hasDerivAt_normalModeMotion_of_apply_eq {A : E →L[ℝ] E} {ω : ℝ} {x y : E}
    (hx : A x = -(ω ^ 2) • x) (hy : A y = -(ω ^ 2) • y) (t : ℝ) :
    HasDerivAt (normalModeMotion ω y (-(ω ^ 2) • x)) (A (normalModeMotion ω x y t)) t := by
  convert hasDerivAt_normalModeMotion ω y (-(ω ^ 2) • x) t using 1
  rw [map_normalModeMotion, hx, hy]

/-- **Uniqueness for `u'' = A u`.** Two solutions of `u'' = A u`, given with their velocities
`u'` and `w'`, that have the same position and velocity at one time agree at all times. -/
theorem eq_of_hasDerivAt_of_hasDerivAt_apply {A : E →L[ℝ] E} {u u' w w' : ℝ → E}
    (hu : ∀ t, HasDerivAt u (u' t) t) (hu' : ∀ t, HasDerivAt u' (A (u t)) t)
    (hw : ∀ t, HasDerivAt w (w' t) t) (hw' : ∀ t, HasDerivAt w' (A (w t)) t) {t₀ : ℝ}
    (h₀ : u t₀ = w t₀) (h₀' : u' t₀ = w' t₀) : u = w := by
  -- The equation is the first-order linear system `(u, u')' = (u', A u)` on `E × E`.
  let V : E × E →L[ℝ] E × E := (ContinuousLinearMap.snd ℝ E E).prod (A.comp (.fst ℝ E E))
  have h := ODE_solution_unique_univ (v := fun _ ↦ V) (s := fun _ ↦ Set.univ)
    (f := fun t ↦ (u t, u' t)) (g := fun t ↦ (w t, w' t)) (t₀ := t₀)
    (fun _ ↦ V.lipschitzWith.lipschitzOnWith) (fun t ↦ ⟨(hu t).prodMk (hu' t), trivial⟩)
    (fun t ↦ ⟨(hw t).prodMk (hw' t), trivial⟩) (Prod.ext h₀ h₀')
  exact funext fun t ↦ congrArg Prod.fst (congrFun h t)

/-- **Superposition of normal modes.** If the initial position and velocity of a solution of
`u'' = A u` are sums `∑ i, x i` and `∑ i, y i` of eigenvectors `x i`, `y i` of `A` for the
eigenvalues `-(ω i)²`, then the solution is the sum of the normal-mode motions of angular
frequencies `ω i`. -/
theorem eq_sum_normalModeMotion {ι : Type*} [Fintype ι] {A : E →L[ℝ] E} {ω : ι → ℝ}
    {x y : ι → E} (hx : ∀ i, A (x i) = -(ω i ^ 2) • x i) (hy : ∀ i, A (y i) = -(ω i ^ 2) • y i)
    {u u' : ℝ → E} (hu : ∀ t, HasDerivAt u (u' t) t) (hu' : ∀ t, HasDerivAt u' (A (u t)) t)
    (h₀ : u 0 = ∑ i, x i) (h₀' : u' 0 = ∑ i, y i) :
    u = fun t ↦ ∑ i, normalModeMotion (ω i) (x i) (y i) t := by
  refine eq_of_hasDerivAt_of_hasDerivAt_apply hu hu'
    (w' := fun t ↦ ∑ i, normalModeMotion (ω i) (y i) (-(ω i ^ 2) • x i) t)
    (fun t ↦ HasDerivAt.fun_sum fun i _ ↦ hasDerivAt_normalModeMotion _ _ _ t)
    (fun t ↦ ?_) (t₀ := 0) (by simpa using h₀) (by simpa using h₀')
  rw [map_sum]
  exact HasDerivAt.fun_sum fun i _ ↦ hasDerivAt_normalModeMotion_of_apply_eq (hx i) (hy i) t

end Normed

end TauCeti
