/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic

/-!
# The velocity of a diffeotopy

The **velocity** `∂ₜ φ_t x` of a diffeotopy `φ_t` at a point `x` and a time `t ∈ [0, 1]`
(`TauCeti.Diffeotopy.velocity`) is the derivative of its motion `(x, t) ↦ φ_t x` on the cylinder
`M × [0, 1]` applied to the unit time vector `∂ₜ = (0, 1)`. Here `1 : TangentSpace (𝓡∂ 1) t` is
Mathlib's unit tangent vector of the interval, so at the two end times this is the one-sided
derivative in the direction of increasing time. Composed with the inverse time slices it gives the
**Eulerian velocity field** `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` (`TauCeti.Diffeotopy.eulerianField`), the
time-dependent vector field generating the diffeotopy, with `X_t (φ_t x) = ∂ₜ φ_t x`
(`TauCeti.Diffeotopy.eulerianField_apply_apply`). The flux form of a diffeotopy is the time
integral of the contraction of a two-form with this velocity, and a diffeotopy is Hamiltonian when
its Eulerian velocity field is a Hamiltonian vector field at every time.

This is the diffeotopy counterpart of `TauCeti.eulerianField` for families of bijections indexed
by `ℝ`: a diffeotopy is indexed by `[0, 1]`, and its velocity is the derivative of the motion on
the cylinder `M × [0, 1]`, including at the end times.

The constant diffeotopy has zero velocity (`TauCeti.Diffeotopy.velocity_refl`,
`TauCeti.Diffeotopy.eulerianField_refl`).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (Φ : Diffeotopy J n M)

/-- The **velocity** `∂ₜ φ_t x` of a diffeotopy at the point `x` and time `t`: the derivative of
the motion `(x, t) ↦ φ_t x` on the unit time vector `∂ₜ = (0, 1)` of the cylinder `M × [0, 1]`. -/
def velocity (t : unitInterval) (x : M) : TangentSpace J (Φ (t, x)) :=
  mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, t) ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))

/-- The velocity is the derivative of the motion on the unit time vector. This restates the
definition, whose body is not exposed. -/
theorem velocity_def (t : unitInterval) (x : M) :
    Φ.velocity t x =
      mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, t) ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) :=
  (rfl)

/-- The **Eulerian velocity field** `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` of a diffeotopy at time `t`: the
vector field whose value at `y` is the velocity of the motion through `φ_t⁻¹ y`. -/
def eulerianField (t : unitInterval) (y : M) : TangentSpace J y :=
  Φ.velocity t ((Φ.timeSlice t).symm y)

/-- The Eulerian velocity field at `y` is the velocity at `φ_t⁻¹ y`. This restates the
definition, whose body is not exposed. -/
theorem eulerianField_def (t : unitInterval) (y : M) :
    Φ.eulerianField t y = Φ.velocity t ((Φ.timeSlice t).symm y) :=
  (rfl)

/-- At the point `φ_t x`, the Eulerian velocity field is the velocity of the motion through `x`. -/
@[simp]
theorem eulerianField_apply_apply (t : unitInterval) (x : M) :
    Φ.eulerianField t (Φ (t, x)) = Φ.velocity t x := by
  rw [eulerianField_def]
  -- Replace `φ_t⁻¹ (φ_t x)` by `x`; the tangent spaces at both points are the model space.
  generalize hz : (Φ.timeSlice t).symm (Φ (t, x)) = z
  rw [← timeSlice_apply, Diffeomorph.symm_apply_apply] at hz
  subst hz
  rfl

/-- The constant diffeotopy has zero velocity. -/
@[simp]
theorem velocity_refl (t : unitInterval) (x : M) : (refl J n M).velocity t x = 0 := by
  have hcyl : (refl J n M).cylinderMap = Prod.fst := funext fun p ↦ by simp [cylinderMap_apply]
  rw [velocity_def, hcyl, mfderiv_fst]
  rfl

/-- The constant diffeotopy has zero Eulerian velocity field. -/
@[simp]
theorem eulerianField_refl (t : unitInterval) : (refl J n M).eulerianField t = 0 :=
  funext fun y ↦ (refl J n M).eulerianField_def t y ▸ velocity_refl t _

end Diffeotopy

end TauCeti
