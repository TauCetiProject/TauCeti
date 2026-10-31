/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Pair

/-!
# Radial reduction of central-force motion

Let `V` be a finite-dimensional real inner product space, with phase space `V × V` and standard
symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ`, and let `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` be a central-force
Hamiltonian (`TauCeti.centralForceHamiltonian`). Away from the collision set `q = 0`, write
`r = ‖q‖` for the distance to the origin, `p_r = ⟪q, p⟫ / ‖q‖` for the radial momentum
(`TauCeti.radialMomentum`), and `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` for the squared length of the angular
momentum bivector `q ∧ p`. In the plane `ℓ²` is the square of the angular momentum
`L = q₁p₂ - q₂p₁` (`TauCeti.sq_angularMomentum`).

The kinetic energy splits as `‖p‖² = p_r² + ℓ² / r²`, so

`H(q, p) = p_r² / (2m) + U_ℓ(r)`, with the *effective potential* `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`

(`TauCeti.effectivePotential`). The squared angular momentum `ℓ²` Poisson-commutes with `H` in
every dimension. Fixing its value, the radial motion is the one-dimensional Hamiltonian system on
the half-line `r > 0` with phase space `ℝ × ℝ` and *reduced Hamiltonian*

`H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`,

which is the one-dimensional central-force Hamiltonian of the effective potential,
`centralForceHamiltonian m (effectivePotential m ℓ U)` on `ℝ × ℝ`. Its Hamilton equations are
`r' = p_r / m`, `p_r' = ℓ² / (m r³) - U'(r)`. The *radial projection* `(q, p) ↦ (r, p_r)`
(`TauCeti.radialProjection`) carries the Hamiltonian vector field of `H` to that of `H_ℓ`, where
`ℓ²` is the value at the point. Hence it maps every integral curve of `H` avoiding the collision
set to an integral curve of the reduced Hamiltonian `H_ℓ` for the conserved value of `ℓ²`.

Two consequences describe the qualitative radial motion:

* **Turning points.** For `m > 0` the energy dominates the effective potential,
  `U_ℓ(r) ≤ H`, with equality exactly where the radial momentum vanishes. So a motion of energy
  `E` stays in the region `U_ℓ(r) ≤ E`, and its radial turning points lie on `U_ℓ(r) = E`.
* **Circular orbits.** The equilibria of the reduced system are the points `(r₀, 0)` with `r₀` a
  critical point of `U_ℓ`. Correspondingly, the uniform circular motion of radius `r₀ > 0` and
  angular velocity `ω` (`TauCeti.circularMotion`) solves Hamilton's equations exactly when the
  central force supplies the centripetal force, `U'(r₀) = m r₀ ω²`, that is exactly when `r₀` is
  a critical point of the effective potential for the angular momentum `ℓ = m r₀² ω` of this
  motion.

## Main definitions

* `TauCeti.radialMomentum`: the radial momentum `p_r = ⟪q, p⟫ / ‖q‖`.
* `TauCeti.radialProjection`: the radial projection `(q, p) ↦ (‖q‖, p_r)`.
* `TauCeti.effectivePotential m ℓ U`: the effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`.
* `TauCeti.circularMotion m r₀ ω u w`: the uniform circular motion of radius `r₀` and angular
  velocity `ω` in the plane of orthonormal vectors `u` and `w`, with momentum `m q'`.

## Main results

* `TauCeti.centralForceHamiltonian_radialProjection`: `H(q, p) = H_ℓ(r, p_r)`.
* `TauCeti.stdSymplecticForm_poissonBracket_sq_sub_inner_sq_centralForceHamiltonian`:
  conservation of `ℓ²`, `{ℓ², H} = 0`.
* `TauCeti.sq_sub_inner_sq_eq_of_hasDerivAt`: `ℓ²` is constant along integral curves of `H`.
* `TauCeti.stdSymplecticForm_hamiltonianVectorField_effectivePotential`: the reduced Hamilton
  equations `r' = p_r / m`, `p_r' = ℓ² / (m r³) - U'(r)`.
* `TauCeti.fderiv_radialProjection_hamiltonianVectorField_centralForceHamiltonian`: the radial
  projection carries `X_H` to `X_{H_ℓ}`.
* `TauCeti.hasDerivAt_radialProjection_comp`: integral curves of `H` project to integral curves
  of `H_ℓ`.
* `TauCeti.effectivePotential_le_centralForceHamiltonian`,
  `TauCeti.centralForceHamiltonian_eq_effectivePotential_iff`: the effective potential bounds the
  energy, with equality exactly at the radial turning points.
* `TauCeti.stdSymplecticForm_hamiltonianVectorField_effectivePotential_eq_zero_iff`: the
  equilibria of the reduced system are the critical points of the effective potential.
* `TauCeti.forall_hasDerivAt_circularMotion_iff`: circular motions solve Hamilton's equations
  exactly at the critical points of the effective potential.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Sections 3.2–3.6.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The radial momentum and the effective potential -/

/-- The radial momentum `p_r = ⟪q, p⟫ / ‖q‖`, the component of the momentum `p` along the unit
vector in the direction of the position `q`. It is `0` on the collision set `q = 0`. -/
noncomputable def radialMomentum (x : V × V) : ℝ :=
  ⟪x.1, x.2⟫_ℝ / ‖x.1‖

theorem radialMomentum_def (x : V × V) : radialMomentum x = ⟪x.1, x.2⟫_ℝ / ‖x.1‖ :=
  (rfl)

@[simp]
theorem radialMomentum_apply (q p : V) : radialMomentum (q, p) = ⟪q, p⟫_ℝ / ‖q‖ :=
  (rfl)

/-- The radial momentum vanishes exactly when the momentum is orthogonal to the position. -/
theorem radialMomentum_eq_zero_iff {x : V × V} : radialMomentum x = 0 ↔ ⟪x.1, x.2⟫_ℝ = 0 := by
  rcases eq_or_ne x.1 0 with hq | hq
  · simp [radialMomentum, hq]
  · simp [radialMomentum, norm_ne_zero_iff.2 hq]

/-- The radial projection `(q, p) ↦ (‖q‖, p_r)` of the phase space `V × V` onto the phase space
`ℝ × ℝ` of the radial motion. -/
noncomputable def radialProjection (x : V × V) : ℝ × ℝ :=
  (‖x.1‖, radialMomentum x)

@[simp]
theorem radialProjection_fst (x : V × V) : (radialProjection x).1 = ‖x.1‖ :=
  (rfl)

@[simp]
theorem radialProjection_snd (x : V × V) : (radialProjection x).2 = radialMomentum x :=
  (rfl)

@[simp]
theorem radialProjection_apply (q p : V) :
    radialProjection (q, p) = (‖q‖, ⟪q, p⟫_ℝ / ‖q‖) :=
  (rfl)

/-- The effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)` of a particle of mass `m` with angular
momentum `ℓ` in the central potential `U`: the potential `U` plus the centrifugal term. -/
noncomputable def effectivePotential (m ℓ : ℝ) (U : ℝ → ℝ) (r : ℝ) : ℝ :=
  ℓ ^ 2 / (2 * m * r ^ 2) + U r

@[simp]
theorem effectivePotential_apply (m ℓ : ℝ) (U : ℝ → ℝ) (r : ℝ) :
    effectivePotential m ℓ U r = ℓ ^ 2 / (2 * m * r ^ 2) + U r :=
  (rfl)

/-- Away from `r = 0`, the derivative of the effective potential is
`U_ℓ'(r) = U'(r) - ℓ² / (m r³)`. -/
theorem hasDerivAt_effectivePotential {m ℓ : ℝ} {U : ℝ → ℝ} {U' r : ℝ} (hU : HasDerivAt U U' r)
    (hr : r ≠ 0) :
    HasDerivAt (effectivePotential m ℓ U) (U' - ℓ ^ 2 / (m * r ^ 3)) r := by
  have h := (((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)).const_mul (ℓ ^ 2 / (2 * m))).add hU
  refine (h.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  · rcases eq_or_ne m 0 with hm | hm
    · simp [hm]
    · field_simp
      ring

/-- Away from `r = 0`, `r` is a critical point of the effective potential exactly when
`U'(r) = ℓ² / (m r³)`. -/
theorem hasDerivAt_effectivePotential_zero_iff {m ℓ : ℝ} {U : ℝ → ℝ} {U' r : ℝ}
    (hU : HasDerivAt U U' r) (hr : r ≠ 0) :
    HasDerivAt (effectivePotential m ℓ U) 0 r ↔ U' = ℓ ^ 2 / (m * r ^ 3) := by
  have h := hasDerivAt_effectivePotential (m := m) (ℓ := ℓ) hU hr
  exact ⟨fun h' ↦ sub_eq_zero.1 (h.unique h'), fun h' ↦ by rwa [h', sub_self] at h⟩

/-- On the closed half-line `r ≥ 0`, the reduced Hamiltonian, the one-dimensional central-force
Hamiltonian of the effective potential, is `H_ℓ(r, p_r) = p_r² / (2m) + ℓ² / (2 m r²) + U(r)`. -/
theorem centralForceHamiltonian_effectivePotential_apply {m ℓ : ℝ} {U : ℝ → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (p_r : ℝ) :
    centralForceHamiltonian m (effectivePotential m ℓ U) (r, p_r) =
      p_r ^ 2 / (2 * m) + ℓ ^ 2 / (2 * m * r ^ 2) + U r := by
  simp [Real.norm_of_nonneg hr, add_assoc]

/-! ### The energy in radial form -/

/-- **The kinetic energy in radial form.** Away from the collision set,
`‖p‖² = p_r² + ℓ² / ‖q‖²`, where `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` is the squared angular momentum. -/
theorem norm_snd_sq_eq_radialMomentum_sq_add {x : V × V} (hq : x.1 ≠ 0) :
    ‖x.2‖ ^ 2 =
      radialMomentum x ^ 2 + (‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) / ‖x.1‖ ^ 2 := by
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  rw [radialMomentum]
  field_simp
  ring

/-- **The energy in radial form.** Away from the collision set, a central-force Hamiltonian is the
reduced Hamiltonian `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)` of the radial projection, for `ℓ²` the
squared angular momentum `‖q‖² ‖p‖² - ⟪q, p⟫²`. -/
theorem centralForceHamiltonian_radialProjection {m ℓ : ℝ} {U : ℝ → ℝ} {x : V × V}
    (hq : x.1 ≠ 0) (hℓ : ℓ ^ 2 = ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) :
    centralForceHamiltonian m (effectivePotential m ℓ U) (radialProjection x) =
      centralForceHamiltonian m U x := by
  have hH : centralForceHamiltonian m U x = ‖x.2‖ ^ 2 / (2 * m) + U ‖x.1‖ :=
    centralForceHamiltonian_apply m U x.1 x.2
  rw [radialProjection, centralForceHamiltonian_effectivePotential_apply (norm_nonneg _), hH,
    norm_snd_sq_eq_radialMomentum_sq_add hq, hℓ]
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  rcases eq_or_ne m 0 with hm | hm
  · simp [hm]
  · field_simp

/-- **The effective potential bounds the energy.** For a nonnegative mass, away from the collision
set, `U_ℓ(‖q‖) ≤ H(q, p)` for the squared angular momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`. So a motion
of energy `E` and angular momentum `ℓ` stays in the region `U_ℓ(r) ≤ E`. -/
theorem effectivePotential_le_centralForceHamiltonian {m ℓ : ℝ} (hm : 0 ≤ m) {U : ℝ → ℝ}
    {x : V × V} (hq : x.1 ≠ 0) (hℓ : ℓ ^ 2 = ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) :
    effectivePotential m ℓ U ‖x.1‖ ≤ centralForceHamiltonian m U x := by
  rw [← centralForceHamiltonian_radialProjection hq hℓ, radialProjection,
    centralForceHamiltonian_effectivePotential_apply (norm_nonneg _), effectivePotential, add_assoc]
  have : 0 ≤ radialMomentum x ^ 2 / (2 * m) := div_nonneg (sq_nonneg _) (by linarith)
  linarith

/-- **Turning points.** For a nonzero mass, away from the collision set, the energy equals the
effective potential `U_ℓ(‖q‖)`, for the squared angular momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`,
exactly when the radial momentum vanishes. -/
theorem centralForceHamiltonian_eq_effectivePotential_iff {m ℓ : ℝ} (hm : m ≠ 0) {U : ℝ → ℝ}
    {x : V × V} (hq : x.1 ≠ 0) (hℓ : ℓ ^ 2 = ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) :
    centralForceHamiltonian m U x = effectivePotential m ℓ U ‖x.1‖ ↔ radialMomentum x = 0 := by
  rw [← centralForceHamiltonian_radialProjection hq hℓ, radialProjection,
    centralForceHamiltonian_effectivePotential_apply (norm_nonneg _), effectivePotential, add_assoc]
  simp [hm]

/-! ### Derivatives of the squared angular momentum and of the radial projection -/

/-- The partial gradients of the squared angular momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` are
`∇_q ℓ² = 2 ‖p‖² q - 2 ⟪q, p⟫ p` and `∇_p ℓ² = 2 ‖q‖² p - 2 ⟪q, p⟫ q`. -/
theorem hasFDerivAt_sq_sub_inner_sq (x : V × V) :
    HasFDerivAt (fun y : V × V ↦ ‖y.1‖ ^ 2 * ‖y.2‖ ^ 2 - ⟪y.1, y.2⟫_ℝ ^ 2)
      ((innerSL ℝ ((2 * ‖x.2‖ ^ 2) • x.1 - (2 * ⟪x.1, x.2⟫_ℝ) • x.2)).coprod
        (innerSL ℝ ((2 * ‖x.1‖ ^ 2) • x.2 - (2 * ⟪x.1, x.2⟫_ℝ) • x.1))) x := by
  have h12 := (hasFDerivAt_fst (p := x)).inner ℝ (hasFDerivAt_snd (p := x))
  refine ((((hasFDerivAt_fst (p := x)).norm_sq).mul (hasFDerivAt_snd (p := x)).norm_sq).sub
    (h12.mul h12)).congr_of_eventuallyEq (.of_forall fun y ↦ by simp [sq]) |>.congr_fderiv
    (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [real_inner_comm]
  ring

/-- Away from the collision set, the derivative of the radial projection `(q, p) ↦ (‖q‖, p_r)`
sends `(δq, δp)` to `(⟪q, δq⟫ / ‖q‖, ⟪p / ‖q‖ - (⟪q, p⟫ / ‖q‖³) q, δq⟫ + ⟪q / ‖q‖, δp⟫)`. -/
theorem hasFDerivAt_radialProjection {x : V × V} (hq : x.1 ≠ 0) :
    HasFDerivAt radialProjection
      (((innerSL ℝ (‖x.1‖⁻¹ • x.1)).coprod 0).prod
        ((innerSL ℝ (‖x.1‖⁻¹ • x.2 - (⟪x.1, x.2⟫_ℝ / ‖x.1‖ ^ 3) • x.1)).coprod
          (innerSL ℝ (‖x.1‖⁻¹ • x.1)))) x := by
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hn := (hasFDerivAt_norm_of_ne hq).comp x (hasFDerivAt_fst (p := x))
  have hi := (hasDerivAt_inv hr).comp_hasFDerivAt x hn
  have h12 := (hasFDerivAt_fst (p := x)).inner ℝ (hasFDerivAt_snd (p := x))
  refine (hn.prodMk (h12.mul hi)).congr_of_eventuallyEq
    (.of_forall fun y ↦ by simp [radialProjection, radialMomentum, div_eq_mul_inv]) |>.congr_fderiv
    (ContinuousLinearMap.ext fun v ↦ Prod.ext ?_ ?_)
  · simp
  · simp [real_inner_comm]
    field_simp
    ring

/-! ### Uniform circular motion -/

/-- The uniform circular motion `q(t) = r₀ (cos(ω t) u + sin(ω t) w)` of radius `r₀` and angular
velocity `ω` in the plane of `u` and `w`, together with the momentum `p(t) = m q'(t)` of a particle
of mass `m`. -/
noncomputable def circularMotion (m r₀ ω : ℝ) (u w : V) (t : ℝ) : V × V :=
  (r₀ • (Real.cos (ω * t) • u + Real.sin (ω * t) • w),
    (m * r₀ * ω) • (-Real.sin (ω * t) • u + Real.cos (ω * t) • w))

@[simp]
theorem circularMotion_apply (m r₀ ω : ℝ) (u w : V) (t : ℝ) :
    circularMotion m r₀ ω u w t =
      (r₀ • (Real.cos (ω * t) • u + Real.sin (ω * t) • w),
        (m * r₀ * ω) • (-Real.sin (ω * t) • u + Real.cos (ω * t) • w)) :=
  (rfl)

/-- The derivative of the circular motion: `q' = r₀ ω (-sin(ω t) u + cos(ω t) w)` and
`p' = -m r₀ ω² (cos(ω t) u + sin(ω t) w)`. -/
theorem hasDerivAt_circularMotion (m r₀ ω : ℝ) (u w : V) (t : ℝ) :
    HasDerivAt (circularMotion m r₀ ω u w)
      ((r₀ * ω) • (-Real.sin (ω * t) • u + Real.cos (ω * t) • w),
        -((m * r₀ * ω ^ 2) • (Real.cos (ω * t) • u + Real.sin (ω * t) • w))) t := by
  have hl : HasDerivAt (fun t : ℝ ↦ ω * t) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hc := (Real.hasDerivAt_cos (ω * t)).comp t hl
  have hs := (Real.hasDerivAt_sin (ω * t)).comp t hl
  refine (HasDerivAt.prodMk (((hc.smul_const u).add (hs.smul_const w)).const_smul r₀)
    (((hs.neg.smul_const u).add (hc.smul_const w)).const_smul (m * r₀ * ω))).congr_deriv ?_
  ext
  · simp only [smul_add, smul_smul, neg_smul]
    module
  · simp only [smul_add, smul_smul, neg_smul]
    module

/-- The circular motion stays at distance `r₀ ≥ 0` from the origin with zero radial momentum, so
its radial projection is the point `(r₀, 0)`. -/
theorem radialProjection_circularMotion (m : ℝ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (ω : ℝ) {u w : V}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0) (t : ℝ) :
    radialProjection (circularMotion m r₀ ω u w t) = (r₀, 0) := by
  have h := norm_smul_add_smul_eq_one hu hw huw (Real.cos_sq_add_sin_sq (ω * t))
  simp only [circularMotion, radialProjection, radialMomentum, norm_smul, h, Real.norm_eq_abs,
    abs_of_nonneg hr₀, mul_one, Prod.mk.injEq, true_and]
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    real_inner_self_eq_norm_sq, hu, hw, huw, real_inner_comm u w, RCLike.conj_to_real]
  ring

/-- The squared angular momentum of the circular motion is `(m r₀² ω)²`. -/
theorem sq_sub_inner_sq_circularMotion (m r₀ ω : ℝ) {u w : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (huw : ⟪u, w⟫_ℝ = 0) (t : ℝ) :
    ‖(circularMotion m r₀ ω u w t).1‖ ^ 2 * ‖(circularMotion m r₀ ω u w t).2‖ ^ 2 -
        ⟪(circularMotion m r₀ ω u w t).1, (circularMotion m r₀ ω u w t).2⟫_ℝ ^ 2 =
      (m * r₀ ^ 2 * ω) ^ 2 := by
  have h₁ := norm_smul_add_smul_eq_one hu hw huw (Real.cos_sq_add_sin_sq (ω * t))
  have h₂ := norm_smul_add_smul_eq_one hu hw huw (a := -Real.sin (ω * t)) (b := Real.cos (ω * t))
    (by rw [neg_sq, Real.sin_sq_add_cos_sq])
  simp only [circularMotion, norm_smul, h₁, h₂, Real.norm_eq_abs, mul_one, mul_pow, sq_abs,
    inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
    hu, hw, huw, real_inner_comm u w, RCLike.conj_to_real]
  ring

variable [FiniteDimensional ℝ V]

/-! ### Conservation of the squared angular momentum -/

/-- **Conservation of the squared angular momentum.** Away from the collision set, the squared
length `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` of the angular momentum bivector Poisson-commutes with every
central-force Hamiltonian, in every dimension. -/
theorem stdSymplecticForm_poissonBracket_sq_sub_inner_sq_centralForceHamiltonian {m : ℝ}
    {U : ℝ → ℝ} {U' : ℝ} {x : V × V} (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) :
    (stdSymplecticForm (V := V)).poissonBracket
      (fun y : V × V ↦ ‖y.1‖ ^ 2 * ‖y.2‖ ^ 2 - ⟪y.1, y.2⟫_ℝ ^ 2)
      (centralForceHamiltonian m U) x = 0 := by
  rw [stdSymplecticForm_poissonBracket (hasFDerivAt_sq_sub_inner_sq x)
    (hasFDerivAt_centralForceHamiltonian hU hq)]
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm x.1 x.2]
  field_simp
  ring

/-- **Conservation of the squared angular momentum along the motion.** Let `γ` be an integral
curve of the Hamiltonian vector field of a central-force Hamiltonian on a preconnected open set `s`
of times, avoiding the collision set, with `U` differentiable along it. Then the squared angular
momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` of `γ` takes the same value at all times `t₀, t ∈ s`. -/
theorem sq_sub_inner_sq_eq_of_hasDerivAt {m : ℝ} {U : ℝ → ℝ} {γ : ℝ → V × V} {s : Set ℝ}
    (hs : IsOpen s) (hs' : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    ‖(γ t).1‖ ^ 2 * ‖(γ t).2‖ ^ 2 - ⟪(γ t).1, (γ t).2⟫_ℝ ^ 2 =
      ‖(γ t₀).1‖ ^ 2 * ‖(γ t₀).2‖ ^ 2 - ⟪(γ t₀).1, (γ t₀).2⟫_ℝ ^ 2 := by
  -- The derivative of `ℓ²` along `γ` is the Poisson bracket `{ℓ², H} = 0`.
  have hderiv (t : ℝ) (ht : t ∈ s) : HasDerivAt
      ((fun y : V × V ↦ ‖y.1‖ ^ 2 * ‖y.2‖ ^ 2 - ⟪y.1, y.2⟫_ℝ ^ 2) ∘ γ) 0 t := by
    have h := (hasFDerivAt_sq_sub_inner_sq (γ t)).comp_hasDerivAt t (hγ t ht)
    rwa [← (hasFDerivAt_sq_sub_inner_sq (γ t)).fderiv,
      ← SymplecticForm.poissonBracket_eq_fderiv,
      stdSymplecticForm_poissonBracket_sq_sub_inner_sq_centralForceHamiltonian
        (hU t ht).hasDerivAt (hq t ht)] at h
  exact hs.is_const_of_deriv_eq_zero hs'
    (fun t ht ↦ (hderiv t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hderiv t ht).deriv) ht ht₀

/-! ### The reduced Hamiltonian system -/

/-- **Hamilton's equations for the radial motion.** On the half-line `r > 0`, the Hamiltonian
vector field of the reduced Hamiltonian `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)` is
`(p_r / m, ℓ² / (m r³) - U'(r))`. -/
theorem stdSymplecticForm_hamiltonianVectorField_effectivePotential {m ℓ : ℝ} {U : ℝ → ℝ}
    {U' r : ℝ} (hU : HasDerivAt U U' r) (hr : 0 < r) (p_r : ℝ) :
    (stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U)) (r, p_r) =
      (p_r / m, ℓ ^ 2 / (m * r ^ 3) - U') := by
  have hU' : HasDerivAt (effectivePotential m ℓ U) (U' - ℓ ^ 2 / (m * r ^ 3)) ‖(r, p_r).1‖ := by
    rw [Real.norm_of_nonneg hr.le]
    exact hasDerivAt_effectivePotential hU hr.ne'
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian hU' (by exact hr.ne'),
    Real.norm_of_nonneg hr.le]
  ext
  · simp [div_eq_inv_mul]
  · simp [hr.ne']

/-- **Equilibria of the radial motion.** For a nonzero mass, the reduced Hamiltonian vector field
vanishes at `(r, p_r)`, `r > 0`, exactly when `p_r = 0` and `r` is a critical point of the
effective potential. These are the circular orbits of radius `r`. -/
theorem stdSymplecticForm_hamiltonianVectorField_effectivePotential_eq_zero_iff {m ℓ : ℝ}
    (hm : m ≠ 0) {U : ℝ → ℝ} {U' r : ℝ} (hU : HasDerivAt U U' r) (hr : 0 < r) (p_r : ℝ) :
    (stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U)) (r, p_r) = 0 ↔
      p_r = 0 ∧ HasDerivAt (effectivePotential m ℓ U) 0 r := by
  rw [stdSymplecticForm_hamiltonianVectorField_effectivePotential hU hr,
    hasDerivAt_effectivePotential_zero_iff hU hr.ne']
  simp [hm, sub_eq_zero, eq_comm (a := U')]

/-! ### The radial projection of the Hamiltonian flow -/

/-- **Radial reduction of the Hamiltonian vector field.** Away from the collision set, the radial
projection `(q, p) ↦ (‖q‖, p_r)` carries the Hamiltonian vector field of a central-force
Hamiltonian `H` at `x` to the Hamiltonian vector field of the reduced Hamiltonian
`H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`, where `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` is the squared angular
momentum at `x`. -/
theorem fderiv_radialProjection_hamiltonianVectorField_centralForceHamiltonian {m ℓ : ℝ}
    {U : ℝ → ℝ} {U' : ℝ} {x : V × V} (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0)
    (hℓ : ℓ ^ 2 = ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) :
    fderiv ℝ radialProjection x
        ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) x) =
      (stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U)) (radialProjection x) := by
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  rw [(hasFDerivAt_radialProjection hq).fderiv,
    stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian hU hq, radialProjection,
    stdSymplecticForm_hamiltonianVectorField_effectivePotential hU (norm_pos_iff.2 hq), hℓ]
  ext
  · simp [real_inner_smul_right, radialMomentum]
    field_simp
  · simp [real_inner_smul_right]
    field_simp
    ring

/-- **Radial reduction of central-force motion.** Let `γ` be an integral curve of the Hamiltonian
vector field of a central-force Hamiltonian on a preconnected open set `s` of times, avoiding the
collision set, with `U` differentiable along it. If `ℓ²` is the squared angular momentum
`‖q‖² ‖p‖² - ⟪q, p⟫²` of `γ` at one time `t₀ ∈ s`, then `t ↦ (‖q(t)‖, p_r(t))` is an integral curve
on `s` of the Hamiltonian vector field of the reduced Hamiltonian
`H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`. -/
theorem hasDerivAt_radialProjection_comp {m ℓ : ℝ} {U : ℝ → ℝ} {γ : ℝ → V × V} {s : Set ℝ}
    (hs : IsOpen s) (hs' : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖) {t₀ : ℝ}
    (ht₀ : t₀ ∈ s)
    (hℓ : ℓ ^ 2 = ‖(γ t₀).1‖ ^ 2 * ‖(γ t₀).2‖ ^ 2 - ⟪(γ t₀).1, (γ t₀).2⟫_ℝ ^ 2) :
    ∀ t ∈ s, HasDerivAt (radialProjection ∘ γ)
      ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U)) (radialProjection (γ t))) t := by
  intro t ht
  have h := ((hasFDerivAt_radialProjection (hq t ht)).comp_hasDerivAt t (hγ t ht))
  rwa [← (hasFDerivAt_radialProjection (hq t ht)).fderiv,
    fderiv_radialProjection_hamiltonianVectorField_centralForceHamiltonian (hU t ht).hasDerivAt
      (hq t ht) (hℓ.trans (sq_sub_inner_sq_eq_of_hasDerivAt hs hs' hγ hq hU ht₀ ht).symm)] at h

/-! ### Circular orbits -/

/-- **Circular orbits and the centripetal force.** For a nonzero mass and a radius `r₀ > 0`, the
uniform circular motion of radius `r₀` and angular velocity `ω` in the plane of orthonormal
vectors `u` and `w` is an integral curve of the central-force Hamiltonian vector field exactly
when the central force supplies the centripetal force, `U'(r₀) = m r₀ ω²`. -/
theorem forall_hasDerivAt_circularMotion_iff_eq {m : ℝ} (hm : m ≠ 0) {U : ℝ → ℝ} {U' r₀ : ℝ}
    (hU : HasDerivAt U U' r₀) (hr₀ : 0 < r₀) (ω : ℝ) {u w : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (huw : ⟪u, w⟫_ℝ = 0) :
    (∀ t, HasDerivAt (circularMotion m r₀ ω u w)
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U)
        (circularMotion m r₀ ω u w t)) t) ↔ U' = m * r₀ * ω ^ 2 := by
  have hX (t : ℝ) : (stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m U) (circularMotion m r₀ ω u w t) =
        ((r₀ * ω) • (-Real.sin (ω * t) • u + Real.cos (ω * t) • w),
          -(U' • (Real.cos (ω * t) • u + Real.sin (ω * t) • w))) := by
    have hn : ‖(circularMotion m r₀ ω u w t).1‖ = r₀ := by
      rw [← radialProjection_fst, radialProjection_circularMotion m hr₀.le ω hu hw huw t]
    rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian (hn ▸ hU)
      (fun h ↦ hr₀.ne' (by rw [← hn, h, norm_zero])), hn]
    ext
    · simp only [circularMotion, smul_smul]
      field_simp
    · simp only [circularMotion, smul_smul]
      field_simp
  simp_rw [hX]
  constructor
  · intro h
    have h0 := congrArg Prod.snd ((hasDerivAt_circularMotion m r₀ ω u w 0).unique (h 0))
    simp only [mul_zero, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero,
      neg_inj] at h0
    have hu0 : u ≠ 0 := fun h ↦ by simp [h] at hu
    exact (smul_left_injective ℝ hu0 h0).symm
  · intro h t
    convert hasDerivAt_circularMotion m r₀ ω u w t using 3
    rw [h]

/-- **Circular orbits are the critical points of the effective potential.** For a nonzero mass
and a radius `r₀ > 0`, the uniform circular motion of radius `r₀` and angular velocity `ω` in the
plane of orthonormal vectors `u` and `w` is an integral curve of the central-force Hamiltonian
vector field exactly when `r₀` is a critical point of the effective potential `U_ℓ` for the
angular momentum `ℓ = m r₀² ω` of this motion. -/
theorem forall_hasDerivAt_circularMotion_iff {m : ℝ} (hm : m ≠ 0) {U : ℝ → ℝ} {U' r₀ : ℝ}
    (hU : HasDerivAt U U' r₀) (hr₀ : 0 < r₀) (ω : ℝ) {u w : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (huw : ⟪u, w⟫_ℝ = 0) :
    (∀ t, HasDerivAt (circularMotion m r₀ ω u w)
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U)
        (circularMotion m r₀ ω u w t)) t) ↔
      HasDerivAt (effectivePotential m (m * r₀ ^ 2 * ω) U) 0 r₀ := by
  have he : (m * r₀ ^ 2 * ω) ^ 2 / (m * r₀ ^ 3) = m * r₀ * ω ^ 2 := by
    field_simp
  rw [forall_hasDerivAt_circularMotion_iff_eq hm hU hr₀ ω hu hw huw,
    hasDerivAt_effectivePotential_zero_iff hU hr₀.ne', he]

end TauCeti
