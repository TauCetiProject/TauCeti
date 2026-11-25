/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Frequency
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Period
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Rotation
import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Basic

/-!
# The Kepler actions are action variables

Identify the configuration plane with `ℂ`, as for the rotations of the plane, so that a particle
of mass `m > 0` in the Kepler potential `-κ / r` has phase space `ℂ × ℂ`, energy
`H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` and angular momentum `L = q₁p₂ - q₂p₁`. On the bound phase space
`{q ≠ 0, H < 0, L ≠ 0}` (`TauCeti.keplerBoundPhaseSpace`) the **radial action** is the function

`I_r = κ √(m / (-2H)) - |L|`

(`TauCeti.keplerRadialAction`). At each state it is the radial action quadrature
`TauCeti.radialAction` between the turning radii of the state
(`TauCeti.keplerRadialAction_eq_radialAction`), and the energy is
`H = -m κ² / (2 (I_r + |L|)²)` (`TauCeti.keplerActionHamiltonian_keplerRadialAction`).

This file shows that `I_r` and the signed angular action `I_θ = L` are action variables: their
Hamiltonian flows are periodic with period `2π`.

* The Hamiltonian flow of `L` is the rotation of the plane, so every solution of Hamilton's
  equations for `L` is `2π`-periodic (`TauCeti.periodic_of_forall_hasDerivAt_angularMomentum`).
* On the bound phase space the Hamiltonian vector field of `I_r` is
  `X_{I_r} = c X_H - sign(L) X_L` with `c = κ √(m / (-2H)) / (-2H)`
  (`TauCeti.stdSymplecticForm_hamiltonianVectorField_keplerRadialAction`). Hence `I_r`
  Poisson-commutes with `H` and with `L`, and along a solution `γ` of Hamilton's equations for
  `I_r` the energy `E` and the angular momentum `ℓ` are constant. Undoing the rotation by the angle
  `sign(ℓ) t / c` turns `γ` into the Kepler motion `η(u) = exp (sign(ℓ) u i / c) • γ(u / c)`, which
  is periodic with period `T = 2π √(m / κ) a^(3/2)`, `a = κ / (-2E)`, by Kepler's third law
  (`TauCeti.periodic_of_forall_hasDerivAt_kepler`). Since `c = √(m / κ) a^(3/2)`, the period is
  `T = 2π c`, and `γ(t) = exp (-sign(ℓ) t i) • η(c t)` returns after the time `2π`: the rotation
  by the angle `-sign(ℓ) 2π` is the identity. So every solution of Hamilton's equations for `I_r`
  in the bound phase space is `2π`-periodic
  (`TauCeti.periodic_of_forall_hasDerivAt_keplerRadialAction`), and through every state of the
  bound phase space there is one defined for all time
  (`TauCeti.exists_hasDerivAt_keplerRadialAction`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 50.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 10.8.
-/

public section

noncomputable section

open Complex Real

namespace TauCeti

variable {m κ : ℝ}

/-- The **radial action** `I_r = κ √(m / (-2H)) - |L|` of the planar Kepler problem with mass `m`
and potential `-κ / r`, as a function on the phase space `ℂ × ℂ`, where `H` is the energy and `L`
the angular momentum. On the bound phase space it is the radial action quadrature between the
turning radii (`TauCeti.keplerRadialAction_eq_radialAction`). -/
def keplerRadialAction (m κ : ℝ) (x : ℂ × ℂ) : ℝ :=
  κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) - |angularMomentum 1 I x|

/-- The formula for the radial action of the Kepler problem on phase space. -/
theorem keplerRadialAction_def (m κ : ℝ) (x : ℂ × ℂ) :
    keplerRadialAction m κ x =
      κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) - |angularMomentum 1 I x| :=
  (rfl)

/-- The bound phase space of the planar Kepler problem on `ℂ × ℂ`: the states off the collision
set with negative energy and nonzero angular momentum. -/
theorem mem_keplerBoundPhaseSpace_orthonormalBasisOneI {x : ℂ × ℂ} :
    x ∈ keplerBoundPhaseSpace orthonormalBasisOneI m κ ↔
      x.1 ≠ 0 ∧ centralForceHamiltonian m (fun r ↦ -κ / r) x < 0 ∧ angularMomentum 1 I x ≠ 0 := by
  simp [coe_orthonormalBasisOneI]

/-- A state of negative Kepler energy forces an attractive potential, `κ > 0`. -/
private theorem pos_of_centralForceHamiltonian_kepler_neg (hm : 0 < m) {x : ℂ × ℂ}
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x < 0) : 0 < κ := by
  obtain ⟨q, p⟩ := x
  by_contra hκ
  have h₁ : 0 ≤ -κ / ‖q‖ := div_nonneg (by linarith) (norm_nonneg _)
  have h₂ : 0 ≤ ‖p‖ ^ 2 / (2 * m) := by positivity
  rw [centralForceHamiltonian_apply] at hE
  linarith

/-- **The Kepler energy in the action variables.** At a state of negative energy, for `m > 0`,
the energy is `H = -m κ² / (2 (I_r + |L|)²)`. -/
theorem keplerActionHamiltonian_keplerRadialAction (hm : 0 < m) {x : ℂ × ℂ}
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x < 0) :
    keplerActionHamiltonian m κ (keplerRadialAction m κ x, angularMomentum 1 I x) =
      centralForceHamiltonian m (fun r ↦ -κ / r) x := by
  have hκ := (pos_of_centralForceHamiltonian_kepler_neg hm hE).ne'
  set E := centralForceHamiltonian m (fun r ↦ -κ / r) x
  have hs : √(m / (-2 * E)) ^ 2 = m / (-2 * E) := sq_sqrt (div_pos hm (by linarith)).le
  rw [keplerActionHamiltonian_def, keplerRadialAction_def, sub_add_cancel, mul_pow, hs]
  field_simp

/-- **The radial action is the radial quadrature.** At a state of the bound phase space with
energy `E` and angular momentum `ℓ`, for `m > 0`, the radial action is the radial action
quadrature `TauCeti.radialAction` between the turning radii of the Kepler problem. -/
theorem keplerRadialAction_eq_radialAction (hm : 0 < m) {x : ℂ × ℂ}
    (hx : x ∈ keplerBoundPhaseSpace orthonormalBasisOneI m κ) :
    keplerRadialAction m κ x =
      radialAction m (fun r ↦ -κ / r) (angularMomentum 1 I x)
        (centralForceHamiltonian m (fun r ↦ -κ / r) x)
        (keplerPeriapsisRadius m κ (angularMomentum 1 I x)
          (centralForceHamiltonian m (fun r ↦ -κ / r) x))
        (keplerApoapsisRadius m κ (angularMomentum 1 I x)
          (centralForceHamiltonian m (fun r ↦ -κ / r) x)) := by
  obtain ⟨hq, hE, hL⟩ := mem_keplerBoundPhaseSpace_orthonormalBasisOneI.1 hx
  have hmin := centralForceHamiltonian_kepler_min_le orthonormalBasisOneI (κ := κ) hm hq
    (by simpa [coe_orthonormalBasisOneI] using hL)
  simp only [coe_orthonormalBasisOneI, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hmin
  rw [kepler_radialAction_turningRadii hm (pos_of_centralForceHamiltonian_kepler_neg hm hE) hL
    hmin hE, keplerRadialAction_def]

/-- The derivative of `E ↦ √(m / (-2E))` at `E ≠ 0` is `√(m / (-2E)) / (-2E)`. -/
private theorem hasDerivAt_sqrt_div_neg_two_mul (m : ℝ) {E : ℝ} (hE : E ≠ 0) :
    HasDerivAt (fun E ↦ √(m / (-2 * E))) (√(m / (-2 * E)) / (-2 * E)) E := by
  have h2E : -2 * E ≠ 0 := mul_ne_zero (by norm_num) hE
  -- Write `m = s (-2E)`, so that `√(m / (-2E)) = √s`.
  obtain ⟨s, rfl⟩ : ∃ s, m = s * (-2 * E) := ⟨m / (-2 * E), by field_simp⟩
  rw [mul_div_cancel_right₀ _ h2E]
  by_cases hs : s = 0
  · simpa [hs] using hasDerivAt_const E (0 : ℝ)
  have hd : HasDerivAt (fun E' ↦ s * (-2 * E) / (-2 * E'))
      ((0 * (-2 * E) - s * (-2 * E) * (-2 * 1)) / (-2 * E) ^ 2) E :=
    (hasDerivAt_const E _).div ((hasDerivAt_id' E).const_mul (-2)) h2E
  refine (hd.sqrt (by rwa [mul_div_cancel_right₀ _ h2E])).congr_deriv ?_
  -- Both sides are `-(s / √s) / (2E)`, and `s / √s = √s`.
  rw [mul_div_cancel_right₀ _ h2E]
  conv_rhs => rw [← div_sqrt (x := s)]
  field_simp
  ring

/-- Kepler's third law in the radial action: for `m, κ > 0` and energy `E < 0`, the period
`2π √(m / κ) a^(3/2)` of the Kepler motions with semi-major axis `a = κ / (-2E)` is `2π` times
the coefficient `κ √(m / (-2E)) / (-2E)` of `X_H` in the Hamiltonian vector field of the radial
action. -/
private theorem kepler_period_eq_mul_two_pi (hm : 0 < m) (hκ : 0 < κ) {E : ℝ} (hE : E < 0) :
    2 * π * √(m / κ) * (κ / (-2 * E)) ^ (3 / 2 : ℝ) =
      κ * √(m / (-2 * E)) / (-2 * E) * (2 * π) := by
  have ha : 0 < κ / (-2 * E) := div_pos hκ (by linarith)
  have h32 : (κ / (-2 * E)) ^ (3 / 2 : ℝ) = κ / (-2 * E) * √(κ / (-2 * E)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add ha, rpow_one, ← sqrt_eq_rpow]
  have hs : √(m / (-2 * E)) = √(m / κ) * √(κ / (-2 * E)) := by
    rw [← sqrt_mul (div_nonneg hm.le hκ.le)]
    congr 1
    field_simp
  rw [h32, hs]
  ring

/-- **The differential of the radial action.** Off the collision set, at a state of nonzero energy
`E` and nonzero angular momentum `ℓ`, the differential of the radial action is
`dI_r = c dH - sign(ℓ) dL`, with `c = κ √(m / (-2E)) / (-2E)`. -/
theorem hasFDerivAt_keplerRadialAction {x : ℂ × ℂ} (hq : x.1 ≠ 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x ≠ 0) (hL : angularMomentum 1 I x ≠ 0) :
    HasFDerivAt (keplerRadialAction m κ)
      ((κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) /
          (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) •
          fderiv ℝ (centralForceHamiltonian m (fun r ↦ -κ / r)) x -
        (SignType.sign (angularMomentum 1 I x) : ℝ) • fderiv ℝ (angularMomentum 1 I) x) x := by
  have hH := (hasFDerivAt_centralForceHamiltonian (m := m)
    (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 hq)) hq).differentiableAt.hasFDerivAt
  have hL' := (hasFDerivAt_angularMomentum (1 : ℂ) I x).differentiableAt.hasFDerivAt
  have h := (((hasDerivAt_sqrt_div_neg_two_mul m hE).comp_hasFDerivAt x hH).const_mul κ).sub
    ((hasDerivAt_abs hL).comp_hasFDerivAt x hL')
  refine h.congr_fderiv ?_
  rw [smul_smul, mul_div_assoc]

/-- **The Hamiltonian vector field of the radial action.** Off the collision set, at a state of
nonzero energy `E` and nonzero angular momentum `ℓ`, the Hamiltonian vector field of the radial
action is `X_{I_r} = c X_H - sign(ℓ) X_L`, with `c = κ √(m / (-2E)) / (-2E)`. -/
theorem stdSymplecticForm_hamiltonianVectorField_keplerRadialAction {x : ℂ × ℂ} (hq : x.1 ≠ 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x ≠ 0) (hL : angularMomentum 1 I x ≠ 0) :
    (stdSymplecticForm (V := ℂ)).hamiltonianVectorField (keplerRadialAction m κ) x =
      (κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) /
          (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) •
          (stdSymplecticForm (V := ℂ)).hamiltonianVectorField
            (centralForceHamiltonian m (fun r ↦ -κ / r)) x -
        (SignType.sign (angularMomentum 1 I x) : ℝ) •
          (stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I) x := by
  rw [eq_comm, SymplecticForm.eq_hamiltonianVectorField_iff,
    (hasFDerivAt_keplerRadialAction hq hE hL).fderiv]
  intro v
  simp [map_sub, map_smul]

/-- **The radial action is a first integral of the energy.** Off the collision set, at a state of
nonzero energy and nonzero angular momentum, the energy Poisson-commutes with the radial action. -/
theorem stdSymplecticForm_poissonBracket_centralForceHamiltonian_keplerRadialAction {x : ℂ × ℂ}
    (hq : x.1 ≠ 0) (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x ≠ 0)
    (hL : angularMomentum 1 I x ≠ 0) :
    (stdSymplecticForm (V := ℂ)).poissonBracket (centralForceHamiltonian m (fun r ↦ -κ / r))
      (keplerRadialAction m κ) x = 0 := by
  rw [SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_hamiltonianVectorField_keplerRadialAction hq hE hL]
  simp [SymplecticForm.fderiv_apply_hamiltonianVectorField,
    ← SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum]

/-- **The radial and angular actions Poisson-commute.** Off the collision set, at a state of
nonzero energy and nonzero angular momentum, the angular momentum Poisson-commutes with the radial
action. -/
theorem stdSymplecticForm_poissonBracket_angularMomentum_keplerRadialAction {x : ℂ × ℂ}
    (hq : x.1 ≠ 0) (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x ≠ 0)
    (hL : angularMomentum 1 I x ≠ 0) :
    (stdSymplecticForm (V := ℂ)).poissonBracket (angularMomentum 1 I) (keplerRadialAction m κ)
      x = 0 := by
  rw [SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_hamiltonianVectorField_keplerRadialAction hq hE hL]
  simp [SymplecticForm.fderiv_apply_hamiltonianVectorField,
    ← SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_poissonBracket_angularMomentum_centralForceHamiltonian]

/-- Along a solution `γ` of Hamilton's equations for the radial action in the bound phase space,
the energy `E` and the angular momentum `ℓ` are constant, so `γ` moves with velocity
`c X_H - sign(ℓ) X_L` for the constant `c = κ √(m / (-2E)) / (-2E)`. -/
private theorem hasDerivAt_of_forall_hasDerivAt_keplerRadialAction {γ : ℝ → ℂ × ℂ}
    (hγ : ∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := ℂ)).hamiltonianVectorField (keplerRadialAction m κ) (γ t)) t)
    (hB : ∀ t, γ t ∈ keplerBoundPhaseSpace orthonormalBasisOneI m κ) (t : ℝ) :
    HasDerivAt γ
      ((κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) (γ 0))) /
          (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) (γ 0))) •
          (stdSymplecticForm (V := ℂ)).hamiltonianVectorField
            (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t) +
        (-(SignType.sign (angularMomentum 1 I (γ 0)) : ℝ)) •
          (stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I) (γ t)) t := by
  have hB' := fun t ↦ mem_keplerBoundPhaseSpace_orthonormalBasisOneI.1 (hB t)
  -- The energy and the angular momentum Poisson-commute with `I_r`, so they are constant.
  have hHc := stdSymplecticForm.apply_eq_of_hasDerivWithinAt_of_poissonBracket_eq_zero
    isPreconnected_univ (fun t _ ↦ (hγ t).hasDerivWithinAt)
    (fun t _ ↦ (hasFDerivAt_centralForceHamiltonian (m := m) (hasDerivAt_kepler_potential κ
      (norm_ne_zero_iff.2 (hB' t).1)) (hB' t).1).differentiableAt)
    (fun t _ ↦ stdSymplecticForm_poissonBracket_centralForceHamiltonian_keplerRadialAction
      (hB' t).1 (hB' t).2.1.ne (hB' t).2.2) (Set.mem_univ 0) (Set.mem_univ t)
  have hLc := stdSymplecticForm.apply_eq_of_hasDerivWithinAt_of_poissonBracket_eq_zero
    isPreconnected_univ (fun t _ ↦ (hγ t).hasDerivWithinAt)
    (fun t _ ↦ (hasFDerivAt_angularMomentum (1 : ℂ) I (γ t)).differentiableAt)
    (fun t _ ↦ stdSymplecticForm_poissonBracket_angularMomentum_keplerRadialAction
      (hB' t).1 (hB' t).2.1.ne (hB' t).2.2) (Set.mem_univ 0) (Set.mem_univ t)
  have h := hγ t
  rwa [stdSymplecticForm_hamiltonianVectorField_keplerRadialAction (hB' t).1 (hB' t).2.1.ne
    (hB' t).2.2, hHc, hLc, sub_eq_add_neg, ← neg_smul] at h

/-- **The radial action is an action variable.** For `m > 0`, every curve in the bound phase space
of the planar Kepler problem which solves Hamilton's equations for the radial action at all times
is periodic with period `2π`. -/
theorem periodic_of_forall_hasDerivAt_keplerRadialAction (hm : 0 < m) {γ : ℝ → ℂ × ℂ}
    (hγ : ∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := ℂ)).hamiltonianVectorField (keplerRadialAction m κ) (γ t)) t)
    (hB : ∀ t, γ t ∈ keplerBoundPhaseSpace orthonormalBasisOneI m κ) :
    Function.Periodic γ (2 * π) := by
  have hB' := fun t ↦ mem_keplerBoundPhaseSpace_orthonormalBasisOneI.1 (hB t)
  have hκ := pos_of_centralForceHamiltonian_kepler_neg hm (hB' 0).2.1
  have hγ' := hasDerivAt_of_forall_hasDerivAt_keplerRadialAction hγ hB
  set E := centralForceHamiltonian m (fun r ↦ -κ / r) (γ 0)
  set c := κ * √(m / (-2 * E)) / (-2 * E)
  set σ : ℝ := ↑(SignType.sign (angularMomentum 1 I (γ 0)))
  have hE : E < 0 := (hB' 0).2.1
  have hc : 0 < c := div_pos (mul_pos hκ (sqrt_pos.2 (div_pos hm (by linarith)))) (by linarith)
  -- Undoing the rotation and rescaling time by `c` gives a Kepler motion `η`.
  set η : ℝ → ℂ × ℂ := fun u ↦ Circle.exp (σ / c * u) • γ (1 / c * u)
  have hη (u : ℝ) : HasDerivAt η ((stdSymplecticForm (V := ℂ)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (η u)) u := by
    have h := hasDerivAt_circleExp_mul_smul_comp_mul
      (fun z y ↦ centralForceHamiltonian_smul m (fun r ↦ -κ / r) z y) (a := σ / c) (b := 1 / c)
      (t := u) (hγ' _)
    rwa [one_div_mul_cancel hc.ne', one_smul, show σ / c + 1 / c * -σ = 0 by ring, zero_smul,
      add_zero] at h
  have hηq (u : ℝ) : (η u).1 ≠ 0 := by
    simpa [η, Circle.smul_def] using (hB' (1 / c * u)).1
  have hη0 : centralForceHamiltonian m (fun r ↦ -κ / r) (η 0) = -κ / (2 * (κ / (-2 * E))) := by
    have hE2 : -κ / (2 * (κ / (-2 * E))) = E := by field_simp
    simp only [η, mul_zero, Circle.exp_zero, one_smul]
    rw [hE2]
  have hper : Function.Periodic η (c * (2 * π)) := by
    have h := periodic_of_forall_hasDerivAt_kepler hm hκ (div_pos hκ (by linarith)) hη hηq hη0
    rwa [kepler_period_eq_mul_two_pi hm hκ hE] at h
  have hγη (t : ℝ) : γ t = Circle.exp (-σ * t) • η (c * t) := by
    simp only [η, smul_smul, ← Circle.exp_add]
    rw [show σ / c * (c * t) = σ * t by field_simp, show 1 / c * (c * t) = t by field_simp,
      neg_mul, neg_add_cancel, Circle.exp_zero, one_smul]
  -- The rotation by the angle `-2π σ` is the identity, since `σ = ±1`.
  have hσ : Circle.exp (-σ * (2 * π)) = 1 := by
    rcases (hB' 0).2.2.lt_or_gt with h | h
    · simp [σ, sign_neg h]
    · simp [σ, sign_pos h]
  intro t
  rw [hγη, hγη t, mul_add, mul_add, hper, Circle.exp_add, hσ, mul_one]

/-- **The flow of the radial action.** For `m > 0`, through every state of the bound phase space of
the planar Kepler problem passes a curve in the bound phase space solving Hamilton's equations for
the radial action at all times. By `TauCeti.periodic_of_forall_hasDerivAt_keplerRadialAction` it
is periodic with period `2π`. -/
theorem exists_hasDerivAt_keplerRadialAction (hm : 0 < m) {x : ℂ × ℂ}
    (hx : x ∈ keplerBoundPhaseSpace orthonormalBasisOneI m κ) :
    ∃ γ : ℝ → ℂ × ℂ, γ 0 = x ∧ ∀ t, γ t ∈ keplerBoundPhaseSpace orthonormalBasisOneI m κ ∧
      HasDerivAt γ
        ((stdSymplecticForm (V := ℂ)).hamiltonianVectorField (keplerRadialAction m κ) (γ t)) t := by
  obtain ⟨hq, hE, hL⟩ := mem_keplerBoundPhaseSpace_orthonormalBasisOneI.1 hx
  have hκ := pos_of_centralForceHamiltonian_kepler_neg hm hE
  -- The Kepler motion through `x` is defined for all time.
  have hx := pow_ne_zero 2 (show angularMomentum (orthonormalBasisOneI 0) (orthonormalBasisOneI 1)
    x ≠ 0 by simpa [coe_orthonormalBasisOneI] using hL)
  rw [sq_angularMomentum] at hx
  obtain ⟨η, hη0, hη, hηq⟩ := exists_hasDerivAt_kepler_of_sq_sub_inner_sq_ne_zero hm hκ hq hx
  -- Along it the energy and the angular momentum are constant.
  have hHc (t : ℝ) : centralForceHamiltonian m (fun r ↦ -κ / r) (η t) =
      centralForceHamiltonian m (fun r ↦ -κ / r) x :=
    hη0 ▸ centralForceHamiltonian_eq_of_hasDerivAt isPreconnected_univ (fun t _ ↦ hη t)
      (fun t _ ↦ hηq t) (fun t _ ↦ (hasDerivAt_kepler_potential κ
        (norm_ne_zero_iff.2 (hηq t))).differentiableAt) (Set.mem_univ 0) (Set.mem_univ t)
  have hLc (t : ℝ) : angularMomentum 1 I (η t) = angularMomentum 1 I x :=
    hη0 ▸ stdSymplecticForm.apply_eq_of_hasDerivWithinAt_of_poissonBracket_eq_zero
      isPreconnected_univ (fun t _ ↦ (hη t).hasDerivWithinAt)
      (fun t _ ↦ (hasFDerivAt_angularMomentum (1 : ℂ) I (η t)).differentiableAt)
      (fun t _ ↦ stdSymplecticForm_poissonBracket_angularMomentum_centralForceHamiltonian 1 I)
      (Set.mem_univ 0) (Set.mem_univ t)
  -- Rotate it by the angle `-σ t` and rescale time by `c`.
  set c := κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) /
    (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)
  set σ : ℝ := ↑(SignType.sign (angularMomentum 1 I x))
  refine ⟨fun t ↦ Circle.exp (-σ * t) • η (c * t), by simp [hη0], fun t ↦ ?_⟩
  have hHt : centralForceHamiltonian m (fun r ↦ -κ / r) (Circle.exp (-σ * t) • η (c * t)) =
      centralForceHamiltonian m (fun r ↦ -κ / r) x :=
    (centralForceHamiltonian_smul m _ _ _).trans (hHc _)
  have hLt : angularMomentum 1 I (Circle.exp (-σ * t) • η (c * t)) = angularMomentum 1 I x :=
    (angularMomentum_circle_smul _ _).trans (hLc _)
  have hqt : (Circle.exp (-σ * t) • η (c * t)).1 ≠ 0 := by
    simpa [Circle.smul_def] using hηq (c * t)
  refine ⟨mem_keplerBoundPhaseSpace_orthonormalBasisOneI.2 ⟨hqt, hHt ▸ hE, hLt ▸ hL⟩, ?_⟩
  have h := hasDerivAt_circleExp_mul_smul_comp_mul
    (fun z y ↦ centralForceHamiltonian_smul m (fun r ↦ -κ / r) z y) (α := 1) (β := 0)
    (a := -σ) (b := c) (t := t) (by simpa using hη (c * t))
  rw [stdSymplecticForm_hamiltonianVectorField_keplerRadialAction hqt (hHt ▸ hE.ne)
    (hLt ▸ hL), hHt, hLt]
  rwa [mul_one, mul_zero, add_zero, neg_smul, ← sub_eq_add_neg] at h

end TauCeti
