/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Period
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Frequency
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Euclidean.Circle
import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Rotation

/-!
# The Kepler actions generate `2π`-periodic flows

A particle of mass `m > 0` in a plane `V`, with orthonormal basis `b`, moving in the attractive
Kepler potential `-κ / r`, `κ > 0`, has the energy `H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` and the
angular momentum `L(q, p) = q₁p₂ - q₂p₁`. On the bound phase space `{q ≠ 0, H < 0, L ≠ 0}`
(`TauCeti.keplerBoundPhaseSpace`) its action variables are the signed angular action `I_θ = L` and
the radial action

`I_r = κ √(m / (-2H)) - |L|`

(`TauCeti.keplerRadialAction`). This is the radial quadrature `TauCeti.radialAction` between the
two turning radii of the level (`TauCeti.keplerRadialAction_eq_radialAction`), and in these
variables the energy is `H = -m κ² / (2 (I_r + |I_θ|)²)`
(`TauCeti.keplerActionHamiltonian_keplerRadialAction`). This file shows that both are action
variables in the sense that their Hamiltonian flows, for the standard symplectic form, are
`2π`-periodic.

* **The angular action.** For the orientation `o` of `b`, with quarter turn `J`, the Hamiltonian
  vector field of `L` is `(J q, J p)`
  (`TauCeti.stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation`). Its
  flow is the rotation `(q, p) ↦ (R_t q, R_t p)` of the plane by the angle `t`, so it is
  `2π`-periodic (`TauCeti.periodic_of_forall_hasDerivAt_angularMomentum`). These facts hold for
  every central force and are proved in
  `TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Rotation`.
* **The radial action.** Off the collision set, where `H ≠ 0` and `L ≠ 0`, the differential of
  `I_r` is `dI_r = Ω_r⁻¹ dH - sign(L) dL` (`TauCeti.hasFDerivAt_keplerRadialAction`), so its
  Hamiltonian vector field is

  `X_{I_r} = Ω_r⁻¹ X_H - sign(L) X_L`, with `Ω_r⁻¹ = κ √(m / (-2H)) / (-2H)`

  (`TauCeti.stdSymplecticForm_hamiltonianVectorField_keplerRadialAction`). Since `H` and `L`
  Poisson-commute, `I_r` Poisson-commutes with both
  (`TauCeti.stdSymplecticForm_poissonBracket_centralForceHamiltonian_keplerRadialAction`,
  `TauCeti.stdSymplecticForm_poissonBracket_angularMomentum_keplerRadialAction`), and both are
  constant along its solutions. If `γ` solves Hamilton's equations for
  `I_r` in the bound phase space, then rotating `γ(Ω_r τ)` back by the angle
  `sign(L) Ω_r τ` gives a solution of Hamilton's equations for `H`, a bound Kepler motion of the
  same energy `E`. By Kepler's third law (`TauCeti.periodic_of_forall_hasDerivAt_kepler`) it is
  periodic, with period `2π √(m / κ) a^(3/2) = 2π / Ω_r` for `a = κ / (-2E)`. Undoing the
  rescaling, `γ` returns after time `2π`, up to a rotation by the angle `±2π`, which is the
  identity. So every such `γ` is `2π`-periodic
  (`TauCeti.periodic_of_forall_hasDerivAt_keplerRadialAction`). Conversely, through every state of
  the bound phase space there is such a solution defined for all time
  (`TauCeti.exists_forall_hasDerivAt_keplerRadialAction`).

Together with the frequencies `∂H/∂I_r = Ω_r` and `∂H/∂I_θ = sign(I_θ) Ω_r` of
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Frequency`, these are the action
variables of the bound Kepler problem on each of its components `L > 0` and `L < 0`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 50.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 10.8.
-/

public section

namespace TauCeti

open Real Set Module
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V) {m κ : ℝ}

/-! ### The radial action -/

/-- The **radial action** `κ √(m / (-2H)) - |L|` of the planar Kepler problem, as a function on
phase space, for the energy `H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` and the angular momentum
`L = q₁p₂ - q₂p₁` in the orthonormal basis `b`. On the bound phase space it is the radial
quadrature between the turning radii (`TauCeti.keplerRadialAction_eq_radialAction`). -/
noncomputable def keplerRadialAction (m κ : ℝ) (x : V × V) : ℝ :=
  κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) -
    |angularMomentum (b 0) (b 1) x|

/-- The formula for the radial action. -/
theorem keplerRadialAction_apply (m κ : ℝ) (x : V × V) :
    keplerRadialAction b m κ x =
      κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) -
        |angularMomentum (b 0) (b 1) x| :=
  (rfl)

/-- On the bound phase space, the radial action is the radial quadrature
`TauCeti.radialAction` of the level between its two turning radii. -/
theorem keplerRadialAction_eq_radialAction (hm : 0 < m) {x : V × V}
    (hx : x ∈ keplerBoundPhaseSpace b m κ) :
    keplerRadialAction b m κ x =
      radialAction m (fun r ↦ -κ / r) (angularMomentum (b 0) (b 1) x)
        (centralForceHamiltonian m (fun r ↦ -κ / r) x)
        (keplerPeriapsisRadius m κ (angularMomentum (b 0) (b 1) x)
          (centralForceHamiltonian m (fun r ↦ -κ / r) x))
        (keplerApoapsisRadius m κ (angularMomentum (b 0) (b 1) x)
          (centralForceHamiltonian m (fun r ↦ -κ / r) x)) := by
  obtain ⟨hq, hE, hℓ⟩ := (mem_keplerBoundPhaseSpace b).1 hx
  rw [kepler_radialAction_turningRadii hm (pos_of_mem_keplerBoundPhaseSpace b hm hx) hℓ
    (centralForceHamiltonian_kepler_min_le b hm hq hℓ) hE, keplerRadialAction_apply]

/-- At a state of negative energy, for `m > 0`, the energy is `-m κ² / (2 (I_r + |I_θ|)²)` in the
radial action `I_r` and the signed angular action `I_θ = L`. -/
theorem keplerActionHamiltonian_keplerRadialAction (hm : 0 < m) {x : V × V}
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x < 0) :
    keplerActionHamiltonian m κ (keplerRadialAction b m κ x, angularMomentum (b 0) (b 1) x) =
      centralForceHamiltonian m (fun r ↦ -κ / r) x := by
  have hu : 0 < -2 * centralForceHamiltonian m (fun r ↦ -κ / r) x := by linarith
  have hs := sq_sqrt (div_pos hm hu).le
  -- A state of negative energy forces an attractive potential, `κ ≠ 0`.
  have hκ : κ ≠ 0 := by
    rintro rfl
    rw [← Prod.mk.eta (p := x), centralForceHamiltonian_apply] at hE
    have hp : 0 ≤ ‖x.2‖ ^ 2 / (2 * m) := by positivity
    simp only [neg_zero, zero_div, add_zero] at hE
    linarith
  rw [keplerActionHamiltonian_def, keplerRadialAction_apply, sub_add_cancel, mul_pow, hs]
  field_simp

/-- **The differential of the radial action.** Off the collision set, at a state of nonzero
energy `E` and nonzero angular momentum `ℓ`, the differential of the radial action is
`dI_r = Ω_r⁻¹ dH - sign(ℓ) dL`, with `Ω_r⁻¹ = κ √(m / (-2E)) / (-2E)`. -/
theorem hasFDerivAt_keplerRadialAction {x : V × V} (hq : x.1 ≠ 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x ≠ 0)
    (hℓ : angularMomentum (b 0) (b 1) x ≠ 0) :
    HasFDerivAt (keplerRadialAction b m κ)
      ((κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) /
          (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) •
          fderiv ℝ (centralForceHamiltonian m (fun r ↦ -κ / r)) x -
        (SignType.sign (angularMomentum (b 0) (b 1) x) : ℝ) •
          fderiv ℝ (angularMomentum (b 0) (b 1)) x) x := by
  have hH := (hasFDerivAt_centralForceHamiltonian (m := m)
    (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 hq)) hq).differentiableAt.hasFDerivAt
  have hL := (hasFDerivAt_angularMomentum (b 0) (b 1) x).differentiableAt.hasFDerivAt
  have h := (((hasDerivAt_sqrt_div m (mul_ne_zero (by norm_num) hE)).comp_hasFDerivAt x
    (hH.const_mul (-2))).const_mul κ).sub ((hasDerivAt_abs hℓ).comp_hasFDerivAt x hL)
  refine h.congr_fderiv ?_
  rw [smul_smul, smul_smul]
  congr 2
  field_simp

variable [FiniteDimensional ℝ V]

/-- **Hamilton's equations for the radial action.** Off the collision set, at a state of nonzero
energy and nonzero angular momentum, the Hamiltonian vector field of the radial action is
`Ω_r⁻¹ X_H - sign(L) X_L`, where `X_H` and `X_L` are those of the energy and the angular momentum
and `Ω_r⁻¹ = κ √(m / (-2H)) / (-2H)` is the inverse of the radial frequency. -/
theorem stdSymplecticForm_hamiltonianVectorField_keplerRadialAction {x : V × V} (hq : x.1 ≠ 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x ≠ 0)
    (hℓ : angularMomentum (b 0) (b 1) x ≠ 0) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (keplerRadialAction b m κ) x =
      (κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) /
          (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) •
        (stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) x -
      (SignType.sign (angularMomentum (b 0) (b 1) x) : ℝ) •
        (stdSymplecticForm (V := V)).hamiltonianVectorField (angularMomentum (b 0) (b 1)) x := by
  rw [eq_comm, SymplecticForm.eq_hamiltonianVectorField_iff,
    (hasFDerivAt_keplerRadialAction b hq hE hℓ).fderiv]
  intro v
  simp [map_sub, map_smul]

/-- **The radial action is a first integral of the energy.** Off the collision set, at a state of
nonzero energy and nonzero angular momentum, the energy Poisson-commutes with the radial action. -/
theorem stdSymplecticForm_poissonBracket_centralForceHamiltonian_keplerRadialAction {x : V × V}
    (hq : x.1 ≠ 0) (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x ≠ 0)
    (hℓ : angularMomentum (b 0) (b 1) x ≠ 0) :
    (stdSymplecticForm (V := V)).poissonBracket (centralForceHamiltonian m (fun r ↦ -κ / r))
      (keplerRadialAction b m κ) x = 0 := by
  rw [SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_hamiltonianVectorField_keplerRadialAction b hq hE hℓ]
  simp [SymplecticForm.fderiv_apply_hamiltonianVectorField,
    ← SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum]

/-- **The radial and angular actions Poisson-commute.** Off the collision set, at a state of
nonzero energy and nonzero angular momentum, the angular momentum Poisson-commutes with the radial
action. -/
theorem stdSymplecticForm_poissonBracket_angularMomentum_keplerRadialAction {x : V × V}
    (hq : x.1 ≠ 0) (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x ≠ 0)
    (hℓ : angularMomentum (b 0) (b 1) x ≠ 0) :
    (stdSymplecticForm (V := V)).poissonBracket (angularMomentum (b 0) (b 1))
      (keplerRadialAction b m κ) x = 0 := by
  rw [SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_hamiltonianVectorField_keplerRadialAction b hq hE hℓ]
  simp [SymplecticForm.fderiv_apply_hamiltonianVectorField,
    ← SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_poissonBracket_angularMomentum_centralForceHamiltonian]

/-! ### The flow of the radial action -/

/-- Along a curve off the collision set whose velocity is a combination of the Hamiltonian vector
fields of the Kepler energy and of the angular momentum, both are conserved. -/
private theorem energy_angularMomentum_eq_of_hasDerivAt {γ : ℝ → V × V} {a c : ℝ → ℝ}
    (hγ : ∀ t, HasDerivAt γ
      (a t • (stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t) +
        c t • (stdSymplecticForm (V := V)).hamiltonianVectorField
          (angularMomentum (b 0) (b 1)) (γ t)) t)
    (hq : ∀ t, (γ t).1 ≠ 0) (t : ℝ) :
    centralForceHamiltonian m (fun r ↦ -κ / r) (γ t) =
        centralForceHamiltonian m (fun r ↦ -κ / r) (γ 0) ∧
      angularMomentum (b 0) (b 1) (γ t) = angularMomentum (b 0) (b 1) (γ 0) := by
  have hH (s : ℝ) := (hasFDerivAt_centralForceHamiltonian (m := m)
    (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hq s))) (hq s)).differentiableAt
  have hL (s : ℝ) := (hasFDerivAt_angularMomentum (b 0) (b 1) (γ s)).differentiableAt
  -- The energy and the angular momentum Poisson-commute.
  have hHL (s : ℝ) : fderiv ℝ (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ s)
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (angularMomentum (b 0) (b 1))
        (γ s)) = 0 := by
    rw [← SymplecticForm.poissonBracket_eq_fderiv,
      stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum]
  have hLH (s : ℝ) : fderiv ℝ (angularMomentum (b 0) (b 1)) (γ s)
      ((stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ s)) = 0 := by
    rw [← SymplecticForm.poissonBracket_eq_fderiv, ← SymplecticForm.neg_poissonBracket,
      stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum, neg_zero]
  constructor
  · refine is_const_of_deriv_eq_zero
      (fun s ↦ ((hH s).hasFDerivAt.comp_hasDerivAt s (hγ s)).differentiableAt) (fun s ↦ ?_) t 0
    rw [((hH s).hasFDerivAt.comp_hasDerivAt s (hγ s)).deriv]
    simp [hHL s]
  · refine is_const_of_deriv_eq_zero
      (fun s ↦ ((hL s).hasFDerivAt.comp_hasDerivAt s (hγ s)).differentiableAt) (fun s ↦ ?_) t 0
    rw [((hL s).hasFDerivAt.comp_hasDerivAt s (hγ s)).deriv]
    simp [hLH s]

section Rotation

variable [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- **Rotating and rescaling a Kepler-type motion.** If `γ` moves along `a X_H + s (J q, J p)` off
the collision set, for constants `a` and `s`, then rotating `γ (k t)` by the angle `θ' t` gives a
curve moving along `k a X_H + (k s + θ') (J q, J p)`. -/
private theorem hasDerivAt_rotation_comp_kepler {γ : ℝ → V × V} {a s k θ' : ℝ}
    (hv : ∀ t, HasDerivAt γ
      (a • (stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t) +
        s • (o.rightAngleRotation (γ t).1, o.rightAngleRotation (γ t).2)) t)
    (hq : ∀ t, (γ t).1 ≠ 0) (t : ℝ) :
    HasDerivAt (fun t ↦ (o.rotation (θ' * t : ℝ) (γ (k * t)).1,
        o.rotation (θ' * t : ℝ) (γ (k * t)).2))
      ((k * a) • (stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r))
          (o.rotation (θ' * t : ℝ) (γ (k * t)).1, o.rotation (θ' * t : ℝ) (γ (k * t)).2) +
        (k * s + θ') • (o.rightAngleRotation (o.rotation (θ' * t : ℝ) (γ (k * t)).1),
          o.rightAngleRotation (o.rotation (θ' * t : ℝ) (γ (k * t)).2))) t := by
  have hk : HasDerivAt (fun t ↦ k * t) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hθ : HasDerivAt (fun t ↦ θ' * t) θ' t := by
    simpa using (hasDerivAt_id t).const_mul θ'
  have hγk := (hv (k * t)).scomp t hk
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_linearIsometryEquiv _
    (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hq _))) (hq _)]
  convert (o.hasDerivAt_rotation hθ hγk.fst).prodMk (o.hasDerivAt_rotation hθ hγk.snd) using 1
  · rfl
  -- The quarter turn commutes with the rotations.
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Function.comp_apply,
    map_add, map_smul, o.linearIsometryEquiv_comp_rightAngleRotation, o.det_rotation,
    zero_lt_one] <;> module

end Rotation

/-- The inverse radial frequency `κ √(m / (-2E)) / (-2E)` at a negative energy `E` is
`√(m / κ) a^(3/2)` for `a = κ / (-2E)`, so that `2π` times it is the Kepler period. -/
private theorem mul_sqrt_div_div_eq_sqrt_mul_rpow (hm : 0 < m) (hκ : 0 < κ) {E : ℝ}
    (hE : E < 0) :
    κ * √(m / (-2 * E)) / (-2 * E) = √(m / κ) * (κ / (-2 * E)) ^ (3 / 2 : ℝ) := by
  have hu : 0 < -2 * E := by linarith
  have ha : 0 < κ / (-2 * E) := div_pos hκ hu
  have h32 : (κ / (-2 * E)) ^ (3 / 2 : ℝ) = κ / (-2 * E) * √(κ / (-2 * E)) := by
    rw [sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      rpow_add' ha.le (by norm_num), rpow_one]
  have hmul : m / κ * (κ / (-2 * E)) = m / (-2 * E) := by
    field_simp
  rw [h32, mul_left_comm, ← sqrt_mul (div_pos hm hκ).le, hmul]
  ring

/-- **The radial action is an action variable.** Let `m > 0`. Every solution `γ` of
Hamilton's equations for the Kepler radial action `I_r = κ √(m / (-2H)) - |L|`, defined for all
time and staying in the bound phase space `{q ≠ 0, H < 0, L ≠ 0}`, is `2π`-periodic. -/
theorem periodic_of_forall_hasDerivAt_keplerRadialAction (hm : 0 < m) {γ : ℝ → V × V}
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (keplerRadialAction b m κ) (γ t)) t)
    (hB : ∀ t, γ t ∈ keplerBoundPhaseSpace b m κ) :
    Function.Periodic γ (2 * π) := by
  have : Fact (finrank ℝ V = 2) := ⟨by simp [finrank_eq_card_basis b.toBasis]⟩
  set o : Orientation ℝ V (Fin 2) := b.toBasis.orientation
  have hq (t : ℝ) : (γ t).1 ≠ 0 := ((mem_keplerBoundPhaseSpace b).1 (hB t)).1
  have hκ := pos_of_mem_keplerBoundPhaseSpace b hm (hB 0)
  obtain ⟨-, hE, hℓ⟩ := (mem_keplerBoundPhaseSpace b).1 (hB 0)
  set E := centralForceHamiltonian m (fun r ↦ -κ / r) (γ 0)
  set σ : ℝ := ((SignType.sign (angularMomentum (b 0) (b 1) (γ 0)) : SignType) : ℝ)
  set c := κ * √(m / (-2 * E)) / (-2 * E)
  have hc : 0 < c := div_pos (mul_pos hκ (sqrt_pos.2 (div_pos hm (by linarith))))
    (by linarith)
  -- The energy and the angular momentum are conserved, so `γ` moves along `c X_H - σ X_L`.
  have hγ' (t : ℝ) := stdSymplecticForm_hamiltonianVectorField_keplerRadialAction b (hq t)
    ((mem_keplerBoundPhaseSpace b).1 (hB t)).2.1.ne ((mem_keplerBoundPhaseSpace b).1 (hB t)).2.2 ▸
    hγ t
  have hcons := energy_angularMomentum_eq_of_hasDerivAt b (fun t ↦ by
    simpa only [sub_eq_add_neg, ← neg_smul] using hγ' t) hq
  have hv (t : ℝ) : HasDerivAt γ
      (c • (stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t) +
        (-σ) • (o.rightAngleRotation (γ t).1, o.rightAngleRotation (γ t).2)) t := by
    have h := hγ' t
    rwa [(hcons t).1, (hcons t).2,
      stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation b rfl,
      sub_eq_add_neg, ← neg_smul] at h
  -- Rotating `γ (τ / c)` by the angle `σ τ / c` gives a bound Kepler motion `δ`.
  set δ : ℝ → V × V := fun τ ↦ (o.rotation (σ * c⁻¹ * τ : ℝ) (γ (c⁻¹ * τ)).1,
    o.rotation (σ * c⁻¹ * τ : ℝ) (γ (c⁻¹ * τ)).2) with hδdef
  have hδ (τ : ℝ) : HasDerivAt δ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (δ τ)) τ := by
    have h := hasDerivAt_rotation_comp_kepler o (k := c⁻¹) (θ' := σ * c⁻¹) hv hq τ
    rwa [inv_mul_cancel₀ hc.ne', one_smul, show c⁻¹ * -σ + σ * c⁻¹ = 0 by ring, zero_smul,
      add_zero] at h
  -- By Kepler's third law `δ` is periodic, with period `2π c`.
  have hδq (τ : ℝ) : (δ τ).1 ≠ 0 := by simpa [hδdef] using hq (c⁻¹ * τ)
  have hδE : centralForceHamiltonian m (fun r ↦ -κ / r) (δ 0) = -κ / (2 * (κ / (-2 * E))) := by
    have hδ0 : δ 0 = γ 0 := by simp [hδdef]
    have hEa : -κ / (2 * (κ / (-2 * E))) = E := by field_simp [hκ.ne', hE.ne]
    rw [hδ0, hEa]
  have hper := periodic_of_forall_hasDerivAt_kepler hm hκ (div_pos hκ (by linarith)) hδ hδq hδE
  rw [mul_assoc (2 * π), ← mul_sqrt_div_div_eq_sqrt_mul_rpow hm hκ hE] at hper
  -- So `γ`, which is `δ (c t)` rotated back by the angle `σ t`, is `2π`-periodic, as `σ = ±1`.
  have hγδ (t : ℝ) : γ t = (o.rotation (-(σ * t) : ℝ) (δ (c * t)).1,
      o.rotation (-(σ * t) : ℝ) (δ (c * t)).2) := by
    simp only [hδdef, inv_mul_cancel_left₀ hc.ne', mul_assoc σ, Real.Angle.coe_neg,
      ← o.rotation_symm, LinearIsometryEquiv.symm_apply_apply]
  have hσ (t : ℝ) : ((-(σ * (t + 2 * π)) : ℝ) : Real.Angle) = ((-(σ * t) : ℝ) : Real.Angle) := by
    rcases hℓ.lt_or_gt with h | h <;> simp [σ, h, mul_add]
  intro t
  rw [hγδ, hγδ t, hσ, mul_add, mul_comm c (2 * π), hper]

/-- **The flow of the radial action is global on the bound phase space.** Let `m > 0`. Through
every state of the bound phase space there is a solution of Hamilton's equations for the Kepler
radial action which is defined for all time and stays in the bound phase space. -/
theorem exists_forall_hasDerivAt_keplerRadialAction (hm : 0 < m) {x : V × V}
    (hx : x ∈ keplerBoundPhaseSpace b m κ) :
    ∃ γ : ℝ → V × V, γ 0 = x ∧ ∀ t, γ t ∈ keplerBoundPhaseSpace b m κ ∧
      HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
        (keplerRadialAction b m κ) (γ t)) t := by
  have : Fact (finrank ℝ V = 2) := ⟨by simp [finrank_eq_card_basis b.toBasis]⟩
  set o : Orientation ℝ V (Fin 2) := b.toBasis.orientation with ho
  obtain ⟨-, hE, hℓ⟩ := (mem_keplerBoundPhaseSpace b).1 hx
  have hκ := pos_of_mem_keplerBoundPhaseSpace b hm hx
  -- A Kepler motion `η` through `x` is global on the bound phase space, and conserves the energy
  -- and the angular momentum.
  obtain ⟨η, hη0, hη⟩ := SymplecticForm.exists_forall_hasDerivAt_of_isCompleteVectorField
    stdSymplecticForm (U := keplerBoundPhaseSpace b m κ)
    (f := fun y ↦ centralForceEnergyMomentum b m (fun r ↦ -κ / r) y 0)
    (contMDiff_pi_module_iff.1 (contMDiff_centralForceEnergyMomentum_keplerBoundPhaseSpace b) 0
      |>.of_le (by simp))
    (isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace b hm hκ 0) hx
  simp only [centralForceEnergyMomentum_zero] at hη
  have hηq (t : ℝ) : (η t).1 ≠ 0 := ((mem_keplerBoundPhaseSpace b).1 (hη t).1).1
  have hcons := energy_angularMomentum_eq_of_hasDerivAt b (a := fun _ ↦ 1) (c := fun _ ↦ 0)
    (fun t ↦ by simpa only [one_smul, zero_smul, add_zero] using (hη t).2) hηq
  set σ : ℝ := ((SignType.sign (angularMomentum (b 0) (b 1) x) : SignType) : ℝ) with hσ
  set c := κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) /
    (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x) with hc
  -- The solution runs along `η` at the speed `c`, rotated by the angle `-σ t`.
  refine ⟨fun t ↦ (o.rotation (-σ * t : ℝ) (η (c * t)).1, o.rotation (-σ * t : ℝ) (η (c * t)).2),
    by simp [hη0], fun t ↦ ?_⟩
  have hHt : centralForceHamiltonian m (fun r ↦ -κ / r) (o.rotation (-σ * t : ℝ) (η (c * t)).1,
      o.rotation (-σ * t : ℝ) (η (c * t)).2) = centralForceHamiltonian m (fun r ↦ -κ / r) x := by
    rw [centralForceHamiltonian_linearIsometryEquiv, (hcons (c * t)).1, hη0]
  have hLt := (angularMomentum_rotation b rfl (-σ * t : ℝ) (η (c * t))).trans
    ((hcons _).2.trans (congrArg _ hη0))
  have hqt : (o.rotation (-σ * t : ℝ) (η (c * t)).1, o.rotation (-σ * t : ℝ) (η (c * t)).2).1 ≠
      0 := by simpa using hηq (c * t)
  refine ⟨(mem_keplerBoundPhaseSpace b).2 ⟨hqt, hHt ▸ hE, hLt ▸ hℓ⟩, ?_⟩
  rw [stdSymplecticForm_hamiltonianVectorField_keplerRadialAction b hqt (hHt ▸ hE.ne) (hLt ▸ hℓ),
    hHt, hLt,
    stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation b rfl, ← hc,
    ← hσ, ← ho, sub_eq_add_neg, ← neg_smul]
  have h := hasDerivAt_rotation_comp_kepler o (a := 1) (s := 0) (k := c) (θ' := -σ)
    (fun t ↦ by simpa only [one_smul, zero_smul, add_zero] using (hη t).2) hηq t
  rwa [mul_one, mul_zero, zero_add] at h

end TauCeti
