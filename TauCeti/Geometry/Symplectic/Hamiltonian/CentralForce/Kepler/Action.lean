/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Period
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Frequency
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.InnerProductSpace.TwoDim
import TauCeti.Geometry.Euclidean.Circle

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
  flow is the rotation `(q, p) ↦ (R_t q, R_t p)` of the plane by the angle `t`
  (`TauCeti.hasDerivAt_rotation_hamiltonianVectorField_angularMomentum`), and every solution of
  Hamilton's equations for `L` is such a rotation of its initial state
  (`TauCeti.eq_rotation_of_forall_hasDerivAt_angularMomentum`). So it is
  `2π`-periodic (`TauCeti.periodic_of_forall_hasDerivAt_angularMomentum`).
* **The radial action.** On the bound phase space the Hamiltonian vector field of `I_r` is

  `X_{I_r} = Ω_r⁻¹ X_H - sign(L) X_L`, with `Ω_r⁻¹ = κ √(m / (-2H)) / (-2H)`

  (`TauCeti.stdSymplecticForm_hamiltonianVectorField_keplerRadialAction`). Since `H` and `L`
  Poisson-commute, both are constant along its solutions. If `γ` solves Hamilton's equations for
  `I_r` in the bound phase space, then rotating `γ(τ / Ω_r)` back by the angle
  `sign(L) τ / Ω_r` gives a solution of Hamilton's equations for `H`, a bound Kepler motion of the
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

/-! ### The angular momentum generates the rotations of the plane -/

section Rotation

variable [Fact (finrank ℝ V = 2)] {o : Orientation ℝ V (Fin 2)}

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

/-- In the plane of a positively oriented orthonormal basis, the angular momentum `q₁p₂ - q₂p₁` is
the area form `ω(q, p)`. -/
theorem angularMomentum_eq_areaForm (hb : b.toBasis.orientation = o) (x : V × V) :
    angularMomentum (b 0) (b 1) x = o.areaForm x.1 x.2 := by
  obtain ⟨q, p⟩ := x
  rw [← o.inner_rightAngleRotation_left, o.rightAngleRotation_eq_inner_smul_sub_inner_smul hb,
    angularMomentum_apply, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_comm p (b 1), real_inner_comm p (b 0)]

/-- Rotating positions and momenta alike preserves the angular momentum. -/
theorem angularMomentum_rotation (hb : b.toBasis.orientation = o) (θ : Real.Angle)
    (x : V × V) :
    angularMomentum (b 0) (b 1) (o.rotation θ x.1, o.rotation θ x.2) =
      angularMomentum (b 0) (b 1) x := by
  simp only [angularMomentum_eq_areaForm b hb, ← o.inner_rightAngleRotation_left]
  rw [o.rightAngleRotation_rotation, LinearIsometryEquiv.inner_map_map]

/-- **The angular momentum generates the rotations.** In the plane of a positively oriented
orthonormal basis, the Hamiltonian vector field of the angular momentum is `(J q, J p)`, for the
quarter turn `J`. -/
theorem stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation
    (hb : b.toBasis.orientation = o) (x : V × V) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (angularMomentum (b 0) (b 1)) x =
      (o.rightAngleRotation x.1, o.rightAngleRotation x.2) := by
  rw [stdSymplecticForm_hamiltonianVectorField_angularMomentum,
    o.rightAngleRotation_eq_inner_smul_sub_inner_smul hb,
    o.rightAngleRotation_eq_inner_smul_sub_inner_smul hb]

/-- **The Hamiltonian flow of the angular momentum is the rotation of the plane.** In the plane of
a positively oriented orthonormal basis, `t ↦ (R_t q, R_t p)` solves Hamilton's equations for the
angular momentum. -/
theorem hasDerivAt_rotation_hamiltonianVectorField_angularMomentum
    (hb : b.toBasis.orientation = o) (x : V × V) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (o.rotation s x.1, o.rotation s x.2))
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (angularMomentum (b 0) (b 1))
        (o.rotation t x.1, o.rotation t x.2)) t := by
  rw [stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation b hb]
  have h (v : V) := o.hasDerivAt_rotation (hasDerivAt_id t) (hasDerivAt_const t v)
  simpa using (h x.1).prodMk (h x.2)

/-- **Every motion of the angular momentum is a rotation.** In the plane of a positively oriented
orthonormal basis, a solution `γ` of Hamilton's equations for the angular momentum, defined for all
time, is `γ t = (R_t q, R_t p)` for its initial state `(q, p)`. -/
theorem eq_rotation_of_forall_hasDerivAt_angularMomentum
    (hb : b.toBasis.orientation = o) {γ : ℝ → V × V}
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (angularMomentum (b 0) (b 1)) (γ t)) t) (t : ℝ) :
    γ t = (o.rotation t (γ 0).1, o.rotation t (γ 0).2) := by
  simp_rw [stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation b hb]
    at hγ
  -- Rotating `γ s` back by the angle `s` gives a constant curve.
  have hδ (s : ℝ) : HasDerivAt (fun s : ℝ ↦ (o.rotation (-s : ℝ) (γ s).1,
      o.rotation (-s : ℝ) (γ s).2)) 0 s := by
    have hθ := hasDerivAt_neg s
    convert (o.hasDerivAt_rotation hθ (hγ s).fst).prodMk (o.hasDerivAt_rotation hθ (hγ s).snd)
      using 1
    ext <;> simp [o.rightAngleRotation_rotation]
  have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hδ s).differentiableAt)
    (fun s ↦ (hδ s).deriv) t 0
  simp only [neg_zero, Real.Angle.coe_zero, o.rotation_zero, LinearIsometryEquiv.coe_refl, id_eq,
    Prod.mk.injEq] at hconst
  have hinv (v : V) : o.rotation (-t : ℝ) (o.rotation t v) = v := by
    rw [o.rotation_rotation, ← Real.Angle.coe_add, neg_add_cancel, Real.Angle.coe_zero,
      o.rotation_zero, LinearIsometryEquiv.coe_refl, id_eq]
  ext
  · exact (o.rotation (-t : ℝ)).injective (hconst.1.trans (hinv _).symm)
  · exact (o.rotation (-t : ℝ)).injective (hconst.2.trans (hinv _).symm)

end Rotation

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

/-- For `m > 0` the bound phase space is empty unless the potential is attractive, `κ > 0`. -/
private theorem pos_of_mem_keplerBoundPhaseSpace (hm : 0 < m) {x : V × V}
    (hx : x ∈ keplerBoundPhaseSpace b m κ) : 0 < κ := by
  obtain ⟨hq, hE, -⟩ := (mem_keplerBoundPhaseSpace b).1 hx
  rw [← Prod.mk.eta (p := x), centralForceHamiltonian_apply] at hE
  have hp : 0 ≤ ‖x.2‖ ^ 2 / (2 * m) := by positivity
  have hr : 0 < ‖x.1‖ := norm_pos_iff.2 hq
  by_contra! hκ
  have : 0 ≤ -κ / ‖x.1‖ := div_nonneg (by linarith) hr.le
  linarith

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

/-- On the bound phase space, the energy is `-m κ² / (2 (I_r + |I_θ|)²)` in the radial action
`I_r` and the signed angular action `I_θ = L`. -/
theorem keplerActionHamiltonian_keplerRadialAction (hm : 0 < m) {x : V × V}
    (hx : x ∈ keplerBoundPhaseSpace b m κ) :
    keplerActionHamiltonian m κ (keplerRadialAction b m κ x, angularMomentum (b 0) (b 1) x) =
      centralForceHamiltonian m (fun r ↦ -κ / r) x := by
  have hu : 0 < -2 * centralForceHamiltonian m (fun r ↦ -κ / r) x := by
    linarith [((mem_keplerBoundPhaseSpace b).1 hx).2.1]
  have hs := sq_sqrt (div_pos hm hu).le
  have hκ := pos_of_mem_keplerBoundPhaseSpace b hm hx
  rw [keplerActionHamiltonian_def, keplerRadialAction_apply, sub_add_cancel, mul_pow, hs]
  field_simp

variable [FiniteDimensional ℝ V]

/-- **The angular action is an action variable.** In the plane of an orthonormal basis, every
solution of Hamilton's equations for the angular momentum, defined for all time, is `2π`-periodic.
-/
theorem periodic_of_forall_hasDerivAt_angularMomentum {γ : ℝ → V × V}
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (angularMomentum (b 0) (b 1)) (γ t)) t) :
    Function.Periodic γ (2 * π) := fun t ↦ by
  have : Fact (finrank ℝ V = 2) := ⟨by simp [finrank_eq_card_basis b.toBasis]⟩
  rw [eq_rotation_of_forall_hasDerivAt_angularMomentum b rfl hγ,
    eq_rotation_of_forall_hasDerivAt_angularMomentum b rfl hγ t,
    Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]

/-- The energy `κ √(m / (-2E))` of the action `I_r + |I_θ|`, as a function of the energy `E < 0`,
has derivative `κ √(m / (-2E)) / (-2E)`, the inverse of the radial frequency. -/
private theorem hasDerivAt_mul_sqrt_div_neg_two_mul (hm : 0 < m) {E : ℝ} (hE : E < 0) :
    HasDerivAt (fun E ↦ κ * √(m / (-2 * E))) (κ * √(m / (-2 * E)) / (-2 * E)) E := by
  have hu : 0 < -2 * E := by linarith
  have hd : HasDerivAt (fun E ↦ m / (-2 * E)) (2 * m / (-2 * E) ^ 2) E := by
    convert ((hasDerivAt_id E).const_mul (-2)).inv hu.ne' |>.const_mul m using 1
    · ext E
      simp [div_eq_mul_inv]
    · simp
      field_simp
  convert (hd.sqrt (div_pos hm hu).ne').const_mul κ using 1
  set y := m / (-2 * E) with hy
  have hy0 : 0 < y := div_pos hm hu
  have hmy : m = √y ^ 2 * (-2 * E) := by
    rw [sq_sqrt hy0.le, hy]
    field_simp [hE.ne]
  have hs0 : √y ≠ 0 := (sqrt_pos.2 hy0).ne'
  rw [hmy]
  field_simp

/-- **Hamilton's equations for the radial action.** On the bound phase space, the Hamiltonian
vector field of the radial action is `Ω_r⁻¹ X_H - sign(L) X_L`, where `X_H` and `X_L` are those of
the energy and the angular momentum and `Ω_r⁻¹ = κ √(m / (-2H)) / (-2H)` is the inverse of the
radial frequency. -/
theorem stdSymplecticForm_hamiltonianVectorField_keplerRadialAction (hm : 0 < m) {x : V × V}
    (hx : x ∈ keplerBoundPhaseSpace b m κ) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (keplerRadialAction b m κ) x =
      (κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) /
          (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) •
        (stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) x -
      (SignType.sign (angularMomentum (b 0) (b 1) x) : ℝ) •
        (stdSymplecticForm (V := V)).hamiltonianVectorField (angularMomentum (b 0) (b 1)) x := by
  obtain ⟨hq, hE, hℓ⟩ := (mem_keplerBoundPhaseSpace b).1 hx
  have hH := (hasFDerivAt_centralForceHamiltonian (m := m)
    (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 hq)) hq).differentiableAt.hasFDerivAt
  have hL := (hasFDerivAt_angularMomentum (b 0) (b 1) x).differentiableAt.hasFDerivAt
  have hI := ((hasDerivAt_mul_sqrt_div_neg_two_mul (κ := κ) hm hE).comp_hasFDerivAt x hH).sub
    (hL.abs hℓ)
  rw [eq_comm, SymplecticForm.eq_hamiltonianVectorField_iff,
    (show HasFDerivAt (keplerRadialAction b m κ) _ x from hI).fderiv]
  intro v
  simp [map_sub, map_smul]

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

/-- Rotating positions and momenta alike commutes with the Kepler Hamiltonian vector field. -/
private theorem hamiltonianVectorField_kepler_rotation (θ : Real.Angle) {y : V × V}
    (hq : y.1 ≠ 0) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m (fun r ↦ -κ / r)) (o.rotation θ y.1, o.rotation θ y.2) =
      (o.rotation θ ((stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) y).1,
        o.rotation θ ((stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) y).2) := by
  have hq' : o.rotation θ y.1 ≠ 0 := by simpa using hq
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian
    (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 hq')) hq',
    stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian
    (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 hq)) hq]
  simp [map_smul]

/-- **Unwinding the flow of the radial action.** If `γ` moves along `c X_H - σ X_L` off the
collision set, for constants `c ≠ 0` and `σ`, then rotating `γ (τ / c)` by the angle `σ τ / c`
gives a solution of Hamilton's equations for the Kepler energy. -/
private theorem hasDerivAt_rotation_comp_kepler {γ : ℝ → V × V} {c σ : ℝ} (hc : c ≠ 0)
    (hv : ∀ t, HasDerivAt γ
      (c • (stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t) -
        σ • (o.rightAngleRotation (γ t).1, o.rightAngleRotation (γ t).2)) t)
    (hq : ∀ t, (γ t).1 ≠ 0) (τ : ℝ) :
    HasDerivAt (fun τ ↦ (o.rotation (σ * (c⁻¹ * τ) : ℝ) (γ (c⁻¹ * τ)).1,
        o.rotation (σ * (c⁻¹ * τ) : ℝ) (γ (c⁻¹ * τ)).2))
      ((stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m (fun r ↦ -κ / r))
        (o.rotation (σ * (c⁻¹ * τ) : ℝ) (γ (c⁻¹ * τ)).1,
          o.rotation (σ * (c⁻¹ * τ) : ℝ) (γ (c⁻¹ * τ)).2)) τ := by
  have hk : HasDerivAt (fun τ ↦ c⁻¹ * τ) c⁻¹ τ := by
    simpa using (hasDerivAt_id τ).const_mul c⁻¹
  have hθ : HasDerivAt (fun τ ↦ σ * (c⁻¹ * τ)) (σ * c⁻¹) τ := hk.const_mul σ
  have hγk := (hv (c⁻¹ * τ)).scomp τ hk
  rw [hamiltonianVectorField_kepler_rotation o _ (hq _)]
  convert (o.hasDerivAt_rotation hθ hγk.fst).prodMk (o.hasDerivAt_rotation hθ hγk.snd) using 1
  · rfl
  ext <;> simp [o.rightAngleRotation_rotation, smul_sub, smul_smul, hc] <;> module

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
  have hγ' (t : ℝ) := stdSymplecticForm_hamiltonianVectorField_keplerRadialAction b hm (hB t) ▸
    hγ t
  have hcons := energy_angularMomentum_eq_of_hasDerivAt b (fun t ↦ by
    simpa only [sub_eq_add_neg, ← neg_smul] using hγ' t) hq
  have hv (t : ℝ) : HasDerivAt γ
      (c • (stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t) -
        σ • (o.rightAngleRotation (γ t).1, o.rightAngleRotation (γ t).2)) t := by
    have h := hγ' t
    rwa [(hcons t).1, (hcons t).2,
      stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation b rfl] at h
  -- Rotating `γ (τ / c)` back by the angle `σ τ / c` gives a bound Kepler motion `δ`.
  set δ : ℝ → V × V := fun τ ↦ (o.rotation (σ * (c⁻¹ * τ) : ℝ) (γ (c⁻¹ * τ)).1,
    o.rotation (σ * (c⁻¹ * τ) : ℝ) (γ (c⁻¹ * τ)).2) with hδdef
  have hδ (τ : ℝ) : HasDerivAt δ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (δ τ)) τ :=
    hasDerivAt_rotation_comp_kepler o hc.ne' hv hq τ
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
    simp only [hδdef, inv_mul_cancel_left₀ hc.ne', o.rotation_rotation, ← Real.Angle.coe_add,
      neg_add_cancel, Real.Angle.coe_zero, o.rotation_zero, LinearIsometryEquiv.coe_refl, id_eq]
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
  obtain ⟨hq, hE, hℓ⟩ := (mem_keplerBoundPhaseSpace b).1 hx
  have hκ := pos_of_mem_keplerBoundPhaseSpace b hm hx
  -- A Kepler motion `η` through `x` is global, and conserves the energy and the angular momentum.
  obtain ⟨η, hη0, hη⟩ := exists_forall_hasDerivAt_kepler hm hκ hq
    (by rw [← sq_angularMomentum b]; exact pow_ne_zero 2 hℓ)
  have hcons := energy_angularMomentum_eq_of_hasDerivAt b (a := fun _ ↦ 1) (c := fun _ ↦ 0)
    (fun t ↦ by simpa using (hη t).2) (fun t ↦ (hη t).1)
  set σ : ℝ := ((SignType.sign (angularMomentum (b 0) (b 1) x) : SignType) : ℝ) with hσ
  set c := κ * √(m / (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x)) /
    (-2 * centralForceHamiltonian m (fun r ↦ -κ / r) x) with hc
  -- The solution runs along `η` at the speed `c`, rotated by the angle `-σ t`.
  refine ⟨fun t ↦ (o.rotation (-(σ * t) : ℝ) (η (c * t)).1,
    o.rotation (-(σ * t) : ℝ) (η (c * t)).2),
    by simp [hη0], fun t ↦ ?_⟩
  have hHt : centralForceHamiltonian m (fun r ↦ -κ / r) (o.rotation (-(σ * t) : ℝ) (η (c * t)).1,
      o.rotation (-(σ * t) : ℝ) (η (c * t)).2) = centralForceHamiltonian m (fun r ↦ -κ / r) x := by
    have hrot (y : V × V) : centralForceHamiltonian m (fun r ↦ -κ / r)
        (o.rotation (-(σ * t) : ℝ) y.1, o.rotation (-(σ * t) : ℝ) y.2) =
          centralForceHamiltonian m (fun r ↦ -κ / r) y := by
      obtain ⟨q, p⟩ := y
      simp [centralForceHamiltonian_apply]
    rw [hrot, (hcons (c * t)).1, hη0]
  have hLt := (angularMomentum_rotation b rfl (-(σ * t) : ℝ) (η (c * t))).trans
    ((hcons _).2.trans (congrArg _ hη0))
  have hmem := (mem_keplerBoundPhaseSpace b).2 ⟨by simpa using (hη (c * t)).1, hHt ▸ hE, hLt ▸ hℓ⟩
  refine ⟨hmem, ?_⟩
  rw [stdSymplecticForm_hamiltonianVectorField_keplerRadialAction b hm hmem, hHt, hLt,
    stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation b rfl,
    hamiltonianVectorField_kepler_rotation o _ (hη _).1, ← hc, ← hσ, ← ho]
  have hk : HasDerivAt (fun t ↦ c * t) c t := by simpa using (hasDerivAt_id t).const_mul c
  have hθ : HasDerivAt (fun t ↦ -(σ * t)) (-σ) t := by
    simpa using (hasDerivAt_id t).const_mul (-σ)
  have hηk := (hη (c * t)).2.scomp t hk
  convert (o.hasDerivAt_rotation hθ hηk.fst).prodMk (o.hasDerivAt_rotation hθ hηk.snd) using 1
  · rfl
  ext <;> simp <;> module

end TauCeti
