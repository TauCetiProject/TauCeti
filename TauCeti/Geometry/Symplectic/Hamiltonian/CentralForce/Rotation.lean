/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Linear
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.Complex.Inner

/-!
# The rotational moment map of planar central forces

Identify the configuration plane `ℝ²` with `ℂ`, so that the phase space of a planar particle is
`ℂ × ℂ` with positions `q` and momenta `p`, standard symplectic form `ω₀ = dq₁ ∧ dp₁ + dq₂ ∧ dp₂`
and angular momentum `L(q, p) = q₁ p₂ - q₂ p₁` (`TauCeti.angularMomentum 1 I`). The circle group
`Circle ⊆ ℂ` acts on the phase space by rotating positions and momenta alike,
`z • (q, p) = (z q, z p)`.

This action is the symmetry behind the conservation of angular momentum:

* every rotation is a linear symplectomorphism of `(ℂ × ℂ, ω₀)`, as is every isometry of a real
  inner product space `V` fixing the origin, acting on `V × V` (`TauCeti.stdSymplecticForm_smul`).
  It preserves the angular momentum (`TauCeti.angularMomentum_circle_smul`) and every
  central-force Hamiltonian `‖p‖² / (2m) + U(‖q‖)` (`TauCeti.centralForceHamiltonian_smul`);
* the Hamiltonian vector field of `L` at `(q, p)` is `(i q, i p)`
  (`TauCeti.stdSymplecticForm_hamiltonianVectorField_angularMomentum_one_I`), so
  the rotation `t ↦ exp (t i) • x` by the angle `t` is the integral curve of the Hamiltonian
  vector field of `L` through `x`
  (`TauCeti.hasDerivAt_circleExp_smul_hamiltonianVectorField_angularMomentum`): the Hamiltonian
  flow of the angular momentum is the rotation of the plane, with period `2π`;
* the angular momentum is the **rotational moment map**. For an element `ξ` of the Lie algebra of
  the circle, with image `ι_* ξ ∈ ℂ` under the derivative of the inclusion `ι : Circle → ℂ`, the
  quadratic moment map of the linear action is `μ(x)(ξ) = Im (ι_* ξ) L(x)`
  (`TauCeti.stdSymplecticForm_linearActionMomentMap_circle_apply`). So `x ↦ L(x) Im (ι_* ·)` is the
  moment map of a Hamiltonian circle action (`TauCeti.hamiltonianTorusData_angularMomentum`),
  and its component along the generator of `t ↦ exp (t i)` is `L` itself
  (`TauCeti.stdSymplecticForm_linearActionMomentMap_circle_apply_mfderiv_circleExp`).
* the rotations preserve the punctured phase space `{(q, p) | q ≠ 0}`
  (`TauCeti.puncturedPhaseSpace`), where singular central potentials are smooth, and the angular
  momentum restricts to the moment map of a Hamiltonian circle action there
  (`TauCeti.hamiltonianTorusData_angularMomentum_puncturedPhaseSpace`).

The conservation law `{H, L} = 0` for a central-force Hamiltonian `H` is
`TauCeti.stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum`.

## Main results

* `TauCeti.angularMomentum_circle_smul`: rotations preserve `L`.
* `TauCeti.stdSymplecticForm_hamiltonianVectorField_angularMomentum_one_I`: the Hamiltonian
  vector field of `L` is `(q, p) ↦ (i q, i p)`.
* `TauCeti.hasDerivAt_circleExp_smul_hamiltonianVectorField_angularMomentum`: the Hamiltonian
  flow of `L` is the rotation of the plane.
* `TauCeti.eq_circleExp_smul_of_hasDerivAt_angularMomentum`,
  `TauCeti.periodic_of_forall_hasDerivAt_angularMomentum`: every solution of Hamilton's equations
  for `L` is a rotation, so it is periodic with period `2π`.
* `TauCeti.hasDerivAt_circleExp_mul_smul_comp_mul`: the rotations commute with the Hamiltonian
  flow of every rotation-invariant Hamiltonian, so rotating a solution adds a multiple of `X_L` to
  its velocity.
* `TauCeti.hamiltonianTorusData_angularMomentum`,
  `TauCeti.hamiltonianTorusData_angularMomentum_puncturedPhaseSpace`: the rotations are a
  Hamiltonian circle action with moment map the angular momentum, on the phase space and on the
  punctured phase space.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 20 (Noether's theorem and the rotations of the plane).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 11 (momentum maps, with the angular momentum as the
  momentum map of rotations).
-/

public section

noncomputable section

open Complex
open scoped Manifold InnerProductSpace ComplexConjugate ContDiff

namespace TauCeti

/-- The angular momentum `q₁ p₂ - q₂ p₁` of a planar particle, with the plane identified with
`ℂ`, is the imaginary part of `conj q * p`. -/
theorem angularMomentum_one_I (q p : ℂ) : angularMomentum 1 I (q, p) = (conj q * p).im := by
  simp only [angularMomentum_apply, Complex.inner, mul_im, mul_re, one_re, one_im, I_re, I_im,
    conj_re, conj_im]
  ring

/-- Rotations preserve the planar angular momentum. -/
@[simp]
theorem angularMomentum_circle_smul (z : Circle) (x : ℂ × ℂ) :
    angularMomentum 1 I (z • x) = angularMomentum 1 I x := by
  obtain ⟨q, p⟩ := x
  have hz : conj (z : ℂ) * z = 1 := by
    rw [conj_mul', Circle.norm_coe, ofReal_one, one_pow]
  simp only [Circle.smul_def, Prod.smul_mk, smul_eq_mul, angularMomentum_one_I]
  rw [map_mul, mul_mul_mul_comm, hz, one_mul]

/-- **The planar angular momentum generates the rotations.** With the plane identified with `ℂ`,
the Hamiltonian vector field of `L(q, p) = q₁ p₂ - q₂ p₁` at `(q, p)` is `(i q, i p)`. -/
theorem stdSymplecticForm_hamiltonianVectorField_angularMomentum_one_I (x : ℂ × ℂ) :
    (stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I) x =
      (I * x.1, I * x.2) := by
  rw [stdSymplecticForm_hamiltonianVectorField_angularMomentum,
    inner_one_smul_I_sub_inner_I_smul_one, inner_one_smul_I_sub_inner_I_smul_one]

/-- **The Hamiltonian flow of the angular momentum is the rotation of the plane.** The rotation
`t ↦ exp (t i) • x` of a point of phase space by the angle `t` is the integral curve through `x` of
the Hamiltonian vector field of the angular momentum. -/
theorem hasDerivAt_circleExp_smul_hamiltonianVectorField_angularMomentum (x : ℂ × ℂ) (t : ℝ) :
    HasDerivAt (fun s ↦ Circle.exp s • x)
      ((stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I)
        (Circle.exp t • x)) t := by
  rw [stdSymplecticForm_hamiltonianVectorField_angularMomentum_one_I]
  -- The scalar action of the circle is the action of the complex number `exp (t i)`.
  simp only [Circle.smul_def]
  refine ((hasDerivAt_coe_circleExp t).smul_const x).congr_deriv ?_
  obtain ⟨q, p⟩ := x
  simp only [Prod.smul_mk, smul_eq_mul, mul_assoc]

/-- **Rotations and the flow of a rotation-invariant Hamiltonian.** Let `H` be invariant under the
rotations, and let the curve `γ` move at time `b t` with velocity `α X_H + β X_L`, a fixed
combination of the Hamiltonian vector fields of `H` and of the angular momentum `L`. Then the
rotated and rescaled curve `s ↦ exp (a s i) • γ(b s)` moves at time `t` with velocity
`(b α) X_H + (a + b β) X_L`: rotating by the angle `a s` adds `a X_L`, because the rotations
commute with both fields. -/
theorem hasDerivAt_circleExp_mul_smul_comp_mul {H : ℂ × ℂ → ℝ}
    (hH : ∀ (z : Circle) y, H (z • y) = H y) {γ : ℝ → ℂ × ℂ} {α β a b t : ℝ}
    (hγ : HasDerivAt γ ((α • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField H (γ (b * t)) +
      β • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I)
        (γ (b * t))) : ℂ × ℂ) (b * t)) :
    HasDerivAt (fun s ↦ Circle.exp (a * s) • γ (b * s))
      ((b * α) • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField H
          (Circle.exp (a * t) • γ (b * t)) +
        (a + b * β) • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I)
          (Circle.exp (a * t) • γ (b * t))) t := by
  have he : HasDerivAt (fun s : ℝ ↦ ((Circle.exp (a * s) : Circle) : ℂ))
      ((a : ℂ) * (I * Circle.exp (a * t))) t := by
    exact ((hasDerivAt_coe_circleExp (a * t)).scomp t
      (((hasDerivAt_id' t).const_mul a).congr_deriv (mul_one a))).congr_deriv
        (Complex.real_smul ..)
  have hb : HasDerivAt (fun s ↦ γ (b * s))
      (b • (α • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField H (γ (b * t)) +
        β • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I)
          (γ (b * t)))) t := by
    have h := hγ.scomp t (((hasDerivAt_id' t).const_mul b).congr_deriv (mul_one b))
    exact h
  -- The rotations commute with `X_H` by invariance, and with `X_L = (i q, i p)` by linearity.
  have hX : (stdSymplecticForm (V := ℂ)).hamiltonianVectorField H
      (Circle.exp (a * t) • γ (b * t)) =
        Circle.exp (a * t) • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField H (γ (b * t)) :=
    stdSymplecticForm_hamiltonianVectorField_smul (hH _) _
  rw [hX, stdSymplecticForm_hamiltonianVectorField_angularMomentum_one_I]
  have hfun : (fun s ↦ Circle.exp (a * s) • γ (b * s)) =
      fun s ↦ ((Circle.exp (a * s) : Circle) : ℂ) • γ (b * s) :=
    funext fun s ↦ Circle.smul_def _ _
  rw [hfun]
  refine (he.smul hb).congr_deriv ?_
  rw [stdSymplecticForm_hamiltonianVectorField_angularMomentum_one_I]
  generalize (stdSymplecticForm (V := ℂ)).hamiltonianVectorField H (γ (b * t)) = X
  obtain ⟨q, p⟩ := γ (b * t)
  obtain ⟨X₁, X₂⟩ := X
  ext <;> simp [Circle.smul_def] <;> ring

/-- **Every Hamiltonian motion of the angular momentum is a rotation.** A curve `γ` solving
Hamilton's equations for the angular momentum `L` at all times is `t ↦ exp (t i) • γ 0`. -/
theorem eq_circleExp_smul_of_hasDerivAt_angularMomentum {γ : ℝ → ℂ × ℂ}
    (hγ : ∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I) (γ t)) t)
    (t : ℝ) : γ t = Circle.exp t • γ 0 := by
  -- Rotating back by the angle `s` gives a curve with velocity `(-1 + 1) X_L = 0`.
  have hd (s : ℝ) : HasDerivAt (fun s ↦ Circle.exp (-1 * s) • γ (1 * s)) 0 s := by
    have h := hasDerivAt_circleExp_mul_smul_comp_mul (angularMomentum_circle_smul) (α := 0)
      (β := 1) (a := -1) (b := 1) (t := s) (by simpa using hγ s)
    simpa using h
  have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0
  simp only [neg_one_mul, one_mul, neg_zero, Circle.exp_zero, one_smul] at hc
  rw [← hc, smul_smul, ← Circle.exp_add, add_neg_cancel, Circle.exp_zero, one_smul]

/-- **The angular momentum is an action variable.** Every curve solving Hamilton's equations for
the angular momentum at all times is periodic with period `2π`. -/
theorem periodic_of_forall_hasDerivAt_angularMomentum {γ : ℝ → ℂ × ℂ}
    (hγ : ∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I) (γ t)) t) :
    Function.Periodic γ (2 * Real.pi) := fun t ↦ by
  rw [eq_circleExp_smul_of_hasDerivAt_angularMomentum hγ,
    eq_circleExp_smul_of_hasDerivAt_angularMomentum hγ t, Circle.periodic_exp]

/-- **The quadratic moment map of the rotations.** For an element `ξ` of the Lie algebra of the
circle, the quadratic moment map of the rotation action on `ℂ × ℂ` is the angular momentum
multiplied by the imaginary part of `ι_* ξ`, the image of `ξ` under the derivative of the inclusion
`ι : Circle → ℂ`. -/
theorem stdSymplecticForm_linearActionMomentMap_circle_apply (x : ℂ × ℂ)
    (ξ : GroupLieAlgebra (𝓡 1) Circle) :
    stdSymplecticForm.linearActionMomentMap (𝓡 1) Circle x ξ =
      (mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1 ξ).im * angularMomentum 1 I x := by
  obtain ⟨q, p⟩ := x
  rw [SymplecticForm.linearActionMomentMap_apply, fundamentalLinearMap_circle_apply,
    angularMomentum_one_I]
  generalize mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1 ξ = ζ
  simp only [stdSymplecticForm_apply, Prod.smul_mk, smul_eq_mul, Complex.inner, mul_re, mul_im,
    conj_re, conj_im]
  ring

/-- **The angular momentum generates the rotations.** Along the generator of `t ↦ exp (t i)`, the
velocity of `Circle.exp` at `0`, the quadratic moment map of the rotations is the angular
momentum. -/
theorem stdSymplecticForm_linearActionMomentMap_circle_apply_mfderiv_circleExp (x : ℂ × ℂ) :
    stdSymplecticForm.linearActionMomentMap (𝓡 1) Circle x
      (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ)) = angularMomentum 1 I x := by
  refine (stdSymplecticForm_linearActionMomentMap_circle_apply x _).trans ?_
  rw [mvfderiv_coe_mfderiv_circleExp, I_im, one_mul]

/-- **The rotational moment map.** The rotations of the planar phase space are a Hamiltonian
circle action whose moment map is the angular momentum: `x ↦ L(x) Im (ι_* ·)`, where `ι_* ξ` is the
image of `ξ` under the derivative of the inclusion `ι : Circle → ℂ`. -/
theorem hamiltonianTorusData_angularMomentum :
    (stdSymplecticForm (V := ℂ)).constSmooth.HamiltonianTorusData fun x ↦
      angularMomentum 1 I x •
        (imCLM ∘L mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1).toLinearMap := by
  have h : (fun x ↦ angularMomentum 1 I x •
      (imCLM ∘L mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1).toLinearMap) =
      stdSymplecticForm.linearActionMomentMap (𝓡 1) Circle := by
    ext x ξ
    rw [stdSymplecticForm_linearActionMomentMap_circle_apply, LinearMap.smul_apply, smul_eq_mul,
      mul_comm, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, imCLM_apply]
  rw [h]
  exact SymplecticForm.hamiltonianTorusData_linearActionMomentMap (I := 𝓡 1) (T := Circle)
    stdSymplecticForm fun g u w ↦ stdSymplecticForm_smul (V := ℂ) g u w

/-- **The rotational moment map on the punctured phase space.** On the punctured phase space
`{(q, p) | q ≠ 0}` of a planar particle, with the standard symplectic form restricted from `ℂ × ℂ`,
the rotations are a Hamiltonian circle action whose moment map is the angular momentum:
`x ↦ L(x) Im (ι_* ·)`, where `ι_* ξ` is the image of `ξ` under the derivative of the inclusion
`ι : Circle → ℂ`. -/
theorem hamiltonianTorusData_angularMomentum_puncturedPhaseSpace :
    SmoothTwoForm.HamiltonianTorusData
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace ℂ → ℂ × ℂ) contMDiff_subtypeVal
        (stdSymplecticForm (V := ℂ)).constSmooth) fun x ↦
      angularMomentum 1 I (x : ℂ × ℂ) •
        (imCLM ∘L mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1).toLinearMap :=
  hamiltonianTorusData_angularMomentum.mpullback contMDiff_subtypeVal
    coe_smul_puncturedPhaseSpace

end TauCeti
