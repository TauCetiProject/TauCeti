/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Linear
import Mathlib.Analysis.Complex.Isometry

/-!
# The rotational moment map of planar central forces

Identify the configuration plane `ℝ²` with `ℂ`, so that the phase space of a planar particle is
`ℂ × ℂ` with positions `q` and momenta `p`, standard symplectic form `ω₀ = dq₁ ∧ dp₁ + dq₂ ∧ dp₂`
and angular momentum `L(q, p) = q₁ p₂ - q₂ p₁` (`TauCeti.angularMomentum 1 I`). The circle group
`Circle ⊆ ℂ` acts on the phase space by rotating positions and momenta alike,
`z • (q, p) = (z q, z p)`.

This action is the symmetry behind the conservation of angular momentum:

* every rotation is a linear symplectomorphism of `(ℂ × ℂ, ω₀)`
  (`TauCeti.stdSymplecticForm_circle_smul`) and preserves the angular momentum and every
  central-force Hamiltonian `‖p‖² / (2m) + U(‖q‖)` (`TauCeti.angularMomentum_circle_smul`,
  `TauCeti.centralForceHamiltonian_circle_smul`);
* the rotation `t ↦ exp (t i) • x` by the angle `t` is the integral curve of the Hamiltonian
  vector field of `L` through `x` (`TauCeti.hasDerivAt_circleExp_smul`): the Hamiltonian flow of
  the angular momentum is the rotation of the plane, with period `2π`;
* the angular momentum is the **rotational moment map**. For an element `ξ` of the Lie algebra of
  the circle, with image `ι_* ξ ∈ ℂ` under the derivative of the inclusion `ι : Circle → ℂ`, the
  quadratic moment map of the linear action is `μ(x)(ξ) = Im (ι_* ξ) L(x)`
  (`TauCeti.linearActionMomentMap_circle_apply`). So `x ↦ L(x) Im (ι_* ·)` is a
  coadjoint-equivariant group-level moment map (`TauCeti.isEquivariantMomentMap_angularMomentum`),
  and its component along the generator of `t ↦ exp (t i)` is `L` itself
  (`TauCeti.linearActionMomentMap_circle_apply_mfderiv_circleExp`).

The conservation law `{H, L} = 0` for a central-force Hamiltonian `H` is
`TauCeti.stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum`.

## Main results

* `TauCeti.stdSymplecticForm_circle_smul`: rotations are symplectic.
* `TauCeti.angularMomentum_circle_smul`, `TauCeti.centralForceHamiltonian_circle_smul`:
  rotations preserve `L` and `H`.
* `TauCeti.hasDerivAt_circleExp_smul`: the Hamiltonian flow of `L` is the rotation of the plane.
* `TauCeti.isEquivariantMomentMap_angularMomentum`: the angular momentum is the equivariant
  moment map of the rotations.

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
open scoped Manifold InnerProductSpace ComplexConjugate

namespace TauCeti

/-- The angular momentum `q₁ p₂ - q₂ p₁` of a planar particle, with the plane identified with
`ℂ`, is the imaginary part of `conj q * p`. -/
theorem angularMomentum_one_I (q p : ℂ) : angularMomentum 1 I (q, p) = (conj q * p).im := by
  simp only [angularMomentum_apply, Complex.inner, mul_im, mul_re, one_re, one_im, I_re, I_im,
    conj_re, conj_im]
  ring

/-- **Rotations are symplectic.** Rotating positions and momenta by the same element of the circle
preserves the standard symplectic form of `ℂ × ℂ`. -/
theorem stdSymplecticForm_circle_smul (z : Circle) (x y : ℂ × ℂ) :
    stdSymplecticForm (z • x) (z • y) = stdSymplecticForm x y := by
  -- Multiplication by `z` is the rotation `rotation z`, a linear isometry of `ℂ`.
  have h (a b : ℂ) : ⟪(z : ℂ) * a, (z : ℂ) * b⟫_ℝ = ⟪a, b⟫_ℝ := by
    simpa only [rotation_apply] using (rotation z).inner_map_map a b
  simp only [stdSymplecticForm_apply, Circle.smul_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    h]

/-- Rotations preserve the planar angular momentum. -/
@[simp]
theorem angularMomentum_circle_smul (z : Circle) (x : ℂ × ℂ) :
    angularMomentum 1 I (z • x) = angularMomentum 1 I x := by
  obtain ⟨q, p⟩ := x
  have hz : conj (z : ℂ) * z = 1 := by
    rw [conj_mul', Circle.norm_coe, ofReal_one, one_pow]
  simp only [Circle.smul_def, Prod.smul_mk, smul_eq_mul, angularMomentum_one_I]
  rw [map_mul, mul_mul_mul_comm, hz, one_mul]

/-- Rotations preserve every central-force Hamiltonian `‖p‖² / (2m) + U(‖q‖)`, on the phase space
`V × V` of any complex normed space `V`, where the circle acts by `z • (q, p) = (z q, z p)`. -/
@[simp]
theorem centralForceHamiltonian_circle_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (m : ℝ) (U : ℝ → ℝ) (z : Circle) (x : V × V) :
    centralForceHamiltonian m U (z • x) = centralForceHamiltonian m U x := by
  obtain ⟨q, p⟩ := x
  simp only [Circle.smul_def, Prod.smul_mk, centralForceHamiltonian_apply, norm_smul,
    Circle.norm_coe, one_mul]

/-- The infinitesimal rotation `z ↦ ⟪z, 1⟫ i - ⟪z, i⟫` of the plane `ℂ` is multiplication by `i`. -/
private theorem inner_one_smul_I_sub_inner_I_smul_one (z : ℂ) :
    ⟪z, 1⟫_ℝ • I - ⟪z, I⟫_ℝ • (1 : ℂ) = I * z := by
  apply Complex.ext <;> simp [Complex.inner]

/-- **The Hamiltonian flow of the angular momentum is the rotation of the plane.** The rotation
`t ↦ exp (t i) • x` of a point of phase space by the angle `t` is the integral curve through `x` of
the Hamiltonian vector field of the angular momentum. -/
theorem hasDerivAt_circleExp_smul (x : ℂ × ℂ) (t : ℝ) :
    HasDerivAt (fun s ↦ Circle.exp s • x)
      ((stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I)
        (Circle.exp t • x)) t := by
  rw [stdSymplecticForm_hamiltonianVectorField_angularMomentum,
    inner_one_smul_I_sub_inner_I_smul_one, inner_one_smul_I_sub_inner_I_smul_one]
  -- The scalar action of the circle is the action of the complex number `exp (t i)`.
  refine ((hasDerivAt_coe_circleExp t).smul_const x).congr_deriv ?_
  obtain ⟨q, p⟩ := x
  simp only [Circle.smul_def, Prod.smul_mk, smul_eq_mul, mul_assoc]

/-- **The quadratic moment map of the rotations.** For an element `ξ` of the Lie algebra of the
circle, the quadratic moment map of the rotation action on `ℂ × ℂ` is the angular momentum
multiplied by the imaginary part of `ι_* ξ`, the image of `ξ` under the derivative of the inclusion
`ι : Circle → ℂ`. -/
theorem linearActionMomentMap_circle_apply (x : ℂ × ℂ) (ξ : GroupLieAlgebra (𝓡 1) Circle) :
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
theorem linearActionMomentMap_circle_apply_mfderiv_circleExp (x : ℂ × ℂ) :
    stdSymplecticForm.linearActionMomentMap (𝓡 1) Circle x
      (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ)) = angularMomentum 1 I x := by
  refine (linearActionMomentMap_circle_apply x _).trans ?_
  rw [mvfderiv_coe_mfderiv_circleExp, I_im, one_mul]

/-- **The rotational moment map.** The angular momentum is a coadjoint-equivariant group-level
moment map of the rotations of the planar phase space: `x ↦ L(x) Im (ι_* ·)`, where `ι_* ξ` is the
image of `ξ` under the derivative of the inclusion `ι : Circle → ℂ`. -/
theorem isEquivariantMomentMap_angularMomentum :
    (stdSymplecticForm (V := ℂ)).constSmooth.IsEquivariantMomentMap fun x ↦
      angularMomentum 1 I x •
        (imCLM ∘L mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1).toLinearMap := by
  have h : (fun x ↦ angularMomentum 1 I x •
      (imCLM ∘L mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1).toLinearMap) =
      stdSymplecticForm.linearActionMomentMap (𝓡 1) Circle := by
    ext x ξ
    rw [linearActionMomentMap_circle_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, imCLM_apply]
  rw [h]
  exact SymplecticForm.isEquivariantMomentMap_linearActionMomentMap (I := 𝓡 1) (G := Circle)
    stdSymplecticForm fun g u w ↦ stdSymplecticForm_circle_smul g u w

end TauCeti
