/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Linear
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import TauCeti.Topology.Algebra.ProperAction.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Isometry
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.Complex.Inner
import TauCeti.Analysis.InnerProductSpace.TwoDim
import TauCeti.Geometry.Euclidean.Circle

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
  (`TauCeti.hamiltonianTorusData_angularMomentum_puncturedPhaseSpace`). The rotations act freely
  (`TauCeti.stabilizer_circle_puncturedPhaseSpace_eq_bot`) and properly on it. Two of its states
  differ by a rotation exactly when they have the same radius, radial momentum and angular
  momentum (`TauCeti.exists_circle_smul_eq_iff`), since the rotations preserve the radius and the
  radial momentum (`TauCeti.radialProjection_circle_smul`): `conj q * p` has real part `⟪q, p⟫`
  and imaginary part `L`, so the rotation by `q / q'` carries `(q', p')` to `(q, p)`.

The conservation law `{H, L} = 0` for a central-force Hamiltonian `H` is
`TauCeti.stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum`.

The same holds in any real inner product plane `V`, without choosing an identification with `ℂ`.
For a positively oriented orthonormal basis `b` of an oriented plane, with quarter turn `J` and
rotations `R_t` (`Orientation.rotation`):

* the angular momentum is the area form, `L(q, p) = ω(q, p)`
  (`TauCeti.angularMomentum_eq_areaForm`), so the rotations preserve it
  (`TauCeti.angularMomentum_rotation`);
* the Hamiltonian vector field of `L` is `(J q, J p)`
  (`TauCeti.stdSymplecticForm_hamiltonianVectorField_angularMomentum_eq_rightAngleRotation`), its
  flow is `t ↦ (R_t q, R_t p)`
  (`TauCeti.hasDerivAt_rotation_hamiltonianVectorField_angularMomentum`), and every solution of
  Hamilton's equations for `L` is such a rotation of its initial state
  (`TauCeti.eq_rotation_of_forall_hasDerivAt_angularMomentum`). So every such solution is
  `2π`-periodic (`TauCeti.periodic_of_forall_hasDerivAt_angularMomentum`).

## Main results

* `TauCeti.angularMomentum_circle_smul`: rotations preserve `L`.
* `TauCeti.stdSymplecticForm_hamiltonianVectorField_angularMomentum_one_I`: the Hamiltonian
  vector field of `L` is `(q, p) ↦ (i q, i p)`.
* `TauCeti.hasDerivAt_circleExp_smul_hamiltonianVectorField_angularMomentum`: the Hamiltonian
  flow of `L` is the rotation of the plane.
* `TauCeti.eq_circleExp_smul_of_hasDerivAt_angularMomentum`: every solution of Hamilton's
  equations for `L` is a rotation `t ↦ exp (t i) • γ 0`.
* `TauCeti.hasDerivAt_circleExp_mul_smul_comp_mul`: the rotations commute with the Hamiltonian
  flow of every rotation-invariant Hamiltonian, so rotating a solution adds a multiple of `X_L` to
  its velocity.
* `TauCeti.hamiltonianTorusData_angularMomentum`,
  `TauCeti.hamiltonianTorusData_angularMomentum_puncturedPhaseSpace`: the rotations are a
  Hamiltonian circle action with moment map the angular momentum, on the phase space and on the
  punctured phase space.
* `TauCeti.exists_circle_smul_eq_iff`: the rotation orbits of the punctured phase space are the
  common levels of the radius, the radial momentum and the angular momentum.
* `TauCeti.eq_rotation_of_forall_hasDerivAt_angularMomentum`,
  `TauCeti.periodic_of_forall_hasDerivAt_angularMomentum`: in an oriented inner product plane, the
  Hamiltonian flow of `L` is the rotation of the plane, so it is `2π`-periodic.

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

/-- Rotations preserve the radius and the radial momentum. -/
@[simp]
theorem radialProjection_circle_smul (g : Circle) (x : ℂ × ℂ) :
    radialProjection (g • x) = radialProjection x := by
  obtain ⟨q, p⟩ := x
  have hq : ‖(g : ℂ) * q‖ = ‖q‖ := by simp
  have hqp : ⟪(g : ℂ) * q, (g : ℂ) * p⟫_ℝ = ⟪q, p⟫_ℝ := by
    simpa [rotation_apply] using (rotation g).inner_map_map q p
  simp only [Circle.smul_def, Prod.smul_mk, smul_eq_mul, radialProjection_apply, hq, hqp]

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
      ((a : ℂ) * (I * Circle.exp (a * t))) t :=
    ((hasDerivAt_coe_circleExp (a * t)).scomp t
      (((hasDerivAt_id' t).const_mul a).congr_deriv (mul_one a))).congr_deriv
        (Complex.real_smul ..)
  have hb : HasDerivAt (fun s ↦ γ (b * s))
      (b • (α • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField H (γ (b * t)) +
        β • (stdSymplecticForm (V := ℂ)).hamiltonianVectorField (angularMomentum 1 I)
          (γ (b * t)))) t := by
    simpa only [Function.comp_def] using
      hγ.scomp t (((hasDerivAt_id' t).const_mul b).congr_deriv (mul_one b))
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

/-- The rotations act properly on the punctured planar phase space, as the circle is compact. -/
instance : ProperSMul Circle (puncturedPhaseSpace ℂ) :=
  properSMul_of_compactSpace _ _

/-- The rotations act freely on the punctured planar phase space: a rotation fixing a state of
nonzero position is the identity. -/
theorem stabilizer_circle_puncturedPhaseSpace_eq_bot (x : puncturedPhaseSpace ℂ) :
    MulAction.stabilizer Circle x = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  have h : (z : ℂ) * (x : ℂ × ℂ).1 = (x : ℂ × ℂ).1 :=
    congrArg (fun y : puncturedPhaseSpace ℂ ↦ (y : ℂ × ℂ).1) (MulAction.mem_stabilizer_iff.1 hz)
  exact Circle.coe_inj.1 (mul_right_cancel₀ (mem_puncturedPhaseSpace.1 x.property)
    (h.trans (one_mul _).symm))

/-- **The rotation orbits are the common levels of `(r, p_r, L)`.** Two states of the punctured
planar phase space differ by a rotation exactly when they have the same radius, radial momentum
and angular momentum. -/
theorem exists_circle_smul_eq_iff {x x' : puncturedPhaseSpace ℂ} :
    (∃ g : Circle, g • x' = x) ↔
      radialProjection (x : ℂ × ℂ) = radialProjection (x' : ℂ × ℂ) ∧
        angularMomentum 1 I (x : ℂ × ℂ) = angularMomentum 1 I (x' : ℂ × ℂ) := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun ⟨hr, hL⟩ ↦ ?_⟩
  · rw [← hg, coe_smul_puncturedPhaseSpace]
    exact ⟨radialProjection_circle_smul g _, angularMomentum_circle_smul g _⟩
  obtain ⟨⟨q, p⟩, hq⟩ := x
  obtain ⟨⟨q', p'⟩, hq'⟩ := x'
  rw [mem_puncturedPhaseSpace] at hq hq'
  simp only [radialProjection_apply, Prod.mk.injEq] at hr
  obtain ⟨hn, hrad⟩ := hr
  have hn₀ : ‖q'‖ ≠ 0 := norm_ne_zero_iff.2 hq'
  rw [hn, div_left_inj₀ hn₀] at hrad
  rw [angularMomentum_one_I, angularMomentum_one_I] at hL
  -- `conj q * p` is determined by `⟪q, p⟫ = Re (conj q * p)` and `L = Im (conj q * p)`.
  have hc : conj q * p = conj q' * p' := Complex.ext (by
    simpa [Complex.inner, mul_re, mul_comm] using hrad) hL
  have hg : ‖q / q'‖ = 1 := by rw [norm_div, hn, div_self hn₀]
  obtain ⟨g, hgq⟩ : ∃ g : Circle, (g : ℂ) * q' = q :=
    ⟨⟨q / q', by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hg⟩,
      div_mul_cancel₀ q hq'⟩
  refine ⟨g, Subtype.ext ?_⟩
  -- The rotation by `g = q / q'` acts on positions and momenta by multiplication by `g`.
  simp only [coe_smul_puncturedPhaseSpace, Circle.smul_def, Prod.smul_mk, smul_eq_mul, hgq,
    Prod.mk.injEq, true_and]
  -- `conj q * (g p') = |g|² conj q' * p' = conj q * p`, and `q ≠ 0`.
  have hconj : conj (g : ℂ) * g = 1 := by
    rw [conj_mul', Circle.norm_coe, ofReal_one, one_pow]
  refine mul_left_cancel₀ (map_ne_zero (starRingEnd ℂ) |>.2 hq) ?_
  rw [hc, ← hgq, map_mul]
  linear_combination (conj q' * p') * hconj

/-! ### Rotations of an oriented plane -/

section OrientedPlane

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V)

section Fact

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
  simp only [angularMomentum_eq_areaForm b hb]
  exact o.areaForm_comp_linearIsometryEquiv _ (by simp [o.det_rotation]) _ _

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
    -- The quarter turn commutes with the rotations.
    ext <;> simp [o.linearIsometryEquiv_comp_rightAngleRotation, o.det_rotation]
  have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hδ s).differentiableAt)
    (fun s ↦ (hδ s).deriv) t 0
  simp only [neg_zero, Real.Angle.coe_zero, o.rotation_zero, LinearIsometryEquiv.coe_refl, id_eq,
    Prod.mk.injEq] at hconst
  rw [← hconst.1, ← hconst.2]
  simp only [Real.Angle.coe_neg, ← o.rotation_symm, LinearIsometryEquiv.apply_symm_apply]

end Fact

/-- **The angular action is an action variable.** In the plane of an orthonormal basis, every
solution of Hamilton's equations for the angular momentum, defined for all time, is `2π`-periodic.
-/
theorem periodic_of_forall_hasDerivAt_angularMomentum [FiniteDimensional ℝ V] {γ : ℝ → V × V}
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (angularMomentum (b 0) (b 1)) (γ t)) t) :
    Function.Periodic γ (2 * Real.pi) := fun t ↦ by
  have : Fact (finrank ℝ V = 2) := ⟨by simp [finrank_eq_card_basis b.toBasis]⟩
  rw [eq_rotation_of_forall_hasDerivAt_angularMomentum b rfl hγ,
    eq_rotation_of_forall_hasDerivAt_angularMomentum b rfl hγ t,
    Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]

end OrientedPlane

end TauCeti
