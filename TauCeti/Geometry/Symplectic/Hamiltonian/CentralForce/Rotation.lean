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
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Complex.Inner
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

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

/-! ### The rotations of the punctured phase space -/

section PuncturedPhaseSpace

variable {V G : Type*} [NormedAddCommGroup V] [Group G] [DistribMulAction G V]

/-- A group acting linearly on `V` acts on the punctured phase space `{(q, p) | q ≠ 0}` by acting
on positions and momenta alike: for instance, a rotation keeps the particle away from the centre
of force. -/
instance : MulAction G (puncturedPhaseSpace V) where
  smul g x := ⟨g • (x : V × V), mem_puncturedPhaseSpace.2 <| by
    simpa [smul_ne_zero_iff_ne] using mem_puncturedPhaseSpace.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : V × V))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : V × V))

@[simp]
theorem coe_smul_puncturedPhaseSpace (g : G) (x : puncturedPhaseSpace V) :
    ((g • x : puncturedPhaseSpace V) : V × V) = g • (x : V × V) :=
  (rfl)

variable [NormedSpace ℝ V] {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace G] [ChartedSpace H G]
  {n : ℕ∞ω}

/-- A group acting smoothly and linearly on `V` acts smoothly on the punctured phase space. -/
instance [ContMDiffSMul I 𝓘(ℝ, V) n G V] :
    ContMDiffSMul I 𝓘(ℝ, V × V) n G (puncturedPhaseSpace V) where
  contMDiff_smul := by
    have hx : ContMDiff (I.prod 𝓘(ℝ, V × V)) 𝓘(ℝ, V × V) n
        fun p : G × puncturedPhaseSpace V ↦ (p.2 : V × V) :=
      contMDiff_subtype_val.comp contMDiff_snd
    have hsmul := contMDiff_smul (I := I) (I' := 𝓘(ℝ, V)) (n := n) (G := G) (M := V)
    have hfst : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, V) n Prod.fst := contDiff_fst.contMDiff
    have hsnd : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, V) n Prod.snd := contDiff_snd.contMDiff
    exact (ContMDiff.subtypeVal_comp_iff (puncturedPhaseSpace V) _).1 <|
      (hsmul.comp (contMDiff_fst.prodMk (hfst.comp hx))).prodMk_space
        (hsmul.comp (contMDiff_fst.prodMk (hsnd.comp hx)))

/-- Each element of a group acting smoothly and linearly on `V` acts smoothly on the punctured
phase space. -/
instance [ContMDiffConstSMul 𝓘(ℝ, V) n G V] :
    ContMDiffConstSMul 𝓘(ℝ, V × V) n G (puncturedPhaseSpace V) := by
  refine ⟨fun g ↦ (ContMDiff.subtypeVal_comp_iff (puncturedPhaseSpace V) _).1 ?_⟩
  have hsmul := ContMDiffConstSMul.contMDiff_const_smul (I := 𝓘(ℝ, V)) (n := n) (M := V) g
  have hfst : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, V) n Prod.fst := contDiff_fst.contMDiff
  have hsnd : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, V) n Prod.snd := contDiff_snd.contMDiff
  exact (hsmul.comp (hfst.comp contMDiff_subtype_val)).prodMk_space
    (hsmul.comp (hsnd.comp contMDiff_subtype_val))

end PuncturedPhaseSpace

/-- **The rotational moment map on the punctured phase space.** On the punctured phase space
`{(q, p) | q ≠ 0}` of a planar particle, with the standard symplectic form restricted from `ℂ × ℂ`,
the rotations are a Hamiltonian circle action whose moment map is the angular momentum:
`x ↦ L(x) Im (ι_* ·)`, where `ι_* ξ` is the image of `ξ` under the derivative of the inclusion
`ι : Circle → ℂ`. -/
theorem hamiltonianTorusData_angularMomentum_puncturedPhaseSpace :
    SmoothTwoForm.HamiltonianTorusData
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace ℂ → ℂ × ℂ) contMDiff_subtype_val
        (stdSymplecticForm (V := ℂ)).constSmooth) fun x ↦
      angularMomentum 1 I (x : ℂ × ℂ) •
        (imCLM ∘L mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1).toLinearMap :=
  hamiltonianTorusData_angularMomentum.mpullback contMDiff_subtype_val
    coe_smul_puncturedPhaseSpace

end TauCeti
