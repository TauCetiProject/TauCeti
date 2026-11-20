/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Critical
public import TauCeti.Geometry.Symplectic.Hamiltonian.Complete
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible

import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce

/-!
# The spherical pendulum is a completely integrable system

The phase space `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` of the spherical pendulum is a smooth
four-dimensional submanifold of `ℝ³ × ℝ³`
(`TauCeti.isSmoothEmbedding_coe_sphericalPendulumPhaseSpace`). This file gives it the restriction
of the standard symplectic form `ω₀((a, b), (a', b')) = ⟪a, b'⟫ - ⟪b, a'⟫` of `ℝ³ × ℝ³`
(`TauCeti.sphericalPendulumSymplecticForm`), and shows that the energy `H(q, p) = ‖p‖² / 2 + q₃`
and the vertical angular momentum `J(q, p) = q₁ p₂ - q₂ p₁` form a completely integrable system
for it.

The tangent space of the phase space at `(q, p)` is the kernel of the differential of the
constraint map `g(q, p) = (‖q‖², ⟪q, p⟫)`: the vectors `(a, b)` with `⟪q, a⟫ = 0` and
`⟪q, b⟫ + ⟪a, p⟫ = 0`. This subspace is symplectic for `ω₀`
(`TauCeti.isSymplectic_ker_fderiv_sphericalPendulumConstraint`): if `(a, b)` is tangent and
`ω₀`-orthogonal to every tangent vector, pairing it with the tangent vector `(0, a)` gives
`‖a‖² = 0`, and then pairing it with the tangent vector `(b, -⟪b, p⟫ q)` gives `‖b‖² = 0`. So the
inclusion of the phase space is a symplectic submanifold embedding
(`TauCeti.isSymplecticSubmanifoldEmbedding_coe_sphericalPendulumPhaseSpace`), and the restricted
form is symplectic (`TauCeti.isSymplectic_sphericalPendulumSymplecticForm`).

The ambient Hamiltonian vector field of `H`, `(p, -e₃)`, is not tangent to the phase space, so the
dynamics of the pendulum is not the restriction of the ambient dynamics. The ambient Hamiltonian
vector field of `J` is the infinitesimal rotation `(R q, R p)` about the vertical axis, with
`R z = (-z₂, z₁, 0)`, and it is tangent to the phase space
(`TauCeti.hamiltonianVectorField_angularMomentum_mem_ker_fderiv_sphericalPendulumConstraint`). So
the Hamiltonian vector field of the restriction of `J` is this rotation
(`TauCeti.mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_angularMomentum`), and
the bracket of the restrictions of `H` and `J` is the ambient bracket
`{H, J}(q, p) = dH (R q, R p) = ⟪p, R p⟫ + (R q)₃ = 0`
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_comp_of_mem_range`,
`TauCeti.stdSymplecticForm_poissonBracket_sphericalPendulumHamiltonian_angularMomentum`,
`TauCeti.poissonBracket_sphericalPendulumHamiltonian_angularMomentum_comp_subtypeVal`).

The critical points of `F = (H, J)` on the phase space all have vertical momentum `p₃ = 0`
(`TauCeti.not_isRegularPoint_sphericalPendulumEnergyMomentum_iff`), and the points with `p₃ ≠ 0`
are dense: away from the poles the vertical momentum is changed by moving `p` along the tangent
vector `e₃ - q₃ q`, and the poles are limits of points away from them. So the regular points are
dense (`TauCeti.dense_setOf_isRegularPoint_sphericalPendulumEnergyMomentum`), and `(H, J)` is a
completely integrable system on the phase space
(`TauCeti.isIntegrableSystem_sphericalPendulumEnergyMomentum`). Since the energy is proper, so is
`F` (`TauCeti.isProperMap_sphericalPendulumEnergyMomentum`), and the Hamiltonian vector fields
of `H` and `J` on the phase space are complete
(`isCompleteVectorField_hamiltonianVectorField_sphericalPendulumHamiltonian_comp_subtypeVal`,
`TauCeti.isCompleteVectorField_hamiltonianVectorField_angularMomentum_sphericalPendulumPhaseSpace`).

Identifying covectors on the sphere with tangent vectors by the round metric, the restriction of
`ω₀` is the canonical symplectic form of the cotangent bundle of the sphere; that comparison is not
made here.

## Main declarations

* `TauCeti.sphericalPendulumSymplecticForm`: the restriction of `ω₀` to the phase space.
* `TauCeti.isSymplectic_sphericalPendulumSymplecticForm`: it is symplectic.
* `TauCeti.mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_angularMomentum`: the
  Hamiltonian vector field of `J` on the phase space is the rotation `(R q, R p)`.
* `TauCeti.poissonBracket_sphericalPendulumHamiltonian_angularMomentum_comp_subtypeVal`:
  `{H, J} = 0` on the phase space.
* `TauCeti.dense_setOf_isRegularPoint_sphericalPendulumEnergyMomentum`: the regular points of
  `F = (H, J)` on the phase space are dense.
* `TauCeti.isIntegrableSystem_sphericalPendulumEnergyMomentum`: the spherical pendulum is a
  completely integrable system.
* `TauCeti.isProperMap_sphericalPendulumEnergyMomentum`: `F` is proper.
* `isCompleteVectorField_hamiltonianVectorField_sphericalPendulumHamiltonian_comp_subtypeVal`,
  `isCompleteVectorField_hamiltonianVectorField_angularMomentum_sphericalPendulumPhaseSpace`: the
  Hamiltonian flows of `H` and `J` are complete.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum as a constrained system in `ℝ³ × ℝ³`).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (integrable systems).
-/

public section

open Function Module Set Filter
open scoped InnerProductSpace Manifold ContDiff Topology

namespace TauCeti

/-! ### The symplectic form -/

/-- The symplectic form of the spherical pendulum: the restriction to the phase space `T*S²` of the
standard symplectic form `ω₀((a, b), (a', b')) = ⟪a, b'⟫ - ⟪b, a'⟫` of `ℝ³ × ℝ³`. -/
noncomputable def sphericalPendulumSymplecticForm :
    SmoothTwoForm 𝓘(ℝ, Fin 4 → ℝ) sphericalPendulumPhaseSpace :=
  SmoothForm.mpullback (Subtype.val : sphericalPendulumPhaseSpace → _)
    isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).constSmooth

theorem sphericalPendulumSymplecticForm_def :
    sphericalPendulumSymplecticForm =
      SmoothForm.mpullback (Subtype.val : sphericalPendulumPhaseSpace → _)
        isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
        (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).constSmooth :=
  (rfl)

/-- The symplectic form of the spherical pendulum evaluates as `ω₀` on the tangent images in
`ℝ³ × ℝ³`. -/
theorem eval₂_sphericalPendulumSymplecticForm (x : sphericalPendulumPhaseSpace)
    (v w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x) :
    SmoothBundleForm.eval₂ sphericalPendulumSymplecticForm x v w =
      stdSymplecticForm
        (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
          Subtype.val x v)
        (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
          Subtype.val x w) := by
  rw [sphericalPendulumSymplecticForm_def, SmoothForm.eval₂_mpullback,
    SymplecticForm.fromTangentSpace_constSmooth_apply, NormedSpace.fromTangentSpace_apply,
    NormedSpace.fromTangentSpace_apply]

/-- The tangent space `{(a, b) : ⟪q, a⟫ = 0, ⟪q, b⟫ + ⟪a, p⟫ = 0}` of the level of the constraint
map through `(q, p)`, `q ≠ 0`, is a symplectic subspace of `ℝ³ × ℝ³`: it meets its `ω₀`-orthogonal
only in zero. -/
theorem isSymplectic_ker_fderiv_sphericalPendulumConstraint
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} (hx : x.1 ≠ 0) :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).IsSymplectic
      (fderiv ℝ sphericalPendulumConstraint x).ker := by
  have hker (v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
      v ∈ (fderiv ℝ sphericalPendulumConstraint x).ker ↔
        ⟪x.1, v.1⟫_ℝ = 0 ∧ ⟪x.1, v.2⟫_ℝ + ⟪v.1, x.2⟫_ℝ = 0 := by
    simp [fderiv_sphericalPendulumConstraint_apply]
  rw [SymplecticForm.isSymplectic_iff_disjoint, Submodule.disjoint_def]
  rintro ⟨a, b⟩ hab hort
  rw [hker] at hab
  have ho := SymplecticForm.mem_orthogonal_iff'.1 hort
  -- Pairing with the tangent vector `(0, a)` gives `‖a‖² = 0`.
  have ha : a = 0 := by
    have h := ho (0, a) ((hker _).2 ⟨inner_zero_right _, by simpa using hab.1⟩)
    simpa using h
  subst ha
  have hq : ⟪x.1, x.1⟫_ℝ ≠ 0 := inner_self_ne_zero.2 hx
  -- Pairing with the tangent vector `(b, -(⟪b, p⟫ / ⟪q, q⟫) q)` gives `‖b‖² = 0`.
  have h := ho (b, -(⟪b, x.2⟫_ℝ / ⟪x.1, x.1⟫_ℝ) • x.1) ((hker _).2 ⟨by simpa using hab.2, by
    rw [inner_smul_right]
    field_simp
    ring⟩)
  simpa using h

/-- **The phase space of the spherical pendulum is a symplectic submanifold** of `ℝ³ × ℝ³` with
its standard symplectic form. -/
theorem isSymplecticSubmanifoldEmbedding_coe_sphericalPendulumPhaseSpace :
    (SymplecticForm.isNondegenerate_constSmooth
      (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3)))).IsSymplecticSubmanifoldEmbedding
      𝓘(ℝ, Fin 4 → ℝ) (Subtype.val : sphericalPendulumPhaseSpace → _) := by
  rw [SmoothTwoForm.IsNondegenerate.isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
    isSmoothEmbedding_coe_sphericalPendulumPhaseSpace,
    SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_iff_forall]
  intro x
  rw [SymplecticForm.isNondegenerate_constSmooth_symplecticFormAt,
    range_mfderiv_coe_sphericalPendulumPhaseSpace]
  exact isSymplectic_ker_fderiv_sphericalPendulumConstraint
    (norm_ne_zero_iff.1 ((mem_sphericalPendulumPhaseSpace.1 x.2).1.symm ▸ one_ne_zero))

/-- **The symplectic form of the spherical pendulum is symplectic.** -/
theorem isSymplectic_sphericalPendulumSymplecticForm :
    sphericalPendulumSymplecticForm.IsSymplectic :=
  isSymplecticSubmanifoldEmbedding_coe_sphericalPendulumPhaseSpace.isSymplectic_mpullback
    (SymplecticForm.isSymplectic_constSmooth _)

/-! ### The energy and the angular momentum commute -/

/-- The ambient Hamiltonian vector of the vertical angular momentum, the infinitesimal rotation
`(R q, R p)` about the vertical axis, lies in the kernel of the differential of the constraint map:
the rotations preserve `‖q‖²` and `⟪q, p⟫`. -/
theorem hamiltonianVectorField_angularMomentum_mem_ker_fderiv_sphericalPendulumConstraint
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).hamiltonianVectorField
        (angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)) x ∈
      (fderiv ℝ sphericalPendulumConstraint x).ker := by
  rw [stdSymplecticForm_hamiltonianVectorField_angularMomentum, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, fderiv_sphericalPendulumConstraint_apply]
  simp only [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
    EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left, RCLike.conj_to_real,
    Prod.mk_eq_zero]
  constructor <;> ring

/-- The energy and the vertical angular momentum Poisson-commute on `ℝ³ × ℝ³`: the derivative of the
energy along the infinitesimal rotation `(R q, R p)` is `⟪p, R p⟫ + (R q)₃ = 0`. -/
theorem stdSymplecticForm_poissonBracket_sphericalPendulumHamiltonian_angularMomentum
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).poissonBracket sphericalPendulumHamiltonian
      (angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)) x = 0 := by
  have hH : HasFDerivAt sphericalPendulumHamiltonian
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ sphericalPendulumEnergyMomentum x)) x := by
    convert ((contDiff_sphericalPendulumEnergyMomentum (n := 1)).differentiable one_ne_zero
      x).hasFDerivAt.fst using 1
    exact funext fun y ↦ (fst_sphericalPendulumEnergyMomentum y).symm
  rw [SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_hamiltonianVectorField_angularMomentum, hH.fderiv,
    ContinuousLinearMap.comp_apply, fderiv_sphericalPendulumEnergyMomentum_apply]
  simp [inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right]
  ring

/-- **The Hamiltonian vector field of the vertical angular momentum on the phase space** is the
infinitesimal rotation `(R q, R p)` about the vertical axis: the differential of the inclusion of
the phase space carries it to the ambient Hamiltonian vector field of the vertical angular
momentum. -/
theorem mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_angularMomentum
    (x : sphericalPendulumPhaseSpace) :
    mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        Subtype.val x (sphericalPendulumSymplecticForm.hamiltonianVectorField
          (fun y ↦ angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
            (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) x) =
      (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).hamiltonianVectorField
        (angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)) x := by
  have hk : (SymplecticForm.constSmooth stdSymplecticForm).hamiltonianVectorField
      (angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)) x ∈
        (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
          Subtype.val x).range := by
    rw [range_mfderiv_coe_sphericalPendulumPhaseSpace,
      SymplecticForm.hamiltonianVectorField_constSmooth]
    exact hamiltonianVectorField_angularMomentum_mem_ker_fderiv_sphericalPendulumConstraint _
  simpa only [Function.comp_def, SymplecticForm.hamiltonianVectorField_constSmooth] using
    isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate
      |>.mfderiv_hamiltonianVectorField_comp_of_mem_range
        (SymplecticForm.isNondegenerate_constSmooth _)
        isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
        sphericalPendulumSymplecticForm_def.symm
        (hasFDerivAt_angularMomentum _ _ _).differentiableAt.mdifferentiableAt hk

/-- **The energy and the vertical angular momentum of the spherical pendulum Poisson-commute** for
its symplectic form. The rotations about the vertical axis are tangent to the phase space and
preserve the energy. -/
theorem poissonBracket_sphericalPendulumHamiltonian_angularMomentum_comp_subtypeVal
    (x : sphericalPendulumPhaseSpace) :
    sphericalPendulumSymplecticForm.poissonBracket (fun y ↦ sphericalPendulumHamiltonian y)
      (fun y ↦ angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
        (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) x = 0 := by
  have hF := (contDiff_sphericalPendulumEnergyMomentum (n := 1)).differentiable one_ne_zero
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
  -- The bracket is the ambient one, since the ambient Hamiltonian vector of `J` is tangent.
  have h := isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate
    |>.poissonBracket_comp_of_mem_range (SymplecticForm.isNondegenerate_constSmooth _)
      isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
      sphericalPendulumSymplecticForm_def.symm
      (g := sphericalPendulumHamiltonian) (by simpa using hF.fst.mdifferentiableAt)
      (hasFDerivAt_angularMomentum _ _ _).differentiableAt.mdifferentiableAt (by
        rw [SymplecticForm.hamiltonianVectorField_constSmooth]
        exact ⟨_, mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_angularMomentum x⟩)
  rwa [Function.comp_def, Function.comp_def, SymplecticForm.poissonBracket_constSmooth,
    stdSymplecticForm_poissonBracket_sphericalPendulumHamiltonian_angularMomentum] at h

/-! ### Density of the regular points -/

/-- Away from the poles, a point of the phase space is a limit of points with nonzero vertical
momentum: move `p` along the tangent vector `e₃ - q₃ q`. -/
private theorem mem_closure_setOf_snd_apply_two_ne_zero {x : sphericalPendulumPhaseSpace}
    (hx : (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 ≠ 1) :
    x ∈ closure {y : sphericalPendulumPhaseSpace |
      (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 ≠ 0} := by
  obtain ⟨⟨q, p⟩, hx'⟩ := x
  obtain ⟨hq, hqp⟩ := mem_sphericalPendulumPhaseSpace.1 hx'
  dsimp only at hx hq hqp
  by_cases hp : p 2 ≠ 0
  · exact subset_closure hp
  rw [not_not] at hp
  set w : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 2 1 - q 2 • q
  have hw : ⟪q, w⟫_ℝ = 0 := by
    simp [w, inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right, hq]
  let g (ε : ℝ) : sphericalPendulumPhaseSpace :=
    ⟨(q, p + ε • w), mem_sphericalPendulumPhaseSpace.2
      ⟨hq, by rw [inner_add_right, inner_smul_right, hqp, hw, mul_zero, add_zero]⟩⟩
  have hg : Tendsto g (𝓝[≠] 0) (𝓝 ⟨(q, p), hx'⟩) := by
    have hc : Continuous g := (continuous_const.prodMk
      (continuous_const.add (continuous_id.smul continuous_const))).subtype_mk _
    simpa [g] using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  refine mem_closure_of_tendsto hg ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have h1 : 1 - q 2 * q 2 ≠ 0 := by
    intro h
    exact hx (by linear_combination -h)
  simpa [g, w, hp, PiLp.single_apply] using mul_ne_zero hε h1

/-- The points of the phase space away from the poles are dense: rotate `q` off the pole towards
`e₁` and project `p` back to the tangent plane. -/
private theorem dense_setOf_sq_apply_two_ne_one :
    Dense {x : sphericalPendulumPhaseSpace |
      (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 ≠ 1} := by
  rintro ⟨⟨q, p⟩, hx⟩
  by_cases h2 : q 2 ^ 2 ≠ 1
  · exact subset_closure h2
  rw [not_not] at h2
  obtain ⟨hq, hqp⟩ := mem_sphericalPendulumPhaseSpace.1 hx
  have hq0 : q 0 = 0 := by
    have := (sum_sq_eq_one_and_sum_mul_eq_zero_of_mem_sphericalPendulumPhaseSpace hx).1
    nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
  set u : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  have hqu : ⟪q, u⟫_ℝ = 0 := by simp [u, EuclideanSpace.inner_single_right, hq0]
  -- The rotated position `cos ε q + sin ε u` and the projected momentum.
  let r (ε : ℝ) : EuclideanSpace ℝ (Fin 3) := Real.cos ε • q + Real.sin ε • u
  have hr (ε : ℝ) : ⟪r ε, r ε⟫_ℝ = 1 := by
    simp only [r, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, hq, real_inner_comm q u, hqu, RCLike.conj_to_real]
    simp only [u, PiLp.norm_single, norm_one]
    linear_combination Real.cos_sq_add_sin_sq ε
  have hmem (ε : ℝ) : (r ε, p - ⟪r ε, p⟫_ℝ • r ε) ∈ sphericalPendulumPhaseSpace := by
    refine mem_sphericalPendulumPhaseSpace.2 ⟨?_, ?_⟩
    · rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq,
        hr]
    · rw [inner_sub_right, inner_smul_right, hr, mul_one, sub_self]
  let g (ε : ℝ) : sphericalPendulumPhaseSpace := ⟨_, hmem ε⟩
  have hrc : Continuous r := (Real.continuous_cos.smul continuous_const).add
    (Real.continuous_sin.smul continuous_const)
  have hg : Tendsto g (𝓝[>] 0) (𝓝 ⟨(q, p), hx⟩) := by
    have hc : Continuous g := by
      refine Continuous.subtype_mk ?_ hmem
      fun_prop
    simpa [g, r, hqp] using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  refine mem_closure_of_tendsto hg ?_
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with ε hε
  have hs : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε.1 hε.2
  have hc : r ε 2 = Real.cos ε * q 2 := by simp [r, u]
  have hr2 : r ε 2 ^ 2 ≠ 1 := by
    rw [hc, mul_pow, h2, mul_one]
    intro h
    nlinarith [Real.cos_sq_add_sin_sq ε]
  exact hr2

/-- The points of the phase space with nonzero vertical momentum `p₃` are dense. -/
private theorem dense_setOf_snd_apply_two_ne_zero :
    Dense {x : sphericalPendulumPhaseSpace |
      (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 ≠ 0} :=
  dense_closure.1 (dense_setOf_sq_apply_two_ne_one.mono fun _ hx ↦
    mem_closure_setOf_snd_apply_two_ne_zero hx)

/-- **The regular points of the spherical pendulum are dense** in its phase space: every point with
nonzero vertical momentum is a regular point of the energy–momentum map. -/
theorem dense_setOf_isRegularPoint_sphericalPendulumEnergyMomentum :
    Dense {x | IsRegularPoint 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) x} := by
  refine dense_setOf_snd_apply_two_ne_zero.mono fun x hx ↦ ?_
  by_contra h
  rcases (not_isRegularPoint_sphericalPendulumEnergyMomentum_iff x).1 h with ⟨hp, -⟩ | ⟨-, hp, -⟩
  · exact hx (by simp [hp])
  · exact hx hp

/-! ### The integrable system -/

/-- **The spherical pendulum is a completely integrable system.** On the phase space `T*S²` with
the restriction of the standard symplectic form of `ℝ³ × ℝ³`, the energy `H = ‖p‖² / 2 + q₃` and
the vertical angular momentum `J = q₁ p₂ - q₂ p₁` Poisson-commute and are independent on a dense
set. -/
theorem isIntegrableSystem_sphericalPendulumEnergyMomentum :
    sphericalPendulumSymplecticForm.IsIntegrableSystem fun x : sphericalPendulumPhaseSpace ↦
      ![sphericalPendulumHamiltonian x,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))] := by
  let e := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  have he : (fun x : sphericalPendulumPhaseSpace ↦
      ![sphericalPendulumHamiltonian x,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]) =
      e ∘ fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y := by
    funext x
    simp [e]
  refine ⟨?_, fun i j x ↦ ?_, ?_, by simp⟩
  · rw [he]
    exact e.contDiff.contMDiff.comp (contDiff_sphericalPendulumEnergyMomentum.contMDiff.comp
      isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff)
  · have h := poissonBracket_sphericalPendulumHamiltonian_angularMomentum_comp_subtypeVal x
    fin_cases i <;> fin_cases j
    · exact SmoothTwoForm.poissonBracket_self _ _ _
    · exact h
    · rw [← SmoothTwoForm.neg_poissonBracket, neg_eq_zero]
      simpa using h
    · exact SmoothTwoForm.poissonBracket_self _ _ _
  · -- Composing with the linear equivalence `e` preserves regular points.
    refine dense_setOf_isRegularPoint_sphericalPendulumEnergyMomentum.mono fun x hx ↦ ?_
    rw [Set.mem_ofPred_eq, he]
    refine IsRegularPoint.comp (isRegularPoint_iff.2 ?_) hx
    rw [mfderiv_eq_fderiv, e.fderiv]
    exact e.surjective

/-- **The energy–momentum map of the spherical pendulum is proper**, since its energy component is
proper. -/
theorem isProperMap_sphericalPendulumEnergyMomentum :
    IsProperMap fun x : sphericalPendulumPhaseSpace ↦
      ![sphericalPendulumHamiltonian x,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))] :=
  isProperMap_of_comp_of_t2
    (contMDiff_iff.1 isIntegrableSystem_sphericalPendulumEnergyMomentum.contMDiff).1
    (continuous_apply 0) isProperMap_sphericalPendulumHamiltonian_comp_subtypeVal

/-- **The energy flow of the spherical pendulum is complete**: the energy is proper, so its
Hamiltonian vector field on the phase space is complete. -/
theorem isCompleteVectorField_hamiltonianVectorField_sphericalPendulumHamiltonian_comp_subtypeVal :
    IsCompleteVectorField (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) :=
  isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate
    |>.isCompleteVectorField_hamiltonianVectorField_of_isProperMap_self
      ((contMDiff_pi_module_iff.1 isIntegrableSystem_sphericalPendulumEnergyMomentum.contMDiff
        0).of_le (by simp))
      isProperMap_sphericalPendulumHamiltonian_comp_subtypeVal

/-- **The rotation flow of the spherical pendulum is complete**: the energy is a proper first
integral of the vertical angular momentum, so the Hamiltonian vector field of the vertical angular
momentum on the phase space is complete. -/
theorem isCompleteVectorField_hamiltonianVectorField_angularMomentum_sphericalPendulumPhaseSpace :
    IsCompleteVectorField (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
        (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) := by
  simpa using isIntegrableSystem_sphericalPendulumEnergyMomentum
    |>.isCompleteVectorField_hamiltonianVectorField_of_isProperMap
      isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate
      isProperMap_sphericalPendulumEnergyMomentum 1

end TauCeti
