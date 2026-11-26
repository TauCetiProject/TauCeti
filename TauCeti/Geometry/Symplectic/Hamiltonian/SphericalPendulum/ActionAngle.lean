/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.GlobalActionAngle
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Fibration
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Monodromy
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-!
# The spherical pendulum has no global action–angle coordinates around its focus–focus value

Let `F = (H, J)` be the energy–momentum map of the spherical pendulum, and let
`γ(t) = (1 + r cos t, r sin t)` be a circle about its focus–focus value `(1, 0)`. Let `U` be any
open set of regular values of `F` containing `γ`, so that over `U` the map `F` is a regular
Lagrangian torus fibration
(`TauCeti.isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec`). This file proves
that this fibration has **no global action–angle coordinates**
(`TauCeti.not_exists_actionAngle_sphericalPendulumEnergyMomentumVec`): there is no injective local
diffeomorphism `Φ` from the states over `U` into the cotangent bundle of a torus `(ℝ/pℤ)^ι`
pulling the canonical symplectic form back to the symplectic form of the pendulum, whose actions
are functions `a` of the values of `F`. This is Duistermaat's conclusion from the nontrivial
Hamiltonian monodromy of the pendulum.

Global action–angle coordinates would make the period lattice at every `b ∈ U` the lattice spanned
by the covectors `p • daⱼ(b)` (`periodLattice_eq_closure_of_actionAngle`, in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`), so they would frame the
period lattices by exact one-forms. No `C¹` map `a` does that
(`TauCeti.not_forall_periodLattice_eq_closure_sphericalPendulum`). In the coordinates of the plane,
a covector `w ↦ v ⬝ᵥ w` at `b` is a period exactly when `v` lies in the stabilizer of the states
over `b` under the Hamiltonian flow action of `F`
(`TauCeti.mem_hamiltonianFlowStabilizer_sphericalPendulum_iff_mem_periodLattice`), since
restricting `F` to the states over `U` does not change these stabilizers
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowStabilizer_mpullback_subtype_val`). So the
vectors representing `p • daⱼ(γ(t))` are continuous sections of the period lattices of the
pendulum along `γ`, returning to their values after one turn. By the Hamiltonian monodromy of the
pendulum, such sections have zero energy component off the axis `j = 0`
(`TauCeti.apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum`). But the period
lattice contains `(T, -Θ)`, whose energy component is the positive first-return time `T`, so the
`p • daⱼ` cannot span it.

Off the axis, a circle of regular values runs above the curve of relative equilibria
(`TauCeti.mem_sphericalPendulumTurningPointDomain_of_mem_sphericalPendulumRegularValues`), so no
restriction on the radius `r` is needed beyond `γ ⊆ U`.

## Main results

* `TauCeti.mem_hamiltonianFlowStabilizer_sphericalPendulum_iff_mem_periodLattice`: the period
  lattices of the fibration over `U`, in the coordinates of the plane, are the stabilizers of the
  flow action.
* `TauCeti.not_forall_periodLattice_eq_closure_sphericalPendulum`: the period lattices over an
  open set of regular values containing a circle about `(1, 0)` are not framed by exact forms.
* `TauCeti.not_exists_actionAngle_sphericalPendulumEnergyMomentumVec`: there are no global
  action–angle coordinates over any open set of regular values containing a circle about `(1, 0)`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 3 (the spherical pendulum).
* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum and its monodromy).
-/

public section

open Function Set Real TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {U : Opens (Fin 2 → ℝ)}

/-- **The period lattices over an open set of regular values, in the coordinates of the plane.**
Let `U` be an open set of regular values of the energy–momentum map `![H, J]` of the spherical
pendulum, and `y` a state over `b ∈ U`. A vector `v` of the plane is a period of `y`, that is it
lies in the stabilizer of `y` under the Hamiltonian flow action of `![H, J]`, exactly when the
covector `w ↦ v ⬝ᵥ w` at `b` lies in the period lattice of the Lagrangian torus fibration over
`U`. -/
theorem mem_hamiltonianFlowStabilizer_sphericalPendulum_iff_mem_periodLattice
    (hU : U ≤ sphericalPendulumRegularValues)
    (y : U.comap ⟨_, isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff.continuous⟩)
    {v : Fin 2 → ℝ} {α : (Fin 2 → ℝ) →L[ℝ] ℝ} (hα : ∀ w, α w = v ⬝ᵥ w) :
    v ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec y ↔
      α ∈ (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
        (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed
        ⟨sphericalPendulumEnergyMomentumVec y, y.property⟩ := by
  set h := isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU
  have hκ : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ (Subtype.val : U → Fin 2 → ℝ) :=
    contMDiff_subtypeVal
  -- The covector `α` is the differential of `c ↦ v ⬝ᵥ c`, the composite of the linear map
  -- `φ = v ⬝ᵥ ·` with the inclusion of `U`.
  have hdα : mvfderiv 𝓘(ℝ, Fin 2 → ℝ) (fun c : U ↦ v ⬝ᵥ (c : Fin 2 → ℝ))
      ⟨sphericalPendulumEnergyMomentumVec y, y.property⟩ = α := by
    let φ : (Fin 2 → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductEquiv ℝ (Fin 2) v)
    have hφ : (fun c : U ↦ v ⬝ᵥ (c : Fin 2 → ℝ)) = φ ∘ Subtype.val :=
      funext fun c ↦ by simp [φ, dotProductEquiv]
    refine ContinuousLinearMap.ext fun w ↦ ?_
    rw [hφ, Manifold.mvfderiv_comp_subtype_val]
    refine ((mvfderiv_eq_fderiv_apply (𝕜 := ℝ) φ _ w).trans ?_).trans (hα w).symm
    rw [φ.fderiv]
    simp [φ, dotProductEquiv]
  -- The stabilizers for the restriction of `![H, J]` to the states over `U` are those of `![H, J]`.
  refine Iff.trans ?_ (h.mem_periodLattice_iff_mem_hamiltonianFlowStabilizer _ _ hκ ⟨y, rfl⟩ v
    hdα).symm
  exact (SetLike.ext_iff.1
    (isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer_mpullback_subtype_val
      isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
      isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
      isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec
      (hκ.comp h.contMDiff)
      (h.poissonBracket_comp_apply_eq_zero_of_mdifferentiable (hκ.mdifferentiable (by simp)))
      (h.isCompleteVectorField_hamiltonianVectorField_comp_apply (hκ.of_le (by simp))) y) v).symm

variable {r : ℝ}

/-- A circle of regular values about `(1, 0)` runs above the curve of relative equilibria off the
axis `j = 0`. -/
private theorem mem_sphericalPendulumTurningPointDomain_circle (hr : 0 < r)
    (hU : U ≤ sphericalPendulumRegularValues) (hγU : ∀ t, ![1 + r * cos t, r * sin t] ∈ U)
    {t : ℝ} (hs : sin t ≠ 0) :
    (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain := by
  simpa using mem_sphericalPendulumTurningPointDomain_of_mem_sphericalPendulumRegularValues
    (hU (hγU t)) (by simpa using mul_ne_zero hr.ne' hs)

/-- If the covector `p • Dⱼ` lies in the period lattice at the value of a state `y` over `U`, then
the vector of the plane representing it is a period of `y`. -/
private theorem mem_hamiltonianFlowStabilizer_of_smul_comp_mem_periodLattice
    (hU : U ≤ sphericalPendulumRegularValues)
    (y : U.comap ⟨_, isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff.continuous⟩)
    {ι : Type*} {p : ℝ} {D : (Fin 2 → ℝ) →L[ℝ] ι → ℝ} {j : ι}
    (hD : p • (ContinuousLinearMap.proj j).comp D ∈
      (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
        (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed
        ⟨sphericalPendulumEnergyMomentumVec y, y.property⟩) :
    (fun i ↦ p * D (Pi.single i 1) j) ∈
      isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec y := by
  refine (mem_hamiltonianFlowStabilizer_sphericalPendulum_iff_mem_periodLattice hU y
    fun w ↦ ?_).2 hD
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  conv_lhs => rw [pi_eq_sum_univ' w, map_sum]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- `TauCeti.not_forall_periodLattice_eq_closure_sphericalPendulum` for a circle of positive
radius `r`. -/
private theorem not_forall_periodLattice_eq_closure_of_pos (hr : 0 < r)
    (hU : U ≤ sphericalPendulumRegularValues) (hγU : ∀ t, ![1 + r * cos t, r * sin t] ∈ U)
    {ι : Type*} [Fintype ι] (p : ℝ) {a : U → ι → ℝ}
    (ha : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ι → ℝ) 1 a) :
    ¬ ∀ b, (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
        (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed b =
      AddSubgroup.closure (range fun j ↦ p • (ContinuousLinearMap.proj j).comp
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ι → ℝ) a b : (Fin 2 → ℝ) →L[ℝ] ι → ℝ)) := by
  intro hΛ
  -- States `y t` over the circle `γ(t) = (1 + r cos t, r sin t)`.
  let γ : ℝ → U := fun t ↦ ⟨_, hγU t⟩
  choose y hy using fun t ↦
    (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).surjective (γ t)
  have hb (t : ℝ) : (⟨sphericalPendulumEnergyMomentumVec (y t), (y t).property⟩ : U) = γ t := hy t
  have hx (t : ℝ) : sphericalPendulumEnergyMomentum (y t : sphericalPendulumPhaseSpace) =
      (1 + r * cos t, r * sin t) := by
    simpa using (sphericalPendulumEnergyMomentumVec_eq_iff _ ![1 + r * cos t, r * sin t]).1
      (congrArg Subtype.val (hb t))
  have hγT (t : ℝ) (hs : sin t ≠ 0) := mem_sphericalPendulumTurningPointDomain_circle hr hU hγU hs
  -- The vectors `s j t` of the plane representing the covectors `p • daⱼ(γ t)` are continuous
  -- sections of the period lattices along `γ`, returning to their values after one turn.
  let D : U → (Fin 2 → ℝ) →L[ℝ] ι → ℝ := mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ι → ℝ) a
  -- Read the differentials `da_b` as linear maps of the plane, which they are by definition of the
  -- tangent spaces of `U` and of `ι → ℝ`.
  replace hΛ (b : U) := (hΛ b).trans (congrArg AddSubgroup.closure (congrArg range
    (funext fun j ↦ (rfl : _ = p • (ContinuousLinearMap.proj j).comp (D b)))))
  let s : ι → ℝ → Fin 2 → ℝ := fun j t i ↦ p * D (γ t) (Pi.single i 1) j
  have hsmem (j : ι) (t : ℝ) := mem_hamiltonianFlowStabilizer_of_smul_comp_mem_periodLattice hU
    (y t) (D := D (γ t)) (by rw [hb, hΛ]; exact AddSubgroup.subset_closure ⟨j, rfl⟩)
  have hs (j : ι) : Continuous (s j) := continuous_pi fun i ↦ continuous_const.mul
    ((continuous_apply j).comp
      (((Manifold.continuous_mfderiv_of_contMDiff_opens ha one_ne_zero).comp
        (continuous_induced_rng.2 (by fun_prop) : Continuous γ)).clm_apply continuous_const))
  have hper (j : ι) : s j (2 * π) = s j 0 := by
    simp only [s, show γ (2 * π) = γ 0 from Subtype.ext (by simp [γ])]
  -- By the monodromy, these sections have zero energy component off the axis.
  have hπ : π / 2 ∈ Icc 0 (2 * π) := ⟨by positivity, by linarith [pi_pos]⟩
  have hsin : sin (π / 2) ≠ 0 := by simp
  have hzero (j : ι) : p * D (γ (π / 2)) (Pi.single 0 1) j = 0 :=
    apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum hr hγT
      (fun t _ _ ↦ hx t) (hs j).continuousOn (fun t _ _ ↦ hsmem j t) (hper j) hπ hsin
  -- But they span the period `(T, -Θ)` at `γ(π / 2)`, whose energy component is `T > 0`.
  set u : Fin 2 → ℝ := ![sphericalPendulumPeriod (1 + r * cos (π / 2)) (r * sin (π / 2)),
    -sphericalPendulumRotationAngle (1 + r * cos (π / 2)) (r * sin (π / 2))]
  have hu := (mem_hamiltonianFlowStabilizer_sphericalPendulum_iff_mem_periodLattice hU (y (π / 2))
    (v := u) (α := LinearMap.toContinuousLinearMap (dotProductEquiv ℝ (Fin 2) u))
    (fun w ↦ by simp [dotProductEquiv])).1 (by
      rw [hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure_of_mem
        (hγT _ hsin) (hx _)]
      exact AddSubgroup.subset_closure (mem_insert _ _))
  rw [hb, hΛ] at hu
  obtain ⟨m, hm⟩ := AddSubgroup.mem_closure_range_iff_of_fintype.1 hu
  have h₀ := DFunLike.congr_fun hm (Pi.single 0 1)
  simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, hzero, smul_zero, Finset.sum_const_zero] at h₀
  exact (sphericalPendulumPeriod_pos_of_mem (hγT _ hsin)).ne'
    (by simpa [dotProductEquiv, u] using h₀)

/-- **The period lattices around the focus–focus value are not framed by exact forms.** Let `U`
be an open set of regular values of the energy–momentum map `![H, J]` of the spherical pendulum
containing a circle `γ(t) = (1 + r cos t, r sin t)` about the focus–focus value `(1, 0)`. Then no
`C¹` map `a : U → ℝ^ι` and no `p` make the covectors `p • daⱼ(b)` span the period lattice of the
Lagrangian torus fibration over `U` at every `b ∈ U`: the transported periods would be closed
continuous sections of the period lattices along `γ`, which the Hamiltonian monodromy forbids. -/
theorem not_forall_periodLattice_eq_closure_sphericalPendulum
    (hU : U ≤ sphericalPendulumRegularValues) (hγU : ∀ t, ![1 + r * cos t, r * sin t] ∈ U)
    {ι : Type*} [Fintype ι] (p : ℝ) {a : U → ι → ℝ}
    (ha : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ι → ℝ) 1 a) :
    ¬ ∀ b, (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
        (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed b =
      AddSubgroup.closure (range fun j ↦ p • (ContinuousLinearMap.proj j).comp
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ι → ℝ) a b : (Fin 2 → ℝ) →L[ℝ] ι → ℝ)) := by
  -- The radius is nonzero, since `(1, 0)` is a critical value, and only the circle of radius `|r|`
  -- traced by `γ` matters.
  have hr : r ≠ 0 := by
    rintro rfl
    simpa using (mem_sphericalPendulumRegularValues_iff_mem_image_and_ne.1 (hU (hγU 0))).2.2.1
  refine not_forall_periodLattice_eq_closure_of_pos (abs_pos.2 hr) hU (fun t ↦ ?_) p ha
  rcases le_or_gt 0 r with h | h
  · simpa [abs_of_nonneg h] using hγU t
  · simpa [abs_of_neg h, cos_add_pi, sin_add_pi] using hγU (t + π)

/-- **The spherical pendulum has no global action–angle coordinates.** Let `U` be an open set of
regular values of the energy–momentum map `![H, J]` of the spherical pendulum containing a circle
`γ(t) = (1 + r cos t, r sin t)` about the focus–focus value `(1, 0)`. Then for no
period `p > 0` and no finite index type `ι` is there an injective local diffeomorphism `Φ` from the
states over `U` into the cotangent bundle of the torus `(ℝ/pℤ)^ι` which pulls the canonical
symplectic form back to the symplectic form of the pendulum and whose actions are a function `a`
of the values of `![H, J]`: the regular Lagrangian torus fibration of the pendulum over `U` has no
global action–angle coordinates, because its Hamiltonian monodromy around `(1, 0)` is
nontrivial. -/
theorem not_exists_actionAngle_sphericalPendulumEnergyMomentumVec
    (hU : U ≤ sphericalPendulumRegularValues) (hγU : ∀ t, ![1 + r * cos t, r * sin t] ∈ U)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) [Fact (0 < p)] :
    ¬ ∃ (a : U → ι → ℝ) (Φ : U.comap
        ⟨_, isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff.continuous⟩ →
          CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
      (hΦ : IsLocalDiffeomorph 𝓘(ℝ, Fin 4 → ℝ)
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ),
      Injective Φ ∧
        SmoothForm.mpullback Φ hΦ.contMDiff
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (ι → AddCircle p)) =
          SmoothForm.mpullback Subtype.val contMDiff_subtypeVal sphericalPendulumSymplecticForm ∧
        ∀ y, CotangentBundle.torusActions p (Φ y) =
          a ⟨sphericalPendulumEnergyMomentumVec y, y.property⟩ := by
  rintro ⟨a, Φ, hΦ, hΦi, hΦσ, hΦa⟩
  have h := isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU
  -- Global action–angle coordinates frame the period lattices by the exact forms `p • daⱼ`.
  exact not_forall_periodLattice_eq_closure_sphericalPendulum hU hγU p
    ((h.contMDiff_of_actionAngle p hΦ hΦa).of_le (by simp))
    (h.periodLattice_eq_closure_of_actionAngle p _ hΦ hΦσ hΦa fun _ ↦ hΦi.injOn)

end TauCeti
