/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Regular
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Integrable
import Mathlib.Topology.LocalAtTarget
import TauCeti.Geometry.Manifold.RegularValue.Factorization

/-!
# The regular part of the spherical pendulum is a Lagrangian torus fibration

The spherical pendulum is the completely integrable system `F = (H, J)` on `T*S²`, with energy
`H(q, p) = ‖p‖² / 2 + q₃` and vertical angular momentum `J(q, p) = q₁ p₂ - q₂ p₁`
(`TauCeti.isIntegrableSystem_sphericalPendulumEnergyMomentum`, which reads `F` as the map
`![H, J]` into `Fin 2 → ℝ`). Its critical values are the values `(-1, 0)` and `(1, 0)` of the two
equilibria and the curve of relative equilibria
(`TauCeti.image_setOf_not_isRegularPoint_sphericalPendulumEnergyMomentum`).

This file collects the regular values of `F` lying in its image into an open subset `B` of the
plane (`TauCeti.sphericalPendulumRegularValues`): these are the values of `F` other than the
values `(-1, 0)` and `(1, 0)` of the equilibria and the values of the relative equilibria
(`TauCeti.mem_sphericalPendulumRegularValues_iff`). The energy–momentum map is proper and its
fibres are connected, so over `B`, that is on the open set
`TauCeti.sphericalPendulumRegularPart` of states over `B`, it is a regular Lagrangian torus
fibration (`TauCeti.isLagrangianTorusFibration_sphericalPendulum`), an instance of
`TauCeti.SmoothTwoForm.IsIntegrableSystem.isLagrangianTorusFibration_restrictPreimage`. So its
fibres are two-tori (`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`), and it
carries the fibrewise action of `T*B` and the period lattices
(`IsLagrangianTorusFibration.periodLattice`) of Lagrangian torus fibrations.

The base `B` contains a punctured neighbourhood of `(1, 0)`
(`TauCeti.eventually_mem_sphericalPendulumRegularValues_nhdsNE`), so loops of regular values
around the focus–focus value lie in `B`; transport of the period lattice of this fibration around
such a loop is the Hamiltonian monodromy of the spherical pendulum.

## Main declarations

* `TauCeti.sphericalPendulumRegularValues`: the open set of regular values in the image of `F`.
* `TauCeti.sphericalPendulumRegularPart`: the open set of states over it.
* `TauCeti.mem_sphericalPendulumRegularValues_iff`: its explicit description.
* `TauCeti.eventually_mem_sphericalPendulumRegularValues_nhdsNE`: it contains a punctured
  neighbourhood of the focus–focus value `(1, 0)`.
* `TauCeti.isLagrangianTorusFibration_sphericalPendulum`: over it, `F` is a regular Lagrangian
  torus fibration.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706.
-/

public section

open Function Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace TauCeti

/-- The energy–momentum map `![H, J]` of the spherical pendulum is `(H, J)` followed by the linear
identification of `ℝ × ℝ` with `Fin 2 → ℝ`. -/
private theorem sphericalPendulum_matrixVec_eq :
    (fun x : sphericalPendulumPhaseSpace ↦
      ![sphericalPendulumHamiltonian x,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]) =
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm ∘
        fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y := by
  funext x
  simp

/-- The value of `![H, J]` at a point of the phase space is `c` exactly when the value of `(H, J)`
there is `(c 0, c 1)`. -/
private theorem sphericalPendulum_matrixVec_eq_iff (x : sphericalPendulumPhaseSpace)
    (c : Fin 2 → ℝ) :
    ![sphericalPendulumHamiltonian x,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))] = c ↔
      sphericalPendulumEnergyMomentum x = (c 0, c 1) := by
  rw [Prod.ext_iff, fst_sphericalPendulumEnergyMomentum, snd_sphericalPendulumEnergyMomentum,
    funext_iff, Fin.forall_fin_two]
  simp [eq_comm]

/-- A point of the phase space of the spherical pendulum is a regular point of `![H, J]` exactly
when it is a regular point of `(H, J)`. -/
private theorem isRegularPoint_sphericalPendulum_iff (x : sphericalPendulumPhaseSpace) :
    IsRegularPoint 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (fun y : sphericalPendulumPhaseSpace ↦
      ![sphericalPendulumHamiltonian y,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]) x ↔
      IsRegularPoint 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) x := by
  set e := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  -- The linear identification and its inverse are regular everywhere.
  have he (a : ℝ × ℝ) : IsRegularPoint 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin 2 → ℝ) e a := by
    rw [isRegularPoint_iff, mfderiv_eq_fderiv, e.fderiv]
    exact e.surjective
  have he' (a : Fin 2 → ℝ) : IsRegularPoint 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ × ℝ) e.symm a := by
    rw [isRegularPoint_iff, mfderiv_eq_fderiv, e.symm.fderiv]
    exact e.symm.surjective
  rw [sphericalPendulum_matrixVec_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ (he _).comp h⟩
  -- `(H, J)` is `![H, J]` followed by the inverse identification.
  have h' := (he' _).comp h
  rwa [← comp_assoc, ContinuousLinearEquiv.symm_symm,
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).self_comp_symm, id_comp] at h'

/-- A vector `c` of the plane is a regular value of `![H, J]` exactly when `(c 0, c 1)` is a
regular value of `(H, J)`. -/
private theorem isRegularValue_sphericalPendulum_iff (c : Fin 2 → ℝ) :
    IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (fun y : sphericalPendulumPhaseSpace ↦
      ![sphericalPendulumHamiltonian y,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]) c ↔
      IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) (c 0, c 1) := by
  rw [isRegularValue_iff, isRegularValue_iff]
  refine forall_congr' fun x ↦ ?_
  rw [isRegularPoint_sphericalPendulum_iff, sphericalPendulum_matrixVec_eq_iff]

/-- **The regular values of the spherical pendulum**: the values `c` of its energy–momentum map
`![H, J]` which are regular values, an open subset of the plane. -/
noncomputable def sphericalPendulumRegularValues : Opens (Fin 2 → ℝ) where
  carrier := range (fun y : sphericalPendulumPhaseSpace ↦
      ![sphericalPendulumHamiltonian y,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]) ∩
    {c | IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (fun y : sphericalPendulumPhaseSpace ↦
      ![sphericalPendulumHamiltonian y,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]) c}
  is_open' := isOpen_range_inter_setOf_isRegularValue
    isIntegrableSystem_sphericalPendulumEnergyMomentum.contMDiff (by simp)
    isProperMap_sphericalPendulumEnergyMomentum.isClosedMap

/-- Membership in `sphericalPendulumRegularValues`, in terms of the energy–momentum map `![H, J]`.
-/
theorem mem_sphericalPendulumRegularValues {c : Fin 2 → ℝ} :
    c ∈ sphericalPendulumRegularValues ↔
      c ∈ range (fun y : sphericalPendulumPhaseSpace ↦
        ![sphericalPendulumHamiltonian y,
          angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
            (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]) ∧
        IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (fun y : sphericalPendulumPhaseSpace ↦
          ![sphericalPendulumHamiltonian y,
            angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
              (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]) c :=
  Iff.rfl

/-- **The regular values of the spherical pendulum, explicitly.** A vector `c = (h, j)` is a
regular value in the image of the energy–momentum map exactly when it lies in the image of `(H, J)`
and is neither `(-1, 0)`, nor `(1, 0)`, nor a point with `j ≠ 0` at which `h` is the minimum
value of the effective potential `V_j` on `(-1, 1)`. -/
theorem mem_sphericalPendulumRegularValues_iff {c : Fin 2 → ℝ} :
    c ∈ sphericalPendulumRegularValues ↔
      (c 0, c 1) ∈ sphericalPendulumEnergyMomentum '' sphericalPendulumPhaseSpace ∧
        (c 0, c 1) ≠ (-1, 0) ∧ (c 0, c 1) ≠ (1, 0) ∧
          ¬ (c 1 ≠ 0 ∧
            IsLeast (sphericalPendulumEffectivePotential (c 1) '' Ioo (-1) 1) (c 0)) := by
  rw [mem_sphericalPendulumRegularValues, isRegularValue_sphericalPendulum_iff,
    isRegularValue_sphericalPendulumEnergyMomentum_iff]
  refine and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, x.property, (sphericalPendulum_matrixVec_eq_iff x c).1 hx⟩
  · rintro ⟨y, hy, hyc⟩
    exact ⟨⟨y, hy⟩, (sphericalPendulum_matrixVec_eq_iff ⟨y, hy⟩ c).2 hyc⟩

/-- **The regular values surround the focus–focus value.** Every vector of the plane close to
`(1, 0)`, other than `(1, 0)` itself, is a regular value in the image of the energy–momentum map of
the spherical pendulum. -/
theorem eventually_mem_sphericalPendulumRegularValues_nhdsNE :
    ∀ᶠ c in 𝓝[≠] ![(1 : ℝ), 0], c ∈ sphericalPendulumRegularValues := by
  -- Read the vectors of the plane as pairs `(c 0, c 1)`.
  have ht : Tendsto (fun c : Fin 2 → ℝ ↦ (c 0, c 1)) (𝓝[≠] ![(1 : ℝ), 0])
      (𝓝[≠] ((1 : ℝ), (0 : ℝ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous fun c : Fin 2 → ℝ ↦ (c 0, c 1) := by fun_prop
      simpa using hc.continuousWithinAt.tendsto (x := ![(1 : ℝ), 0]) (s := {![(1 : ℝ), 0]}ᶜ)
    · filter_upwards [self_mem_nhdsWithin] with c hc
      refine fun h ↦ hc ?_
      rw [mem_singleton_iff, Prod.ext_iff] at h
      rw [mem_singleton_iff]
      ext i
      fin_cases i
      · exact h.1
      · exact h.2
  filter_upwards [ht.eventually (eventually_isRegularValue_sphericalPendulumEnergyMomentum_nhdsNE),
    ht.eventually (nhdsWithin_le_nhds
      (isOpen_interior.mem_nhds mem_interior_image_sphericalPendulumEnergyMomentum))] with c hreg hc
  rw [mem_sphericalPendulumRegularValues, isRegularValue_sphericalPendulum_iff]
  obtain ⟨y, hy, hyc⟩ := interior_subset hc
  exact ⟨⟨⟨y, hy⟩, (sphericalPendulum_matrixVec_eq_iff ⟨y, hy⟩ c).2 hyc⟩, hreg⟩

/-- **The regular part of the phase space of the spherical pendulum**: the open set of states whose
value of the energy–momentum map `![H, J]` is a regular value, the preimage of
`sphericalPendulumRegularValues`. -/
noncomputable def sphericalPendulumRegularPart : Opens sphericalPendulumPhaseSpace :=
  sphericalPendulumRegularValues.comap
    ⟨_, isIntegrableSystem_sphericalPendulumEnergyMomentum.contMDiff.continuous⟩

/-- A state lies in the regular part of the phase space of the spherical pendulum exactly when its
value of `![H, J]` is a regular value. -/
@[simp]
theorem mem_sphericalPendulumRegularPart {x : sphericalPendulumPhaseSpace} :
    x ∈ sphericalPendulumRegularPart ↔
      ![sphericalPendulumHamiltonian x,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))] ∈
        sphericalPendulumRegularValues :=
  Iff.rfl

/-- **The regular part of the spherical pendulum is a Lagrangian torus fibration.** Over the open
set of its regular values `B = sphericalPendulumRegularValues`, the energy–momentum map `![H, J]`
of the spherical pendulum, restricted to the open subset of the phase space lying over `B`, is a
regular Lagrangian torus fibration for the restriction of the symplectic form: a proper submersion
onto `B` with connected Lagrangian fibres. -/
theorem isLagrangianTorusFibration_sphericalPendulum :
    (isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate.mpullback_subtype_val
      sphericalPendulumRegularPart).IsLagrangianTorusFibration 𝓘(ℝ, Fin 2 → ℝ)
      fun x : sphericalPendulumRegularPart ↦ (⟨![sphericalPendulumHamiltonian x,
        angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))],
        mem_sphericalPendulumRegularPart.1 x.property⟩ : sphericalPendulumRegularValues) := by
  refine isIntegrableSystem_sphericalPendulumEnergyMomentum
    |>.isLagrangianTorusFibration_restrictPreimage
      isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate sphericalPendulumRegularValues
      (fun c hc ↦ hc.2) (fun c hc ↦ ?_)
      (IsProperMap.restrictPreimage isProperMap_sphericalPendulumEnergyMomentum _)
  -- The inclusion of the phase space carries the fibre of `![H, J]` over `c` onto the fibre of
  -- `(H, J)` over `(c 0, c 1)`, which is connected.
  set G := fun y : sphericalPendulumPhaseSpace ↦
    ![sphericalPendulumHamiltonian y,
      angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
        (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))]
  obtain ⟨x, rfl⟩ := hc.1
  have hEx := (sphericalPendulum_matrixVec_eq_iff x (G x)).1 rfl
  have himage : Subtype.val '' (G ⁻¹' {G x}) = sphericalPendulumPhaseSpace ∩
      sphericalPendulumEnergyMomentum ⁻¹' {sphericalPendulumEnergyMomentum x} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, ((sphericalPendulum_matrixVec_eq_iff y _).1 hy).trans hEx.symm⟩
    · rintro ⟨hz, hzx⟩
      exact ⟨⟨z, hz⟩, (sphericalPendulum_matrixVec_eq_iff ⟨z, hz⟩ _).2 (hzx.trans hEx), rfl⟩
  have hconn := isConnected_sphericalPendulumPhaseSpace_inter_preimage_singleton
    (mem_image_of_mem _ x.property)
  rw [← himage] at hconn
  exact ⟨hconn.nonempty.of_image,
    Topology.IsEmbedding.subtypeVal.isInducing.isPreconnected_image.1 hconn.isPreconnected⟩

end TauCeti
