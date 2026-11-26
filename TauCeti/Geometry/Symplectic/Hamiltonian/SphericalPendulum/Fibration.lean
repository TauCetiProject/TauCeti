/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Regular
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.TurningPoint
import Mathlib.Topology.LocalAtTarget
import TauCeti.Geometry.Manifold.RegularValue.Factorization
import TauCeti.Topology.Connected.Basic

/-!
# The regular part of the spherical pendulum is a Lagrangian torus fibration

The spherical pendulum is the completely integrable system `F = (H, J)` on `T*S²`, with energy
`H(q, p) = ‖p‖² / 2 + q₃` and vertical angular momentum `J(q, p) = q₁ p₂ - q₂ p₁`
(`TauCeti.isIntegrableSystem_sphericalPendulumEnergyMomentumVec`, which reads `F` as the map
`TauCeti.sphericalPendulumEnergyMomentumVec`, that is `![H, J]`, into `Fin 2 → ℝ`). Its critical
values are the values `(-1, 0)` and `(1, 0)` of the two equilibria and the curve of relative
equilibria
(`TauCeti.image_setOf_not_isRegularPoint_sphericalPendulumEnergyMomentum`).

This file collects the regular values of `F` lying in its image into an open subset `B` of the
plane (`TauCeti.sphericalPendulumRegularValues`): these are the values of `F` other than the
values `(-1, 0)` and `(1, 0)` of the equilibria and the values of the relative equilibria
(`TauCeti.mem_sphericalPendulumRegularValues_iff_mem_image_and_ne`); off the axis `j = 0` they lie
strictly above the curve of relative equilibria
(`TauCeti.mem_sphericalPendulumTurningPointDomain_of_mem_sphericalPendulumRegularValues`). The
energy–momentum map is proper and its fibres are connected, so over every open set `U ⊆ B` of
regular values, for instance `B` itself, it is a regular Lagrangian torus fibration on the open set
of states over `U` (`TauCeti.isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec`), an
instance of `TauCeti.SmoothTwoForm.IsIntegrableSystem.isLagrangianTorusFibration_restrictPreimage`.
So its fibres are two-tori (`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`), and it
carries the fibrewise action of `T*U` and the period lattices
(`IsLagrangianTorusFibration.periodLattice`) of Lagrangian torus fibrations.

The base `B` contains a punctured neighbourhood of `(1, 0)`
(`TauCeti.eventually_mem_sphericalPendulumRegularValues_nhdsNE`), so loops of regular values
around the focus–focus value lie in `B`; transport of the period lattice of this fibration around
such a loop is the Hamiltonian monodromy of the spherical pendulum.

## Main declarations

* `TauCeti.sphericalPendulumRegularValues`: the open set of regular values in the image of `F`.
* `TauCeti.mem_sphericalPendulumRegularValues_iff_mem_image_and_ne`: its explicit description.
* `TauCeti.mem_sphericalPendulumTurningPointDomain_of_mem_sphericalPendulumRegularValues`: a regular
  value off the axis lies strictly above the curve of relative equilibria.
* `TauCeti.eventually_mem_sphericalPendulumRegularValues_nhdsNE`: it contains a punctured
  neighbourhood of the focus–focus value `(1, 0)`.
* `TauCeti.isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec`: over every open set of
  regular values, in particular over all of them, `F` is a regular Lagrangian torus fibration.

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

/-- **The regular values of the spherical pendulum**: the values `c` of its energy–momentum map
`![H, J]` which are regular values, an open subset of the plane. -/
noncomputable def sphericalPendulumRegularValues : Opens (Fin 2 → ℝ) where
  carrier := range sphericalPendulumEnergyMomentumVec ∩
    {c | IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) sphericalPendulumEnergyMomentumVec c}
  is_open' := isOpen_range_inter_setOf_isRegularValue
    isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff (by simp)
    isProperMap_sphericalPendulumEnergyMomentumVec.isClosedMap

/-- Membership in `sphericalPendulumRegularValues`, in terms of the energy–momentum map `![H, J]`.
-/
@[simp]
theorem mem_sphericalPendulumRegularValues_iff {c : Fin 2 → ℝ} :
    c ∈ sphericalPendulumRegularValues ↔ c ∈ range sphericalPendulumEnergyMomentumVec ∧
      IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) sphericalPendulumEnergyMomentumVec c :=
  Iff.rfl

/-- **The regular values of the spherical pendulum, explicitly.** A vector `c = (h, j)` is a
regular value in the image of the energy–momentum map exactly when it lies in the image of `(H, J)`
and is neither `(-1, 0)`, nor `(1, 0)`, nor a point with `j ≠ 0` at which `h` is the minimum
value of the effective potential `V_j` on `(-1, 1)`. -/
theorem mem_sphericalPendulumRegularValues_iff_mem_image_and_ne {c : Fin 2 → ℝ} :
    c ∈ sphericalPendulumRegularValues ↔
      (c 0, c 1) ∈ sphericalPendulumEnergyMomentum '' sphericalPendulumPhaseSpace ∧
        (c 0, c 1) ≠ (-1, 0) ∧ (c 0, c 1) ≠ (1, 0) ∧
          ¬ (c 1 ≠ 0 ∧
            IsLeast (sphericalPendulumEffectivePotential (c 1) '' Ioo (-1) 1) (c 0)) := by
  rw [mem_sphericalPendulumRegularValues_iff, isRegularValue_sphericalPendulumEnergyMomentumVec_iff,
    isRegularValue_sphericalPendulumEnergyMomentum_iff]
  refine and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, x.property, (sphericalPendulumEnergyMomentumVec_eq_iff x c).1 hx⟩
  · rintro ⟨y, hy, hyc⟩
    exact ⟨⟨y, hy⟩, (sphericalPendulumEnergyMomentumVec_eq_iff ⟨y, hy⟩ c).2 hyc⟩

/-- **Regular values off the axis lie above the relative equilibria.** A regular value `(h, j)` in
the image of the energy–momentum map of the spherical pendulum with `j ≠ 0` lies strictly above
the curve of relative equilibria: `h` exceeds the minimum of the effective potential `V_j`. -/
theorem mem_sphericalPendulumTurningPointDomain_of_mem_sphericalPendulumRegularValues
    {c : Fin 2 → ℝ} (hc : c ∈ sphericalPendulumRegularValues) (hc₁ : c 1 ≠ 0) :
    (c 0, c 1) ∈ sphericalPendulumTurningPointDomain := by
  obtain ⟨himg, -, -, hleast⟩ := mem_sphericalPendulumRegularValues_iff_mem_image_and_ne.1 hc
  obtain ⟨z₀, hz₀, hmin⟩ := (existsUnique_isMinOn_sphericalPendulumEffectivePotential hc₁).exists
  have hle := (mk_mem_image_sphericalPendulumEnergyMomentum_iff_of_isMinOn hc₁ hz₀ hmin _).1 himg
  -- If `h` were the minimum value `V_j(z₀)`, it would be the least value of `V_j`.
  refine mem_sphericalPendulumTurningPointDomain_iff.2
    ⟨hc₁, z₀, hz₀, hle.lt_of_ne fun heq ↦ hleast ⟨hc₁, ⟨z₀, hz₀, heq⟩, ?_⟩⟩
  rintro _ ⟨z, hz, rfl⟩
  exact heq ▸ hmin hz

/-- **The regular values surround the focus–focus value.** Every vector of the plane close to
`(1, 0)`, other than `(1, 0)` itself, is a regular value in the image of the energy–momentum map of
the spherical pendulum. -/
theorem eventually_mem_sphericalPendulumRegularValues_nhdsNE :
    ∀ᶠ c in 𝓝[≠] ![(1 : ℝ), 0], c ∈ sphericalPendulumRegularValues := by
  -- Read the vectors of the plane as pairs `(c 0, c 1)`.
  have ht : Tendsto (Homeomorph.finTwoArrow (X := ℝ)) (𝓝[≠] ![(1 : ℝ), 0])
      (𝓝[≠] ((1 : ℝ), (0 : ℝ))) :=
    (Homeomorph.finTwoArrow.map_punctured_nhds_eq _).le
  filter_upwards [ht.eventually (eventually_isRegularValue_sphericalPendulumEnergyMomentum_nhdsNE),
    ht.eventually (nhdsWithin_le_nhds
      (isOpen_interior.mem_nhds mem_interior_image_sphericalPendulumEnergyMomentum))] with c hreg hc
  rw [mem_sphericalPendulumRegularValues_iff, isRegularValue_sphericalPendulumEnergyMomentumVec_iff]
  obtain ⟨y, hy, hyc⟩ := interior_subset hc
  exact ⟨⟨⟨y, hy⟩, (sphericalPendulumEnergyMomentumVec_eq_iff ⟨y, hy⟩ c).2 hyc⟩, hreg⟩

/-- **The spherical pendulum is a Lagrangian torus fibration over every open set of regular
values.** Let `U` be an open set of regular values in the image of the energy–momentum map `![H, J]`
of the spherical pendulum, for instance the set `sphericalPendulumRegularValues` of all of them.
Restricted to the open subset of the phase space lying over `U`, the map `![H, J]` is a regular
Lagrangian torus fibration onto `U` for the restriction of the symplectic form: a proper submersion
with connected Lagrangian fibres. -/
theorem isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec
    {U : Opens (Fin 2 → ℝ)} (hU : U ≤ sphericalPendulumRegularValues) :
    (isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate.mpullback_subtype_val
      (U.comap ⟨_, isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff.continuous⟩)
      ).IsLagrangianTorusFibration 𝓘(ℝ, Fin 2 → ℝ)
      fun x ↦ (⟨sphericalPendulumEnergyMomentumVec x, x.property⟩ : U) := by
  refine isIntegrableSystem_sphericalPendulumEnergyMomentumVec
    |>.isLagrangianTorusFibration_restrictPreimage
      isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate U
      (fun c hc ↦ (hU hc).2) (fun c hc ↦ ?_)
      (IsProperMap.restrictPreimage isProperMap_sphericalPendulumEnergyMomentumVec _)
  -- The inclusion of the phase space carries the fibre of `![H, J]` over `c` onto the fibre of
  -- `(H, J)` over `(c 0, c 1)`, which is connected.
  obtain ⟨x, rfl⟩ := (hU hc).1
  have hfib : sphericalPendulumEnergyMomentumVec ⁻¹' {sphericalPendulumEnergyMomentumVec x} =
      Subtype.val ⁻¹'
        (sphericalPendulumEnergyMomentum ⁻¹' {sphericalPendulumEnergyMomentum x}) := by
    ext y
    simp [sphericalPendulumEnergyMomentumVec_eq_iff, Prod.ext_iff]
  rw [← Topology.IsInducing.subtypeVal.isConnected_image, hfib, Subtype.image_preimage_coe]
  exact isConnected_sphericalPendulumPhaseSpace_inter_preimage_singleton
    (mem_image_of_mem _ x.property)

end TauCeti
