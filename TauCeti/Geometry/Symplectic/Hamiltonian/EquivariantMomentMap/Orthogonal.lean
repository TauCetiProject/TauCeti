/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Unitary.Adjoint
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# Shifted moment maps of the orthogonal group of a plane

For a connected Lie group, a moment map is coadjoint-equivariant as soon as its cocycle vanishes
(`TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero`). For
a group with several connected components this fails, and equivariance needs in addition one
element of each component acting equivariantly (`SmoothTwoForm.IsMomentMap.`
`isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero_and_apply_smul`).
This file shows that the component condition cannot be dropped, already for the orthogonal group
`O(2)` of a two-dimensional real inner product space `V`, whose two components are the rotations
`SO(2)` and the reflections.

The coadjoint representation of `O(2)` is the determinant: rotations act trivially on `so(2)*`
and reflections act by `-1` (`TauCeti.coadjointRepresentation_unitary_eq_det_smul`). Let `μ` be a
coadjoint-equivariant moment map of a smooth action of `O(2)` on a manifold with a two-form `σ`,
for instance the moment map of the cotangent lift of the rotations and reflections of `V` to
`T*V`, and shift it by a constant `ν ∈ so(2)*`. The shifted map `μ + ν` is again a moment map, and:

* it is equivariant under an element `g` exactly when `g` is a rotation or `ν = 0`, since
  `Ad*_g ν = ν` for a rotation and `Ad*_g ν = -ν` for a reflection
  (`TauCeti.coadjointRepresentation_unitary_eq_self_iff`);
* in particular it is equivariant under the identity component `SO(2)`, an open subgroup, so its
  cocycle vanishes at every point
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_add_const_eq_zero`);
* but it is coadjoint-equivariant only for `ν = 0`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isEquivariantMomentMap_add_const_iff`).

So for `ν ≠ 0` the shift `μ + ν` is infinitesimally equivariant and equivariant on the identity
component, and it is the equivariance of a reflection, the component condition, that fails. For
the cotangent lift to `T*V` this is
`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap_add_const_iff`.

## References

* E. Meinrenken, *Symplectic Geometry*, lecture notes, University of Toronto, 2000, Remark 7.13
  (equivariance of moment maps for connected and disconnected groups).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §12.3 (the nonequivariance cocycle and shifted momentum maps).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

local notation "O(" V ")" => unitary (V →L[ℝ] V)

local notation "𝔬(" V ")" => GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V))

namespace SmoothTwoForm.IsEquivariantMomentMap

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction O(V) M]
  [ContMDiffSMul (Unitary.model (V →L[ℝ] V)) I' ∞ O(V) M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ 𝔬(V)}

/-- **A shifted moment map of `O(2)` has vanishing cocycle.** For a two-dimensional real inner
product space `V`, a coadjoint-equivariant moment map `μ` of an action of `O(V)` and any constant
`ν ∈ so(V)*`, the cocycle of the moment map `μ + ν` vanishes at every point: `μ + ν` is
equivariant under the rotations, an open subgroup. -/
theorem momentCocycle_add_const_eq_zero (h : σ.IsEquivariantMomentMap μ) (hV : finrank ℝ V = 2)
    (ν : Module.Dual ℝ 𝔬(V)) (x : M) :
    σ.momentCocycle (InfinitesimalAction.fundamental (Unitary.model (V →L[ℝ] V)) O(V) I' M)
      (fun y ↦ μ y + ν) x = 0 :=
  (h.toIsMomentMap.add_const ν).momentCocycle_eq_zero_of_eventually_apply_smul <|
    Filter.eventually_of_mem (isOpen_specialOrthogonalGroup.mem_nhds (one_mem _)) fun g hg ↦ by
      rw [h.apply_smul, map_add,
        (coadjointRepresentation_unitary_eq_self_iff hV (ν := ν)).2 (Or.inl hg)]

/-- **A shifted moment map of `O(2)` is equivariant only without shift.** For a two-dimensional
real inner product space `V`, a coadjoint-equivariant moment map `μ` of an action of `O(V)` on a
nonempty manifold and a constant `ν ∈ so(V)*`, the shift `μ + ν` is coadjoint-equivariant exactly
when `ν = 0`, although its cocycle vanishes for every `ν`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_add_const_eq_zero`): a reflection
acts on `so(V)*` by `-1`. -/
theorem isEquivariantMomentMap_add_const_iff [Nonempty M] (h : σ.IsEquivariantMomentMap μ)
    (hV : finrank ℝ V = 2) (ν : Module.Dual ℝ 𝔬(V)) :
    σ.IsEquivariantMomentMap (fun x ↦ μ x + ν) ↔ ν = 0 := by
  rw [h.add_const_iff]
  refine ⟨fun hν ↦ ?_, fun hν g ↦ by rw [hν, map_zero]⟩
  obtain ⟨r, hr⟩ := Unitary.exists_det_eq_neg_one (V := V) (by omega)
  refine ((coadjointRepresentation_unitary_eq_self_iff hV).1 (hν r)).resolve_left fun hrs ↦ ?_
  rw [mem_specialOrthogonalGroup_iff, hr] at hrs
  norm_num at hrs

end SmoothTwoForm.IsEquivariantMomentMap

namespace CotangentBundle

/-- **Shifted cotangent moment maps of `O(2)`.** For a two-dimensional real inner product space
`V`, the moment map `μ` of the cotangent lift to `T*V` of the action of `O(V)` on `V`, shifted by
a constant `ν ∈ so(V)*`, is coadjoint-equivariant exactly when `ν = 0`, although its cocycle
vanishes for every `ν`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_add_const_eq_zero` applied to
`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap`). -/
theorem isEquivariantMomentMap_momentMap_add_const_iff (hV : finrank ℝ V = 2)
    (ν : Module.Dual ℝ 𝔬(V)) :
    (symplecticForm 𝓘(ℝ, V) V).IsEquivariantMomentMap
        (fun z ↦ momentMap (Unitary.model (V →L[ℝ] V)) O(V) z + ν) ↔ ν = 0 :=
  have : Nonempty (CotangentBundle 𝓘(ℝ, V) V) := ⟨⟨(0 : V), 0⟩⟩
  isEquivariantMomentMap_momentMap.isEquivariantMomentMap_add_const_iff hV ν

end CotangentBundle

end TauCeti
