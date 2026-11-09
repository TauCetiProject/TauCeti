/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# Restricting moment maps to subgroups and along homomorphisms

Let a Lie group `G` act on a manifold `M` with a moment map `μ : M → 𝔤*` for a two-form `σ`, and
let a second Lie group `K` act on `M` through a homomorphism `φ : K →* G` that is differentiable at
the identity: `k • x = φ k • x`. Write `dφ : 𝔨 → 𝔤` for the differential of `φ` at the identity
(`MonoidHom.groupLieAlgebraMap`). Then the composite of `μ` with the dual map `dφ^* : 𝔤* → 𝔨*`,

`x ↦ μ x ∘ dφ`,

is a moment map of the action of `K`. Indeed, the fundamental vector field of `ξ ∈ 𝔨` is that of
`dφ ξ ∈ 𝔤` (`MonoidHom.fundamentalVectorField_groupLieAlgebraMap`), so the component
`⟨μ ∘ dφ, ξ⟩` is the component `⟨μ, dφ ξ⟩`, whose Hamiltonian vector field is `(dφ ξ)_M = ξ_M`.

Coadjoint equivariance is preserved, because `dφ` intertwines the adjoint actions,
`dφ (Ad_k ξ) = Ad_{φ k} (dφ ξ)` (`MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`).
More precisely, the defect from equivariance of the restricted map is the restriction of the
defect of `μ`,

`θ_K(k, x) = θ_G(φ k, x) ∘ dφ`

(`TauCeti.momentDefect_comp_groupLieAlgebraMap`), so a coadjoint-equivariant moment map restricts
to a coadjoint-equivariant moment map
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_monoidHom`). The main instance is the
restriction of a Hamiltonian action to a Lie subgroup `L ≤ G`, where `φ` is the inclusion and
`μ ∘ dφ` is `μ` followed by restriction of covectors from `𝔤` to the Lie algebra of `L`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_subtype`). This is the moment map of a normal
subgroup used in reduction in stages, and the moment map of a subtorus of a torus action.

## Main results

* `TauCeti.momentDefect_comp_groupLieAlgebraMap`: the defect of `μ ∘ dφ` is the restriction of
  the defect of `μ`.
* `TauCeti.SmoothTwoForm.IsMomentMap.comp_monoidHom`: `μ ∘ dφ` is a moment map of the action of
  `K` by fundamental vector fields.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_monoidHom`: restriction of a group-level
  moment map along a homomorphism.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_subtype`: restriction of a group-level moment
  map to a Lie subgroup.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, §22 (restriction of Hamiltonian actions
  to subgroups).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §12.3 (momentum maps of subgroup actions).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

section Defect

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I 1 G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace HK]
  {J : ModelWithCorners 𝕜 F HK} {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]
  [LieGroup J 1 K]
  {M : Type*} [MulAction G M] [MulAction K M] {μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)}

/-- **The defect of a restricted map.** If `K` acts through a homomorphism `φ : K →* G` that is
differentiable at the identity, the defect from coadjoint equivariance of `x ↦ μ x ∘ dφ` is the
defect of `μ` at `φ k`, restricted along `dφ`. -/
theorem momentDefect_comp_groupLieAlgebraMap {φ : K →* G}
    (hsmul : ∀ (k : K) (x : M), k • x = φ k • x) (hφ : MDifferentiableAt J I φ 1) (k : K)
    (x : M) :
    momentDefect (fun y ↦ (μ y).comp (φ.groupLieAlgebraMap J I).toLinearMap) k x =
      (momentDefect μ (φ k) x).comp (φ.groupLieAlgebraMap J I).toLinearMap := by
  ext ξ
  have hAd := φ.groupLieAlgebraMap_adjointContinuousLinearMap hφ k⁻¹ ξ
  rw [map_inv] at hAd
  simp only [momentDefect_def, LinearMap.sub_apply, LinearMap.comp_apply,
    Lie.coadjointRepresentation_apply, ContinuousLinearMap.coe_coe, hsmul, hAd]

end Defect

namespace SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup J (minSmoothness ℝ 3) K]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] [MulAction K M] [ContMDiffSMul J I' ∞ K M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] lieGroupOne

/-- **Restriction of a moment map along a homomorphism.** If `K` acts through a homomorphism
`φ : K →* G` that is differentiable at the identity, and `μ` is a moment map of the action of `G`
by fundamental vector fields, then `x ↦ μ x ∘ dφ` is a moment map of the action of `K` by
fundamental vector fields. -/
theorem IsMomentMap.comp_monoidHom
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (φ : K →* G)
    (hφ : MDifferentiableAt J I φ 1) (hsmul : ∀ (k : K) (x : M), k • x = φ k • x) :
    σ.IsMomentMap (InfinitesimalAction.fundamental J K I' M) fun x ↦
      (μ x).comp (φ.groupLieAlgebraMap J I).toLinearMap where
  contMDiff ξ := by
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] using
      h.contMDiff (φ.groupLieAlgebraMap J I ξ)
  isHamiltonianVectorField ξ := by
    have hX := h.isHamiltonianVectorField (φ.groupLieAlgebraMap J I ξ)
    rw [InfinitesimalAction.fundamental_apply,
      φ.fundamentalVectorField_groupLieAlgebraMap hφ hsmul] at hX
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      InfinitesimalAction.fundamental_apply] using hX

namespace IsEquivariantMomentMap

/-- **Restriction of a group-level moment map along a homomorphism.** If `K` acts through a
homomorphism `φ : K →* G` that is differentiable at the identity, `k • x = φ k • x`, and `μ` is a
coadjoint-equivariant moment map of the action of `G`, then `x ↦ μ x ∘ dφ` is a
coadjoint-equivariant moment map of the action of `K`, where `dφ` is the differential of `φ` at the
identity. -/
theorem comp_monoidHom (h : σ.IsEquivariantMomentMap μ) (φ : K →* G)
    (hφ : MDifferentiableAt J I φ 1) (hsmul : ∀ (k : K) (x : M), k • x = φ k • x) :
    σ.IsEquivariantMomentMap fun x ↦
      (μ x).comp (φ.groupLieAlgebraMap J I).toLinearMap := by
  have hμ := (isEquivariantMomentMap_iff_momentDefect_eq_zero.1 h).2
  refine isEquivariantMomentMap_iff_momentDefect_eq_zero.2
    ⟨h.toIsMomentMap.comp_monoidHom φ hφ hsmul, fun k x ↦ ?_⟩
  rw [momentDefect_comp_groupLieAlgebraMap hsmul hφ, hμ, LinearMap.zero_comp]

/-- **Restriction of a group-level moment map to a Lie subgroup.** If a subgroup `L` of `G` carries
a Lie group structure for which the inclusion is differentiable at the identity, a
coadjoint-equivariant moment map `μ` of the action of `G` restricts to the coadjoint-equivariant
moment map `x ↦ μ x ∘ dι` of the action of `L`, where `dι` is the differential of the inclusion
`ι : L → G` at the identity. -/
theorem comp_subtype {L : Subgroup G} [ChartedSpace HK L] [LieGroup J (minSmoothness ℝ 3) L]
    [ContMDiffSMul J I' ∞ L M] (h : σ.IsEquivariantMomentMap μ)
    (hL : MDifferentiableAt J I (Subtype.val : L → G) 1) :
    σ.IsEquivariantMomentMap fun x ↦
      (μ x).comp (L.subtype.groupLieAlgebraMap J I).toLinearMap :=
  h.comp_monoidHom L.subtype hL fun _ _ ↦ (Subgroup.smul_def _ _)

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
