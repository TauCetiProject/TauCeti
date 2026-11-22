/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
import TauCeti.LinearAlgebra.Dual.Annihilator

/-!
# The candidate residual moment map of reduction in stages, along the level

Let a Lie group `G` act on a manifold `M` with a coadjoint-equivariant moment map `μ : M → 𝔤*`,
and let `N` be a closed normal subgroup of `G` with Lie algebra `𝔫 ⊆ 𝔤`. Reduction in stages
reduces first by `N`, then by the residual action of `G ⧸ N`. The moment map of `N` is the
restriction `μ_N = μ|𝔫` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_subtype`), and this
file supplies the pointwise data of the second stage, for **level data supplied as a map**
`i : Z → M` into the zero level of `μ_N`, as in `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction`.
Everything here lives on `Z`, before passing to the first reduced space; the descent to that space
and the moment map property there are not proved here.

* On the zero level of `μ_N`, the moment map `μ` takes values in the annihilator `𝔫⁰`
  (`TauCeti.Lie.comp_groupLieAlgebraMap_subtype_eq_zero_iff`), and this
  level is invariant under the normalizer of `N`
  (`TauCeti.apply_smul_mem_dualAnnihilator_groupLieSubalgebra`).
* Through the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰`, the restriction of `μ` to the level is a map
  `TauCeti.residualMomentMapLift : Z → (𝔤 ⧸ 𝔫)*`, characterized by `⟨μ_res z, [ξ]⟩ = ⟨μ (i z), ξ⟩`.
  It is the candidate lift to `Z` of the residual moment map on the first reduced space.
* Write `[g] · φ` for the dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*` induced by the adjoint
  representation, and pull it back along `G → G ⧸ N` to an action of `G` by `g · φ = [g] · φ`.
  If `G` acts on `Z` compatibly with `i` and `μ` is coadjoint-equivariant, the map is
  `G`-equivariant for this pulled-back action, `μ_res (g • z) = [g] · μ_res z`
  (`TauCeti.residualMomentMapLift_smul`). Likewise, if `N` acts on `Z` compatibly with `i`, the
  map is `N`-invariant
  (`TauCeti.residualMomentMapLift_subgroup_smul_eq_self`); this is the invariance needed for it
  to descend along the projection to the first reduced space. This pulled-back equivariance is
  what is proved here, and it uses no Lie group structure on `G ⧸ N`. When `G ⧸ N` carries a
  quotient Lie group structure, the differential at the identity of the projection `G → G ⧸ N`
  induces a canonical isomorphism `𝔤 ⧸ 𝔫 ≃ Lie(G ⧸ N)`, and under it the dual action corresponds
  to the coadjoint action of `G ⧸ N`; that comparison is not proved here.
* At every point `z` where `i` is manifold differentiable, the components of the map satisfy the
  moment map equation pulled back to `Z`: `d⟨μ_res, [ξ]⟩ = i^* (ι_{ξ_M} σ)` at `z`
  (`TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_residualMomentMapLift_apply_mk`). This is the
  equation to be descended along reduction data `p : Z → Q`, `p^* η = i^* σ`, to the moment map of
  the residual action on the first reduced space.

## Main definitions

* `TauCeti.residualMomentMapLift`: the map `Z → (𝔤 ⧸ 𝔫)*` induced by `μ` on the zero level of
  `μ_N`, the candidate lift of the residual moment map.

## Main results

* `TauCeti.residualMomentMapLift_eq_zero_iff`: the map vanishes exactly where `μ` does.
* `TauCeti.residualMomentMapLift_smul`: the map is `G`-equivariant for the dual action of `G ⧸ N`
  pulled back to `G`.
* `TauCeti.residualMomentMapLift_subgroup_smul_eq_self`: the map is `N`-invariant.
* `TauCeti.contMDiff_residualMomentMapLift_apply`: its components are of class `C^n` along a
  `C^n` level map, when the components of `μ` are.
* `TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_residualMomentMapLift_apply_mk`: the moment map
  equation of the map along the level, at points where `i` is manifold differentiable.

## References

* J. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007 (reduction by a normal subgroup).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

open Lie

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {M Z : Type*} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {N : Subgroup G} {i : Z → M}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable (μ N i) in
/-- **The candidate lift to the level of the residual moment map of reduction in stages.** For a
map `i : Z → M` into the zero level of the moment map of `N`, so that `μ (i z)` annihilates the Lie
algebra `𝔫` of `N`, this sends `z` to `μ (i z)` read as a linear form on `𝔤 ⧸ 𝔫`, through the
identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` (`Submodule.dualQuotEquivDualAnnihilator`). When `N` is closed and
normal, `μ_res (n • z) = μ_res z` for `n ∈ N` whenever `i (n • z) = n • i z` and `μ` is
coadjoint-equivariant for `n` at `i z` (`TauCeti.residualMomentMapLift_subgroup_smul_eq_self`); its
descent to the first reduced space, and the moment map property of the descended map, are not part
of this definition. -/
def residualMomentMapLift
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    (z : Z) :
    Module.Dual ℝ (GroupLieAlgebra I G ⧸ (N.groupLieSubalgebra (I := I)).toSubmodule) :=
  (N.groupLieSubalgebra (I := I)).toSubmodule.dualQuotEquivDualAnnihilator.symm
    ⟨μ (i z), hi z⟩

/-- The definition of `TauCeti.residualMomentMapLift`, whose body is not exposed. -/
theorem residualMomentMapLift_def
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    (z : Z) :
    residualMomentMapLift μ N i hi z =
      (N.groupLieSubalgebra (I := I)).toSubmodule.dualQuotEquivDualAnnihilator.symm
        ⟨μ (i z), hi z⟩ :=
  (rfl)

/-- The lifted residual moment map takes the value `⟨μ (i z), ξ⟩` on the class of `ξ`. -/
@[simp]
theorem residualMomentMapLift_apply_mk
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    (z : Z) (ξ : GroupLieAlgebra I G) :
    residualMomentMapLift μ N i hi z (Submodule.Quotient.mk ξ) = μ (i z) ξ := by
  rw [residualMomentMapLift_def, Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk,
    Submodule.dualAnnihilator_mk_apply]

/-- Under the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰`, the lifted residual moment map is `μ ∘ i`. -/
@[simp]
theorem dualQuotEquivDualAnnihilator_residualMomentMapLift
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    (z : Z) :
    (N.groupLieSubalgebra (I := I)).toSubmodule.dualQuotEquivDualAnnihilator
      (residualMomentMapLift μ N i hi z) = ⟨μ (i z), hi z⟩ := by
  rw [residualMomentMapLift_def, LinearEquiv.apply_symm_apply]

/-- The lifted residual moment map vanishes at `z` exactly when `μ` vanishes at `i z`. -/
@[simp]
theorem residualMomentMapLift_eq_zero_iff
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    (z : Z) :
    residualMomentMapLift μ N i hi z = 0 ↔ μ (i z) = 0 := by
  rw [residualMomentMapLift_def, LinearEquiv.map_eq_zero_iff, Submodule.mk_eq_zero]

/-- **The lifted residual moment map is `G`-equivariant for the pulled-back dual action.** Let `g`
act on `(𝔤 ⧸ 𝔫)*` through its class `[g] ∈ G ⧸ N`, by the dual of the action of `G ⧸ N` on
`𝔤 ⧸ 𝔫` induced by the adjoint representation. If `i (g • z) = g • i z` and `μ` is
coadjoint-equivariant for `g` at `i z`, then `μ_res (g • z) = [g] · μ_res z`. -/
theorem residualMomentMapLift_smul [SMul G M] [SMul G Z] [N.Normal]
    (hN : IsClosed (N : Set G))
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    {g : G} {z : Z} (hiG : i (g • z) = g • i z)
    (hμ : μ (g • i z) = coadjointRepresentation ℝ I G g (μ (i z))) :
    residualMomentMapLift μ N i hi (g • z) =
      (N.quotientAdjointRepresentation (I := I) hN).dual g (residualMomentMapLift μ N i hi z) := by
  rw [residualMomentMapLift_def, residualMomentMapLift_def,
    ← dualQuotEquivDualAnnihilator_symm_coadjointRepresentation_apply hN g (hi z)]
  congr 2
  rw [hiG, hμ]

/-- **The lifted residual moment map is `N`-invariant**: `μ_res (n • z) = μ_res z` for `n ∈ N`.
This assumes that `N` is closed and normal, and uses only an action of `N` on `Z`, compatibility
`i (n • z) = n • i z` of `i` with `n` at `z`, and the coadjoint equivariance of `μ` for `n` at
`i z`. -/
theorem residualMomentMapLift_subgroup_smul_eq_self [SMul G M] [SMul N Z] [N.Normal]
    (hN : IsClosed (N : Set G))
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    {n : N} {z : Z} (hiN : i (n • z) = (n : G) • i z)
    (hμ : μ ((n : G) • i z) = coadjointRepresentation ℝ I G n (μ (i z))) :
    residualMomentMapLift μ N i hi (n • z) = residualMomentMapLift μ N i hi z := by
  rw [residualMomentMapLift_def, residualMomentMapLift_def]
  congr 2
  rw [hiN, hμ]
  exact coadjointRepresentation_apply_eq_self_of_mem_dualAnnihilator_groupLieSubalgebra
    hN n.property (hi z)

section Regularity

variable {E' H' E₀ H₀ : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace Z] [ChartedSpace H₀ Z]

/-- **The components of the lifted residual moment map are of class `C^n`** along a level map `i`
of class `C^n`, when the components `⟨μ, ξ⟩` of `μ` are: on the class of `ξ` the component is
`⟨μ, ξ⟩ ∘ i`. -/
theorem contMDiff_residualMomentMapLift_apply {n : WithTop ℕ∞}
    (hμ : ∀ ξ : GroupLieAlgebra I G, ContMDiff I' 𝓘(ℝ) n fun x ↦ μ x ξ)
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    (hi' : ContMDiff I₀ I' n i)
    (q : GroupLieAlgebra I G ⧸ (N.groupLieSubalgebra (I := I)).toSubmodule) :
    ContMDiff I₀ 𝓘(ℝ) n fun z ↦ residualMomentMapLift μ N i hi z q := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [residualMomentMapLift_apply_mk]
  exact (hμ ξ).comp hi'

end Regularity

namespace SmoothTwoForm.IsMomentMap

variable {E' H' E₀ H₀ : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace Z] [ChartedSpace H₀ Z]
  {σ : SmoothTwoForm I' M} {a : InfinitesimalAction (GroupLieAlgebra I G) I' M}

/-- **The moment map equation of the lifted residual moment map along the level.** If `μ` is a
moment map for `σ` and the generated vector fields `ξ_M`, and `i : Z → M` is differentiable at
`z`, then the component of the lifted residual moment map along the class of `ξ` has derivative
`v ↦ σ(ξ_M (i z), di v)` at `z`: it is `i^* (ι_{ξ_M} σ) = d⟨μ ∘ i, ξ⟩`. -/
theorem mvfderiv_residualMomentMapLift_apply_mk (h : σ.IsMomentMap a μ)
    (hi : ∀ z, μ (i z) ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator)
    (ξ : GroupLieAlgebra I G) {z : Z} (hi' : MDifferentiableAt I₀ I' i z)
    (v : TangentSpace I₀ z) :
    mvfderiv I₀ (fun z ↦ residualMomentMapLift μ N i hi z (Submodule.Quotient.mk ξ)) z v =
      SmoothBundleForm.eval₂ σ (i z) (a ξ (i z)) (mfderiv I₀ I' i z v) := by
  have hcomp : (fun z ↦ residualMomentMapLift μ N i hi z (Submodule.Quotient.mk ξ)) =
      (fun x ↦ μ x ξ) ∘ i :=
    funext fun z ↦ residualMomentMapLift_apply_mk hi z ξ
  rw [hcomp, mvfderiv_comp_apply z (((h.contMDiff ξ) (i z)).mdifferentiableAt (by simp))
    hi',
    isHamiltonianVectorField_iff.1 (h.isHamiltonianVectorField ξ)]

end SmoothTwoForm.IsMomentMap

end TauCeti
