/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# The residual moment map of reduction in stages, along the level

Let a Lie group `G` act on a manifold `M` with a coadjoint-equivariant moment map `μ : M → 𝔤*`,
and let `N` be a closed normal subgroup of `G` with Lie algebra `𝔫 ⊆ 𝔤`. Reduction in stages
reduces first by `N`, then by the residual action of `G ⧸ N`. The moment map of `N` is the
restriction `μ_N = μ|𝔫` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_subtype`), and this
file supplies the pointwise data of the second stage, for **level data supplied as a map**
`i : Z → M` into the zero level of `μ_N`, as in `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction`.
Everything here lives on `Z`, before passing to the first reduced space.

* On the zero level of `μ_N`, the moment map `μ` takes values in the annihilator `𝔫⁰`
  (`TauCeti.Lie.EmbeddedLieSubgroupData.comp_groupLieAlgebraMap_subtype_eq_zero_iff`), and this
  level is invariant under the normalizer of `N`
  (`TauCeti.apply_smul_mem_dualAnnihilator_groupLieSubalgebraOfSubgroup`).
* Through the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰`, the restriction of `μ` to the level is a map
  `TauCeti.residualMomentMapLift : Z → (𝔤 ⧸ 𝔫)*`, characterized by `⟨μ_res z, [ξ]⟩ = ⟨μ (i z), ξ⟩`.
  It is the lift to `Z` of the residual moment map on the first reduced space.
* If `G` acts on `Z` compatibly with `i`, this map is equivariant for the dual action of `G ⧸ N`
  on `(𝔤 ⧸ 𝔫)*` (`TauCeti.residualMomentMapLift_smul`), and it is invariant under `N`
  (`TauCeti.residualMomentMapLift_subgroup_smul`). No Lie group structure on `G ⧸ N` is needed;
  under the identification `Lie(G ⧸ N) ≃ 𝔤 ⧸ 𝔫` of a quotient Lie group structure on `G ⧸ N`,
  this dual action corresponds to the coadjoint action of `G ⧸ N`.
* The components of the map satisfy the moment map equation pulled back to `Z`:
  `d⟨μ_res, [ξ]⟩ = i^* (ι_{ξ_M} σ)`
  (`TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_residualMomentMapLift_apply_mk`). This is the
  equation to be descended along reduction data `p : Z → Q`, `p^* η = i^* σ`, to the moment map of
  the residual action on the first reduced space.

## Main definitions

* `TauCeti.residualMomentMapLift`: the map `Z → (𝔤 ⧸ 𝔫)*` induced by `μ` on the zero level of
  `μ_N`.

## Main results

* `TauCeti.apply_smul_mem_dualAnnihilator_groupLieSubalgebraOfSubgroup`: the zero level of `μ_K`
  is invariant under the normalizer of `K`.
* `TauCeti.residualMomentMapLift_eq_zero_iff`: the map vanishes exactly where `μ` does.
* `TauCeti.residualMomentMapLift_smul`: the map is `G ⧸ N`-equivariant.
* `TauCeti.residualMomentMapLift_subgroup_smul`: the map is `N`-invariant.
* `TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_residualMomentMapLift_apply_mk`: its components
  are smooth along a smooth level.
* `TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_residualMomentMapLift_apply_mk`: the moment map
  equation of the map along the level.

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
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {M Z : Type*} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {N : Subgroup G} {i : Z → M}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The zero level of the moment map of a subgroup is invariant under its normalizer.** If `μ`
is coadjoint-equivariant and `μ x` annihilates the Lie algebra `𝔨` of a subgroup `K`, then so does
`μ (g • x)` for every `g` in the normalizer of `K`. -/
theorem apply_smul_mem_dualAnnihilator_groupLieSubalgebraOfSubgroup [SMul G M] {K : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hμ : ∀ (g : G) (x : M), μ (g • x) = coadjointRepresentation ℝ I G g (μ x)) {x : M}
    (hx : μ x ∈ (groupLieSubalgebraOfSubgroup (I := I) K).toSubmodule.dualAnnihilator) :
    μ (g • x) ∈ (groupLieSubalgebraOfSubgroup (I := I) K).toSubmodule.dualAnnihilator :=
  hμ g x ▸ coadjointRepresentation_apply_mem_dualAnnihilator_groupLieSubalgebraOfSubgroup hg hx

variable (μ N i) in
/-- **The residual moment map of reduction in stages, lifted to the level.** For a map `i : Z → M`
into the zero level of the moment map of `N`, so that `μ (i z)` annihilates the Lie algebra `𝔫` of
`N`, this sends `z` to `μ (i z)` read as a linear form on `𝔤 ⧸ 𝔫`, through the identification
`(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` (`Submodule.dualQuotEquivDualAnnihilator`). The residual moment map on the first
reduced space is the map this one descends to. -/
def residualMomentMapLift
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) :
    Module.Dual ℝ (GroupLieAlgebra I G ⧸ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule) :=
  (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualQuotEquivDualAnnihilator.symm
    ⟨μ (i z), hi z⟩

/-- The definition of `TauCeti.residualMomentMapLift`, whose body is not exposed. -/
theorem residualMomentMapLift_def
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) :
    residualMomentMapLift μ N i hi z =
      (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualQuotEquivDualAnnihilator.symm
        ⟨μ (i z), hi z⟩ :=
  (rfl)

/-- The lifted residual moment map takes the value `⟨μ (i z), ξ⟩` on the class of `ξ`. -/
@[simp]
theorem residualMomentMapLift_apply_mk
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) (ξ : GroupLieAlgebra I G) :
    residualMomentMapLift μ N i hi z (Submodule.Quotient.mk ξ) = μ (i z) ξ :=
  (rfl)

/-- Under the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰`, the lifted residual moment map is `μ ∘ i`. -/
@[simp]
theorem dualQuotEquivDualAnnihilator_residualMomentMapLift
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) :
    (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualQuotEquivDualAnnihilator
      (residualMomentMapLift μ N i hi z) = ⟨μ (i z), hi z⟩ := by
  rw [residualMomentMapLift_def, LinearEquiv.apply_symm_apply]

/-- The coercion to `𝔤*` of the image of the lifted residual moment map under
`(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` is `μ ∘ i`. -/
theorem coe_dualQuotEquivDualAnnihilator_residualMomentMapLift
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) :
    ((groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualQuotEquivDualAnnihilator
      (residualMomentMapLift μ N i hi z) : Module.Dual ℝ (GroupLieAlgebra I G)) = μ (i z) := by
  rw [dualQuotEquivDualAnnihilator_residualMomentMapLift]

/-- The lifted residual moment map vanishes at `z` exactly when `μ` vanishes at `i z`. -/
@[simp]
theorem residualMomentMapLift_eq_zero_iff
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) :
    residualMomentMapLift μ N i hi z = 0 ↔ μ (i z) = 0 := by
  rw [residualMomentMapLift_def, LinearEquiv.map_eq_zero_iff, Submodule.mk_eq_zero]

/-- **The lifted residual moment map is `G ⧸ N`-equivariant.** If `μ` is coadjoint-equivariant and
`G` acts on `Z` compatibly with `i`, then `μ_res (g • z) = [g] · μ_res z` for the dual action of
`G ⧸ N` on `(𝔤 ⧸ 𝔫)*` induced by the adjoint representation. -/
theorem residualMomentMapLift_smul [SMul G M] [SMul G Z] [N.Normal]
    (hN : IsClosed (N : Set G))
    (hμ : ∀ (g : G) (x : M), μ (g • x) = coadjointRepresentation ℝ I G g (μ x))
    (hiG : ∀ (g : G) (z : Z), i (g • z) = g • i z)
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (g : G) (z : Z) :
    residualMomentMapLift μ N i hi (g • z) =
      (quotientAdjointRepresentation (I := I) N hN).dual g (residualMomentMapLift μ N i hi z) := by
  rw [residualMomentMapLift_def, residualMomentMapLift_def,
    ← dualQuotEquivDualAnnihilator_symm_coadjointRepresentation_apply hN g (hi z)]
  congr 2
  rw [hiG, hμ]

/-- **The lifted residual moment map is `N`-invariant**: `μ_res (n • z) = μ_res z` for `n ∈ N`.
Only an action of `N` on `Z` and the `N`-equivariance of `μ` are used. -/
theorem residualMomentMapLift_subgroup_smul [SMul G M] [SMul N Z] [N.Normal]
    (hN : IsClosed (N : Set G))
    (hμ : ∀ (n : N) (x : M), μ ((n : G) • x) = coadjointRepresentation ℝ I G n (μ x))
    (hiN : ∀ (n : N) (z : Z), i (n • z) = (n : G) • i z)
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (n : N) (z : Z) :
    residualMomentMapLift μ N i hi (n • z) = residualMomentMapLift μ N i hi z := by
  rw [residualMomentMapLift_def, residualMomentMapLift_def]
  congr 2
  rw [hiN, hμ]
  exact coadjointRepresentation_apply_eq_self_of_mem_dualAnnihilator_groupLieSubalgebraOfSubgroup
    hN n.2 (hi z)

/-- **The lifted residual moment map is `N`-invariant**, for an action of `G` on `Z`:
`μ_res (n • z) = μ_res z` for `n ∈ N`. -/
theorem residualMomentMapLift_smul_of_mem [SMul G M] [SMul G Z] [N.Normal]
    (hN : IsClosed (N : Set G))
    (hμ : ∀ (g : G) (x : M), μ (g • x) = coadjointRepresentation ℝ I G g (μ x))
    (hiG : ∀ (g : G) (z : Z), i (g • z) = g • i z)
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    {n : G} (hn : n ∈ N) (z : Z) :
    residualMomentMapLift μ N i hi (n • z) = residualMomentMapLift μ N i hi z :=
  residualMomentMapLift_subgroup_smul hN (fun n ↦ hμ n) (fun n ↦ hiG n) hi ⟨n, hn⟩ z

namespace SmoothTwoForm.IsMomentMap

variable {E' H' E₀ H₀ : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace Z] [ChartedSpace H₀ Z]
  {σ : SmoothTwoForm I' M} {a : InfinitesimalAction (GroupLieAlgebra I G) I' M}

/-- **The components of the lifted residual moment map are smooth** along a level map `i` of
class `C^n`, `n ≤ ∞`, since each is the component `⟨μ, ξ⟩` of the moment map composed with `i`. -/
theorem contMDiff_residualMomentMapLift_apply_mk (h : σ.IsMomentMap a μ)
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (ξ : GroupLieAlgebra I G) {n : WithTop ℕ∞} (hn : n ≤ ∞) (hi' : ContMDiff I₀ I' n i) :
    ContMDiff I₀ 𝓘(ℝ) n fun z ↦ residualMomentMapLift μ N i hi z (Submodule.Quotient.mk ξ) := by
  simp only [residualMomentMapLift_apply_mk]
  exact ((h.contMDiff ξ).of_le hn).comp hi'

/-- **The moment map equation of the lifted residual moment map along the level.** If `μ` is a
moment map for `σ` and the generated vector fields `ξ_M`, and `i : Z → M` is differentiable at
`z`, then the component of the lifted residual moment map along the class of `ξ` has derivative
`v ↦ σ(ξ_M (i z), di v)` at `z`: it is `i^* (ι_{ξ_M} σ) = d⟨μ ∘ i, ξ⟩`. -/
theorem mvfderiv_residualMomentMapLift_apply_mk (h : σ.IsMomentMap a μ)
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
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
