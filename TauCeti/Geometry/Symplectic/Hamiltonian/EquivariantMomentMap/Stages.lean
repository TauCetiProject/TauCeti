/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# The residual moment map of reduction in stages

Let a Lie group `G` act on a manifold `M` with a coadjoint-equivariant moment map `μ : M → 𝔤*`,
and let `N` be a closed normal subgroup of `G` with Lie algebra `𝔫 ⊆ 𝔤`. Reduction in stages
reduces first by `N`, then by the residual action of `G ⧸ N`. The moment map of `N` is the
restriction `μ_N = μ|𝔫` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_subtype`), and this
file supplies the pointwise data of the second stage, for **level data supplied as a map**
`i : Z → M` into the zero level of `μ_N`, as in `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction`.

* On the zero level of `μ_N`, the moment map `μ` takes values in the annihilator `𝔫⁰`
  (`TauCeti.Lie.EmbeddedLieSubgroupData.comp_groupLieAlgebraMap_subtype_eq_zero_iff`), and this
  level is `G`-invariant (`TauCeti.apply_smul_mem_dualAnnihilator`).
* Through the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰`, the restriction of `μ` to the level is a map
  `TauCeti.residualMomentMap : Z → (𝔤 ⧸ 𝔫)*`, characterized by `⟨μ_res z, [ξ]⟩ = ⟨μ (i z), ξ⟩`.
* If `G` acts on `Z` compatibly with `i`, the residual map is equivariant for the dual action of
  `G ⧸ N` on `(𝔤 ⧸ 𝔫)*` (`TauCeti.residualMomentMap_smul`); in particular it is invariant under
  `N` (`TauCeti.residualMomentMap_smul_of_mem`). This dual action is the coadjoint action of
  `G ⧸ N` once `𝔤 ⧸ 𝔫` is identified with its Lie algebra.
* The components of the residual map satisfy the moment map equation pulled back to `Z`:
  `d⟨μ_res, [ξ]⟩ = i^* (ι_{ξ_M} σ)`
  (`TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_residualMomentMap_apply_mk`). This is the equation
  to be descended along reduction data `p : Z → Q`, `p^* η = i^* σ`, to the moment map of the
  residual action on the first reduced space.

## Main definitions

* `TauCeti.residualMomentMap`: the map `Z → (𝔤 ⧸ 𝔫)*` induced by `μ` on the zero level of `μ_N`.

## Main results

* `TauCeti.apply_smul_mem_dualAnnihilator`: the zero level of `μ_N` is `G`-invariant.
* `TauCeti.residualMomentMap_smul`: the residual map is `G ⧸ N`-equivariant.
* `TauCeti.residualMomentMap_smul_of_mem`: the residual map is `N`-invariant.
* `TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_residualMomentMap_apply_mk`: the moment map
  equation of the residual map along the level.

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

/-- **The zero level of the moment map of a normal subgroup is invariant.** If `μ` is
coadjoint-equivariant and `μ x` annihilates the Lie algebra `𝔫` of a normal subgroup `N`, then so
does `μ (g • x)` for every `g ∈ G`. -/
theorem apply_smul_mem_dualAnnihilator [MulAction G M] [N.Normal]
    (hμ : ∀ (g : G) (x : M), μ (g • x) = coadjointRepresentation ℝ I G g (μ x)) (g : G) {x : M}
    (hx : μ x ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator) :
    μ (g • x) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator :=
  hμ g x ▸ coadjointRepresentation_apply_mem_dualAnnihilator g hx

variable (μ N i) in
/-- **The residual moment map** of reduction in stages. For a map `i : Z → M` into the zero level
of the moment map of `N`, so that `μ (i z)` annihilates the Lie algebra `𝔫` of `N`, the residual
map sends `z` to `μ (i z)` read as a linear form on `𝔤 ⧸ 𝔫`, through the identification
`(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` (`Submodule.dualQuotEquivDualAnnihilator`). -/
def residualMomentMap
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) :
    Module.Dual ℝ (GroupLieAlgebra I G ⧸ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule) :=
  (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualQuotEquivDualAnnihilator.symm
    ⟨μ (i z), hi z⟩

/-- The residual moment map takes the value `⟨μ (i z), ξ⟩` on the class of `ξ`. -/
@[simp]
theorem residualMomentMap_apply_mk
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) (ξ : GroupLieAlgebra I G) :
    residualMomentMap μ N i hi z (Submodule.Quotient.mk ξ) = μ (i z) ξ :=
  (rfl)

/-- Under the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰`, the residual moment map is `μ ∘ i`. -/
@[simp]
theorem coe_dualQuotEquivDualAnnihilator_residualMomentMap
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (z : Z) :
    ((groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualQuotEquivDualAnnihilator
      (residualMomentMap μ N i hi z) : Module.Dual ℝ (GroupLieAlgebra I G)) = μ (i z) := by
  rw [residualMomentMap, LinearEquiv.apply_symm_apply]

/-- **The residual moment map is `G ⧸ N`-equivariant.** If `μ` is coadjoint-equivariant and `G`
acts on `Z` compatibly with `i`, then `μ_res (g • z) = [g] · μ_res z` for the dual action of
`G ⧸ N` on `(𝔤 ⧸ 𝔫)*` induced by the adjoint representation. -/
theorem residualMomentMap_smul [MulAction G M] [MulAction G Z] [N.Normal]
    (hN : IsClosed (N : Set G))
    (hμ : ∀ (g : G) (x : M), μ (g • x) = coadjointRepresentation ℝ I G g (μ x))
    (hiG : ∀ (g : G) (z : Z), i (g • z) = g • i z)
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (g : G) (z : Z) :
    residualMomentMap μ N i hi (g • z) =
      (quotientAdjointRepresentation (I := I) N hN).dual g (residualMomentMap μ N i hi z) := by
  rw [residualMomentMap, residualMomentMap,
    ← dualQuotEquivDualAnnihilator_symm_coadjointRepresentation_apply hN g (hi z)]
  congr 2
  rw [hiG, hμ]

/-- **The residual moment map is `N`-invariant**: `μ_res (n • z) = μ_res z` for `n ∈ N`. -/
theorem residualMomentMap_smul_of_mem [MulAction G M] [MulAction G Z] [N.Normal]
    (hN : IsClosed (N : Set G))
    (hμ : ∀ (g : G) (x : M), μ (g • x) = coadjointRepresentation ℝ I G g (μ x))
    (hiG : ∀ (g : G) (z : Z), i (g • z) = g • i z)
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    {n : G} (hn : n ∈ N) (z : Z) :
    residualMomentMap μ N i hi (n • z) = residualMomentMap μ N i hi z := by
  rw [residualMomentMap_smul hN hμ hiG hi, (QuotientGroup.eq_one_iff n).2 hn, map_one,
    one_apply_eq_self]

namespace SmoothTwoForm.IsMomentMap

variable {E' H' E₀ H₀ : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace Z] [ChartedSpace H₀ Z]
  {σ : SmoothTwoForm I' M} {a : InfinitesimalAction (GroupLieAlgebra I G) I' M}

/-- **The moment map equation of the residual moment map along the level.** If `μ` is a moment map
for `σ` and the generated vector fields `ξ_M`, and `i : Z → M` is smooth, then the component of
the residual moment map along the class of `ξ` has derivative `v ↦ σ(ξ_M (i z), di v)`: it is
`i^* (ι_{ξ_M} σ) = d⟨μ ∘ i, ξ⟩`. -/
theorem mvfderiv_residualMomentMap_apply_mk (h : σ.IsMomentMap a μ) (hi' : ContMDiff I₀ I' ∞ i)
    (hi : ∀ z, μ (i z) ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator)
    (ξ : GroupLieAlgebra I G) (z : Z) (v : TangentSpace I₀ z) :
    mvfderiv I₀ (fun z ↦ residualMomentMap μ N i hi z (Submodule.Quotient.mk ξ)) z v =
      SmoothBundleForm.eval₂ σ (i z) (a ξ (i z)) (mfderiv I₀ I' i z v) := by
  have hcomp : (fun z ↦ residualMomentMap μ N i hi z (Submodule.Quotient.mk ξ)) =
      (fun x ↦ μ x ξ) ∘ i :=
    funext fun z ↦ residualMomentMap_apply_mk hi z ξ
  rw [hcomp, mvfderiv_comp_apply z (((h.contMDiff ξ) (i z)).mdifferentiableAt (by simp))
    ((hi' z).mdifferentiableAt (by simp)),
    isHamiltonianVectorField_iff.1 (h.isHamiltonianVectorField ξ)]

end SmoothTwoForm.IsMomentMap

end TauCeti
