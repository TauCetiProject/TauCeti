/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# Equivariant moment maps for product actions

If a Lie group acts on two manifolds with coadjoint-equivariant moment maps `μ` and `ν`,
then its diagonal action on their product has moment map `(x, y) ↦ μ x + ν y` for the product
two-form (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod`). The infinitesimal moment-map
identity follows from the existing product construction; coadjoint equivariance follows from
linearity of the coadjoint representation.

More generally, let a Lie group `K` act on `M × N` through homomorphisms `φ : K →* G` and
`ψ : K →* G'`, `k • (x, y) = (φ k • x, ψ k • y)`. Then

`(x, y) ↦ μ x ∘ dφ + ν y ∘ dψ`

is a coadjoint-equivariant moment map of the action of `K`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_comp_monoidHom`). The fundamental vector field
of `ξ ∈ Lie(K)` is the product of the fundamental vector fields of `dφ ξ` and `dψ ξ`
(`TauCeti.fundamentalVectorField_prod_of_smul_eq`), and `dφ`, `dψ` intertwine the adjoint actions.

The main case is the **product of two Hamiltonian spaces**: `G × G'` acting factorwise on
`M × N`, with `φ` and `ψ` the projections. Identifying the dual of the Lie algebra of `G × G'` with
`𝔤* × 𝔤'*` (`TauCeti.Lie.dualProdDualEquivDual`), its moment map is `(x, y) ↦ (μ x, ν y)`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prodMap`). Since this identification is a linear
equivalence, the level of the product moment map at `(c, c')` is the product `μ⁻¹(c) × ν⁻¹(c')` of
the levels, and the coadjoint stabilizer of `(c, c')` is `G_c × G'_c'`
(`TauCeti.Lie.stabilizer_coadjointRepresentation_dualProdDualEquivDual`). So the reduced space of
the product at `(c, c')` is built from the product of the reduction data of the factors. Mathlib
has no factorwise action instance of `G × G'` on `M × N` (to avoid diamonds with the diagonal
action), so the action is an arbitrary one satisfying `g • (x, y) = (g.1 • x, g.2 • y)`; such an
action is smooth by `ContMDiffSMul.prod_of_smul_eq`.

Neither connectedness of the groups nor nondegeneracy of the forms is needed. In particular,
the constructions apply to disconnected group actions as well as to symplectic actions.

## Main results

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod`: the diagonal action.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_comp_monoidHom`: an action on the product
  through homomorphisms to the two acting groups.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prodMap`: the factorwise action of a product of
  Lie groups.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, §22 (Hamiltonian actions and products).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §11.2 (momentum maps of products).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M] [IsManifold I₁ ∞ M]
  [MulAction G M] [ContMDiffSMul I I₁ ∞ G M]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] [IsManifold I₂ ∞ N]
  [MulAction G N] [ContMDiffSMul I I₂ ∞ G N]
  {σ : SmoothTwoForm I₁ M} {τ : SmoothTwoForm I₂ N}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ν : N → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- The sum of two coadjoint-equivariant moment maps is a coadjoint-equivariant moment map
for the diagonal action on the product, with its product two-form. -/
theorem prod (hμ : σ.IsEquivariantMomentMap μ) (hν : τ.IsEquivariantMomentMap ν) :
    (σ.prod τ).IsEquivariantMomentMap (fun p ↦ μ p.1 + ν p.2) where
  toIsMomentMap := by
    rw [InfinitesimalAction.fundamental_prod]
    exact hμ.toIsMomentMap.prod hν.toIsMomentMap
  apply_smul g p := by
    simp only [Prod.smul_fst, Prod.smul_snd, hμ.apply_smul, hν.apply_smul, map_add]

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [LieGroup I' (minSmoothness ℝ 3) G']
  {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M] [IsManifold I₁ ∞ M]
  [MulAction G M] [ContMDiffSMul I I₁ ∞ G M]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] [IsManifold I₂ ∞ N]
  [MulAction G' N] [ContMDiffSMul I' I₂ ∞ G' N]
  {σ : SmoothTwoForm I₁ M} {τ : SmoothTwoForm I₂ N}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ν : N → Module.Dual ℝ (GroupLieAlgebra I' G')}

attribute [local instance] lieGroupOne

/-- **Moment maps of actions on products through homomorphisms.** Let `K` act on `M × N` through
homomorphisms `φ : K →* G` and `ψ : K →* G'` that are differentiable at the identity,
`k • (x, y) = (φ k • x, ψ k • y)`. If `μ` and `ν` are coadjoint-equivariant moment maps of the
actions of `G` on `M` and of `G'` on `N`, then `(x, y) ↦ μ x ∘ dφ + ν y ∘ dψ` is a
coadjoint-equivariant moment map of the action of `K` for the product two-form, where `dφ` and `dψ`
are the differentials of `φ` and `ψ` at the identity. -/
theorem prod_comp_monoidHom {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    [CompleteSpace EK] [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK}
    {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]
    [LieGroup IK (minSmoothness ℝ 3) K] [MulAction K (M × N)]
    [ContMDiffSMul IK (I₁.prod I₂) ∞ K (M × N)]
    (hμ : σ.IsEquivariantMomentMap μ) (hν : τ.IsEquivariantMomentMap ν) (φ : K →* G)
    (ψ : K →* G') (hφ : MDifferentiableAt IK I φ 1) (hψ : MDifferentiableAt IK I' ψ 1)
    (hsmul : ∀ (k : K) (p : M × N), k • p = (φ k • p.1, ψ k • p.2)) :
    (σ.prod τ).IsEquivariantMomentMap fun p ↦
      (μ p.1).comp (φ.groupLieAlgebraMap IK I).toLinearMap +
        (ν p.2).comp (ψ.groupLieAlgebraMap IK I').toLinearMap where
  contMDiff ξ := by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    exact ((hμ.contMDiff (φ.groupLieAlgebraMap IK I ξ)).comp contMDiff_fst).add
      ((hν.contMDiff (ψ.groupLieAlgebraMap IK I' ξ)).comp contMDiff_snd)
  isHamiltonianVectorField ξ := by
    rw [InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_prod_of_smul_eq φ ψ hφ hψ hsmul]
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      InfinitesimalAction.fundamental_apply] using
      (hμ.isHamiltonianVectorField (φ.groupLieAlgebraMap IK I ξ)).prod
        (hν.isHamiltonianVectorField (ψ.groupLieAlgebraMap IK I' ξ))
        (fun x ↦ hμ.mdifferentiableAt _ x) (fun y ↦ hν.mdifferentiableAt _ y)
  apply_smul k p := by
    ext ξ
    -- `dφ` and `dψ` intertwine the adjoint actions: `dφ (Ad_{k⁻¹} ξ) = Ad_{φ k⁻¹} (dφ ξ)`.
    simp only [hsmul, hμ.apply_smul, hν.apply_smul, LinearMap.add_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, Lie.coadjointRepresentation_apply,
      MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap, map_inv]

/-- **The product of Hamiltonian spaces.** Let `G × G'` act on `M × N` factorwise,
`(g, g') • (x, y) = (g • x, g' • y)`. If `μ` and `ν` are coadjoint-equivariant moment maps of the
actions of `G` on `M` and of `G'` on `N`, then `(x, y) ↦ (μ x, ν y)` is a coadjoint-equivariant
moment map of the action of `G × G'` for the product two-form, where the dual of the Lie algebra
of `G × G'` is identified with `𝔤* × 𝔤'*` by `TauCeti.Lie.dualProdDualEquivDual`. -/
theorem prodMap [MulAction (G × G') (M × N)]
    [ContMDiffSMul (I.prod I') (I₁.prod I₂) ∞ (G × G') (M × N)] (hμ : σ.IsEquivariantMomentMap μ)
    (hν : τ.IsEquivariantMomentMap ν)
    (hsmul : ∀ (g : G × G') (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) :
    (σ.prod τ).IsEquivariantMomentMap fun p ↦
      Lie.dualProdDualEquivDual ℝ I G I' G' (μ p.1, ν p.2) := by
  convert hμ.prod_comp_monoidHom hν (MonoidHom.fst G G') (MonoidHom.snd G G')
    mdifferentiableAt_fst mdifferentiableAt_snd hsmul using 2 with p
  ext ξ
  rw [Lie.dualProdDualEquivDual_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
