/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

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
(`TauCeti.fundamentalVectorField_prod_of_smul_eq`), so the infinitesimal moment-map identity holds
without equivariance (`TauCeti.SmoothTwoForm.IsMomentMap.prod_comp_monoidHom`). Since `dφ` and
`dψ` intertwine the adjoint actions, the defect from coadjoint equivariance of the product map is
the sum of the restricted defects of `μ` and `ν`
(`TauCeti.momentDefect_prod_comp_groupLieAlgebraMap`).

The main case is the **product of two Hamiltonian spaces**: `G × G'` acting factorwise on
`M × N`, with `φ` and `ψ` the projections. Identifying the dual of the Lie algebra of `G × G'` with
`𝔤* × 𝔤'*` (`TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`), its moment map is
`(x, y) ↦ (μ x, ν y)` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prodMap`). Since this
identification is a linear equivalence, the level of the product moment map at `(c, c')` is the
product `μ⁻¹(c) × ν⁻¹(c')` of the levels, and the coadjoint stabilizer of `(c, c')` is
`G_c × G'_c'`
(`TauCeti.Lie.stabilizer_coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual`). So the
reduced space of the product at `(c, c')` is built from the product of the reduction data of the
factors. Mathlib has no factorwise action instance of `G × G'` on `M × N` (to avoid diamonds with
the diagonal action), so the action is an arbitrary one satisfying
`g • (x, y) = (g.1 • x, g.2 • y)`; such an action is smooth by `ContMDiffSMul.prod_of_smul_eq`.

Two Hamiltonian actions on the same manifold combine in the same way. Let `G` and `G'` act on
`(M, σ)` with coadjoint-equivariant moment maps `μ` and `ν`, and let `G × G'` act by
`(g, g') • x = g • g' • x`. If `μ` is invariant under `G'` and `ν` under `G`, then
`x ↦ (μ x, ν x)` is a coadjoint-equivariant moment map of the action of `G × G'`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_of_smul_eq_smul_smul`): the fundamental vector
field of `(ξ, ξ')` is `ξ_M + ξ'_M` (`TauCeti.fundamentalVectorField_eq_add_of_smul_eq_smul_smul`).
The invariance hypotheses cannot be dropped: the translations of `ℝ²` along the two axes commute
and have the moment maps `p` and `-q` for `dq ∧ dp`, but neither is invariant under the other
translation, and the translation action of `ℝ²` has no equivariant moment map. This is the
Hamiltonian action of a product group used to compare reduction by `G × G'` with reduction by `G`
followed by reduction by `G'`.

Neither connectedness of the groups nor nondegeneracy of the forms is needed. In particular,
the constructions apply to disconnected group actions as well as to symplectic actions.

## Main results

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod`: the diagonal action.
* `TauCeti.momentDefect_prod_comp_groupLieAlgebraMap`: the defect of a product map is the sum of
  the restricted defects of the factors.
* `TauCeti.SmoothTwoForm.IsMomentMap.prod_comp_monoidHom`,
  `TauCeti.SmoothTwoForm.IsMomentMap.prodMap`: the moment-map identity for actions on the product
  through homomorphisms and for the factorwise action of a product of Lie groups.
* `TauCeti.SmoothTwoForm.IsMomentMap.differential_prodMap`,
  `TauCeti.SmoothTwoForm.IsMomentMap.forall_differential_surjective_prodMap`: the differential of
  the moment map of a product is the pair of the differentials, so a pair of regular values is a
  regular value.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_comp_monoidHom`: an action on the product
  through homomorphisms to the two acting groups.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prodMap`: the factorwise action of a product of
  Lie groups.
* `TauCeti.SmoothTwoForm.IsMomentMap.prod_of_smul_eq_smul_smul`,
  `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_of_smul_eq_smul_smul`: commuting actions of
  two Lie groups on the same manifold, combined into an action of their product.

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

namespace TauCeti

section Defect

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I 1 G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G']
  [Group G'] [LieGroup I' 1 G']
  {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK] [TopologicalSpace HK]
  {IK : ModelWithCorners 𝕜 EK HK} {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]
  [LieGroup IK 1 K]
  {M N : Type*} [MulAction G M] [MulAction G' N] [MulAction K (M × N)]
  {μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)} {ν : N → Module.Dual 𝕜 (GroupLieAlgebra I' G')}

/-- **The defect of a product map.** If `K` acts on `M × N` through homomorphisms `φ : K →* G` and
`ψ : K →* G'`, the defect from coadjoint equivariance of `(x, y) ↦ μ x ∘ dφ + ν y ∘ dψ` is the sum
of the defects of `μ` at `φ k` and of `ν` at `ψ k`, restricted along `dφ` and `dψ`. -/
theorem momentDefect_prod_comp_groupLieAlgebraMap {φ : K →* G} {ψ : K →* G'}
    (hsmul : ∀ (k : K) (p : M × N), k • p = (φ k • p.1, ψ k • p.2)) (k : K) (p : M × N) :
    momentDefect (fun q : M × N ↦ (μ q.1).comp (φ.groupLieAlgebraMap IK I).toLinearMap +
        (ν q.2).comp (ψ.groupLieAlgebraMap IK I').toLinearMap) k p =
      (momentDefect μ (φ k) p.1).comp (φ.groupLieAlgebraMap IK I).toLinearMap +
        (momentDefect ν (ψ k) p.2).comp (ψ.groupLieAlgebraMap IK I').toLinearMap := by
  ext ξ
  -- `dφ` and `dψ` intertwine the adjoint actions: `dφ (Ad_{k⁻¹} ξ) = Ad_{φ k⁻¹} (dφ ξ)`.
  simp only [momentDefect_def, hsmul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Lie.coadjointRepresentation_apply,
    MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap, map_inv]
  abel

end Defect

namespace SmoothTwoForm

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

namespace IsMomentMap

/-- **Moment maps of actions on products through homomorphisms.** Let `K` act on `M × N` through
homomorphisms `φ : K →* G` and `ψ : K →* G'` that are differentiable at the identity,
`k • (x, y) = (φ k • x, ψ k • y)`. If `μ` and `ν` are moment maps of the actions of `G` on `M` and
of `G'` on `N` by fundamental vector fields, then `(x, y) ↦ μ x ∘ dφ + ν y ∘ dψ` is a moment map of
the action of `K` by fundamental vector fields for the product two-form, where `dφ` and `dψ` are
the differentials of `φ` and `ψ` at the identity. -/
theorem prod_comp_monoidHom {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    [CompleteSpace EK] [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK}
    {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]
    [LieGroup IK (minSmoothness ℝ 3) K] [MulAction K (M × N)]
    [ContMDiffSMul IK (I₁.prod I₂) ∞ K (M × N)]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I₁ M) μ)
    (hν : τ.IsMomentMap (InfinitesimalAction.fundamental I' G' I₂ N) ν) (φ : K →* G)
    (ψ : K →* G') (hφ : MDifferentiableAt IK I φ 1) (hψ : MDifferentiableAt IK I' ψ 1)
    (hsmul : ∀ (k : K) (p : M × N), k • p = (φ k • p.1, ψ k • p.2)) :
    (σ.prod τ).IsMomentMap (InfinitesimalAction.fundamental IK K (I₁.prod I₂) (M × N)) fun p ↦
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
        (hμ.mdifferentiableAt _) (hν.mdifferentiableAt _)

/-- **Moment maps of a product of group actions.** Let `G × G'` act on `M × N` factorwise,
`(g, g') • (x, y) = (g • x, g' • y)`. If `μ` and `ν` are moment maps of the actions of `G` on `M`
and of `G'` on `N` by fundamental vector fields, then `(x, y) ↦ (μ x, ν y)` is a moment map of the
action of `G × G'` by fundamental vector fields for the product two-form, where the dual of the
Lie algebra of `G × G'` is identified with `𝔤* × 𝔤'*` by
`TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`. -/
theorem prodMap [MulAction (G × G') (M × N)]
    [ContMDiffSMul (I.prod I') (I₁.prod I₂) ∞ (G × G') (M × N)]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I₁ M) μ)
    (hν : τ.IsMomentMap (InfinitesimalAction.fundamental I' G' I₂ N) ν)
    (hsmul : ∀ (g : G × G') (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) :
    (σ.prod τ).IsMomentMap
      (InfinitesimalAction.fundamental (I.prod I') (G × G') (I₁.prod I₂) (M × N)) fun p ↦
        Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G' (μ p.1, ν p.2) := by
  convert hμ.prod_comp_monoidHom hν (MonoidHom.fst G G') (MonoidHom.snd G G')
    mdifferentiableAt_fst mdifferentiableAt_snd hsmul using 2 with p
  ext ξ
  simp

/-- **The differential of the moment map of a product.** For `G × G'` acting factorwise on
`M × N`, with moment map `(x, y) ↦ (μ x, ν y)`, the differential at `p` sends a tangent vector
with components `(v₁, v₂)` to `(dμ(v₁), dν(v₂))`, under the identification of the dual of the Lie
algebra of `G × G'` with `𝔤* × 𝔤'*`. -/
theorem differential_prodMap [MulAction (G × G') (M × N)]
    [ContMDiffSMul (I.prod I') (I₁.prod I₂) ∞ (G × G') (M × N)]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I₁ M) μ)
    (hν : τ.IsMomentMap (InfinitesimalAction.fundamental I' G' I₂ N) ν)
    (hsmul : ∀ (g : G × G') (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) (p : M × N)
    (v : TangentSpace (I₁.prod I₂) p) :
    (hμ.prodMap hν hsmul).differential p v =
      Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G'
        (hμ.differential p.1 (Manifold.tangentSpaceProdEquiv p v).1,
          hν.differential p.2 (Manifold.tangentSpaceProdEquiv p v).2) := by
  ext ξ
  simp only [differential_apply_eq_eval₂, Lie.groupLieAlgebraDualProdDualEquivDual_apply,
    InfinitesimalAction.fundamental_apply,
    fundamentalVectorField_prod_of_smul_eq (MonoidHom.fst G G') (MonoidHom.snd G G')
      mdifferentiableAt_fst mdifferentiableAt_snd hsmul, eval₂_prod,
    Manifold.tangentSpaceProdEquiv_prodVectorField]

/-- **Regular values of the moment map of a product.** For `G × G'` acting factorwise on `M × N`,
if `c` is a regular value of `μ` and `c'` is a regular value of `ν`, then `(c, c')` is a regular
value of the moment map `(x, y) ↦ (μ x, ν y)`. -/
theorem forall_differential_surjective_prodMap [MulAction (G × G') (M × N)]
    [ContMDiffSMul (I.prod I') (I₁.prod I₂) ∞ (G × G') (M × N)]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I₁ M) μ)
    (hν : τ.IsMomentMap (InfinitesimalAction.fundamental I' G' I₂ N) ν)
    (hsmul : ∀ (g : G × G') (p : M × N), g • p = (g.1 • p.1, g.2 • p.2))
    {c : Module.Dual ℝ (GroupLieAlgebra I G)} {c' : Module.Dual ℝ (GroupLieAlgebra I' G')}
    (hreg₁ : ∀ x, μ x = c → Function.Surjective (hμ.differential x))
    (hreg₂ : ∀ y, ν y = c' → Function.Surjective (hν.differential y)) (p : M × N)
    (hp : Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G' (μ p.1, ν p.2) =
      Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G' (c, c')) :
    Function.Surjective ((hμ.prodMap hν hsmul).differential p) := by
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj (LinearEquiv.injective _ hp)
  intro f
  obtain ⟨⟨a, b⟩, rfl⟩ := (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G').surjective f
  obtain ⟨v₁, rfl⟩ := hreg₁ p.1 h₁ a
  obtain ⟨v₂, rfl⟩ := hreg₂ p.2 h₂ b
  refine ⟨(Manifold.tangentSpaceProdEquiv p).symm (v₁, v₂), ?_⟩
  rw [differential_prodMap hμ hν hsmul, ContinuousLinearEquiv.apply_symm_apply]

end IsMomentMap

namespace IsEquivariantMomentMap

/-- **Equivariant moment maps of actions on products through homomorphisms.** Let `K` act on
`M × N` through homomorphisms `φ : K →* G` and `ψ : K →* G'` that are differentiable at the
identity, `k • (x, y) = (φ k • x, ψ k • y)`. If `μ` and `ν` are coadjoint-equivariant moment maps
of the actions of `G` on `M` and of `G'` on `N`, then `(x, y) ↦ μ x ∘ dφ + ν y ∘ dψ` is a
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
        (ν p.2).comp (ψ.groupLieAlgebraMap IK I').toLinearMap := by
  refine isEquivariantMomentMap_iff_momentDefect_eq_zero.2
    ⟨hμ.toIsMomentMap.prod_comp_monoidHom hν.toIsMomentMap φ ψ hφ hψ hsmul, fun k p ↦ ?_⟩
  simp [momentDefect_prod_comp_groupLieAlgebraMap hsmul,
    (isEquivariantMomentMap_iff_momentDefect_eq_zero.1 hμ).2,
    (isEquivariantMomentMap_iff_momentDefect_eq_zero.1 hν).2]

/-- **The product of Hamiltonian spaces.** Let `G × G'` act on `M × N` factorwise,
`(g, g') • (x, y) = (g • x, g' • y)`. If `μ` and `ν` are coadjoint-equivariant moment maps of the
actions of `G` on `M` and of `G'` on `N`, then `(x, y) ↦ (μ x, ν y)` is a coadjoint-equivariant
moment map of the action of `G × G'` for the product two-form, where the dual of the Lie algebra
of `G × G'` is identified with `𝔤* × 𝔤'*` by `TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`. -/
theorem prodMap [MulAction (G × G') (M × N)]
    [ContMDiffSMul (I.prod I') (I₁.prod I₂) ∞ (G × G') (M × N)] (hμ : σ.IsEquivariantMomentMap μ)
    (hν : τ.IsEquivariantMomentMap ν)
    (hsmul : ∀ (g : G × G') (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) :
    (σ.prod τ).IsEquivariantMomentMap fun p ↦
      Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G' (μ p.1, ν p.2) where
  toIsMomentMap := hμ.toIsMomentMap.prodMap hν.toIsMomentMap hsmul
  -- The identification `𝔤* × 𝔤'* ≃ Lie(G × G')*` intertwines the coadjoint actions.
  apply_smul g p := by simp [hsmul, hμ.apply_smul, hν.apply_smul]

end IsEquivariantMomentMap

/-! ### Commuting actions on one manifold -/

section Commuting

variable [MulAction G' M] [ContMDiffSMul I' I₁ ∞ G' M] [MulAction (G × G') M]
  [ContMDiffSMul (I.prod I') I₁ ∞ (G × G') M] {ν : M → Module.Dual ℝ (GroupLieAlgebra I' G')}

/-- **Moment maps of commuting actions.** Let `G` and `G'` act on `M`, and let `G × G'` act by
`(g, g') • x = g • g' • x`. If `μ` and `ν` are moment maps of the actions of `G` and of `G'` by
fundamental vector fields, then `x ↦ (μ x, ν x)` is a moment map of the action of `G × G'` by
fundamental vector fields, where the dual of the Lie algebra of `G × G'` is identified with
`𝔤* × 𝔤'*` by `TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`. -/
theorem IsMomentMap.prod_of_smul_eq_smul_smul
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I₁ M) μ)
    (hν : σ.IsMomentMap (InfinitesimalAction.fundamental I' G' I₁ M) ν)
    (hsmul : ∀ (g : G × G') (x : M), g • x = g.1 • g.2 • x) :
    σ.IsMomentMap (InfinitesimalAction.fundamental (I.prod I') (G × G') I₁ M) fun x ↦
      Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G' (μ x, ν x) where
  contMDiff ξ := by
    simp only [Lie.groupLieAlgebraDualProdDualEquivDual_apply]
    exact (hμ.contMDiff _).add (hν.contMDiff _)
  isHamiltonianVectorField ξ := by
    rw [InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_eq_add_of_smul_eq_smul_smul hsmul]
    have h₁ := hμ.isHamiltonianVectorField ((MonoidHom.fst G G').groupLieAlgebraMap (I.prod I') I ξ)
    have h₂ := hν.isHamiltonianVectorField
      ((MonoidHom.snd G G').groupLieAlgebraMap (I.prod I') I' ξ)
    rw [InfinitesimalAction.fundamental_apply] at h₁ h₂
    simp only [Lie.groupLieAlgebraDualProdDualEquivDual_apply]
    exact h₁.add h₂ (fun x ↦ hμ.mdifferentiableAt _ x) (fun x ↦ hν.mdifferentiableAt _ x)

/-- **The differential of the moment map of commuting actions.** For `G × G'` acting on `M` by
`(g, g') • x = g • g' • x`, with moment map `x ↦ (μ x, ν x)`, the differential at `x` is the pair
`(dμ_x, dν_x)`, under the identification of the dual of the Lie algebra of `G × G'` with
`𝔤* × 𝔤'*`. -/
theorem IsMomentMap.differential_prod_of_smul_eq_smul_smul
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I₁ M) μ)
    (hν : σ.IsMomentMap (InfinitesimalAction.fundamental I' G' I₁ M) ν)
    (hsmul : ∀ (g : G × G') (x : M), g • x = g.1 • g.2 • x) (x : M) (v : TangentSpace I₁ x) :
    (hμ.prod_of_smul_eq_smul_smul hν hsmul).differential x v =
      Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G'
        (hμ.differential x v, hν.differential x v) := by
  ext ξ
  simp only [differential_apply, Lie.groupLieAlgebraDualProdDualEquivDual_apply]
  rw [mvfderiv_fun_add (hμ.mdifferentiableAt _ x) (hν.mdifferentiableAt _ x)]
  rfl

/-- **Equivariant moment maps of commuting actions.** Let `G` and `G'` act on `M`, and let `G × G'`
act by `(g, g') • x = g • g' • x`. If `μ` and `ν` are coadjoint-equivariant moment maps of the
actions of `G` and of `G'`, with `μ` invariant under `G'` and `ν` invariant under `G`, then
`x ↦ (μ x, ν x)` is a coadjoint-equivariant moment map of the action of `G × G'`, where the dual of
the Lie algebra of `G × G'` is identified with `𝔤* × 𝔤'*` by
`TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`. -/
theorem IsEquivariantMomentMap.prod_of_smul_eq_smul_smul (hμ : σ.IsEquivariantMomentMap μ)
    (hν : σ.IsEquivariantMomentMap ν) (hsmul : ∀ (g : G × G') (x : M), g • x = g.1 • g.2 • x)
    (hμG' : ∀ (g : G') (x : M), μ (g • x) = μ x) (hνG : ∀ (g : G) (x : M), ν (g • x) = ν x) :
    σ.IsEquivariantMomentMap fun x ↦
      Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' G' (μ x, ν x) where
  toIsMomentMap := hμ.toIsMomentMap.prod_of_smul_eq_smul_smul hν.toIsMomentMap hsmul
  apply_smul g x := by
    rw [Lie.coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual, hsmul, hμ.apply_smul,
      hμG', hνG, hν.apply_smul]

end Commuting

end SmoothTwoForm

end TauCeti
