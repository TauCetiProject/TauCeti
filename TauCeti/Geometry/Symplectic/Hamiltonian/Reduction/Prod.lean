/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

/-!
# Reduced spaces of products

Let Lie groups `G` and `K` act smoothly and properly by symplectomorphisms on symplectic manifolds
`(M, σ)` and `(N, τ)`, with coadjoint-equivariant moment maps `μ` and `ν`. The product `G × K`
acts factorwise on `M × N`, `(g, k) • (x, y) = (g • x, k • y)`, preserving the product form
`σ ⊞ τ`, with moment map `(x, y) ↦ (μ x, ν y)`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prodMap`), whose values are read in the dual of the
Lie algebra of `G × K` through its identification with `𝔤* × 𝔨*`. This file proves that
**Marsden–Weinstein–Meyer reduction commutes with products**: the reduced space of `M × N` at
`(c, c')` is the product of the reduced spaces of `M` at `c` and of `N` at `c'`, as symplectic
manifolds.

The hypotheses of the reduction theorem pass to the product. A pair of regular values is a regular
value (`TauCeti.SmoothTwoForm.IsMomentMap.forall_differential_surjective_prodMap`), the
factorwise product of proper actions is proper (`ProperSMul.prod_of_smul_eq`), and the coadjoint
stabilizer `G_c × K_c'` of `(c, c')` acts freely on the level `μ⁻¹(c) × ν⁻¹(c')` when `G_c` and
`K_c'` act freely on theirs
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCancelSMul_levelSubMulAction_prodMap`).

The orbits of `G_c × K_c'` on the level of the product are the products of orbits, so
`[(x, y)] ↦ ([x], [y])` is a bijection from the reduced space of the product onto the product of
the reduced spaces. It is a diffeomorphism
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientProdDiffeomorph`), for any choice of
the embedded Lie subgroup structures of the three stabilizers that define the quotient atlases: in
both directions, smoothness descends along the orbit projections, which are surjective
submersions, from the smooth maps between the levels, which are embedded submanifolds of `M × N`
and of `M` and `N`.

Finally the diffeomorphism pulls the product `η₁ ⊞ η₂` of the reduced forms of the factors back to
the reduced form of the product
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_orbitRelQuotientProdDiffeomorph_prod`):
both pull back to the restriction of `σ ⊞ τ` to the level of the product, and the orbit projection
is a surjective submersion. So it is a symplectomorphism between the reduced space of the product
and the product of the reduced spaces. Neither statement uses closedness or nondegeneracy of the
forms; for invariant symplectic forms, `η₁`, `η₂` and `η` are the reduced symplectic forms of the
Marsden–Weinstein–Meyer theorem (`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`, in
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace`).

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `mem_levelSubMulAction_prodMap`: the level of the product at `(c, c')` is `μ⁻¹(c) × ν⁻¹(c')`.
* `isCancelSMul_levelSubMulAction_prodMap`: freeness of the stabilizer action passes to products.
* `orbitRelQuotientProdDiffeomorph`: the reduced space of the product is diffeomorphic to the
  product of the reduced spaces, by `[(x, y)] ↦ ([x], [y])`.
* `mpullback_orbitRelQuotientProdDiffeomorph_prod`: this diffeomorphism pulls the product of the
  reduced forms back to the reduced form of the product.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (symplectic reduction).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H' K] [Group K] [LieGroup I' ∞ K]
  {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M] [IsManifold I₁ ∞ M]
  [MulAction G M] [ContMDiffSMul I I₁ ∞ G M]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] [IsManifold I₂ ∞ N]
  [MulAction K N] [ContMDiffSMul I' I₂ ∞ K N]
  [MulAction (G × K) (M × N)] [ContMDiffSMul (I.prod I') (I₁.prod I₂) ∞ (G × K) (M × N)]
  {σ : SmoothTwoForm I₁ M} {τ : SmoothTwoForm I₂ N}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {ν : N → Module.Dual ℝ (GroupLieAlgebra I' K)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {c' : Module.Dual ℝ (GroupLieAlgebra I' K)}
  (hμ : σ.IsEquivariantMomentMap μ) (hν : τ.IsEquivariantMomentMap ν)
  (hsmul : ∀ (g : G × K) (p : M × N), g • p = (g.1 • p.1, g.2 • p.2))

/-! ### The level of a product -/

/-- **The level of the moment map of a product is the product of the levels**: a point `(x, y)`
lies on the level at `(c, c')` exactly when `μ x = c` and `ν y = c'`. -/
theorem mem_levelSubMulAction_prodMap {p : M × N} :
    p ∈ (hμ.prodMap hν hsmul).levelSubMulAction
        (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c')) ↔
      μ p.1 = c ∧ ν p.2 = c' := by
  rw [mem_levelSubMulAction, LinearEquiv.injective _ |>.eq_iff, Prod.mk.injEq]

/-- The level of the product, as a set of points, is the product of the levels. -/
private def levelSubMulActionProdEquiv :
    (hμ.prodMap hν hsmul).levelSubMulAction
        (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c')) ≃
      hμ.levelSubMulAction c × hν.levelSubMulAction c' :=
  (Equiv.subtypeEquivRight fun _ ↦ (hμ.mem_levelSubMulAction_prodMap hν hsmul).trans
    (and_congr hμ.mem_levelSubMulAction.symm hν.mem_levelSubMulAction.symm)).trans
    Equiv.subtypeProdEquivProd

/-- The first component of the identification is the first coordinate of the point. -/
private theorem coe_levelSubMulActionProdEquiv_fst
    (z : (hμ.prodMap hν hsmul).levelSubMulAction
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))) :
    ((hμ.levelSubMulActionProdEquiv hν hsmul z).1 : M) = z.val.1 :=
  (rfl)

/-- The second component of the identification is the second coordinate of the point. -/
private theorem coe_levelSubMulActionProdEquiv_snd
    (z : (hμ.prodMap hν hsmul).levelSubMulAction
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))) :
    ((hμ.levelSubMulActionProdEquiv hν hsmul z).2 : N) = z.val.2 :=
  (rfl)

/-- Two points of the level of the product lie in the same orbit of the stabilizer of `(c, c')`
exactly when their components lie in the same orbits of the stabilizers of `c` and of `c'`. -/
private theorem orbitRel_levelSubMulAction_prod_iff
    (z z' : (hμ.prodMap hν hsmul).levelSubMulAction
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))) :
    MulAction.orbitRel ((Lie.coadjointRepresentation ℝ (I.prod I') (G × K)).stabilizer
        (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))) _ z z' ↔
      MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c) _
          (hμ.levelSubMulActionProdEquiv hν hsmul z).1
          (hμ.levelSubMulActionProdEquiv hν hsmul z').1 ∧
        MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I' K).stabilizer c') _
          (hμ.levelSubMulActionProdEquiv hν hsmul z).2
          (hμ.levelSubMulActionProdEquiv hν hsmul z').2 := by
  have hstab := Lie.stabilizer_coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual
    (𝕜 := ℝ) (I := I) (G := G) (J := I') (K := K) (c, c')
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨h₁, h₂⟩ := Subgroup.mem_prod.1 (SetLike.ext_iff.1 hstab _ |>.1 g.property)
    refine ⟨⟨⟨g.val.1, h₁⟩, Subtype.ext ?_⟩, ⟨⟨g.val.2, h₂⟩, Subtype.ext ?_⟩⟩ <;>
      simp [coe_levelSubMulActionProdEquiv_fst, coe_levelSubMulActionProdEquiv_snd,
        Subgroup.smul_def, hsmul]
  · rintro ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩
    refine ⟨⟨(g₁, g₂), SetLike.ext_iff.1 hstab _ |>.2
      (Subgroup.mem_prod.2 ⟨g₁.property, g₂.property⟩)⟩, Subtype.ext ?_⟩
    have e₁ := congrArg Subtype.val hg₁
    have e₂ := congrArg Subtype.val hg₂
    simp only [SubMulAction.val_smul, Subgroup.smul_def, coe_levelSubMulActionProdEquiv_fst,
      coe_levelSubMulActionProdEquiv_snd] at e₁ e₂
    simp [Subgroup.smul_def, hsmul, e₁, e₂]

/-- **Freeness passes to products.** If the coadjoint stabilizers `G_c` and `K_c'` act freely on
the levels `μ⁻¹(c)` and `ν⁻¹(c')`, then the coadjoint stabilizer of `(c, c')` in `G × K` acts
freely on the level of the product. -/
theorem isCancelSMul_levelSubMulAction_prodMap
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (hμ.levelSubMulAction c)]
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I' K).stabilizer c') (hν.levelSubMulAction c')] :
    IsCancelSMul ((Lie.coadjointRepresentation ℝ (I.prod I') (G × K)).stabilizer
        (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c')))
      ((hμ.prodMap hν hsmul).levelSubMulAction
        (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))) := by
  refine isCancelSMul_iff_stabilizer_eq_bot.2 fun z ↦ ?_
  rw [stabilizer_levelSubMulAction_eq_bot_iff]
  obtain ⟨h₁, h₂⟩ := (hμ.mem_levelSubMulAction_prodMap hν hsmul).1 z.property
  -- The stabilizers of the components of `z` in `G` and in `K` are trivial.
  have hG := (hμ.stabilizer_levelSubMulAction_eq_bot_iff
    ⟨z.val.1, hμ.mem_levelSubMulAction.2 h₁⟩).1 (isCancelSMul_iff_stabilizer_eq_bot.1 ‹_› _)
  have hK := (hν.stabilizer_levelSubMulAction_eq_bot_iff
    ⟨z.val.2, hν.mem_levelSubMulAction.2 h₂⟩).1 (isCancelSMul_iff_stabilizer_eq_bot.1 ‹_› _)
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ ?_
  rw [MulAction.mem_stabilizer_iff, hsmul, Prod.ext_iff] at hg
  exact Prod.ext ((Subgroup.eq_bot_iff_forall _).1 hG _ hg.1)
    ((Subgroup.eq_bot_iff_forall _).1 hK _ hg.2)

/-! ### The level of a product as a manifold -/

variable [I₁.Boundaryless] [I₂.Boundaryless] {n₁ n₂ n : ℕ}
  (hreg₁ : ∀ x, μ x = c → Function.Surjective (hμ.differential x))
  (hreg₂ : ∀ y, ν y = c' → Function.Surjective (hν.differential y))
  (hn₁ : finrank ℝ E₁ - finrank ℝ (GroupLieAlgebra I G) = n₁)
  (hn₂ : finrank ℝ E₂ - finrank ℝ (GroupLieAlgebra I' K) = n₂)
  (hn : finrank ℝ (E₁ × E₂) - finrank ℝ (GroupLieAlgebra (I.prod I') (G × K)) = n)

/-- The identification of the level of the product with the product of the levels is smooth, as
a map into the product of two embedded submanifolds. -/
private theorem contMDiff_levelSubMulActionProdEquiv :
    letI := (hμ.prodMap hν hsmul).levelSubMulActionChartedSpace
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn
    letI := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
    letI := hν.levelSubMulActionChartedSpace c' hreg₂ hn₂
    ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n₁ → ℝ).prod 𝓘(ℝ, Fin n₂ → ℝ)) ∞
      (hμ.levelSubMulActionProdEquiv (c := c) (c' := c') hν hsmul) := by
  have hreg := hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul
    hreg₁ hreg₂
  let := (hμ.prodMap hν hsmul).levelSubMulActionChartedSpace _ hreg hn
  let := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
  let := hν.levelSubMulActionChartedSpace c' hreg₂ hn₂
  have hemb := (hμ.prodMap hν hsmul).isSmoothEmbedding_coe_levelSubMulAction hreg hn
  exact (((hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff_iff_comp).2
      (contMDiff_fst.comp hemb.contMDiff)).prodMk
    (((hν.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff_iff_comp).2
      (contMDiff_snd.comp hemb.contMDiff))

/-- The inverse identification of the product of the levels with the level of the product is
smooth, as a map into an embedded submanifold of `M × N`. -/
private theorem contMDiff_levelSubMulActionProdEquiv_symm :
    letI := (hμ.prodMap hν hsmul).levelSubMulActionChartedSpace
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn
    letI := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
    letI := hν.levelSubMulActionChartedSpace c' hreg₂ hn₂
    ContMDiff (𝓘(ℝ, Fin n₁ → ℝ).prod 𝓘(ℝ, Fin n₂ → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
      (hμ.levelSubMulActionProdEquiv (c := c) (c' := c') hν hsmul).symm := by
  have hreg := hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul
    hreg₁ hreg₂
  let := (hμ.prodMap hν hsmul).levelSubMulActionChartedSpace _ hreg hn
  let := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
  let := hν.levelSubMulActionChartedSpace c' hreg₂ hn₂
  have hemb := (hμ.prodMap hν hsmul).isSmoothEmbedding_coe_levelSubMulAction hreg hn
  exact hemb.contMDiff_iff_comp.2
    ((hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff.prodMap
      (hν.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff)

/-! ### The reduced space of a product -/

section Quotient

variable [ProperSMul G M] [ProperSMul K N]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (hμ.levelSubMulAction c)]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I' K).stabilizer c') (hν.levelSubMulAction c')]
  {F₁ F₂ F : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d₁ : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F₁)
  (d₂ : Lie.EmbeddedLieSubgroupData I' ((Lie.coadjointRepresentation ℝ I' K).stabilizer c') F₂)
  (d : Lie.EmbeddedLieSubgroupData (I.prod I')
    ((Lie.coadjointRepresentation ℝ (I.prod I') (G × K)).stabilizer
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))) F)

/-- **The reduced space of a product is the product of the reduced spaces.** The map
`[(x, y)] ↦ ([x], [y])` from the reduced space of `M × N` at `(c, c')`, for the factorwise action
of `G × K` and the moment map `(x, y) ↦ (μ x, ν y)`, to the product of the reduced spaces of `M`
at `c` and of `N` at `c'` is a diffeomorphism. Each reduced space carries the atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientChartedSpace` of the quotient
manifold theorem, for arbitrary embedded Lie subgroup structures `d`, `d₁`, `d₂` on the coadjoint
stabilizers; the product inherits the hypotheses of the reduction theorem from its factors. -/
def orbitRelQuotientProdDiffeomorph :
    haveI := ProperSMul.prod_of_smul_eq (G := G) (K := K) hsmul
    haveI := hμ.isCancelSMul_levelSubMulAction_prodMap (c := c) (c' := c') hν hsmul
    letI := (hμ.prodMap hν hsmul).orbitRelQuotientChartedSpace
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn d
    letI := hμ.orbitRelQuotientChartedSpace c hreg₁ hn₁ d₁
    letI := hν.orbitRelQuotientChartedSpace c' hreg₂ hn₂ d₂
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ (I.prod I') (G × K)).stabilizer
        (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c')))
        ((hμ.prodMap hν hsmul).levelSubMulAction
          (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace F₁ (Fin n₁ → ℝ)).prod
        𝓘(ℝ, ProperSMul.QuotientModelSpace F₂ (Fin n₂ → ℝ))⟯
      MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (hμ.levelSubMulAction c) ×
        MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I' K).stabilizer c')
          (hν.levelSubMulAction c') :=
  haveI := ProperSMul.prod_of_smul_eq (G := G) (K := K) hsmul
  haveI := hμ.isCancelSMul_levelSubMulAction_prodMap (c := c) (c' := c') hν hsmul
  have hreg := hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul
    hreg₁ hreg₂
  letI := (hμ.prodMap hν hsmul).levelSubMulActionChartedSpace _ hreg hn
  letI := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
  letI := hν.levelSubMulActionChartedSpace c' hreg₂ hn₂
  letI := (hμ.prodMap hν hsmul).orbitRelQuotientChartedSpace _ hreg hn d
  letI := hμ.orbitRelQuotientChartedSpace c hreg₁ hn₁ d₁
  letI := hν.orbitRelQuotientChartedSpace c' hreg₂ hn₂ d₂
  haveI := (hμ.prodMap hν hsmul).isManifold_levelSubMulAction hreg hn
  haveI := hμ.isManifold_levelSubMulAction hreg₁ hn₁
  haveI := hν.isManifold_levelSubMulAction hreg₂ hn₂
  haveI := hμ.isManifold_orbitRelQuotient hreg₁ hn₁ d₁
  haveI := hν.isManifold_orbitRelQuotient hreg₂ hn₂ d₂
  have hsub := (hμ.prodMap hν hsmul).isSubmersion_quotientMk_levelSubMulAction hreg hn d
  have hsub₁₂ := (hμ.isSubmersion_quotientMk_levelSubMulAction hreg₁ hn₁ d₁).prodMap
    (hν.isSubmersion_quotientMk_levelSubMulAction hreg₂ hn₂ d₂)
  { toEquiv := (Quotient.congr (hμ.levelSubMulActionProdEquiv hν hsmul)
      (hμ.orbitRel_levelSubMulAction_prod_iff hν hsmul)).trans (Setoid.prodQuotientEquiv _ _).symm
    -- Smoothness descends along the orbit projections, which are surjective submersions.
    contMDiff_toFun := (hsub.contMDiff_comp_iff Quotient.mk_surjective le_rfl).1
      (hsub₁₂.contMDiff.comp (hμ.contMDiff_levelSubMulActionProdEquiv hν hsmul hreg₁ hreg₂
        hn₁ hn₂ hn))
    contMDiff_invFun := (hsub₁₂.contMDiff_comp_iff
      (Quotient.mk_surjective.prodMap Quotient.mk_surjective) le_rfl).1
      (hsub.contMDiff.comp (hμ.contMDiff_levelSubMulActionProdEquiv_symm hν hsmul hreg₁ hreg₂
        hn₁ hn₂ hn)) }

/-- The diffeomorphism of reduced spaces sends the orbit of `(x, y)` to the pair of the orbits of
`x` and of `y`. -/
@[simp]
theorem orbitRelQuotientProdDiffeomorph_mk
    (z : (hμ.prodMap hν hsmul).levelSubMulAction
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))) :
    haveI := ProperSMul.prod_of_smul_eq (G := G) (K := K) hsmul
    haveI := hμ.isCancelSMul_levelSubMulAction_prodMap (c := c) (c' := c') hν hsmul
    letI := (hμ.prodMap hν hsmul).orbitRelQuotientChartedSpace
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn d
    letI := hμ.orbitRelQuotientChartedSpace c hreg₁ hn₁ d₁
    letI := hν.orbitRelQuotientChartedSpace c' hreg₂ hn₂ d₂
    hμ.orbitRelQuotientProdDiffeomorph hν hsmul hreg₁ hreg₂ hn₁ hn₂ hn d₁ d₂ d
        (Quotient.mk _ z) =
      (Quotient.mk _ ⟨z.val.1, hμ.mem_levelSubMulAction.2
          ((hμ.mem_levelSubMulAction_prodMap hν hsmul).1 z.property).1⟩,
        Quotient.mk _ ⟨z.val.2, hν.mem_levelSubMulAction.2
          ((hμ.mem_levelSubMulAction_prodMap hν hsmul).1 z.property).2⟩) :=
  (rfl)

/-- The inverse diffeomorphism of reduced spaces sends the pair of the orbits of `x` and of `y` to
the orbit of `(x, y)`. -/
@[simp]
theorem orbitRelQuotientProdDiffeomorph_symm_mk (x : hμ.levelSubMulAction c)
    (y : hν.levelSubMulAction c') :
    haveI := ProperSMul.prod_of_smul_eq (G := G) (K := K) hsmul
    haveI := hμ.isCancelSMul_levelSubMulAction_prodMap (c := c) (c' := c') hν hsmul
    letI := (hμ.prodMap hν hsmul).orbitRelQuotientChartedSpace
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn d
    letI := hμ.orbitRelQuotientChartedSpace c hreg₁ hn₁ d₁
    letI := hν.orbitRelQuotientChartedSpace c' hreg₂ hn₂ d₂
    (hμ.orbitRelQuotientProdDiffeomorph hν hsmul hreg₁ hreg₂ hn₁ hn₂ hn d₁ d₂ d).symm
        (Quotient.mk _ x, Quotient.mk _ y) =
      Quotient.mk _ ⟨(x.val, y.val), (hμ.mem_levelSubMulAction_prodMap hν hsmul).2
        ⟨hμ.mem_levelSubMulAction.1 x.property, hν.mem_levelSubMulAction.1 y.property⟩⟩ :=
  (rfl)

/-- **The reduced form of a product is the product of the reduced forms.** Let `η₁` and `η₂` be
the reduced forms of `M` at `c` and of `N` at `c'`, with `π₁^* η₁ = i₁^* σ` and
`π₂^* η₂ = i₂^* τ` for the orbit projections `πᵢ` and the inclusions `iᵢ` of the levels, and let
`η` be the reduced form of `M × N` at `(c, c')`, with `π^* η = i^* (σ ⊞ τ)`. Then the
diffeomorphism `[(x, y)] ↦ ([x], [y])` pulls `η₁ ⊞ η₂` back to `η`: the reduced space of the
product is symplectomorphic to the product of the reduced spaces. -/
theorem mpullback_orbitRelQuotientProdDiffeomorph_prod :
    haveI := ProperSMul.prod_of_smul_eq (G := G) (K := K) hsmul
    haveI := hμ.isCancelSMul_levelSubMulAction_prodMap (c := c) (c' := c') hν hsmul
    letI := (hμ.prodMap hν hsmul).levelSubMulActionChartedSpace
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn
    letI := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
    letI := hν.levelSubMulActionChartedSpace c' hreg₂ hn₂
    letI := (hμ.prodMap hν hsmul).orbitRelQuotientChartedSpace
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn d
    letI := hμ.orbitRelQuotientChartedSpace c hreg₁ hn₁ d₁
    letI := hν.orbitRelQuotientChartedSpace c' hreg₂ hn₂ d₂
    haveI := (hμ.prodMap hν hsmul).isManifold_levelSubMulAction
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn
    haveI := hμ.isManifold_levelSubMulAction hreg₁ hn₁
    haveI := hν.isManifold_levelSubMulAction hreg₂ hn₂
    haveI := (hμ.prodMap hν hsmul).isManifold_orbitRelQuotient
      (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul hreg₁
        hreg₂) hn d
    haveI := hμ.isManifold_orbitRelQuotient hreg₁ hn₁ d₁
    haveI := hν.isManifold_orbitRelQuotient hreg₂ hn₂ d₂
    ∀ (η₁ : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F₁ (Fin n₁ → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (hμ.levelSubMulAction c)))
      (η₂ : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F₂ (Fin n₂ → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I' K).stabilizer c')
          (hν.levelSubMulAction c')))
      (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient
          ((Lie.coadjointRepresentation ℝ (I.prod I') (G × K)).stabilizer
            (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c')))
          ((hμ.prodMap hν hsmul).levelSubMulAction
            (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I' K (c, c'))))),
      SmoothForm.mpullback _
          (hμ.isSubmersion_quotientMk_levelSubMulAction hreg₁ hn₁ d₁).contMDiff η₁ =
        SmoothForm.mpullback Subtype.val
          (hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff σ →
      SmoothForm.mpullback _
          (hν.isSubmersion_quotientMk_levelSubMulAction hreg₂ hn₂ d₂).contMDiff η₂ =
        SmoothForm.mpullback Subtype.val
          (hν.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff τ →
      SmoothForm.mpullback _
          ((hμ.prodMap hν hsmul).isSubmersion_quotientMk_levelSubMulAction
            (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul
              hreg₁ hreg₂) hn d).contMDiff η =
        SmoothForm.mpullback Subtype.val
          ((hμ.prodMap hν hsmul).isSmoothEmbedding_coe_levelSubMulAction
            (hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul
              hreg₁ hreg₂) hn).contMDiff (σ.prod τ) →
      SmoothForm.mpullback (hμ.orbitRelQuotientProdDiffeomorph hν hsmul hreg₁ hreg₂ hn₁ hn₂ hn
          d₁ d₂ d)
          (hμ.orbitRelQuotientProdDiffeomorph hν hsmul hreg₁ hreg₂ hn₁ hn₂ hn d₁ d₂ d).contMDiff
          (η₁.prod η₂) = η := by
  intro η₁ η₂ η hη₁ hη₂ hη
  have := ProperSMul.prod_of_smul_eq (G := G) (K := K) hsmul
  have := hμ.isCancelSMul_levelSubMulAction_prodMap (c := c) (c' := c') hν hsmul
  have hreg := hμ.toIsMomentMap.forall_differential_surjective_prodMap hν.toIsMomentMap hsmul
    hreg₁ hreg₂
  let := (hμ.prodMap hν hsmul).levelSubMulActionChartedSpace _ hreg hn
  let := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
  let := hν.levelSubMulActionChartedSpace c' hreg₂ hn₂
  let := (hμ.prodMap hν hsmul).orbitRelQuotientChartedSpace _ hreg hn d
  let := hμ.orbitRelQuotientChartedSpace c hreg₁ hn₁ d₁
  let := hν.orbitRelQuotientChartedSpace c' hreg₂ hn₂ d₂
  have := (hμ.prodMap hν hsmul).isManifold_levelSubMulAction hreg hn
  have := hμ.isManifold_levelSubMulAction hreg₁ hn₁
  have := hν.isManifold_levelSubMulAction hreg₂ hn₂
  have := (hμ.prodMap hν hsmul).isManifold_orbitRelQuotient hreg hn d
  have := hμ.isManifold_orbitRelQuotient hreg₁ hn₁ d₁
  have := hν.isManifold_orbitRelQuotient hreg₂ hn₂ d₂
  have hsub := (hμ.prodMap hν hsmul).isSubmersion_quotientMk_levelSubMulAction hreg hn d
  -- The product of the reduced forms is reduced data for `σ ⊞ τ` on the product of the levels,
  -- and the level of the product maps to the product of the levels compatibly with the
  -- inclusions into `M × N` and with the orbit projections. The diffeomorphism of reduced spaces
  -- is by definition the map of orbits induced by this identification of the levels, which
  -- gives the last argument `rfl`.
  refine SmoothForm.mpullback_eq_of_mpullback_eq
    ((hμ.prodMap hν hsmul).isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    hsub.contMDiff
    ((hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff.prodMap
      (hν.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff)
    ((hμ.isSubmersion_quotientMk_levelSubMulAction hreg₁ hn₁ d₁).contMDiff.prodMap
      (hν.isSubmersion_quotientMk_levelSubMulAction hreg₂ hn₂ d₂).contMDiff) hη
    (mpullback_prodMap_prod_eq_mpullback_prodMap_prod _ _ _ _ hη₁ hη₂) Quotient.mk_surjective
    (hsub.surjective_mfderiv (by simp))
    (hμ.contMDiff_levelSubMulActionProdEquiv hν hsmul hreg₁ hreg₂ hn₁ hn₂ hn) ?_ _ rfl
  -- The inclusion of the product of the levels, after the identification, is the inclusion of
  -- the level of the product: both send `z` to the pair of the coordinates of `z`.
  rw [SmoothForm.mpullback_mpullback]
  rfl

end Quotient

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
