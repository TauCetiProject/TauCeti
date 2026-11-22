/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Prod
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit
public import TauCeti.Geometry.Symplectic.Manifold.Prod
import TauCeti.Geometry.Manifold.Algebra.Monoid

/-!
# Coadjoint orbits of a product of Lie groups

Let `G` and `K` be real Lie groups with finite-dimensional boundaryless models, with Lie algebras
`𝔤` and `𝔨`, and fix `ν ∈ 𝔤*` and `ν' ∈ 𝔨*`. The dual of the Lie algebra of `G × K` is
`𝔤* × 𝔨*` (`TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`), so `(ν, ν')` is a covector of
`G × K`, with coadjoint stabilizer `G_ν × K_ν'`
(`TauCeti.Lie.stabilizer_coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual`). This file
proves that its coadjoint orbit is the product of the coadjoint orbits of `ν` and `ν'`, as a
symplectic manifold.

* **The Kirillov form of a product.** On `G × K`, the left-invariant Kirillov form of `(ν, ν')` is
  the product `pr_G^* σ_ν + pr_K^* σ_ν'` of the left-invariant Kirillov forms of the factors
  (`Module.Dual.leftInvariantKirillovForm_groupLieAlgebraDualProdDualEquivDual`). This follows
  from additivity of the Kirillov form in the covector, since
  `(ν, ν') = ν ∘ d(pr_G) + ν' ∘ d(pr_K)`, and its naturality along the projections.
* **The product orbit.** The map `[(g, k)] ↦ ([g], [k])` is a diffeomorphism
  `(G × K) ⧸ (G × K)_{(ν, ν')} ≃ (G ⧸ G_ν) × (K ⧸ K_ν')` between the homogeneous orbit manifolds
  (`Module.Dual.coadjointOrbitProdDiffeomorph`). It is the homogeneous-space diffeomorphism
  `(G × K) ⧸ (G_ν × K_ν') ≃ (G ⧸ G_ν) × (K ⧸ K_ν')` of closed subgroups
  (`Subgroup.quotientProdDiffeomorph`).
* It is equivariant for the action of `G × K`
  (`Module.Dual.coadjointOrbitProdDiffeomorph_smul`), and it intertwines the orbit maps into
  `𝔤* × 𝔨*` (`Module.Dual.orbitMap_groupLieAlgebraDualProdDualEquivDual`).
* **The KKS form of a product.** It pulls the product `ω_ν ⊕ ω_ν'` of the
  Kirillov–Kostant–Souriau forms back to the KKS form of `(ν, ν')`
  (`Module.Dual.mpullback_coadjointOrbitProdDiffeomorph_prod`): the coadjoint orbit of a product is
  symplectomorphic to the product of the coadjoint orbits.

## Main definitions

* `Module.Dual.coadjointOrbitProdDiffeomorph ν ν'`: the diffeomorphism
  `(G × K) ⧸ (G × K)_{(ν, ν')} ≃ (G ⧸ G_ν) × (K ⧸ K_ν')`.

## Main results

* `Module.Dual.leftInvariantKirillovForm_groupLieAlgebraDualProdDualEquivDual`:
  `σ_{(ν, ν')} = pr_G^* σ_ν + pr_K^* σ_ν'`.
* `Module.Dual.coadjointOrbitProdDiffeomorph_smul`: the diffeomorphism is equivariant.
* `Module.Dual.orbitMap_groupLieAlgebraDualProdDualEquivDual`: it intertwines the orbit
  maps.
* `Module.Dual.mpullback_coadjointOrbitProdDiffeomorph_prod`: it pulls `ω_ν ⊕ ω_ν'` back to
  `ω_{(ν, ν')}`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 14 (coadjoint orbits and their symplectic structure).
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace Module.Dual

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup J ∞ K]

variable (ν : Module.Dual ℝ (GroupLieAlgebra I G)) (ν' : Module.Dual ℝ (GroupLieAlgebra J K))

/-! ### The Kirillov form of a product group -/

/-- **The Kirillov form of a product group.** The left-invariant Kirillov form of the covector
`(ν, ν')` of `G × K` is the product `pr_G^* σ_ν + pr_K^* σ_ν'` of the left-invariant Kirillov forms
of `ν` and `ν'`. -/
theorem leftInvariantKirillovForm_groupLieAlgebraDualProdDualEquivDual :
    leftInvariantKirillovForm (groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν')) =
      SmoothTwoForm.prod ν.leftInvariantKirillovForm ν'.leftInvariantKirillovForm := by
  -- The covector `(ν, ν')` is `ν ∘ d(pr_G) + ν' ∘ d(pr_K)`.
  have h : groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν') =
      ν ∘ₗ ((ContMDiffMonoidMorphism.fst (I := I) (I' := J) (n := ∞) (G' := K)).toMonoidHom
          |>.groupLieAlgebraMap (I.prod J) I).toLinearMap +
        ν' ∘ₗ ((ContMDiffMonoidMorphism.snd (I := I) (I' := J) (n := ∞) (G := G)).toMonoidHom
          |>.groupLieAlgebraMap (I.prod J) J).toLinearMap := by
    ext ξ
    simp only [groupLieAlgebraDualProdDualEquivDual_apply, LinearMap.add_apply,
      LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContMDiffMonoidMorphism.toMonoidHom_fst,
      ContMDiffMonoidMorphism.toMonoidHom_snd]
  rw [h, leftInvariantKirillovForm_add, ← mpullback_leftInvariantKirillovForm,
    ← mpullback_leftInvariantKirillovForm, SmoothTwoForm.prod_def]
  simp only [ContMDiffMonoidMorphism.coe_fst, ContMDiffMonoidMorphism.coe_snd]

/-! ### The product orbit -/

variable [I.Boundaryless] [J.Boundaryless]

/-- **The coadjoint orbit of a product is the product of the coadjoint orbits.** The map
`[(g, k)] ↦ ([g], [k])` is a diffeomorphism from the coadjoint orbit `(G × K) ⧸ (G × K)_{(ν, ν')}`
of `(ν, ν')` onto the product `(G ⧸ G_ν) × (K ⧸ K_ν')` of the coadjoint orbits of `ν` and `ν'`. It
pulls the product of the KKS forms back to the KKS form
(`Module.Dual.mpullback_coadjointOrbitProdDiffeomorph_prod`). -/
def coadjointOrbitProdDiffeomorph :
    Diffeomorph
      𝓘(ℝ, Subgroup.QuotientModelSpace (I.prod J)
        ((coadjointRepresentation ℝ (I.prod J) (G × K)).stabilizer
          (groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν'))))
      (𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)).prod
        𝓘(ℝ, Subgroup.QuotientModelSpace J ((coadjointRepresentation ℝ J K).stabilizer ν')))
      ((G × K) ⧸ (coadjointRepresentation ℝ (I.prod J) (G × K)).stabilizer
        (groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν')))
      ((G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) ×
        (K ⧸ (coadjointRepresentation ℝ J K).stabilizer ν')) ∞ :=
  Subgroup.quotientProdDiffeomorph I J (isClosed_stabilizer_coadjointRepresentation I ν)
    (isClosed_stabilizer_coadjointRepresentation J ν')
    (stabilizer_coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual (ν, ν'))

/-- The diffeomorphism sends the coset of `(g, k)` to the pair of cosets of `g` and `k`. -/
@[simp]
theorem coadjointOrbitProdDiffeomorph_mk (g : G × K) :
    coadjointOrbitProdDiffeomorph ν ν' g = ((g.1 : G ⧸ _), (g.2 : K ⧸ _)) :=
  Subgroup.quotientProdDiffeomorph_mk _ _ _ g

/-- The inverse diffeomorphism sends the pair of cosets of `g` and `k` to the coset of `(g, k)`. -/
@[simp]
theorem coadjointOrbitProdDiffeomorph_symm_mk (g : G) (k : K) :
    (coadjointOrbitProdDiffeomorph ν ν').symm ((g : G ⧸ _), (k : K ⧸ _)) =
      ((g, k) : (G × K) ⧸ _) :=
  Subgroup.quotientProdDiffeomorph_symm_mk _ _ _ g k

/-- The diffeomorphism composed with the projection of `G × K` onto the coadjoint orbit of `(ν, ν')`
is the product of the projections onto the coadjoint orbits of `ν` and `ν'`. -/
theorem coadjointOrbitProdDiffeomorph_comp_mk :
    coadjointOrbitProdDiffeomorph ν ν' ∘ QuotientGroup.mk =
      Prod.map (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (QuotientGroup.mk : K → K ⧸ (coadjointRepresentation ℝ J K).stabilizer ν') :=
  funext (coadjointOrbitProdDiffeomorph_mk ν ν')

/-- **The product diffeomorphism is equivariant**: the action of `(g, k)` on the coadjoint orbit of
`(ν, ν')` corresponds to the action of `g` and `k` on the two factors. -/
theorem coadjointOrbitProdDiffeomorph_smul (g : G × K)
    (x : (G × K) ⧸ (coadjointRepresentation ℝ (I.prod J) (G × K)).stabilizer
      (groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν'))) :
    coadjointOrbitProdDiffeomorph ν ν' (g • x) =
      (g.1 • (coadjointOrbitProdDiffeomorph ν ν' x).1,
        g.2 • (coadjointOrbitProdDiffeomorph ν ν' x).2) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [MulAction.Quotient.smul_coe, coadjointOrbitProdDiffeomorph_mk, smul_eq_mul,
    Prod.fst_mul, Prod.snd_mul]

/-- **The orbit map of a product.** Under `𝔤* × 𝔨* ≃ Lie(G × K)*`, the orbit map of `(ν, ν')` is
the pair of orbit maps of `ν` and `ν'`, read through the product diffeomorphism. -/
theorem orbitMap_groupLieAlgebraDualProdDualEquivDual
    (x : (G × K) ⧸ (coadjointRepresentation ℝ (I.prod J) (G × K)).stabilizer
      (groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν'))) :
    (coadjointRepresentation ℝ (I.prod J) (G × K)).orbitMap
        (groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν')) x =
      groupLieAlgebraDualProdDualEquivDual ℝ I G J K
        ((coadjointRepresentation ℝ I G).orbitMap ν (coadjointOrbitProdDiffeomorph ν ν' x).1,
          (coadjointRepresentation ℝ J K).orbitMap ν'
            (coadjointOrbitProdDiffeomorph ν ν' x).2) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Representation.orbitMap_mk, coadjointOrbitProdDiffeomorph_mk, Representation.orbitMap_mk,
    Representation.orbitMap_mk, coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual]

/-- **The KKS form of a product.** The product diffeomorphism
`(G × K) ⧸ (G × K)_{(ν, ν')} ≃ (G ⧸ G_ν) × (K ⧸ K_ν')` pulls the product `ω_ν ⊕ ω_ν'` of the
Kirillov–Kostant–Souriau forms back to the KKS form of `(ν, ν')`. So the coadjoint orbit of a
product of Lie groups is symplectomorphic to the product of the coadjoint orbits of the factors. -/
theorem mpullback_coadjointOrbitProdDiffeomorph_prod :
    SmoothForm.mpullback (coadjointOrbitProdDiffeomorph ν ν')
        (coadjointOrbitProdDiffeomorph ν ν').contMDiff
        (SmoothTwoForm.prod ν.coadjointOrbitForm ν'.coadjointOrbitForm) =
      coadjointOrbitForm (groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν')) := by
  have hπ := isSubmersion_quotientMk_stabilizer_coadjointRepresentation ν
  have hπ' := isSubmersion_quotientMk_stabilizer_coadjointRepresentation ν'
  have hπ'' := isSubmersion_quotientMk_stabilizer_coadjointRepresentation
    (groupLieAlgebraDualProdDualEquivDual ℝ I G J K (ν, ν'))
  -- Both sides pull back along `G × K → (G × K) ⧸ (G × K)_{(ν, ν')}` to `σ_{(ν, ν')}`.
  rw [eq_coadjointOrbitForm_iff _ hπ''.contMDiff, SmoothForm.mpullback_mpullback]
  simp only [coadjointOrbitProdDiffeomorph_comp_mk]
  rw [SmoothTwoForm.mpullback_prodMap_prod hπ.contMDiff hπ'.contMDiff,
    mpullback_quotientMk_coadjointOrbitForm, mpullback_quotientMk_coadjointOrbitForm,
    leftInvariantKirillovForm_groupLieAlgebraDualProdDualEquivDual]

end Module.Dual
