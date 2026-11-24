/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Tangent.Prod

/-!
# The coadjoint representation of a product of Lie groups

The dual of the tangent Lie algebra of a product `G × K` of Lie groups is identified with the
product `𝔤* × 𝔨*` of the duals (`TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`): the pair
`(ν, ν')` corresponds to the covector `ν ∘ d(pr_G) + ν' ∘ d(pr_K)`, where `pr_G : G × K → G` and
`pr_K : G × K → K` are the projections.

This identification is equivariant: the coadjoint action of `(g, k)` acts on the two components
by the coadjoint actions of `g` and of `k`
(`TauCeti.Lie.coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual`), because the
projections intertwine the adjoint actions
(`MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`). Consequently the coadjoint
stabilizer of `(ν, ν')` is the product `G_ν × K_ν'` of the coadjoint stabilizers
(`TauCeti.Lie.stabilizer_coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual`).

These are the coadjoint ingredients of the reduction of a product of Hamiltonian spaces by the
product group: a moment map of `G × K` acting factorwise on `M × N` takes values in `𝔤* × 𝔨*`,
its level sets are products of levels, and the stabilizer that acts on the level is a product.

## Main results

* `TauCeti.Lie.coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual`:
  `Ad*_{(g, k)} (ν, ν') = (Ad*_g ν, Ad*_k ν')`.
* `TauCeti.Lie.stabilizer_coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual`:
  `(G × K)_{(ν, ν')} = G_ν × K_ν'`.

## References

* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §9.3 (the adjoint and coadjoint actions).
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti.Lie

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {HK : Type*} [TopologicalSpace HK] {J : ModelWithCorners 𝕜 F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]

variable [LieGroup I 1 G] [LieGroup J 1 K]

/-- **The coadjoint action of a product.** Under `𝔤* × 𝔨* ≃ Lie(G × K)*`, the coadjoint action of
`(g, k)` is the coadjoint action of `g` on the first component and of `k` on the second. -/
@[simp]
theorem coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual (g : G × K)
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K)) :
    coadjointRepresentation 𝕜 (I.prod J) (G × K) g
        (groupLieAlgebraDualProdDualEquivDual 𝕜 I G J K ν) =
      groupLieAlgebraDualProdDualEquivDual 𝕜 I G J K
        (coadjointRepresentation 𝕜 I G g.1 ν.1, coadjointRepresentation 𝕜 J K g.2 ν.2) := by
  ext ξ
  -- The projections intertwine the adjoint actions: `d(pr_G) ∘ Ad_{g⁻¹} = Ad_{g.1⁻¹} ∘ d(pr_G)`.
  simp only [coadjointRepresentation_apply, groupLieAlgebraDualProdDualEquivDual_apply,
    MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap, MonoidHom.coe_fst, MonoidHom.coe_snd,
    Prod.fst_inv, Prod.snd_inv]

/-- **The coadjoint stabilizer of a product** is the product of the coadjoint stabilizers:
`(G × K)_{(ν, ν')} = G_ν × K_ν'`. -/
theorem stabilizer_coadjointRepresentation_groupLieAlgebraDualProdDualEquivDual
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K)) :
    (coadjointRepresentation 𝕜 (I.prod J) (G × K)).stabilizer
        (groupLieAlgebraDualProdDualEquivDual 𝕜 I G J K ν) =
      ((coadjointRepresentation 𝕜 I G).stabilizer ν.1).prod
        ((coadjointRepresentation 𝕜 J K).stabilizer ν.2) := by
  ext g
  simp [Subgroup.mem_prod, Prod.ext_iff]

end TauCeti.Lie
