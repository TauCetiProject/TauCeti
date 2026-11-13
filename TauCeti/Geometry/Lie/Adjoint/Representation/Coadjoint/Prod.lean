/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic

/-!
# The coadjoint representation of a product of Lie groups

The tangent Lie algebra of a product `G × K` of Lie groups at the identity is the product
`𝔤 × 𝔨` of the tangent Lie algebras: the differentials of the projections `pr_G : G × K → G` and
`pr_K : G × K → K` give a continuous linear equivalence `Lie(G × K) ≃ 𝔤 × 𝔨`
(`TauCeti.Lie.groupLieAlgebraProdEquiv`), whose inverse is given by the differentials of the
inclusions of the two factors. Dually, a pair of covectors `ν ∈ 𝔤*`, `ν' ∈ 𝔨*` gives the covector

`ν ∘ d(pr_G) + ν' ∘ d(pr_K)`

on the Lie algebra of `G × K`, and this is a linear equivalence `𝔤* × 𝔨* ≃ Lie(G × K)*`
(`TauCeti.Lie.dualProdDualEquivDual`, Mathlib's `Module.dualProdDualEquivDual` transported along
`TauCeti.Lie.groupLieAlgebraProdEquiv`), whose inverse restricts a covector along the inclusions
of the two factors.

This identification is equivariant: the coadjoint action of `(g, k)` acts on the two components
by the coadjoint actions of `g` and of `k`
(`TauCeti.Lie.coadjointRepresentation_dualProdDualEquivDual`), because the projections intertwine
the adjoint actions (`MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`). Consequently the
coadjoint stabilizer of `(ν, ν')` is the product `G_ν × K_ν'` of the coadjoint stabilizers
(`TauCeti.Lie.stabilizer_coadjointRepresentation_dualProdDualEquivDual`).

These are the coadjoint ingredients of the reduction of a product of Hamiltonian spaces by the
product group: a moment map of `G × K` acting factorwise on `M × N` takes values in `𝔤* × 𝔨*`,
its level sets are products of levels, and the stabilizer that acts on the level is a product.

## Main definitions

* `TauCeti.Lie.dualProdDualEquivDual`: the linear equivalence `𝔤* × 𝔨* ≃ Lie(G × K)*`.

## Main results

* `TauCeti.Lie.coadjointRepresentation_dualProdDualEquivDual`: `Ad*_{(g, k)} (ν, ν') =
  (Ad*_g ν, Ad*_k ν')`.
* `TauCeti.Lie.stabilizer_coadjointRepresentation_dualProdDualEquivDual`: `(G × K)_{(ν, ν')} =
  G_ν × K_ν'`.

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

variable (𝕜 I G J K) in
/-- The dual of the tangent Lie algebra of a product of Lie groups is the product of the duals:
the pair `(ν, ν') ∈ 𝔤* × 𝔨*` corresponds to the covector `ν ∘ d(pr_G) + ν' ∘ d(pr_K)` on the
Lie algebra of `G × K`. This is Mathlib's `Module.dualProdDualEquivDual` transported along
`TauCeti.Lie.groupLieAlgebraProdEquiv`. -/
def dualProdDualEquivDual :
    (Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K)) ≃ₗ[𝕜]
      Module.Dual 𝕜 (GroupLieAlgebra (I.prod J) (G × K)) :=
  (Module.dualProdDualEquivDual 𝕜 _ _).trans
    (groupLieAlgebraProdEquiv 𝕜 I G J K).toLinearEquiv.dualMap

/-- The covector of `G × K` defined by `(ν, ν')` evaluates as `ν ∘ d(pr_G) + ν' ∘ d(pr_K)`. -/
@[simp]
theorem dualProdDualEquivDual_apply
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K))
    (ξ : GroupLieAlgebra (I.prod J) (G × K)) :
    dualProdDualEquivDual 𝕜 I G J K ν ξ =
      ν.1 ((MonoidHom.fst G K).groupLieAlgebraMap (I.prod J) I ξ) +
        ν.2 ((MonoidHom.snd G K).groupLieAlgebraMap (I.prod J) J ξ) := by
  rw [dualProdDualEquivDual, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, groupLieAlgebraProdEquiv_apply,
    Module.dualProdDualEquivDual_apply, LinearMap.coprod_apply]

/-- The pair of covectors of `G` and `K` defined by a covector of `G × K` consists of its
restrictions along the inclusions of the two factors. -/
@[simp]
theorem dualProdDualEquivDual_symm_apply
    (ν : Module.Dual 𝕜 (GroupLieAlgebra (I.prod J) (G × K))) :
    (dualProdDualEquivDual 𝕜 I G J K).symm ν =
      (ν ∘ₗ ((MonoidHom.inl G K).groupLieAlgebraMap I (I.prod J)).toLinearMap,
        ν ∘ₗ ((MonoidHom.inr G K).groupLieAlgebraMap J (I.prod J)).toLinearMap) := by
  rw [LinearEquiv.symm_apply_eq]
  ext ξ
  rw [dualProdDualEquivDual_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, ← map_add,
    MonoidHom.groupLieAlgebraMap_inl_add_groupLieAlgebraMap_inr]

variable [LieGroup I 1 G] [LieGroup J 1 K]

/-- **The coadjoint action of a product.** Under `𝔤* × 𝔨* ≃ Lie(G × K)*`, the coadjoint action of
`(g, k)` is the coadjoint action of `g` on the first component and of `k` on the second. -/
@[simp]
theorem coadjointRepresentation_dualProdDualEquivDual (g : G × K)
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K)) :
    coadjointRepresentation 𝕜 (I.prod J) (G × K) g (dualProdDualEquivDual 𝕜 I G J K ν) =
      dualProdDualEquivDual 𝕜 I G J K
        (coadjointRepresentation 𝕜 I G g.1 ν.1, coadjointRepresentation 𝕜 J K g.2 ν.2) := by
  ext ξ
  -- The projections intertwine the adjoint actions: `d(pr_G) ∘ Ad_{g⁻¹} = Ad_{g.1⁻¹} ∘ d(pr_G)`.
  rw [coadjointRepresentation_apply, dualProdDualEquivDual_apply, dualProdDualEquivDual_apply,
    MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap,
    MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap, coadjointRepresentation_apply,
    coadjointRepresentation_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, Prod.fst_inv,
    Prod.snd_inv]

/-- **The coadjoint stabilizer of a product** is the product of the coadjoint stabilizers:
`(G × K)_{(ν, ν')} = G_ν × K_ν'`. -/
theorem stabilizer_coadjointRepresentation_dualProdDualEquivDual
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K)) :
    (coadjointRepresentation 𝕜 (I.prod J) (G × K)).stabilizer
        (dualProdDualEquivDual 𝕜 I G J K ν) =
      ((coadjointRepresentation 𝕜 I G).stabilizer ν.1).prod
        ((coadjointRepresentation 𝕜 J K).stabilizer ν.2) := by
  ext g
  rw [Representation.mem_stabilizer, coadjointRepresentation_dualProdDualEquivDual,
    EquivLike.apply_eq_iff_eq, Subgroup.mem_prod, Representation.mem_stabilizer,
    Representation.mem_stabilizer, Prod.ext_iff]

end TauCeti.Lie
