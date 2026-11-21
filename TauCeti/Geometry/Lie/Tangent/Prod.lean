/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Tangent.Differential
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The dual of the tangent Lie algebra of a product of groups

The tangent Lie algebra of a product `G × K` at the identity is the product of those of `G` and
`K` (`TauCeti.Manifold.tangentSpaceProdEquiv` at `1`), with the differentials of the projections
`pr_G`, `pr_K` and inclusions of `G × K` as the linear projections and inclusions
(`MonoidHom.groupLieAlgebraMap_fst` and its companions). Dually, a pair of covectors `ν ∈ 𝔤*`,
`ν' ∈ 𝔨*` gives the covector `ν ∘ d(pr_G) + ν' ∘ d(pr_K)` on the Lie algebra of `G × K`, and
this is a linear equivalence `𝔤* × 𝔨* ≃ Lie(G × K)*` whose inverse restricts a covector along the
inclusions of the two factors.

## Main definitions

* `TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`: the linear equivalence
  `𝔤* × 𝔨* ≃ Lie(G × K)*`.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti.Lie

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace HK]
  {J : ModelWithCorners 𝕜 F HK} {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]

variable (𝕜 I G J K) in
/-- The dual of the tangent Lie algebra of a product of Lie groups is the product of the duals:
the pair `(ν, ν') ∈ 𝔤* × 𝔨*` corresponds to the covector `ν ∘ d(pr_G) + ν' ∘ d(pr_K)` on the
Lie algebra of `G × K`. This is Mathlib's `Module.dualProdDualEquivDual` transported along the
identification `TauCeti.Manifold.tangentSpaceProdEquiv` of the tangent space of `G × K` at the
identity with the product of the tangent spaces of `G` and `K`. -/
def groupLieAlgebraDualProdDualEquivDual :
    (Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K)) ≃ₗ[𝕜]
      Module.Dual 𝕜 (GroupLieAlgebra (I.prod J) (G × K)) :=
  (Module.dualProdDualEquivDual 𝕜 _ _).trans
    (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (1 : G × K)).toLinearEquiv.dualMap

/-- The covector of `G × K` defined by `(ν, ν')` evaluates as `ν ∘ d(pr_G) + ν' ∘ d(pr_K)`. -/
@[simp]
theorem groupLieAlgebraDualProdDualEquivDual_apply
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K))
    (ξ : GroupLieAlgebra (I.prod J) (G × K)) :
    groupLieAlgebraDualProdDualEquivDual 𝕜 I G J K ν ξ =
      ν.1 ((MonoidHom.fst G K).groupLieAlgebraMap (I.prod J) I ξ) +
        ν.2 ((MonoidHom.snd G K).groupLieAlgebraMap (I.prod J) J ξ) := by
  -- `TangentSpace` is not reducible to a product type, so `simp` cannot apply the product
  -- lemmas here; after unfolding, both sides are `ν.1 ξ.1 + ν.2 ξ.2` by definition.
  rw [groupLieAlgebraDualProdDualEquivDual, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, Manifold.tangentSpaceProdEquiv_apply,
    MonoidHom.groupLieAlgebraMap_fst, MonoidHom.groupLieAlgebraMap_snd]
  rfl

/-- The covector of `G × K` defined by `(ν, ν')` restricts to `ν` along the inclusion of `G`. -/
@[simp]
theorem groupLieAlgebraDualProdDualEquivDual_comp_groupLieAlgebraMap_inl
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K)) :
    groupLieAlgebraDualProdDualEquivDual 𝕜 I G J K ν ∘ₗ
        ((MonoidHom.inl G K).groupLieAlgebraMap I (I.prod J)).toLinearMap =
      ν.1 := by
  ext ξ
  simp

/-- The covector of `G × K` defined by `(ν, ν')` restricts to `ν'` along the inclusion of `K`. -/
@[simp]
theorem groupLieAlgebraDualProdDualEquivDual_comp_groupLieAlgebraMap_inr
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G) × Module.Dual 𝕜 (GroupLieAlgebra J K)) :
    groupLieAlgebraDualProdDualEquivDual 𝕜 I G J K ν ∘ₗ
        ((MonoidHom.inr G K).groupLieAlgebraMap J (I.prod J)).toLinearMap =
      ν.2 := by
  ext ξ
  simp

/-- A covector of `G × K` is the covector defined by its restrictions along the inclusions of the
two factors. -/
@[simp]
theorem groupLieAlgebraDualProdDualEquivDual_comp_groupLieAlgebraMap_inl_groupLieAlgebraMap_inr
    (ω : Module.Dual 𝕜 (GroupLieAlgebra (I.prod J) (G × K))) :
    groupLieAlgebraDualProdDualEquivDual 𝕜 I G J K
        (ω ∘ₗ ((MonoidHom.inl G K).groupLieAlgebraMap I (I.prod J)).toLinearMap,
          ω ∘ₗ ((MonoidHom.inr G K).groupLieAlgebraMap J (I.prod J)).toLinearMap) =
      ω := by
  ext ξ
  simp [← map_add]

/-- The pair of covectors of `G` and `K` defined by a covector of `G × K` consists of its
restrictions along the inclusions of the two factors. -/
@[simp]
theorem groupLieAlgebraDualProdDualEquivDual_symm_apply
    (ω : Module.Dual 𝕜 (GroupLieAlgebra (I.prod J) (G × K))) :
    (groupLieAlgebraDualProdDualEquivDual 𝕜 I G J K).symm ω =
      (ω ∘ₗ ((MonoidHom.inl G K).groupLieAlgebraMap I (I.prod J)).toLinearMap,
        ω ∘ₗ ((MonoidHom.inr G K).groupLieAlgebraMap J (I.prod J)).toLinearMap) := by
  rw [LinearEquiv.symm_apply_eq,
    groupLieAlgebraDualProdDualEquivDual_comp_groupLieAlgebraMap_inl_groupLieAlgebraMap_inr]

end TauCeti.Lie
