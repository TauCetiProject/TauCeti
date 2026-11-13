/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# The differential at the identity of a group homomorphism

A group homomorphism `φ : K →* G` between groups modelled on manifolds has a differential at the
identity `dφ : Lie(K) → Lie(G)`, a continuous linear map between the tangent Lie algebras. This
file names that map and proves its functor laws: the identity homomorphism has identity
differential, and the chain rule holds at the identity for homomorphisms differentiable there.
It also computes the differentials of the projections and inclusions of a product `G × K`, which
identify the tangent Lie algebra of `G × K` with the product of those of `G` and `K`.

## Main definitions

* `MonoidHom.groupLieAlgebraMap`: the differential at the identity of a group homomorphism, as a
  continuous linear map between tangent Lie algebras.
* `TauCeti.Lie.groupLieAlgebraProdEquiv`: the continuous linear equivalence
  `Lie(G × K) ≃ Lie(G) × Lie(K)` given by the differentials of the two projections.

## Main results

* `MonoidHom.groupLieAlgebraMap_id`: the differential of the identity is the identity.
* `MonoidHom.groupLieAlgebraMap_comp`: the chain rule at the identity.
* `MonoidHom.groupLieAlgebraMap_fst`, `MonoidHom.groupLieAlgebraMap_snd`,
  `MonoidHom.groupLieAlgebraMap_inl`, `MonoidHom.groupLieAlgebraMap_inr`: the tangent Lie algebra
  of `G × K` at the identity is the product of those of `G` and `K`, and the projections and
  inclusions of the factors have the linear projections and inclusions as differentials.
-/

public section

noncomputable section

open scoped Manifold

namespace MonoidHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace HK]
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]

/-- The differential `dφ : Lie(K) → Lie(G)` at the identity of a group homomorphism `φ : K →* G`,
as a continuous linear map between the tangent Lie algebras. It is zero when `φ` is not
differentiable at the identity. -/
def groupLieAlgebraMap (φ : K →* G) (J : ModelWithCorners 𝕜 F HK)
    (I : ModelWithCorners 𝕜 E H) : GroupLieAlgebra J K →L[𝕜] GroupLieAlgebra I G :=
  mfderiv J I φ 1

/-- The differential at the identity of `φ`, applied to `ξ`. -/
theorem groupLieAlgebraMap_apply (φ : K →* G) (J : ModelWithCorners 𝕜 F HK)
    (ξ : GroupLieAlgebra J K) : φ.groupLieAlgebraMap J I ξ = mfderiv J I φ 1 ξ :=
  (rfl)

/-- The differential of the identity homomorphism is the identity. -/
@[simp]
theorem groupLieAlgebraMap_id :
    (MonoidHom.id G).groupLieAlgebraMap I I = ContinuousLinearMap.id 𝕜 (GroupLieAlgebra I G) := by
  ext ξ
  rw [groupLieAlgebraMap_apply, coe_id, mfderiv_id]

/-- **The chain rule at the identity.** The differential of a composite of homomorphisms that are
differentiable at the identity is the composite of their differentials. -/
theorem groupLieAlgebraMap_comp {F' HK' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] [TopologicalSpace HK'] {J' : ModelWithCorners 𝕜 F' HK'} {K' : Type*}
    [TopologicalSpace K'] [ChartedSpace HK' K'] [Group K'] {J : ModelWithCorners 𝕜 F HK}
    (ψ : K →* G) (φ : K' →* K) (hψ : MDifferentiableAt J I ψ 1)
    (hφ : MDifferentiableAt J' J φ 1) :
    (ψ.comp φ).groupLieAlgebraMap J' I =
      (ψ.groupLieAlgebraMap J I).comp (φ.groupLieAlgebraMap J' J) := by
  ext ξ
  simp only [ContinuousLinearMap.comp_apply, groupLieAlgebraMap_apply, coe_comp]
  exact mfderiv_comp_apply_of_eq 1 hψ hφ (map_one φ) ξ

/-! ### Products

The tangent space of `G × K` at the identity is the product of the model spaces of `G` and `K`,
so `GroupLieAlgebra (I.prod J) (G × K)` is `GroupLieAlgebra I G × GroupLieAlgebra J K`. -/

variable (G K) (J : ModelWithCorners 𝕜 F HK)

/-- The differential of the first projection `G × K → G` is the first linear projection. -/
theorem groupLieAlgebraMap_fst :
    (fst G K).groupLieAlgebraMap (I.prod J) I = ContinuousLinearMap.fst 𝕜 E F := by
  rw [groupLieAlgebraMap, coe_fst, mfderiv_fst]
  rfl

/-- The differential of the second projection `G × K → K` is the second linear projection. -/
theorem groupLieAlgebraMap_snd :
    (snd G K).groupLieAlgebraMap (I.prod J) J = ContinuousLinearMap.snd 𝕜 E F := by
  rw [groupLieAlgebraMap, coe_snd, mfderiv_snd]
  rfl

/-- The differential of the inclusion `G → G × K` of the first factor is the first linear
inclusion. -/
theorem groupLieAlgebraMap_inl :
    (inl G K).groupLieAlgebraMap I (I.prod J) = ContinuousLinearMap.inl 𝕜 E F := by
  rw [groupLieAlgebraMap, show ⇑(inl G K) = fun x ↦ (x, 1) from funext inl_apply,
    mfderiv_prod_left]
  rfl

/-- The differential of the inclusion `K → G × K` of the second factor is the second linear
inclusion. -/
theorem groupLieAlgebraMap_inr :
    (inr G K).groupLieAlgebraMap J (I.prod J) = ContinuousLinearMap.inr 𝕜 E F := by
  rw [groupLieAlgebraMap, show ⇑(inr G K) = fun y ↦ (1, y) from funext inr_apply,
    mfderiv_prod_right]
  rfl

variable {G K J}

/-- The first projection undoes the inclusion of the first factor. -/
@[simp]
theorem groupLieAlgebraMap_fst_groupLieAlgebraMap_inl (ξ : GroupLieAlgebra I G) :
    (fst G K).groupLieAlgebraMap (I.prod J) I ((inl G K).groupLieAlgebraMap I (I.prod J) ξ) =
      ξ := by
  rw [groupLieAlgebraMap_fst, groupLieAlgebraMap_inl]
  rfl

/-- The second projection kills the inclusion of the first factor. -/
@[simp]
theorem groupLieAlgebraMap_snd_groupLieAlgebraMap_inl (ξ : GroupLieAlgebra I G) :
    (snd G K).groupLieAlgebraMap (I.prod J) J ((inl G K).groupLieAlgebraMap I (I.prod J) ξ) =
      0 := by
  rw [groupLieAlgebraMap_snd, groupLieAlgebraMap_inl]
  rfl

/-- The first projection kills the inclusion of the second factor. -/
@[simp]
theorem groupLieAlgebraMap_fst_groupLieAlgebraMap_inr (ξ : GroupLieAlgebra J K) :
    (fst G K).groupLieAlgebraMap (I.prod J) I ((inr G K).groupLieAlgebraMap J (I.prod J) ξ) =
      0 := by
  rw [groupLieAlgebraMap_fst, groupLieAlgebraMap_inr]
  rfl

/-- The second projection undoes the inclusion of the second factor. -/
@[simp]
theorem groupLieAlgebraMap_snd_groupLieAlgebraMap_inr (ξ : GroupLieAlgebra J K) :
    (snd G K).groupLieAlgebraMap (I.prod J) J ((inr G K).groupLieAlgebraMap J (I.prod J) ξ) =
      ξ := by
  rw [groupLieAlgebraMap_snd, groupLieAlgebraMap_inr]
  rfl

/-- An element of the Lie algebra of `G × K` is the sum of the inclusions of its two
projections. -/
theorem groupLieAlgebraMap_inl_add_groupLieAlgebraMap_inr
    (ξ : GroupLieAlgebra (I.prod J) (G × K)) :
    (inl G K).groupLieAlgebraMap I (I.prod J) ((fst G K).groupLieAlgebraMap (I.prod J) I ξ) +
      (inr G K).groupLieAlgebraMap J (I.prod J) ((snd G K).groupLieAlgebraMap (I.prod J) J ξ) =
        ξ := by
  rw [groupLieAlgebraMap_fst, groupLieAlgebraMap_snd, groupLieAlgebraMap_inl,
    groupLieAlgebraMap_inr]
  exact Prod.ext (add_zero _) (zero_add _)

end MonoidHom

namespace TauCeti.Lie

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace HK]
  {J : ModelWithCorners 𝕜 F HK} {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]

variable (𝕜 I G J K) in
/-- The tangent Lie algebra of `G × K` at the identity is the product of the tangent Lie algebras
of `G` and `K`: `ξ ↦ (d(pr_G) ξ, d(pr_K) ξ)`, with inverse `(ξ, η) ↦ d(in_G) ξ + d(in_K) η`. -/
def groupLieAlgebraProdEquiv :
    GroupLieAlgebra (I.prod J) (G × K) ≃L[𝕜] GroupLieAlgebra I G × GroupLieAlgebra J K :=
  .equivOfInverse
    (((MonoidHom.fst G K).groupLieAlgebraMap (I.prod J) I).prod
      ((MonoidHom.snd G K).groupLieAlgebraMap (I.prod J) J))
    (((MonoidHom.inl G K).groupLieAlgebraMap I (I.prod J)).coprod
      ((MonoidHom.inr G K).groupLieAlgebraMap J (I.prod J)))
    (fun ξ ↦ by
      rw [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply,
        MonoidHom.groupLieAlgebraMap_inl_add_groupLieAlgebraMap_inr])
    fun ν ↦ by
      ext <;>
      simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply, map_add,
        MonoidHom.groupLieAlgebraMap_fst_groupLieAlgebraMap_inl,
        MonoidHom.groupLieAlgebraMap_snd_groupLieAlgebraMap_inl,
        MonoidHom.groupLieAlgebraMap_fst_groupLieAlgebraMap_inr,
        MonoidHom.groupLieAlgebraMap_snd_groupLieAlgebraMap_inr, Prod.mk_add_mk, add_zero,
        zero_add]

/-- The components of an element of the Lie algebra of `G × K` are its images under the
differentials of the two projections. -/
@[simp]
theorem groupLieAlgebraProdEquiv_apply (ξ : GroupLieAlgebra (I.prod J) (G × K)) :
    groupLieAlgebraProdEquiv 𝕜 I G J K ξ =
      ((MonoidHom.fst G K).groupLieAlgebraMap (I.prod J) I ξ,
        (MonoidHom.snd G K).groupLieAlgebraMap (I.prod J) J ξ) :=
  (rfl)

/-- A pair of elements of the Lie algebras of `G` and `K` is the sum of their images under the
differentials of the two inclusions. -/
@[simp]
theorem groupLieAlgebraProdEquiv_symm_apply (ξ : GroupLieAlgebra I G × GroupLieAlgebra J K) :
    (groupLieAlgebraProdEquiv 𝕜 I G J K).symm ξ =
      (MonoidHom.inl G K).groupLieAlgebraMap I (I.prod J) ξ.1 +
        (MonoidHom.inr G K).groupLieAlgebraMap J (I.prod J) ξ.2 :=
  (rfl)

end TauCeti.Lie
