/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Gluing.Basic
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# Subgroups of Lie groups with an open embedded Lie subgroup

Let `K` be a subgroup of a `C^n` Lie group `G`, and let `ι : T →* K` be a group homomorphism out
of a `C^n` Lie group `T` which is an open embedding for the subspace topology of `K`, and whose
composite with the inclusion `K → G` is a `C^n` immersion. Thus `K` contains the image of `T` as an
open subgroup, and `T` is immersed in `G`. Then `K` is an embedded Lie subgroup of `G`, modelled on
the model of `T`: the translates `k * ι(T)` of the image of `T` cover `K`, and their charts fit
together because they differ by translations of `T`.

The charts are glued, with `TauCeti.chartedSpaceOfIsOpenEmbedding`, from the open embeddings
`t ↦ k * ι t` of `T` into `K`, two of which are related by a left translation of `T`. With these
charts `K` is a `C^n` manifold and a `C^n` Lie group, the inclusion `K → G` is a `C^n` embedding,
and `ι` is a `C^n` local diffeomorphism. Since the inclusion is an immersion, Mathlib's
`ContMDiff.iff_comp_isImmersion` shows that a map into `K` is `C^n` exactly when it is continuous
and its composite with the inclusion is `C^n`.

The typical example is a closed subgroup of a torus with finitely many components, which is the
union of finitely many translates of a subtorus: for instance the kernel of a homomorphism of
complex tori induced by a linear map, whose identity component is a complex subtorus.

## Main definitions

* `Subgroup.chartedSpaceOfIsOpenEmbedding`: the charts on `K` obtained by translating the charts of
  `T`.

## Main results

* `Subgroup.isManifold_chartedSpaceOfIsOpenEmbedding`: these charts form a `C^n` manifold.
* `Subgroup.lieGroup_chartedSpaceOfIsOpenEmbedding`: `K` is a `C^n` Lie group for these charts.
* `Subgroup.isSmoothEmbedding_subtypeVal_chartedSpaceOfIsOpenEmbedding`: the inclusion of `K` into
  `G` is a `C^n` embedding.
* `Subgroup.isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding`: `ι` is a `C^n` local
  diffeomorphism.

The additive versions are `AddSubgroup.chartedSpaceOfIsOpenEmbedding` and its companions.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma) and Chapter 7 (Lie
  subgroups).
-/

public section

open Set Filter Topology Manifold
open scoped ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {G : Type*} [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {T : Type*} [Group T]

namespace Subgroup

variable (K : Subgroup G) {ι : T →* K} [TopologicalSpace G] [TopologicalSpace T]

/-- Each translate `t ↦ k * ι t` of an open embedding `ι : T →* K` is an open embedding. -/
@[to_additive /-- Each translate `t ↦ k + ι t` of an open embedding `ι : T →+ K` is an open
embedding. -/]
private theorem isOpenEmbedding_mul_apply [ContinuousMul G] (hι : IsOpenEmbedding ι) (k : K) :
    IsOpenEmbedding fun t : T ↦ k * ι t := by
  have : ContinuousMul K := K.toSubmonoid.continuousMul
  exact (Homeomorph.mulLeft k).isOpenEmbedding.comp hι

variable [ChartedSpace H' T]

omit [TopologicalSpace G] in
/-- Two translates of the image of `ι` are glued along a left translation of `T`. -/
@[to_additive /-- Two translates of the image of `ι` are glued along a translation of `T`. -/]
private theorem exists_contMDiffAt_mul_apply [LieGroup I' n T] (ι : T →* K) (j k : K) (x y : T)
    (h : j * ι x = k * ι y) :
    ∃ S : T → T, ContMDiffAt I' I' n S x ∧
      (fun t ↦ k * ι t) ∘ S =ᶠ[𝓝 x] fun t ↦ j * ι t := by
  refine ⟨fun s ↦ y * x⁻¹ * s, contMDiff_mul_left.contMDiffAt,
    Eventually.of_forall fun s ↦ ?_⟩
  simp only [Function.comp_apply, map_mul, map_inv, ← mul_assoc, ← h]
  group

variable [ContinuousMul G] (ι)

/-- The charts on a subgroup `K` containing the image of an open embedding `ι : T →* K` of a
charted group: `K` is glued from the translates `k * ι(T)` of the image of `ι`, each charted by
the charts of `T`. -/
@[to_additive (attr := instance_reducible) /-- The charts on an additive subgroup `K` containing
the image of an open embedding `ι : T →+ K` of a charted additive group: `K` is glued from the
translates `k + ι(T)` of the image of `ι`, each charted by the charts of `T`. -/]
noncomputable def chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι) : ChartedSpace H' K :=
  TauCeti.chartedSpaceOfIsOpenEmbedding (U := fun _ : K ↦ T) (isOpenEmbedding_mul_apply K hι)
    fun k ↦ ⟨k, 1, by simp⟩

variable {K ι} [LieGroup I' n T]

/-- The charts `Subgroup.chartedSpaceOfIsOpenEmbedding` form a `C^n` manifold: their transition
maps are translations of `T`. -/
@[to_additive /-- The charts `AddSubgroup.chartedSpaceOfIsOpenEmbedding` form a `C^n` manifold:
their transition maps are translations of `T`. -/]
theorem isManifold_chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    IsManifold I' n K :=
  TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding _ _ (exists_contMDiffAt_mul_apply K ι)

/-- For the charts `Subgroup.chartedSpaceOfIsOpenEmbedding`, each translate `t ↦ k * ι t` is a
`C^n` local diffeomorphism. -/
@[to_additive /-- For the charts `AddSubgroup.chartedSpaceOfIsOpenEmbedding`, each translate
`t ↦ k + ι t` is a `C^n` local diffeomorphism. -/]
private theorem isLocalDiffeomorph_mul_apply (hι : IsOpenEmbedding ι) (k : K) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    IsLocalDiffeomorph I' I' n fun t : T ↦ k * ι t :=
  TauCeti.isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding _ _
    (exists_contMDiffAt_mul_apply K ι) k

/-- For the charts `Subgroup.chartedSpaceOfIsOpenEmbedding`, the open embedding `ι : T →* K` is a
`C^n` local diffeomorphism. -/
@[to_additive /-- For the charts `AddSubgroup.chartedSpaceOfIsOpenEmbedding`, the open embedding
`ι : T →+ K` is a `C^n` local diffeomorphism. -/]
theorem isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    IsLocalDiffeomorph I' I' n ι := by
  simpa using isLocalDiffeomorph_mul_apply (I' := I') (n := n) hι 1

variable [ChartedSpace H G] [LieGroup I n G]

/-- If the image of `T` in `G` is a `C^n` immersion, then for the charts
`Subgroup.chartedSpaceOfIsOpenEmbedding` the inclusion of `K` into `G` is a `C^n` immersion:
near `k` it is the immersion of `T` followed by left multiplication by `k`. -/
@[to_additive /-- If the image of `T` in `G` is a `C^n` immersion, then for the charts
`AddSubgroup.chartedSpaceOfIsOpenEmbedding` the inclusion of `K` into `G` is a `C^n` immersion:
near `k` it is the immersion of `T` followed by translation by `k`. -/]
theorem isImmersion_subtypeVal_chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι)
    (hιG : IsImmersion I' I n fun t ↦ (ι t : G)) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    IsImmersion I' I n (Subtype.val : K → G) := by
  let := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
  have := isManifold_chartedSpaceOfIsOpenEmbedding (I' := I') (n := n) hι
  refine IsImmersionOfComplement.isImmersion (F := hιG.complement) fun k ↦ ?_
  -- Near `k`, the inclusion read through the translate `t ↦ k * ι t` is the immersion of `T`
  -- translated by `k`.
  have h := (hιG.isImmersionOfComplement_complement 1).comp_diffeomorph
    (Diffeomorph.constSmul I n (k : G))
  have hk : ⇑(Diffeomorph.constSmul I n (k : G)) ∘ (fun t ↦ (ι t : G)) =
      Subtype.val ∘ fun t ↦ k * ι t := by
    funext t
    simp
  rw [hk, TauCeti.isImmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff
    (isLocalDiffeomorph_mul_apply hι k 1), map_one, mul_one] at h
  exact h

/-- If the image of `T` in `G` is a `C^n` immersion, then for the charts
`Subgroup.chartedSpaceOfIsOpenEmbedding` the inclusion of `K` into `G` is a `C^n` embedding. -/
@[to_additive /-- If the image of `T` in `G` is a `C^n` immersion, then for the charts
`AddSubgroup.chartedSpaceOfIsOpenEmbedding` the inclusion of `K` into `G` is a `C^n`
embedding. -/]
theorem isSmoothEmbedding_subtypeVal_chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι)
    (hιG : IsImmersion I' I n fun t ↦ (ι t : G)) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    IsSmoothEmbedding I' I n (Subtype.val : K → G) := by
  let := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
  exact ⟨isImmersion_subtypeVal_chartedSpaceOfIsOpenEmbedding hι hιG, IsEmbedding.subtypeVal⟩

/-- If the image of `T` in `G` is a `C^n` immersion, then `K` is a `C^n` Lie group for the charts
`Subgroup.chartedSpaceOfIsOpenEmbedding`. -/
@[to_additive /-- If the image of `T` in `G` is a `C^n` immersion, then `K` is a `C^n` additive
Lie group for the charts `AddSubgroup.chartedSpaceOfIsOpenEmbedding`. -/]
theorem lieGroup_chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι)
    (hιG : IsImmersion I' I n fun t ↦ (ι t : G)) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    LieGroup I' n K := by
  let := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
  have := isManifold_chartedSpaceOfIsOpenEmbedding (I' := I') (n := n) hι
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I n
  -- The group operations of `K` are `C^n` because their composites with the inclusion are.
  have hval := isImmersion_subtypeVal_chartedSpaceOfIsOpenEmbedding hι hιG
  exact
    { contMDiff_mul := (ContMDiff.iff_comp_isImmersion hval).2 ⟨continuous_mul,
        (hval.contMDiff.comp contMDiff_fst).mul (hval.contMDiff.comp contMDiff_snd)⟩
      contMDiff_inv := (ContMDiff.iff_comp_isImmersion hval).2
        ⟨continuous_inv, hval.contMDiff.inv⟩ }

end Subgroup
