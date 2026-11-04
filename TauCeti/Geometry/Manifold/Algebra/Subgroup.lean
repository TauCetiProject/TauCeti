/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sigma

/-!
# Subgroups of Lie groups with an open embedded Lie subgroup

Let `K` be a subgroup of a `C^n` Lie group `G`, and let `ι : T →* K` be a group homomorphism out
of a `C^n` Lie group `T` which is an open embedding for the subspace topology of `K`, and whose
composite with the inclusion `K → G` is a `C^n` immersion. Thus `K` contains the image of `T` as an
open subgroup, and `T` is immersed in `G`. Then `K` is an embedded Lie subgroup of `G`, modelled on
the model of `T`: the translates `k * ι(T)` of the image of `T` cover `K`, and their charts fit
together because they differ by translations of `T`.

The charts are pushed forward along the map `(Σ _ : K, T) → K`, `⟨k, t⟩ ↦ k * ι t`, which is a
surjective local homeomorphism whose fibres are related by left translations of `T`. With these
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
  Mathematics 218, Springer, 2013, Chapter 7 (Lie subgroups) and Chapter 21 (charts pushed forward
  along local homeomorphisms).
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

variable (K : Subgroup G) {ι : T →* K}

/-- The map `⟨k, t⟩ ↦ k * ι t`, whose sheets are the translates of the image of `ι`. -/
@[to_additive /-- The map `⟨k, t⟩ ↦ k + ι t`, whose sheets are the translates of the image of
`ι`. -/]
private def sheetMap (ι : T →* K) (x : Σ _ : K, T) : K :=
  x.1 * ι x.2

@[to_additive]
private theorem sheetMap_mk (ι : T →* K) (k : K) (t : T) : sheetMap K ι ⟨k, t⟩ = k * ι t :=
  rfl

@[to_additive]
private theorem sheetMap_mk_one (ι : T →* K) (k : K) : sheetMap K ι ⟨k, 1⟩ = k := by
  simp [sheetMap_mk]

variable [TopologicalSpace G] [TopologicalSpace T]

@[to_additive]
private theorem isLocalHomeomorph_sheetMap [ContinuousMul G] (hι : IsOpenEmbedding ι) :
    IsLocalHomeomorph (sheetMap K ι) := by
  refine IsLocalHomeomorph.mk _ fun ⟨k, t⟩ ↦ ?_
  have : Nonempty T := ⟨t⟩
  have : ContinuousMul K := K.toSubmonoid.continuousMul
  -- On the sheet through `⟨k, t⟩`, the map is the open embedding `s ↦ k * ι s`.
  have hk : IsOpenEmbedding fun s : T ↦ k * ι s := (Homeomorph.mulLeft k).isOpenEmbedding.comp hι
  have hσ := IsOpenEmbedding.sigmaMk (σ := fun _ : K ↦ T) (i := k)
  refine ⟨(hσ.toOpenPartialHomeomorph _).symm.trans (hk.toOpenPartialHomeomorph _), ?_, ?_⟩
  · simp
  · rintro _ ⟨⟨s, -, rfl⟩, -⟩
    simp [sheetMap_mk, hσ.toOpenPartialHomeomorph_left_inv]

variable [ChartedSpace H' T]

omit [TopologicalSpace G] in
/-- Two points of `Σ _ : K, T` with the same image are related by a left translation of `T`, which
moves one sheet onto the other. -/
@[to_additive /-- Two points of `Σ _ : K, T` with the same image are related by a translation of
`T`, which moves one sheet onto the other. -/]
private theorem exists_contMDiffAt_comp_sheetMap [LieGroup I' n T] (ι : T →* K) (z w : Σ _ : K, T)
    (h : sheetMap K ι z = sheetMap K ι w) :
    ∃ φ : (Σ _ : K, T) → Σ _ : K, T,
      ContMDiffAt I' I' n φ z ∧ φ z = w ∧ sheetMap K ι ∘ φ =ᶠ[𝓝 z] sheetMap K ι := by
  obtain ⟨k, t⟩ := z
  obtain ⟨k', s⟩ := w
  refine ⟨fun y ↦ ⟨k', s * t⁻¹ * y.2⟩, ?_, by simp, ?_⟩
  · refine TauCeti.contMDiffAt_sigma_iff.2 ?_
    exact TauCeti.contMDiffAt_sigmaMk_iff.2 (contMDiff_mul_left (I := I') (a := s * t⁻¹) t)
  · filter_upwards [IsOpenEmbedding.sigmaMk.isOpen_range.mem_nhds ⟨t, rfl⟩]
    rintro _ ⟨y, rfl⟩
    simp only [sheetMap_mk] at h
    simp only [Function.comp_apply, sheetMap_mk, map_mul, map_inv, ← mul_assoc, ← h]
    group

variable [ContinuousMul G] (ι)

/-- The charts on a subgroup `K` containing the image of an open embedding `ι : T →* K` of a
charted group: the chart at `k` is the chart of `T` at the identity, read on the translate
`k * ι(T)` of the image of `ι`. -/
@[to_additive (attr := instance_reducible) /-- The charts on an additive subgroup `K` containing
the image of an open embedding `ι : T →+ K` of a charted additive group: the chart at `k` is the
chart of `T` at zero, read on the translate `k + ι(T)` of the image of `ι`. -/]
noncomputable def chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι) : ChartedSpace H' K :=
  (isLocalHomeomorph_sheetMap K hι).chartedSpaceOfRightInverse
    (g := fun k ↦ ⟨k, 1⟩) (sheetMap_mk_one K ι)

variable {K ι} [LieGroup I' n T]

/-- The charts `Subgroup.chartedSpaceOfIsOpenEmbedding` form a `C^n` manifold: their transition
maps are translations of `T`. -/
@[to_additive /-- The charts `AddSubgroup.chartedSpaceOfIsOpenEmbedding` form a `C^n` manifold:
their transition maps are translations of `T`. -/]
theorem isManifold_chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    IsManifold I' n K :=
  (isLocalHomeomorph_sheetMap K hι).isManifold_chartedSpaceOfRightInverse _
    (exists_contMDiffAt_comp_sheetMap K ι)

@[to_additive]
private theorem isLocalDiffeomorph_sheetMap (hι : IsOpenEmbedding ι) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    IsLocalDiffeomorph I' I' n (sheetMap K ι) :=
  (isLocalHomeomorph_sheetMap K hι).isLocalDiffeomorph_chartedSpaceOfRightInverse _
    (exists_contMDiffAt_comp_sheetMap K ι)

/-- For the charts `Subgroup.chartedSpaceOfIsOpenEmbedding`, the open embedding `ι : T →* K` is a
`C^n` local diffeomorphism. -/
@[to_additive /-- For the charts `AddSubgroup.chartedSpaceOfIsOpenEmbedding`, the open embedding
`ι : T →+ K` is a `C^n` local diffeomorphism. -/]
theorem isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding (hι : IsOpenEmbedding ι) :
    letI := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
    IsLocalDiffeomorph I' I' n ι := by
  let := chartedSpaceOfIsOpenEmbedding (H' := H') K ι hι
  have h : ⇑ι = sheetMap K ι ∘ Sigma.mk 1 := funext fun t ↦ by simp [sheetMap_mk]
  rw [h]
  exact fun t ↦ (TauCeti.isLocalDiffeomorph_sigmaMk 1 t).comp I' K
    (isLocalDiffeomorph_sheetMap hι _)

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
  -- On the sheet through `⟨k, 1⟩`, the inclusion read through `sheetMap` is the immersion of
  -- `T` translated by `k`.
  have h := (hιG.isImmersionOfComplement_complement 1).comp_diffeomorph
    (Diffeomorph.constSmul I n (k : G))
  have hk : ⇑(Diffeomorph.constSmul I n (k : G)) ∘ (fun t ↦ (ι t : G)) =
      (Subtype.val ∘ sheetMap K ι) ∘ Sigma.mk k := by
    funext t
    simp [sheetMap_mk]
  rw [hk, TauCeti.isImmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff
      (TauCeti.isLocalDiffeomorph_sigmaMk k 1),
    TauCeti.isImmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff
      (isLocalDiffeomorph_sheetMap hι _), sheetMap_mk_one] at h
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
