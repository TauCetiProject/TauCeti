/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GrassmannBundle.Map
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian
import TauCeti.Topology.FiberBundle.Separation

/-!
# The Grassmann bundle over a subset of the base

Let `E → B` be a real vector bundle whose fibres are real inner product spaces, and let `W ⊆ B`.
The restriction of `E` to `W` is the pullback `E|_W = ContinuousMap.subtypeVal W *ᵖ E`, whose fibre
over `x ∈ W` is `E x` with its inner product. Its Grassmann bundle `G_k(E|_W)` includes into
`G_k(E)` by `(x, P) ↦ (x, P)` (`TauCeti.grassmannBundle.inclusion`), the map of Grassmann bundles
induced by the inclusion `W → B` covered by the identities of the fibres.

* The inclusion is continuous and injective, and its image is the part `π⁻¹(W)` of `G_k(E)` over
  `W` (`TauCeti.grassmannBundle.range_inclusion`).
* For a finite-rank bundle with continuous fibre norm over a Hausdorff base and an open `W`, it is
  an open embedding (`TauCeti.grassmannBundle.isOpenEmbedding_inclusion`). Corestricted to
  `π⁻¹(W)` it is a continuous bijection whose composite with the projection `π⁻¹(W) → W` is the
  proper projection of `G_k(E|_W)`, so it is proper, hence closed, hence a homeomorphism onto
  `π⁻¹(W)`.

This is the carrier of the restriction of a varifold on `B` to an open subset
(`TauCeti.grassmannBundle.restrictOpens`).

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Proceedings of the Centre for Mathematical
  Analysis, Australian National University 3, 1983, §38.
-/

public section

noncomputable section

open Bundle Filter Set Topology

namespace TauCeti

namespace grassmannBundle

section Map

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  {k : ℕ} (W : Set B)

variable (F E k) in
/-- The inclusion `G_k(E|_W) → G_k(E)`, `(x, P) ↦ (x, P)`, of the Grassmann bundle of the
restriction `ContinuousMap.subtypeVal W *ᵖ E` of `E` to `W`: the map of Grassmann bundles induced
by the inclusion of `W` covered by the identities of the fibres. -/
def inclusion :
    grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k → grassmannBundle F E k :=
  map (ContinuousMap.subtypeVal W) fun x ↦ LinearIsometryEquiv.refl ℝ (E x)

/-- The inclusion keeps the plane and includes the base point. -/
@[simp]
theorem coe_inclusion_apply (p : grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k) :
    (inclusion F E k W p).val = ⟨(p.val.proj : B), p.val.snd⟩ := by
  refine (coe_map_apply (ContinuousMap.subtypeVal W) (fun x ↦ LinearIsometryEquiv.refl ℝ (E x))
    p).trans ?_
  congr 1

/-- The inclusion covers the inclusion of `W`. -/
@[simp]
theorem proj_inclusion (p : grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k) :
    proj (inclusion F E k W p) = ((proj p : W) : B) :=
  proj_map (ContinuousMap.subtypeVal W) (fun x ↦ LinearIsometryEquiv.refl ℝ (E x)) p

/-- The inclusion `G_k(E|_W) → G_k(E)` is injective. -/
theorem inclusion_injective : Function.Injective (inclusion F E k W) :=
  map_injective _ _ Subtype.val_injective

/-- The image of the inclusion is the part `π⁻¹(W)` of `G_k(E)` over `W`. -/
theorem range_inclusion : range (inclusion F E k W) = proj ⁻¹' W := by
  refine Subset.antisymm (range_subset_iff.2 fun p ↦ ?_) fun q hq ↦ ?_
  · rw [mem_preimage, proj_inclusion]
    exact (proj p).property
  obtain ⟨⟨x, P⟩, hP⟩ := q
  rw [mem_preimage, proj_apply] at hq
  -- The fibre of the pullback over `⟨x, hq⟩` is `E x` by definition.
  refine ⟨⟨⟨⟨x, hq⟩, P⟩, mem_grassmannBundle.2
    (show P ∈ Euclidean.grassmannian ℝ (E x) k from mem_grassmannBundle.1 hP)⟩, Subtype.ext ?_⟩
  rw [coe_inclusion_apply]

/-- The preimage under the inclusion of the planes over `A ⊆ B` are the planes over `A ∩ W`. -/
theorem preimage_inclusion_preimage_proj (A : Set B) :
    inclusion F E k W ⁻¹' (proj ⁻¹' A) = proj ⁻¹' (Subtype.val ⁻¹' A) := by
  ext p
  simp only [mem_preimage, proj_inclusion]

/-- The image under the inclusion of the planes over `A ⊆ W` are the planes over the image of
`A` in `B`. -/
theorem image_inclusion_preimage_proj (A : Set W) :
    inclusion F E k W '' (proj ⁻¹' A) = proj ⁻¹' (Subtype.val '' A) := by
  refine Subset.antisymm (image_subset_iff.2 fun p hp ↦ ?_) fun q hq ↦ ?_
  · simp only [mem_preimage, proj_inclusion]
    exact mem_image_of_mem _ hp
  obtain ⟨x, hxA, hx⟩ := hq
  obtain ⟨p, rfl⟩ := (range_inclusion W).ge (show proj q ∈ W from hx ▸ x.property)
  refine ⟨p, ?_, rfl⟩
  rw [proj_inclusion] at hx
  rw [mem_preimage, ← Subtype.val_injective hx]
  exact hxA

end Map

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {k : ℕ} (W : Set B)

/-- **The inclusion of Grassmann bundles is continuous.** -/
theorem continuous_inclusion : Continuous (inclusion F E k W) := by
  refine continuous_map (ContinuousMap.subtypeVal W).continuous fun x₀ ↦ ?_
  -- In coordinates the identity of the fibres is the identity of `F` near `x₀`.
  refine (continuousAt_const (y := ContinuousLinearMap.id ℝ F)).congr ?_
  have hmem : ∀ᶠ x : W in 𝓝 x₀, (x : B) ∈ (trivializationAt F E (x₀ : B)).baseSet :=
    continuous_subtypeVal.continuousAt.eventually_mem
      ((trivializationAt F E (x₀ : B)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E (x₀ : B)))
  filter_upwards [hmem] with x hx
  ext v
  -- The trivialization of the pullback at `x₀` is the pullback of the trivialization of `E` at
  -- `x₀`, whose base set is the preimage of the original one, so `hx` gives membership in it.
  have hx' : x ∈ (trivializationAt F (ContinuousMap.subtypeVal W *ᵖ E) x₀).baseSet := hx
  -- `hx` with the base points written as values of `ContinuousMap.subtypeVal W`, as in the goal.
  have hx'' : ContinuousMap.subtypeVal W x ∈
      (trivializationAt F E (ContinuousMap.subtypeVal W x₀)).baseSet := hx
  rw [ContinuousLinearMap.inCoordinates_eq hx' hx'']
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivialization.continuousLinearEquivAt_pullback]
  exact (((trivializationAt F E (x₀ : B)).continuousLinearEquivAt ℝ _ hx).apply_symm_apply v).symm

variable [T2Space B] [FiniteDimensional ℝ F] [ContinuousFiberNorm F E]

/-- **The inclusion `G_k(E|_W) → G_k(E)` is an open embedding** for an open `W`, when `E` has
finite rank and continuous fibre norm and `B` is Hausdorff. -/
theorem isOpenEmbedding_inclusion (hW : IsOpen W) : IsOpenEmbedding (inclusion F E k W) := by
  have hWo : IsOpen (proj ⁻¹' W : Set (grassmannBundle F E k)) := hW.preimage continuous_proj
  -- The inclusion, corestricted to the planes over `W`.
  let c : grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k → proj ⁻¹' W :=
    codRestrict _ _ fun p ↦ (range_inclusion W).le (mem_range_self p)
  have hc : Continuous c := (continuous_inclusion W).codRestrict _
  -- The projection of the planes over `W` to `W`.
  let q : (proj ⁻¹' W : Set (grassmannBundle F E k)) → W :=
    fun p ↦ ⟨proj p.val, p.property⟩
  have hq : Continuous q := (continuous_proj.comp continuous_subtypeVal).subtype_mk _
  have hqc : q ∘ c = proj := funext fun p ↦ Subtype.ext (proj_inclusion W p)
  have hp : IsProperMap c := isProperMap_of_comp_of_t2 hc hq
    (hqc ▸ isProperMap_proj F (ContinuousMap.subtypeVal W *ᵖ E) k)
  have hbij : Function.Bijective c := by
    refine ⟨fun p p' h ↦ inclusion_injective W (congrArg Subtype.val h), fun p ↦ ?_⟩
    obtain ⟨p', hp'⟩ := (range_inclusion W).ge p.property
    exact ⟨p', Subtype.ext hp'⟩
  let h := (Equiv.ofBijective c hbij).toHomeomorphOfContinuousClosed hc hp.isClosedMap
  exact hWo.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding

end grassmannBundle

end TauCeti
