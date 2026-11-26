/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.Bundle
public import TauCeti.Topology.VectorBundle.GrassmannBundle.Restrict

/-!
# Restriction of a varifold to an open subset

Let `E → B` be a finite-rank real vector bundle with continuous fibre norm over a Hausdorff base,
for instance the tangent bundle of a Riemannian manifold, and let `W ⊆ B` be open. The Grassmann
bundle `G_k(E|_W)` of the restriction `E|_W = ContinuousMap.subtypeVal W *ᵖ E` is the open part
`π⁻¹(W)` of `G_k(E)` (`TauCeti.grassmannBundle.isOpenEmbedding_inclusion`). The **restriction** of
a varifold `V` on `B` to `W` is the varifold `V'` on `W` obtained by pulling `V` back along this
inclusion (`TauCeti.grassmannBundle.restrictOpens`), so `V'(S) = V(S)` for every Borel set `S` of
planes over `W` (Simon, *Lectures on Geometric Measure Theory*, §38; Allard, *On the first
variation of a varifold*, Section 3).

* Pushed back to `G_k(E)`, the restriction is `V⌞W = V.restrict (π⁻¹(W))`
  (`TauCeti.grassmannBundle.map_inclusion_restrictOpens`).
* The restriction commutes with sums, nonnegative multiples and `⌞A`, and of a varifold
  (a measure finite on compact sets) it is a varifold
  (`TauCeti.grassmannBundle.isFiniteMeasureOnCompacts_restrictOpens`).
* The weight of the restriction is `‖V‖` restricted to `W`
  (`TauCeti.grassmannBundle.weight_restrictOpens`), so `spt ‖V'‖ = spt ‖V‖ ∩ W`, the support being
  taken in `W` (`TauCeti.grassmannBundle.support_weight_restrictOpens`).
* Over a Lindelöf base, a varifold is determined by its restrictions to the sets of an open cover
  (`TauCeti.grassmannBundle.ext_of_restrictOpens`).

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. 95 (1972), Section 3.
* L. Simon, *Lectures on Geometric Measure Theory*, §38.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Bundle Topology
open scoped ENNReal

/-- The support of a measure pulled back along an open embedding is the preimage of the support. -/
theorem MeasureTheory.Measure.support_comap_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : IsOpenEmbedding f) (hf' : MeasurableEmbedding f) (μ : Measure Y) :
    (μ.comap f).support = f ⁻¹' μ.support := by
  ext x
  rw [mem_preimage, Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
  constructor
  · intro h U hU
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 (hf.continuous.continuousAt.preimage_mem_nhds hU)
    have := h V (hV.mem_nhds hxV)
    rw [hf'.comap_apply] at this
    exact this.trans_le (measure_mono ((image_mono hVU).trans (image_preimage_subset f U)))
  · intro h U hU
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
    have := h (f '' V) ((hf.isOpenMap V hV).mem_nhds (mem_image_of_mem f hxV))
    rw [← hf'.comap_apply] at this
    exact this.trans_le (measure_mono hVU)

namespace TauCeti.grassmannBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {k : ℕ} (W : Set B)
  (V V₁ V₂ : Measure (grassmannBundle F E k))

/-- The **restriction** of a varifold `V` on `B` to `W ⊆ B`: the measure on the Grassmann bundle
`G_k(E|_W)` of `E|_W = ContinuousMap.subtypeVal W *ᵖ E` pulled back along the inclusion
`G_k(E|_W) → G_k(E)`. For open `W` it gives every Borel set of planes over `W` its `V`-measure
(`TauCeti.grassmannBundle.restrictOpens_apply`). -/
def restrictOpens : Measure (grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k) :=
  V.comap (inclusion F E k W)

variable [T2Space B] [FiniteDimensional ℝ F] [ContinuousFiberNorm F E] {W}

/-- For open `W`, the inclusion `G_k(E|_W) → G_k(E)` is a measurable embedding. -/
theorem measurableEmbedding_inclusion (hW : IsOpen W) :
    MeasurableEmbedding (inclusion F E k W) :=
  (isOpenEmbedding_inclusion W hW).measurableEmbedding

/-- The restriction gives a Borel set of planes over `W` its `V`-measure. -/
theorem restrictOpens_apply (hW : IsOpen W)
    (S : Set (grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k)) :
    restrictOpens W V S = V (inclusion F E k W '' S) :=
  (measurableEmbedding_inclusion hW).comap_apply V S

/-- Pushed back to `G_k(E)`, the restriction of `V` to `W` is `V⌞W`, the part of `V` over `W`. -/
theorem map_inclusion_restrictOpens (hW : IsOpen W) :
    (restrictOpens W V).map (inclusion F E k W) = V.restrict (proj ⁻¹' W) := by
  rw [restrictOpens, (measurableEmbedding_inclusion hW).map_comap, range_inclusion]

/-- The restriction of the zero varifold is zero. -/
@[simp]
theorem restrictOpens_zero (hW : IsOpen W) :
    restrictOpens W (0 : Measure (grassmannBundle F E k)) = 0 := by
  ext S
  rw [restrictOpens_apply _ hW, FunLike.coe_zero, Pi.zero_apply, FunLike.coe_zero, Pi.zero_apply]

/-- Restriction to `W` is additive. -/
theorem restrictOpens_add (hW : IsOpen W) :
    restrictOpens W (V₁ + V₂) = restrictOpens W V₁ + restrictOpens W V₂ := by
  ext S
  simp only [FunLike.coe_add, Pi.add_apply, restrictOpens_apply _ hW]

/-- Restriction to `W` commutes with multiplication by nonnegative scalars. -/
theorem restrictOpens_smul (hW : IsOpen W) (c : ℝ≥0∞) :
    restrictOpens W (c • V) = c • restrictOpens W V := by
  ext S
  simp only [FunLike.coe_smul, Pi.smul_apply, restrictOpens_apply _ hW]

/-- Restriction to `W` commutes with `⌞A`: `(V⌞A)|_W = (V|_W)⌞(A ∩ W)`. -/
theorem restrictOpens_restrict (hW : IsOpen W) (A : Set B) :
    restrictOpens W (V.restrict (proj ⁻¹' A)) =
      (restrictOpens W V).restrict (proj ⁻¹' (Subtype.val ⁻¹' A)) := by
  rw [restrictOpens, (measurableEmbedding_inclusion hW).comap_restrict,
    inclusion_preimage_preimage_proj]
  rfl

/-- **The restriction of a varifold is a varifold**: it is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_restrictOpens (hW : IsOpen W) [IsFiniteMeasureOnCompacts V] :
    IsFiniteMeasureOnCompacts (restrictOpens W V) where
  lt_top_of_isCompact K hK := by
    rw [restrictOpens_apply _ hW]
    exact (hK.image (continuous_inclusion W)).measure_lt_top

/-- Over a Lindelöf base, **a varifold is determined by its restrictions** to the sets of an open
cover. -/
theorem ext_of_restrictOpens [LindelofSpace B] {ι : Type*} {U : ι → Set B}
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (h : ∀ i, restrictOpens (U i) V₁ = restrictOpens (U i) V₂) : V₁ = V₂ :=
  ext_of_restrict_preimage hU hcover fun i ↦ by
    rw [← map_inclusion_restrictOpens _ (hU i), ← map_inclusion_restrictOpens _ (hU i), h i]

variable [MeasurableSpace B] [BorelSpace B]

/-- The weight of the restriction of `V` to `W` is the weight `‖V‖` restricted to `W`, as a
measure on `W`. -/
theorem weight_restrictOpens (hW : IsOpen W) :
    weight (restrictOpens W V) = (weight V).comap Subtype.val := by
  ext A hA
  have hA' : MeasurableSet (Subtype.val '' A : Set B) :=
    (MeasurableEmbedding.subtypeVal hW.measurableSet).measurableSet_image.2 hA
  rw [weight_apply hA, restrictOpens_apply _ hW, image_inclusion_preimage_proj,
    (MeasurableEmbedding.subtypeVal hW.measurableSet).comap_apply, weight_apply hA']

/-- The support of the weight of the restriction of `V` to `W`, a closed subset of `W`, is
`spt ‖V‖ ∩ W`. -/
theorem support_weight_restrictOpens (hW : IsOpen W) :
    (weight (restrictOpens W V)).support = Subtype.val ⁻¹' (weight V).support := by
  rw [weight_restrictOpens _ hW, Measure.support_comap_of_isOpenEmbedding
    hW.isOpenEmbedding_subtypeVal (MeasurableEmbedding.subtypeVal hW.measurableSet)]

end TauCeti.grassmannBundle
