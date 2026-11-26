/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.Bundle
public import TauCeti.MeasureTheory.Measure.Support
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

/-- The restriction to `W` is the pullback of `V` along the inclusion `G_k(E|_W) → G_k(E)`. -/
theorem restrictOpens_def : restrictOpens W V = V.comap (inclusion F E k W) :=
  (rfl)

/-- The restriction of the zero varifold is zero. -/
@[simp]
theorem restrictOpens_zero : restrictOpens W (0 : Measure (grassmannBundle F E k)) = 0 :=
  Measure.comap_zero _

/-- Restriction to `W` commutes with multiplication by nonnegative scalars. -/
@[simp]
theorem restrictOpens_smul (c : ℝ≥0∞) : restrictOpens W (c • V) = c • restrictOpens W V :=
  Measure.comap_smul c

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
  rw [restrictOpens_def, (measurableEmbedding_inclusion hW).map_comap, range_inclusion]

/-- Restriction to `W` is additive. -/
@[simp]
theorem restrictOpens_add (hW : IsOpen W) :
    restrictOpens W (V₁ + V₂) = restrictOpens W V₁ + restrictOpens W V₂ :=
  (measurableEmbedding_inclusion hW).comap_add V₁ V₂

/-- Restriction to `W` commutes with `⌞A`: `(V⌞A)|_W = (V|_W)⌞(A ∩ W)`. -/
@[simp]
theorem restrictOpens_restrict (hW : IsOpen W) (A : Set B) :
    restrictOpens W (V.restrict (proj ⁻¹' A)) =
      (restrictOpens W V).restrict (proj ⁻¹' (Subtype.val ⁻¹' A)) := by
  rw [restrictOpens_def, restrictOpens_def, (measurableEmbedding_inclusion hW).comap_restrict,
    preimage_inclusion_preimage_proj]

/-- **The restriction of a varifold is a varifold**: it is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_restrictOpens (hW : IsOpen W) [IsFiniteMeasureOnCompacts V] :
    IsFiniteMeasureOnCompacts (restrictOpens W V) :=
  IsFiniteMeasureOnCompacts.comap' V (continuous_inclusion W) (measurableEmbedding_inclusion hW)

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
@[simp]
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
