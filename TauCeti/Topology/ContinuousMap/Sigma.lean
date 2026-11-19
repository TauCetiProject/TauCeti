/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Maps.Basic

/-!
# Maps out of and onto the summands of a disjoint union

For a point `z` of the summand `Z i` of a disjoint union `Σ j, Z j`, the continuous map
`ContinuousMap.sigmaRetraction i z` is the identity on `Z i` and sends every other summand to
`z`. It is a retraction of the inclusion `ContinuousMap.sigmaMk i`
(`ContinuousMap.sigmaRetraction_comp_sigmaMk`).

Closed embeddings `f i : Z i → A` with pairwise disjoint, locally finite ranges glue to a closed
embedding `ContinuousMap.sigma f` of the disjoint union (`ContinuousMap.isClosedEmbedding_sigma`):
a closed subset of `Σ j, Z j` is sent to a locally finite union of closed subsets of `A`. Without
local finiteness this fails: the points `1 / (n + 1)` of `ℝ`, one in each summand of
`Σ n : ℕ, Unit`, have a closed union whose image is not closed.

## Main definitions

* `ContinuousMap.sigmaRetraction i z`: the retraction of `Σ j, Z j` onto `Z i` collapsing the
  other summands to `z`.

## Main results

* `ContinuousMap.isClosedEmbedding_sigma`: closed embeddings with pairwise disjoint, locally
  finite ranges glue to a closed embedding of the disjoint union.
-/

public section

namespace ContinuousMap

variable {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]

open scoped Classical in
/-- The retraction of a disjoint union onto its summand `Z i`, sending every other summand to the
point `z`. -/
noncomputable def sigmaRetraction (i : ι) (z : Z i) : C((Σ j, Z j), Z i) where
  toFun p := if h : p.1 = i then h ▸ p.2 else z
  continuous_toFun := continuous_sigma fun j ↦ by
    by_cases h : j = i
    · subst h
      simpa using continuous_id'
    · simpa [h] using continuous_const

@[simp]
theorem sigmaRetraction_sigmaMk (i : ι) (z w : Z i) : sigmaRetraction i z ⟨i, w⟩ = w := by
  simp [sigmaRetraction]

@[simp]
theorem sigmaRetraction_apply_of_ne {i j : ι} (z : Z i) (w : Z j) (h : j ≠ i) :
    sigmaRetraction i z ⟨j, w⟩ = z := by
  simp [sigmaRetraction, h]

@[simp]
theorem sigmaRetraction_comp_sigmaMk (i : ι) (z : Z i) :
    (sigmaRetraction i z).comp (sigmaMk i) = ContinuousMap.id (Z i) := by
  ext w
  exact sigmaRetraction_sigmaMk i z w

open Function Set Topology in
/-- **Closed embeddings with pairwise disjoint, locally finite ranges glue to a closed embedding
of the disjoint union.** -/
theorem isClosedEmbedding_sigma {A : Type*} [TopologicalSpace A] {f : ∀ i, C(Z i, A)}
    (hf : ∀ i, IsClosedEmbedding (f i)) (hd : Pairwise (Disjoint on fun i ↦ range (f i)))
    (hlf : LocallyFinite fun i ↦ range (f i)) :
    IsClosedEmbedding (ContinuousMap.sigma f) := by
  refine .of_continuous_injective_isClosedMap (ContinuousMap.sigma f).continuous ?_ fun s hs ↦ ?_
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    obtain rfl | hij := eq_or_ne i j
    · exact congrArg (Sigma.mk i) ((hf i).injective h)
    · exact ((hd hij).ne_of_mem ⟨x, rfl⟩ ⟨y, rfl⟩ h).elim
  · have : ContinuousMap.sigma f '' s = ⋃ i, f i '' (Sigma.mk i ⁻¹' s) := by
      ext z
      simp [Sigma.exists]
    rw [this]
    exact (hlf.subset fun i ↦ image_subset_range _ _).isClosed_iUnion fun i ↦
      (hf i).isClosedMap _ (hs.preimage continuous_sigmaMk)

end ContinuousMap
