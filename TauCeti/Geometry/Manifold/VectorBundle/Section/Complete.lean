/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Manifold

/-!
# Completeness of the compact derivative topology on bundle sections

For a smooth bundle over a boundaryless manifold with locally compact model and complete
model fibre, the native finite-order and smooth section spaces are complete in the compact
derivative frame topology. Use `ContMDiffSection.frameUniformSpace` for its compatible
additive uniformity. No compactness or countability assumption is needed for completeness.

The coefficient map into the product of native weak Whitney map spaces has closed image,
characterized by the actual bundle transition equations. Completeness of those coefficient
spaces therefore gives completeness of sections. Together with the locally convex structure
and the countable seminorms in `Section.CountableSeminorms`, this supplies the Fréchet
structure whenever countable covering frames and chart exhaustions are available.

## References

* R. Hamilton, *The inverse function theorem of Nash and Moser*, Part I, Example 1.1.5,
  for the Fréchet space of smooth sections.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The additive uniformity compatible with the existing compact derivative frame topology.
It is supplied explicitly because the frame system is a parameter. -/
@[instance_reducible]
def frameUniformSpace : UniformSpace Cₛ^n⟮I; F, V⟯ :=
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  IsTopologicalAddGroup.rightUniformSpace _

/-- The frame uniformity retains the original compact derivative topology on sections. -/
@[simp]
theorem frameUniformSpace_toTopologicalSpace :
    (frameUniformSpace (I := I) (n := n) e U hU).toTopologicalSpace =
      frameTopology (I := I) (n := n) e U hU :=
  (rfl)

/-- The frame uniformity makes sections a uniform additive group. -/
theorem isUniformAddGroup_frameUniformSpace :
    let _ := frameUniformSpace (I := I) (n := n) e U hU
    IsUniformAddGroup Cₛ^n⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  let _ := frameUniformSpace (I := I) (n := n) e U hU
  exact isUniformAddGroup_of_addCommGroup

variable [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E] [I.Boundaryless]
  [CompleteSpace F] [hn : ENat.LEInfty n]

/-- Finite-order and smooth sections of a bundle with complete model fibre form a complete
space for the compact derivative topology of any covering smooth frame system. -/
theorem completeSpace_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameUniformSpace (I := I) (n := n) e U hU
    CompleteSpace Cₛ^n⟮I; F, V⟯ := by
  let _ := frameUniformSpace (I := I) (n := n) e U hU
  let _ := isUniformAddGroup_frameUniformSpace (I := I) (n := n) e U hU
  let _ (i : ι) := IsTopologicalAddGroup.rightUniformSpace C^n⟮I, U i; 𝓘(𝕜, F), F⟯
  let _ (i : ι) : IsUniformAddGroup C^n⟮I, U i; 𝓘(𝕜, F), F⟯ := isUniformAddGroup_of_addCommGroup
  have (i : ι) : CompleteSpace C^n⟮I, U i; 𝓘(𝕜, F), F⟯ := by
    obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1
      (ne_top_of_le_ne_top (by simp : (∞ : ℕ∞ω) ≠ ⊤) hn.out)
    exact ContMDiffMap.completeSpace_manifoldWeakWhitney
  have hj := AddMonoidHom.isUniformInducing_of_isInducing
    (f := (TauCeti.Manifold.sectionFrameCoordinates (I := I) (n := n) e U hU).toAddMonoidHom)
    (isInducing_sectionFrameCoordinates (I := I) (n := n) e U hU)
  exact (completeSpace_iff_isComplete_range hj).2
    (isClosedEmbedding_sectionFrameCoordinates (I := I) (n := n)
      e U hU hcover).isClosed_range.isComplete

end ContMDiffSection
