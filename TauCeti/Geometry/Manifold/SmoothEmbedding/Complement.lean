/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# The complement of a smooth embedding of a compact manifold

For a smooth embedding `f : M → N` of a compact manifold into a Hausdorff manifold, the image of
`f` is compact, hence closed, so its complement is an open subset of `N`
(`TauCeti.SmoothEmbedding.complement`). As an open subset it carries the charts that Mathlib
restricts to it (`TopologicalSpace.Opens.instChartedSpace`), so it is a manifold of the same
smoothness and over the same model as `N`, and it is boundaryless when `N` is
(`ModelWithCorners.BoundarylessManifold.open`). For a knot `K : S¹ → S³` this is the knot
complement `S³ ∖ K`, a boundaryless `3`-manifold. The complement depends only on the image, so
reparametrising the source does not change it
(`TauCeti.SmoothEmbedding.complement_compDiffeomorph`).

A diffeomorphism `e : N ≃ N'` mapping the image of `f` onto the image of `g` maps the complement
of `f` onto the complement of `g`, so it restricts to a diffeomorphism of the complements
(`TauCeti.SmoothEmbedding.complementDiffeomorph`). The embeddings may have different compact
sources, so this covers reparametrisations and orientation reversals as well as ambient motions.

## Main definitions

* `TauCeti.SmoothEmbedding.complement`: the complement of the image of a smooth embedding of a
  compact manifold into a Hausdorff manifold, as an open subset.
* `TauCeti.SmoothEmbedding.complementDiffeomorph`: the restriction to the complements of an
  ambient diffeomorphism mapping one image onto the other.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for the knot
  complement as an invariant of ambient isotopy.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 1, for knot complements.
-/

public section

noncomputable section

namespace TauCeti

open Set TopologicalSpace
open scoped _root_.Manifold ContDiff

namespace SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {H'' : Type*} [TopologicalSpace H''] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 F G}
  {J : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 E'' H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace G M'] [CompactSpace M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N'] [T2Space N']
  {n n' k : ℕ∞ω}

/-- The **complement** of a smooth embedding `f : M → N` of a compact manifold into a Hausdorff
manifold: the open subset `N ∖ f(M)` of the target. Its image is compact, hence closed, which makes
the complement open. -/
def complement (f : SmoothEmbedding I J n M N) : Opens N :=
  ⟨(range f)ᶜ, (isCompact_range (map_continuous f)).isClosed.isOpen_compl⟩

/-- The complement of a smooth embedding, as a set, is the complement of its image. -/
@[simp]
theorem coe_complement (f : SmoothEmbedding I J n M N) : (f.complement : Set N) = (range f)ᶜ :=
  (rfl)

/-- A point lies in the complement of a smooth embedding exactly when it is not in its image. -/
@[simp]
theorem mem_complement {f : SmoothEmbedding I J n M N} {y : N} :
    y ∈ f.complement ↔ y ∉ range f :=
  Iff.rfl

/-- Reparametrising the source of a smooth embedding by a diffeomorphism does not change its
complement. -/
@[simp]
theorem complement_compDiffeomorph {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H M₀]
    [CompactSpace M₀] [IsManifold I n M₀] (f : SmoothEmbedding I J n M N)
    (e : M₀ ≃ₘ^n⟮I, I⟯ M) : (f.compDiffeomorph e).complement = f.complement :=
  Opens.ext (by simp [range_comp])

/-- A diffeomorphism `e` mapping the image of `f` onto the image of `g` maps a point into the
complement of `g` exactly when the point lies in the complement of `f`. -/
theorem apply_mem_complement_iff {f : SmoothEmbedding I J n M N}
    {g : SmoothEmbedding I' J' n' M' N'} (e : N ≃ₘ^k⟮J, J'⟯ N') (h : e '' range f = range g)
    (y : N) : e y ∈ g.complement ↔ y ∈ f.complement := by
  rw [mem_complement, mem_complement, ← h]
  exact not_congr (e.injective.mem_set_image (s := range f))

/-- The **diffeomorphism of complements** induced by an ambient diffeomorphism: a diffeomorphism
`e : N ≃ N'` mapping the image of `f` onto the image of `g` restricts to a diffeomorphism from the
complement of `f` onto the complement of `g`. -/
def complementDiffeomorph {f : SmoothEmbedding I J n M N} {g : SmoothEmbedding I' J' n' M' N'}
    (e : N ≃ₘ^k⟮J, J'⟯ N') (h : e '' range f = range g) :
    f.complement ≃ₘ^k⟮J, J'⟯ g.complement :=
  e.subtype fun y ↦ (apply_mem_complement_iff e h y).symm

/-- The diffeomorphism of complements is the ambient diffeomorphism. -/
@[simp]
theorem coe_complementDiffeomorph_apply {f : SmoothEmbedding I J n M N}
    {g : SmoothEmbedding I' J' n' M' N'} (e : N ≃ₘ^k⟮J, J'⟯ N') (h : e '' range f = range g)
    (y : f.complement) :
    (complementDiffeomorph e h y : N') = e y :=
  e.subtype_apply_coe _ y

/-- The inverse of the diffeomorphism of complements is the inverse ambient diffeomorphism. -/
@[simp]
theorem coe_complementDiffeomorph_symm_apply {f : SmoothEmbedding I J n M N}
    {g : SmoothEmbedding I' J' n' M' N'} (e : N ≃ₘ^k⟮J, J'⟯ N') (h : e '' range f = range g)
    (y : g.complement) :
    ((complementDiffeomorph e h).symm y : N) = e.symm y :=
  e.subtype_symm_apply_coe _ y

end SmoothEmbedding

end TauCeti
