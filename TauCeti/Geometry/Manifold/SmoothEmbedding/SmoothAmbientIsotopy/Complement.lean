/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic

/-!
# The complement of a smooth embedding of a compact manifold

For a smooth embedding `f : M → N` of a compact manifold into a Hausdorff manifold, the image of
`f` is compact, hence closed, so its complement is an open subset of `N`
(`TauCeti.SmoothEmbedding.complement`). As an open subset it carries the charts that Mathlib
restricts to it (`TopologicalSpace.Opens.instChartedSpace`), so it is a manifold of the same
smoothness and over the same model as `N`, and it is boundaryless when `N` is
(`BoundarylessManifold.open`). For a knot `K : S¹ → S³` this is the knot complement `S³ ∖ K`, a
boundaryless `3`-manifold.

A diffeomorphism `e : N ≃ N'` carrying `f` to `g` (`e ∘ f = g`) maps the complement of `f` onto the
complement of `g`, so it restricts to a diffeomorphism of the complements
(`TauCeti.SmoothEmbedding.complementDiffeomorph`). The final diffeomorphism of a diffeotopy
witnessing the smooth ambient isotopy of `f` and `g` is such a map. Hence **smoothly ambient
isotopic embeddings have diffeomorphic complements**
(`TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.nonempty_complementDiffeomorph`). This is the
smooth form of `TauCeti.AmbientIsotopic.nonempty_complementHomeomorph`, which gives only a
homeomorphism and does not ask the complement to be open. It makes the knot complement, as a
smooth manifold up to diffeomorphism, an invariant of the knot type.

## Main definitions

* `TauCeti.SmoothEmbedding.complement`: the complement of the image of a smooth embedding of a
  compact manifold into a Hausdorff manifold, as an open subset.
* `TauCeti.SmoothEmbedding.complementDiffeomorph`: the restriction to the complements of an
  ambient diffeomorphism carrying one embedding to the other.

## Main results

* `TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.nonempty_complementDiffeomorph`: smoothly
  ambient isotopic embeddings have diffeomorphic complements.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for the knot
  complement as an invariant of ambient isotopy.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 1, for knot complements.
-/

public section

noncomputable section

namespace TauCeti

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace SmoothEmbedding

section Complement

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {H'' : Type*} [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 E'' H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
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

/-- A diffeomorphism `e` carrying the embedding `f` to the embedding `g` maps a point into the
complement of `g` exactly when the point lies in the complement of `f`. -/
theorem apply_mem_complement_iff {f : SmoothEmbedding I J n M N}
    {g : SmoothEmbedding I J' n' M N'} (e : N ≃ₘ^k⟮J, J'⟯ N') (h : ∀ x, e (f x) = g x) (y : N) :
    e y ∈ g.complement ↔ y ∈ f.complement := by
  simp only [mem_complement, mem_range, not_exists]
  exact forall_congr' fun x ↦ not_congr
    ⟨fun hx ↦ e.injective ((h x).trans hx), fun hx ↦ (h x).symm.trans (congrArg e hx)⟩

/-- The **diffeomorphism of complements** induced by an ambient diffeomorphism: a diffeomorphism
`e : N ≃ N'` carrying the embedding `f` to the embedding `g` restricts to a diffeomorphism from the
complement of `f` onto the complement of `g`. -/
def complementDiffeomorph {f : SmoothEmbedding I J n M N} {g : SmoothEmbedding I J' n' M N'}
    (e : N ≃ₘ^k⟮J, J'⟯ N') (h : ∀ x, e (f x) = g x) :
    f.complement ≃ₘ^k⟮J, J'⟯ g.complement :=
  e.subtype fun y ↦ (apply_mem_complement_iff e h y).symm

/-- The diffeomorphism of complements is the ambient diffeomorphism. -/
@[simp]
theorem coe_complementDiffeomorph_apply {f : SmoothEmbedding I J n M N}
    {g : SmoothEmbedding I J' n' M N'} (e : N ≃ₘ^k⟮J, J'⟯ N') (h : ∀ x, e (f x) = g x)
    (y : f.complement) :
    (complementDiffeomorph e h y : N') = e y :=
  e.subtype_apply_coe _ y

/-- The inverse of the diffeomorphism of complements is the inverse ambient diffeomorphism. -/
@[simp]
theorem coe_complementDiffeomorph_symm_apply {f : SmoothEmbedding I J n M N}
    {g : SmoothEmbedding I J' n' M N'} (e : N ≃ₘ^k⟮J, J'⟯ N') (h : ∀ x, e (f x) = g x)
    (y : g.complement) :
    ((complementDiffeomorph e h).symm y : N) = e.symm y :=
  e.subtype_symm_apply_coe _ y

end Complement

section AmbientIsotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
  {n : ℕ∞ω} {f g : SmoothEmbedding I J n M N}

/-- **Smoothly ambient isotopic embeddings have diffeomorphic complements.** If a diffeotopy of
the Hausdorff manifold `N` carries the embedding `f` of the compact manifold `M` to `g`, its final
diffeomorphism restricts to a diffeomorphism from `N ∖ f(M)` onto `N ∖ g(M)`. For knots this is the
invariance of the knot complement, as a smooth manifold, under ambient isotopy. -/
theorem SmoothAmbientIsotopic.nonempty_complementDiffeomorph (hfg : SmoothAmbientIsotopic f g) :
    Nonempty (f.complement ≃ₘ^n⟮J, J⟯ g.complement) := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  exact ⟨complementDiffeomorph Φ.final hΦ⟩

end AmbientIsotopy

end SmoothEmbedding

end TauCeti
