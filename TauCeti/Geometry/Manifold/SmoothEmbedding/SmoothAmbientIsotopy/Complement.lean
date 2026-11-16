/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Complement
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic

/-!
# Smoothly ambient isotopic embeddings have diffeomorphic complements

The complement of a smooth embedding `f : M → N` of a compact manifold into a Hausdorff manifold
is the open subset `TauCeti.SmoothEmbedding.complement f` of `N`, a manifold over the model of `N`
that is boundaryless when `N` is (`ModelWithCorners.BoundarylessManifold.open`). For a knot
`K : S¹ → S³` it is the knot complement `S³ ∖ K`, a boundaryless `3`-manifold.

This file shows that **smoothly ambient isotopic embeddings have diffeomorphic complements**
(`TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.nonempty_complementDiffeomorph`). This is the
smooth form of `TauCeti.AmbientIsotopic.nonempty_complementHomeomorph`, which gives only a
homeomorphism and does not ask the complement to be open. It makes the knot complement, as a
smooth manifold up to diffeomorphism, an invariant of the knot type.

## Main results

* `TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.nonempty_complementDiffeomorph`: smoothly
  ambient isotopic embeddings have diffeomorphic complements.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for the knot
  complement as an invariant of ambient isotopy.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 1, for knot complements.
-/

public section

namespace TauCeti

open Set
open scoped _root_.Manifold ContDiff

namespace SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
  {n : ℕ∞ω} {f g : SmoothEmbedding I J n M N}

/-- **Smoothly ambient isotopic embeddings have diffeomorphic complements.** If the embeddings
`f` and `g` of the compact manifold `M` into the Hausdorff manifold `N` are smoothly ambient
isotopic, then their open complements `N ∖ f(M)` and `N ∖ g(M)` are `C^n`-diffeomorphic. For
knots this is the invariance of the knot complement, as a smooth manifold, under ambient isotopy.
For an explicit diffeomorphism, apply `TauCeti.SmoothEmbedding.complementDiffeomorph` to the
final diffeomorphism of a witnessing diffeotopy. -/
theorem SmoothAmbientIsotopic.nonempty_complementDiffeomorph (hfg : SmoothAmbientIsotopic f g) :
    Nonempty (f.complement ≃ₘ^n⟮J, J⟯ g.complement) := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  exact ⟨complementDiffeomorph Φ.final (by rw [← range_comp, Function.comp_def, funext hΦ])⟩

end SmoothEmbedding

end TauCeti
