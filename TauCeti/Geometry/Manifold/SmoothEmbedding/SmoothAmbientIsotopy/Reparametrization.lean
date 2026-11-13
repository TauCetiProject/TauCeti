/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Extension

/-!
# Reparametrizing an embedding along a diffeotopy of its source

Moving the source of an embedding `f : M → N` by a diffeotopy `Ψ` of `M` moves `f` through the
embeddings `x ↦ f (Ψ (t, x))`, a smooth isotopy from `f` to its reparametrization
`f ∘ Ψ.final` (`TauCeti.SmoothEmbedding.smoothIsotopic_compDiffeomorph_final`). For a compact
boundaryless source and a finite-dimensional boundaryless target the isotopy extension theorem
turns this isotopy into an ambient one
(`TauCeti.SmoothEmbedding.smoothAmbientIsotopic_compDiffeomorph_final`): reparametrizing an
embedding by a diffeomorphism of its source diffeotopic to the identity does not change its smooth
ambient-isotopy class. For knots this says that rotating the parameter circle of a knot is
realized by an ambient isotopy.

## Main results

* `TauCeti.SmoothEmbedding.smoothIsotopic_compDiffeomorph_final`: an embedding is smoothly
  isotopic to its reparametrization by the final map of a diffeotopy of the source.
* `TauCeti.SmoothEmbedding.smoothAmbientIsotopic_compDiffeomorph_final`: for a compact source, it
  is smoothly ambient isotopic to that reparametrization.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 8, §1 (isotopy extension).
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

/-- **Reparametrization along a diffeotopy is an isotopy.** An embedding `f` is smoothly isotopic
to its reparametrization by the final map of a diffeotopy `Ψ` of the source, through the
embeddings `x ↦ f (Ψ (t, x))`. -/
theorem smoothIsotopic_compDiffeomorph_final {n : ℕ∞ω} [IsManifold I n M]
    (f : SmoothEmbedding I J n M N) (Ψ : Diffeotopy I n M) :
    SmoothIsotopic f.toContMDiffMap (f.compDiffeomorph Ψ.final).toContMDiffMap :=
  smoothIsotopic_def.2 ⟨{
    toContMDiffMap := ⟨fun p => f (Ψ p), f.contMDiff.comp Ψ.contMDiff⟩
    map_zero_left := fun x => by simp
    map_one_left := fun x => by simp
    isSmoothEmbedding := fun t => by
      simpa [Function.comp_def] using (f.compDiffeomorph (Ψ.timeSlice t)).isSmoothEmbedding }⟩

/-- **Reparametrization along a diffeotopy is an ambient isotopy.** A smooth embedding of a compact
boundaryless manifold into a finite-dimensional boundaryless manifold is smoothly ambient isotopic
to its reparametrization by the final map of any diffeotopy of the source. -/
theorem smoothAmbientIsotopic_compDiffeomorph_final [FiniteDimensional ℝ E'] [I.Boundaryless]
    [J.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [IsManifold J ∞ N] [T2Space N]
    [SigmaCompactSpace N] (f : SmoothEmbedding I J ∞ M N) (Ψ : Diffeotopy I ∞ M) :
    f.SmoothAmbientIsotopic (f.compDiffeomorph Ψ.final) :=
  smoothAmbientIsotopic_iff_toContMDiffMap.2
    (smoothIsotopic_compDiffeomorph_final f Ψ).smoothAmbientIsotopic

end TauCeti.SmoothEmbedding
