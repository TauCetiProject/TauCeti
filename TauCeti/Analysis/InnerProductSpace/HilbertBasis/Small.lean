/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hilbert bases of small Hilbert spaces

If the underlying type of a Hilbert space `E` is `w`-small, then so is every Hilbert basis index
set, being a subset of `E`. Reindexing along `equivShrink` gives a Hilbert basis of `E` indexed
by a type in the universe `w`, `exists_hilbertBasis_of_small`, and hence a linear isometric
equivalence of `E` with `ℓ²(ι, 𝕜)` for some `ι : Type w`.

This realizes a Hilbert space spanned by few vectors, for instance a cyclic subspace of a
representation, as a Hilbert space in a prescribed universe.
-/

public section

universe w

namespace TauCeti

/-- A Hilbert space whose underlying type is `w`-small has a Hilbert basis indexed by a type in the
universe `w`. -/
theorem exists_hilbertBasis_of_small (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [Small.{w} E] :
    ∃ ι : Type w, Nonempty (HilbertBasis ι 𝕜 E) := by
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 E
  let e := equivShrink.{w} s
  refine ⟨Shrink.{w} s, ⟨.mk (b.orthonormal.comp _ e.symm.injective) ?_⟩⟩
  rw [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
  exact b.dense_span.ge

end TauCeti
