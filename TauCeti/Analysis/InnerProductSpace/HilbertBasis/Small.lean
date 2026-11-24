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
equivalence of `E` with `ℓ²(ι, 𝕜)` for some `ι : Type w`. In particular a complete subspace whose
underlying set is `w`-small is the range of a linear isometry from a Hilbert space in the universe
`w`, `Submodule.exists_linearIsometry_range_eq`.

This realizes a Hilbert space spanned by few vectors, for instance a cyclic subspace of a
representation, as a Hilbert space in a prescribed universe.
-/

public section

universe w v

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

/-- A complete subspace of an inner product space whose underlying set is `w`-small is the range
of a linear isometry from a Hilbert space in the universe `w` (or that of `𝕜`, if larger), namely
`ℓ²` over a Hilbert basis of the subspace. -/
theorem Submodule.exists_linearIsometry_range_eq {𝕜 : Type v} {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (W : Submodule 𝕜 E) [CompleteSpace W]
    [Small.{w} (W : Set E)] :
    ∃ (K : Type (max w v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace 𝕜 K)
      (_ : CompleteSpace K) (V : K →ₗᵢ[𝕜] E), Set.range V = W := by
  -- The subtypes of `W` as a submodule and of `W` as a set are the same type.
  have : Small.{w} W := ‹Small.{w} (W : Set E)›
  obtain ⟨ι, ⟨b⟩⟩ := TauCeti.exists_hilbertBasis_of_small.{w} 𝕜 W
  refine ⟨lp (fun _ : ι => 𝕜) 2, inferInstance, inferInstance, inferInstance,
    W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry, ?_⟩
  simp [Set.range_comp, b.repr.symm.surjective.range_eq]
