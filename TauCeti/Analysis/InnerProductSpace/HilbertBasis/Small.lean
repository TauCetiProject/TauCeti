/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Topology.Sequences.Small

/-!
# Hilbert bases of small Hilbert spaces

If the underlying type of a Hilbert space `E` is `w`-small, then so is every Hilbert basis index
set, being a subset of `E`. Reindexing along `equivShrink` gives a Hilbert basis of `E` indexed
by a type in the universe `w`, `exists_hilbertBasis_of_small`, and hence a linear isometric
equivalence of `E` with `ℓ²(ι, 𝕜)` for some `ι : Type w`. Consequently, the closed linear span of
any `w`-small subset of a Hilbert space is the range of a linear isometry from `ℓ²(ι, 𝕜)` with
`ι : Type w` (`exists_linearIsometry_range_eq_topologicalClosure_span`).

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

/-- The closed linear span of a `w`-small subset `s` of a Hilbert space `E` (over a `w`-small
scalar field `𝕜`) is the range of a linear isometry `lp (fun _ : ι => 𝕜) 2 →ₗᵢ[𝕜] E` for some
index type `ι : Type w`. -/
theorem exists_linearIsometry_range_eq_topologicalClosure_span (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [Small.{w} 𝕜]
    (s : Set E) [Small.{w} s] :
    ∃ (ι : Type w) (V : lp (fun _ : ι => 𝕜) 2 →ₗᵢ[𝕜] E),
      Set.range V = ((Submodule.span 𝕜 s).topologicalClosure : Set E) := by
  let W : Submodule 𝕜 E := (Submodule.span 𝕜 s).topologicalClosure
  have : Small.{w} (Submodule.span 𝕜 s) := Submodule.small_span.{w} s
  have hW_small : Small.{w} (W : Set E) := by
    rw [Submodule.topologicalClosure_coe]
    exact Set.small_closure.{w} _
  have : Small.{w} W := hW_small
  obtain ⟨ι, ⟨b⟩⟩ := exists_hilbertBasis_of_small.{w} 𝕜 W
  refine ⟨ι, W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry, ?_⟩
  simp [W, Set.range_comp, b.repr.symm.surjective.range_eq]

end TauCeti
