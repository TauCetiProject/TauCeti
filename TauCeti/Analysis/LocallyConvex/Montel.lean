/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Montel

/-!
# Closed subspaces, products and scalar extensions of Montel spaces

A Montel space (`MontelSpace`) is a topological vector space in which every closed von Neumann
bounded set is compact. This file shows that the Heine–Borel property passes to closed linear
subspaces, to arbitrary products and to extensions of the scalar field.

* `MontelSpace.of_isClosedEmbedding`: if a continuous linear map `f : E →L[𝕜] F` into a Montel
  space is a closed embedding, then `E` is a Montel space. For instance a space of smooth sections
  of a vector bundle sits in this way inside a product of spaces of smooth coefficient functions.
* `MontelSpace.pi`: a product of Hausdorff topological vector spaces that are Montel spaces is a
  Montel space. A bounded set lies in the product of the closures of its projections, which are
  compact, so Tychonoff's theorem applies.
* `MontelSpace.of_isScalarTower`: a Montel space over `𝕜` is a Montel space over every normed
  field extension of `𝕜` acting compatibly, such as a complex space that is a real Montel space.

## References

* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Chapter 34.
-/

public section

open Set Bornology

namespace MontelSpace

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A space with a continuous linear closed embedding into a Montel space is a Montel space. -/
theorem of_isClosedEmbedding [MontelSpace 𝕜 F] (f : E →L[𝕜] F) (hf : Topology.IsClosedEmbedding f) :
    MontelSpace 𝕜 E where
  heine_borel s hs hb := by
    have hc : IsCompact (f '' s) :=
      isCompact_of_isClosed_of_isVonNBounded 𝕜 (hf.isClosedMap s hs) (hb.image f)
    simpa only [preimage_image_eq s hf.injective] using hf.isCompact_preimage hc

/-- A product of Hausdorff topological vector spaces that are Montel spaces is a Montel space. -/
instance pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, ContinuousConstSMul 𝕜 (E i)] [∀ i, T1Space (E i)] [∀ i, MontelSpace 𝕜 (E i)] :
    MontelSpace 𝕜 (∀ i, E i) where
  heine_borel s hs hb := by
    have hc (i : ι) : IsCompact (closure (Function.eval i '' s)) :=
      isCompact_of_isClosed_of_isVonNBounded 𝕜 isClosed_closure
        (hb.image (ContinuousLinearMap.proj (R := 𝕜) (φ := E) i)).closure
    exact (isCompact_univ_pi hc).of_isClosed_subset hs fun x hx i _ ↦
      subset_closure (mem_image_of_mem _ hx)

/-- A Montel space over `𝕜` is a Montel space over every normed field extension `𝕜'` whose action
is compatible with that of `𝕜`, since a set bounded for `𝕜'` is bounded for `𝕜`. For instance a
complex vector space that is a real Montel space is a complex Montel space. -/
theorem of_isScalarTower (𝕜' : Type*) [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' E]
    [IsScalarTower 𝕜 𝕜' E] [MontelSpace 𝕜 E] : MontelSpace 𝕜' E where
  heine_borel _ hs hb := isCompact_of_isClosed_of_isVonNBounded 𝕜 hs (hb.restrict_scalars 𝕜)

end MontelSpace
