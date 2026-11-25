/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Constructions

/-!
# The trivialization of a trivial bundle belongs to its atlas

The atlas of the trivial bundle `B × F` consists of its single trivialization
`Bundle.Trivial.trivialization B F`. Mathlib registers membership in the atlas only for the
preferred trivializations `trivializationAt F (Trivial B F) b`, which instance search does not
unfold to `Bundle.Trivial.trivialization B F`. This file registers the membership of
`Bundle.Trivial.trivialization B F` itself as an instance, so that constructions requiring
`MemTrivializationAtlas`, such as the trivializations of Hom bundles out of a trivial bundle, apply
to it directly.
-/

public section

namespace Bundle.Trivial

/-- The trivialization of a trivial bundle belongs to its atlas. -/
instance memTrivializationAtlas_trivialization (B F : Type*) [TopologicalSpace B]
    [TopologicalSpace F] : MemTrivializationAtlas (trivialization B F) :=
  ⟨Set.mem_singleton _⟩

end Bundle.Trivial
