/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The inverse of the homeomorphism onto the range of an embedding

An embedding `f : X → Y` is a homeomorphism `Topology.IsEmbedding.toHomeomorph` onto its range.
Applying `f` to the inverse of this homeomorphism at a point of the range returns that point
(`Topology.IsEmbedding.apply_toHomeomorph_symm`), complementing Mathlib's
`Topology.IsEmbedding.toHomeomorph_symm_apply`, which evaluates the inverse at points `f x`.
-/

public section

namespace Topology.IsEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An embedding `f` undoes the inverse of its homeomorphism onto its range. -/
theorem apply_toHomeomorph_symm {f : X → Y} (hf : IsEmbedding f) (y : Set.range f) :
    f (hf.toHomeomorph.symm y) = y :=
  Equiv.apply_ofInjective_symm hf.injective y

end Topology.IsEmbedding
