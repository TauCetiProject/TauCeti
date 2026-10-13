/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Basic properties of open partial homeomorphisms

This file collects elementary topological facts about open partial homeomorphisms that are not
in Mathlib.

## Main statements

* `OpenPartialHomeomorph.isClosed_image_symm_of_isCompact`: the inverse of an open partial
  homeomorphism into a Hausdorff space maps compact subsets of its target to closed sets.
-/

public section

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)

/-- The image under `e.symm` of a compact subset of `e.target` is closed when the source space
is Hausdorff. -/
lemma isClosed_image_symm_of_isCompact [T2Space X] {t : Set Y} (ht : IsCompact t)
    (hte : t ⊆ e.target) : IsClosed (e.symm '' t) :=
  (ht.image_of_continuousOn (e.continuousOn_symm.mono hte)).isClosed

end OpenPartialHomeomorph
