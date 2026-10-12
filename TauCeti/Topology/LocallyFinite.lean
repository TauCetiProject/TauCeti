/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite

/-!
# Locally finite families reindexed along a projection

A locally finite family of sets stays locally finite when it is reindexed along the first
projection `ι × κ → ι` with `κ` finite (`LocallyFinite.comp_fst`). Together with
`LocallyFinite.subset`, this makes a family indexed by `ι × κ` whose `(i, k)`-th member lies in
the `i`-th member of a locally finite family locally finite.
-/

public section

open Set

namespace LocallyFinite

variable {ι κ X : Type*} [TopologicalSpace X] {f : ι → Set X}

/-- A locally finite family stays locally finite when reindexed along the first projection
`ι × κ → ι`, for `κ` finite. -/
theorem comp_fst [Finite κ] (hf : LocallyFinite f) : LocallyFinite fun p : ι × κ ↦ f p.1 :=
  fun x ↦
    let ⟨U, hU, hfin⟩ := hf x
    ⟨U, hU, (hfin.prod (finite_univ (α := κ))).subset fun _ hp ↦ ⟨hp, mem_univ _⟩⟩

end LocallyFinite
