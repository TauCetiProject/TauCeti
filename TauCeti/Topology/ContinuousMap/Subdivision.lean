/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# Subdividing a continuous-map square under a cover

A continuous square whose image points each have a neighbourhood in a given family of sets (for
example an open cover) admits a finite grid subdivision such that every closed grid cell maps into
one member of the family. This is useful, in particular, for turning a homotopy between paths
into relations among paths lying in members of an open cover.

The grid construction adapts `coveredPartwise_exists` from
`LeanPool.DirectedTopologyLean4.DihomotopyCover.lean` (LeanPool commit
`34ba5ae88508eccb9d88380a7126a595e3796832`, Apache-2.0; copyright (c) 2026 Dominique Lawson,
Henning Basold, and Peter Bruin). The general form follows Mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`.
-/

public section

open Set
open scoped Topology unitInterval

namespace ContinuousMap

/-- A continuous map from the unit square can be subdivided into a finite grid whose cells each
map into one member of any given family of sets that are neighbourhoods of its image points (for
example an open cover of its image). The times are monotone, start at `0`, and are eventually
constant at `1`; `m` is a bound after which they are constant. -/
theorem exists_grid_subdivision {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (K : C(I × I, X)) (U : ι → Set X)
    (hU : ∀ x, ∃ i, U i ∈ 𝓝 (K x)) :
    ∃ (m : ℕ) (t : ℕ → I), t 0 = 0 ∧ Monotone t ∧
      (∀ n, m ≤ n → t n = 1) ∧
      ∀ j k, ∃ i, MapsTo K (Icc (t j) (t (j + 1)) ×ˢ Icc (t k) (t (k + 1))) (U i) := by
  obtain ⟨t, ht0, hmono, ⟨m, htail⟩, hcell⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (fun i => isOpen_interior.preimage K.continuous) fun x _ =>
        mem_iUnion.2 ((hU x).imp fun _ => mem_interior_iff_mem_nhds.2)
  exact ⟨m, t, ht0, hmono, htail, fun j k =>
    (hcell j k).imp fun _ h => Subset.trans h (preimage_mono interior_subset)⟩

end ContinuousMap
