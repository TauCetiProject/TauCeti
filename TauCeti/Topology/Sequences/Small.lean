/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Small.Set
public import Mathlib.Topology.Sequences

/-!
# Closures of small sets in Fréchet–Urysohn spaces

In a Hausdorff Fréchet–Urysohn space, for instance a metric space, every point of the closure of
a set `s` is the limit of a sequence in `s`, and that limit is unique. So the closure of `s` is
the image of the type of convergent sequences in `s` under the limit map, and it is `w`-small
whenever `s` is, `Set.small_closure`.

This bounds the size of the closed subspace of a Hilbert space spanned by a small set of vectors,
which is how a representation on a large Hilbert space is reduced to subrepresentations on
Hilbert spaces in a fixed universe.
-/

public section

universe w

open Filter Topology

namespace Set

/-- In a Hausdorff Fréchet–Urysohn space, the closure of a `w`-small set is `w`-small. -/
theorem small_closure {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X] [T2Space X]
    (s : Set X) [Small.{w} s] : Small.{w} (closure s) := by
  let lim : {u : ℕ → s // ∃ x, Tendsto (fun n => (u n : X)) atTop (𝓝 x)} → X :=
    fun u => have : Nonempty X := ⟨u.1 0⟩; limUnder atTop fun n => (u.1 n : X)
  refine small_subset (s := Set.range lim) fun x hx => ?_
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 hx
  exact ⟨⟨fun n => ⟨u n, hu n⟩, x, hux⟩, hux.limUnder_eq⟩

end Set
