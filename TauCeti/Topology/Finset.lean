/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.DiscreteSubset

/-!
# Finite sets and filters

This file records two elementary ways in which the complement of a finite set is large: it is a
punctured neighbourhood of every point in a `T1Space`, and it is a neighbourhood of infinity in
every bornological space.

## Main results

* `Finset.compl_mem_nhdsNE` — the complement of a finset is a punctured neighbourhood of
  every point.
* `Finset.compl_mem_cobounded` — the complement of a finset belongs to the cobounded
  filter.
-/

public section

namespace Finset

open Bornology Filter Set Topology

/-- The complement of a finite set is a punctured neighbourhood of every point in a `T1Space`. -/
theorem compl_mem_nhdsNE {α : Type*} [TopologicalSpace α] [T1Space α]
    (s : Finset α) (x : α) : (↑s : Set α)ᶜ ∈ 𝓝[≠] x :=
  mem_codiscrete_iff_forall_mem_nhdsNE.mp (compl_finite_mem_codiscreteWithin s.finite_toSet) x

/-- The complement of a finite set belongs to the cobounded filter. -/
theorem compl_mem_cobounded {α : Type*} [Bornology α]
    (s : Finset α) : (↑s : Set α)ᶜ ∈ cobounded α :=
  isBounded_def.mp s.finite_toSet.isBounded

end Finset

