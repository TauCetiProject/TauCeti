/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Detecting nondiscrete subsets by convergent families

A family converging to a point of a subset while eventually staying in that subset prevents
discreteness if it is frequently different from the limit. This criterion uses only the target
topology and applies, for example, to the range of a homomorphism whose nonidentity values
accumulate at the identity.
-/

public section

open Topology

namespace Filter

/-- A subset containing the limit of an eventually contained family is nondiscrete if the family
is frequently different from the limit. -/
theorem Tendsto.not_isDiscrete {X Y : Type*} [TopologicalSpace Y] {f : X → Y} {l : Filter X}
    {a : Y} {s : Set Y} (hf : Tendsto f l (𝓝 a)) (ha : a ∈ s)
    (hs : ∀ᶠ x in l, f x ∈ s) (hne : ∃ᶠ x in l, f x ≠ a) : ¬ IsDiscrete s := by
  intro hD
  have heq := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf hs
  rw [nhdsWithin_of_mem_discrete hD ha, tendsto_pure] at heq
  exact hne (heq.mono fun _ h hne ↦ hne h)

end Filter
