/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Transporting inducing maps along homeomorphisms

A map is inducing exactly when its conjugate by homeomorphisms of the source and target is
inducing. The product form transports a family of maps into the factors of a product along
homeomorphisms of the source and of every factor.

## Main results

* `Homeomorph.isInducing_iff_of_homeomorph`: maps intertwined by homeomorphisms of the source and
  target are inducing simultaneously.
* `Homeomorph.isInducing_pi_iff_of_homeomorph`: the same for maps into a product, with one
  homeomorphism for every factor.
-/

public section

namespace Homeomorph

open Topology

/-- Maps intertwined by homeomorphisms of the source and of the target induce the topology
simultaneously. -/
theorem isInducing_iff_of_homeomorph {X X' Y Y' : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y'] (e : X ≃ₜ X')
    (e' : Y ≃ₜ Y') {r : X → Y} {r' : X' → Y'} (h : ∀ x, e' (r x) = r' (e x)) :
    IsInducing r ↔ IsInducing r' := by
  have hcomm : e' ∘ r = r' ∘ e := funext h
  rw [← e'.isInducing.of_comp_iff, hcomm]
  refine ⟨fun h' ↦ ?_, fun h' ↦ h'.comp e.isInducing⟩
  simpa [Function.comp_def] using h'.comp e.symm.isInducing

/-- Restriction maps that commute with homeomorphisms of the source and of every target induce
the topology simultaneously. -/
theorem isInducing_pi_iff_of_homeomorph {X X' ι : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] {Y Y' : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    [∀ i, TopologicalSpace (Y' i)] (e : X ≃ₜ X') (e' : ∀ i, Y i ≃ₜ Y' i)
    {r : X → ∀ i, Y i} {r' : X' → ∀ i, Y' i} (h : ∀ x i, e' i (r x i) = r' (e x) i) :
    IsInducing r ↔ IsInducing r' :=
  e.isInducing_iff_of_homeomorph (Homeomorph.piCongrRight e') fun x ↦ funext (h x)

end Homeomorph
