/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# Strong continuity of continuous representations

A continuous representation `π` of a topological monoid is *strongly continuous* when every orbit
`g ↦ π g v` is continuous. This is weaker than continuity of `g ↦ π g` into the continuous linear
endomorphisms, which carry the topology of uniform convergence on bounded sets (the operator norm
topology on a normed space): translation by `ℝ` on `L²(ℝ)` is strongly continuous but not
continuous. In finite dimensions the two notions agree by Mathlib's `continuous_clm_apply`,
which is how finite-dimensional pieces of a strongly continuous representation become genuine
continuous representations.

## Main results

* `ContRepresentation.continuous_subrepresentation_apply` and
  `ContRepresentation.continuous_quotient_apply`: restriction to an invariant submodule and descent
  to the quotient by it preserve strong continuity.
-/

public section

namespace ContRepresentation

section StrongContinuity

variable {R G V : Type*} [Ring R] [Monoid G] [TopologicalSpace G] [AddCommGroup V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  {π : ContRepresentation R G V} {W : Submodule R V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- Restricting a strongly continuous representation to an invariant submodule gives a strongly
continuous representation. -/
theorem continuous_subrepresentation_apply (hπ : ∀ v, Continuous fun g ↦ π g v) (w : W) :
    Continuous fun g ↦ subrepresentation π W hW g w := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  simpa only [Function.comp_def, coe_subrepresentation_apply] using hπ w

/-- Descending a strongly continuous representation to the quotient by an invariant submodule
gives a strongly continuous representation. -/
theorem continuous_quotient_apply (hπ : ∀ v, Continuous fun g ↦ π g v) (x : V ⧸ W) :
    Continuous fun g ↦ quotient π W hW g x := by
  obtain ⟨v, rfl⟩ := W.mkQ_surjective x
  simp only [Submodule.mkQ_apply, quotient_apply_mk]
  exact W.mkQL.continuous.comp (hπ v)

end StrongContinuity

end ContRepresentation
