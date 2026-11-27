/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions

/-!
# Cofinite topology under pullbacks

Pulling back the cofinite topology `TopologicalSpace.cofinite` along an injective map recovers the
cofinite topology on the domain (`Function.Injective.induced_cofinite`).

## Main results

* `Function.Injective.induced_cofinite`: an injective map induces `TopologicalSpace.cofinite` from
  `TopologicalSpace.cofinite`.
-/

public section

open Set Topology

/-- Pulling back the cofinite topology along an injective map yields the cofinite topology. -/
theorem Function.Injective.induced_cofinite {α β : Type*} {f : α → β}
    (hf : Function.Injective f) :
    TopologicalSpace.induced f TopologicalSpace.cofinite = TopologicalSpace.cofinite := by
  ext U
  let : TopologicalSpace β := TopologicalSpace.cofinite
  rw [isOpen_induced_iff]
  simp only [isOpen_mk]
  constructor
  · rintro ⟨V, hV, rfl⟩ ⟨x, hx⟩
    rw [← preimage_compl]
    exact (hV ⟨f x, hx⟩).preimage hf.injOn
  · intro hU
    by_cases hne : U.Nonempty
    · refine ⟨(f '' Uᶜ)ᶜ, fun _ ↦ ?_, ?_⟩
      · simpa only [compl_compl] using (hU hne).image f
      · rw [preimage_compl, hf.preimage_image, compl_compl]
    · rw [not_nonempty_iff_eq_empty.mp hne]
      exact ⟨∅, by simp, preimage_empty⟩
