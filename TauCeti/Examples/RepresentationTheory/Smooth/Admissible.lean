/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Admissible

/-!
# Examples of admissible representations

The zero representation is admissible, and so is a trivial representation on a finitely generated
module. For a compact group, here the trivial group, the trivial action on `ℚ^(ℕ)` is smooth but
not admissible: its invariants under the whole group are the whole infinite-dimensional module.
-/

public section

open Representation

namespace TauCeti

example {A G : Type*} [CommRing A] [Group G] [TopologicalSpace G] (ρ : Representation A G PUnit) :
    IsAdmissible ρ :=
  inferInstance

example {A G : Type*} [CommRing A] [Group G] [TopologicalSpace G] :
    IsAdmissible (trivial A G (Fin 3 → A)) :=
  inferInstance

/-- The trivial action of the trivial group on `ℚ^(ℕ)` is smooth but not admissible. -/
example : IsSmooth (trivial ℚ Unit (ℕ →₀ ℚ)) ∧ ¬IsAdmissible (trivial ℚ Unit (ℕ →₀ ℚ)) := by
  refine ⟨inferInstance, fun h ↦ ?_⟩
  rw [isAdmissible_trivial_iff ⟨⊤, isCompact_univ⟩] at h
  have := Module.Finite.finite_basis (Finsupp.basisSingleOne (R := ℚ) (ι := ℕ))
  exact not_finite ℕ

end TauCeti
