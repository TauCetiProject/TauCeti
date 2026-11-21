/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Uniform bounds for representations of compact groups

A representation `π` of a compact group on a seminormed space whose operator-valued map
`g ↦ π g` is continuous for the operator norm has uniformly bounded action operators
(`ContRepresentation.exists_norm_le_of_compactSpace`).
-/

public section

namespace ContRepresentation

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Monoid G] [TopologicalSpace G]
  [CompactSpace G] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The action operators of a representation of a compact group that is continuous for the
operator norm are uniformly bounded. -/
theorem exists_norm_le_of_compactSpace (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ∃ C, 0 ≤ C ∧ ∀ g, ‖π g‖ ≤ C := by
  obtain ⟨C, hC⟩ := (HasCompactSupport.of_compactSpace ⇑π).exists_bound_of_continuous hπ
  exact ⟨C, (norm_nonneg _).trans (hC 1), hC⟩

end ContRepresentation
