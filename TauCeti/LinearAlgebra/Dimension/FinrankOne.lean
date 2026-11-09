/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Spanning vectors and linear relations in a one-dimensional space

In a one-dimensional vector space over a division ring, a single vector spans exactly when it is
nonzero (`TauCeti.span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one`), and any two vectors
satisfy a nontrivial linear relation (`TauCeti.exists_smul_add_smul_eq_zero_of_finrank_eq_one`).
-/

public section

open Module (finrank)

namespace TauCeti

/-- In a one-dimensional vector space, a singleton spans exactly when its vector is nonzero. -/
theorem span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (hV : finrank K V = 1) (v : V) :
    Submodule.span K {v} = ⊤ ↔ v ≠ 0 := by
  refine ⟨?_, fun hv ↦ (finrank_eq_one_iff_of_ne_zero v hv).mp hV⟩
  rintro h rfl
  have := Module.nontrivial_of_finrank_eq_succ hV
  simp at h

/-- Any two vectors of a one-dimensional vector space satisfy a nontrivial linear relation. -/
theorem exists_smul_add_smul_eq_zero_of_finrank_eq_one {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (hV : finrank K V = 1) (x y : V) :
    ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧ a • x + b • y = 0 := by
  have : Module.Finite K V := Module.finite_of_finrank_eq_succ hV
  have hxy : ¬LinearIndependent K ![x, y] := fun h ↦ by
    simpa [hV] using h.fintype_card_le_finrank
  simp only [LinearIndependent.pair_iff, not_forall, not_and_or] at hxy
  obtain ⟨a, b, h, hab⟩ := hxy
  exact ⟨a, b, hab, h⟩

end TauCeti
