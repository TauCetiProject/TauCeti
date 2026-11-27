/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Orientation
import Mathlib.Data.Set.Card

/-!
# Oriented subspaces of a real module

An oriented subspace consists of a subspace of the prescribed rank and an orientation on it.
In finite dimension the sole zero-dimensional subspace has two choices of orientation.
-/

public section

noncomputable section

open Module

namespace TauCeti

/-- A rank-`k` subspace together with a choice of orientation. -/
abbrev OrientedSubspace (E : Type*) [AddCommGroup E] [Module ℝ E] (k : ℕ) :=
  (P : {P : Submodule ℝ E // finrank ℝ P = k}) × Orientation ℝ P.val (Fin k)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- In finite dimension the two oriented zero planes are classified by their signs.
The value `true` stands for the positive orientation and `false` for its opposite. -/
def orientedSubspaceZeroEquiv [Module.Finite ℝ E] : OrientedSubspace E 0 ≃ Bool := by
  let P : {P : Submodule ℝ E // finrank ℝ P = 0} := ⟨⊥, by simp⟩
  let o : Orientation ℝ P.val (Fin 0) := positiveOrientation
  let f : Bool → OrientedSubspace E 0 := fun b ↦ ⟨P, if b then o else -o⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · have h : f true ≠ f false := fun h ↦
      Module.Ray.ne_neg_self o (eq_of_heq (Sigma.mk.inj h).2)
    intro a b hab
    cases a <;> cases b
    · rfl
    · exact (h hab.symm).elim
    · exact (h hab).elim
    · rfl
  · rintro ⟨⟨Q, hQ⟩, o'⟩
    have hQ' : Q = ⊥ := Submodule.finrank_eq_zero.1 hQ
    subst Q
    rcases o'.eq_or_eq_neg_of_isEmpty with ho | ho
    · exact ⟨true, Sigma.ext rfl (heq_of_eq ho.symm)⟩
    · exact ⟨false, Sigma.ext rfl (heq_of_eq ho.symm)⟩

/-- The positive sign corresponds to the canonically oriented zero subspace. -/
@[simp]
theorem orientedSubspaceZeroEquiv_symm_true [Module.Finite ℝ E] :
    (orientedSubspaceZeroEquiv (E := E)).symm true = ⟨⟨⊥, by simp⟩, positiveOrientation⟩ :=
  (rfl)

/-- The negative sign corresponds to the opposite orientation on the zero subspace. -/
@[simp]
theorem orientedSubspaceZeroEquiv_symm_false [Module.Finite ℝ E] :
    (orientedSubspaceZeroEquiv (E := E)).symm false = ⟨⟨⊥, by simp⟩, -positiveOrientation⟩ :=
  (rfl)

/-- In rank zero the oriented planes are the two orientations of the zero subspace. -/
theorem encard_univ_orientedSubspace_zero [Module.Finite ℝ E] :
    (Set.univ : Set (OrientedSubspace E 0)).encard = 2 := by
  rw [Set.encard_univ, ENat.card_congr orientedSubspaceZeroEquiv]
  simp

end TauCeti
