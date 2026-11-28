/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Orientation
import Mathlib.Data.Set.Card

/-!
# Oriented subspaces over an ordered field

An oriented subspace consists of a subspace of the prescribed rank and an orientation on it.
The sole zero-dimensional subspace has two choices of orientation.
-/

public section

noncomputable section

open Cardinal Module

namespace TauCeti

variable (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A rank-`k` subspace together with a choice of orientation. -/
abbrev OrientedSubspace (E : Type*) [AddCommGroup E] [Module R E] (k : ℕ) :=
  (P : {P : Submodule R E // Module.rank R P = (k : Cardinal)}) × Orientation R P.val (Fin k)

variable {R} {E : Type*} [AddCommGroup E] [Module R E]

/-- The two oriented zero planes are classified by their signs.
The value `true` stands for the positive orientation and `false` for its opposite. -/
def orientedSubspaceZeroEquiv : OrientedSubspace R E 0 ≃ Bool := by
  let P : {P : Submodule R E // Module.rank R P = (0 : Cardinal)} := ⟨⊥, by simp⟩
  let o : Orientation R P.val (Fin 0) := positiveOrientation
  let f : Bool → OrientedSubspace R E 0 := fun b ↦ ⟨P, if b then o else -o⟩
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
    have hQ' : Q = ⊥ := Submodule.rank_eq_zero.1 (by simpa using hQ)
    subst Q
    rcases o'.eq_or_eq_neg_of_isEmpty with ho | ho
    · exact ⟨true, Sigma.ext rfl (heq_of_eq ho.symm)⟩
    · exact ⟨false, Sigma.ext rfl (heq_of_eq ho.symm)⟩

/-- The positive sign corresponds to the canonically oriented zero subspace. -/
@[simp]
theorem orientedSubspaceZeroEquiv_symm_true :
    (orientedSubspaceZeroEquiv (R := R) (E := E)).symm true = ⟨⟨⊥, by simp⟩, positiveOrientation⟩ :=
  (rfl)

/-- The negative sign corresponds to the opposite orientation on the zero subspace. -/
@[simp]
theorem orientedSubspaceZeroEquiv_symm_false :
    (orientedSubspaceZeroEquiv (R := R) (E := E)).symm false =
      ⟨⟨⊥, by simp⟩, -positiveOrientation⟩ :=
  (rfl)

/-- In rank zero the oriented planes are the two orientations of the zero subspace. -/
theorem encard_univ_orientedSubspace_zero :
    (Set.univ : Set (OrientedSubspace R E 0)).encard = 2 := by
  rw [Set.encard_univ, ENat.card_congr orientedSubspaceZeroEquiv]
  simp

end TauCeti
