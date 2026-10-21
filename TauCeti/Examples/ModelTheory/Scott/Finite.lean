/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Scott.Finite

/-!
# Regression examples for the Scott rank of finite structures

These downstream examples check that the orbit-rank bound is sharp for tuples onto the
structure, that empty structures with a nullary relation are covered, and that the level
hypothesis of the embedding theorem cannot be dropped.
-/

namespace TauCeti

open FirstOrder FirstOrder.Language

-- A tuple listing every element of a finite structure has orbit rank zero.
example {L : Language} [L.IsRelational] {M : Type} [L.Structure M] [Finite M] {n : ℕ}
    (a : Fin n → M) (ha : Function.Surjective a) : orbitRank (L := L) a = 0 := by
  simpa [Set.range_eq_univ.mpr ha] using orbitRank_le_natCard_sub_ncard_range (L := L) a

-- An empty structure, even one interpreting a nullary relation, has internal Scott rank one.
example :
    letI L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
    letI : L₀.IsRelational := fun _ => inferInstance
    letI : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
    internalScottRank (L := L₀) Empty = 1 := by
  let L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
  let : L₀.IsRelational := fun _ => inferInstance
  let : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
  refine le_antisymm ?_ one_le_internalScottRank
  simpa using internalScottRank_le_natCard_add_one (L := L₀) Empty

section PureSets

variable [Language.empty.Structure Bool] [Language.empty.Structure Unit]

-- Level zero is too low: the empty tuples of `Bool` and `Unit` agree there, but `Bool` has two
-- elements outside the range of its tuple and does not embed into `Unit`.
example : BFEquiv (L := Language.empty) (0 : Ordinal) 0
      (Fin.elim0 : Fin 0 → Bool) (Fin.elim0 : Fin 0 → Unit) ∧
    IsEmpty (Bool ↪[Language.empty] Unit) := by
  refine ⟨BFEquiv.zero.mpr ((sameAtomicType_iff _ _).mpr
    ⟨fun i => Fin.elim0 i, fun r => isEmptyElim r⟩), ⟨fun f => ?_⟩⟩
  exact Bool.false_ne_true (f.injective (Subsingleton.elim _ _))

end PureSets

end TauCeti
