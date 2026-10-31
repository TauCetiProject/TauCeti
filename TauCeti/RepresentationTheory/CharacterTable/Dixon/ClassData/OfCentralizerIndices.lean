/-
Copyright (c) 2026 Robert Joseph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.GroupTheory.ConjugacyCoverage
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Class data from centralizer indices

Construct native class data from a pairwise nonconjugate list whose centralizer indices sum to
the finite group order. The original list supplies the class numbering without filtering or
reordering.
-/

public section

namespace TauCeti.ClassData

variable {G : Type*} [Group G] [Finite G]

/-- Class data from an exhaustive sum of actual centralizer indices, retaining the given list. -/
@[expose] def ofCentralizerIndices (l : List G)
    (hp : l.Pairwise fun x y => ¬ IsConj x y)
    (hm : (l.map fun x => (Subgroup.centralizer ({x} : Set G)).index).sum = Nat.card G) :
    ClassData G where
  reps := l
  pairwise_not_isConj := hp
  exists_isConj := exists_mem_isConj_of_sum_centralizer_index_eq_card l hp hm

/-- The centralizer-index constructor preserves the original representative list. -/
@[simp] theorem reps_ofCentralizerIndices (l : List G)
    (hp : l.Pairwise fun x y => ¬ IsConj x y)
    (hm : (l.map fun x => (Subgroup.centralizer ({x} : Set G)).index).sum = Nat.card G) :
    (ofCentralizerIndices l hp hm).reps = l := rfl

end TauCeti.ClassData
