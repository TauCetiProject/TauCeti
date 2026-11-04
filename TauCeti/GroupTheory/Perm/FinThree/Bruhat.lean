/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Coxeter
public import TauCeti.GroupTheory.Coxeter.Bruhat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Bruhat order on the symmetric group on three letters

In `S₃`, two distinct permutations are comparable in Bruhat order precisely when their
Coxeter lengths are distinct. Thus its four levels have sizes `1, 2, 2, 1`, with every
vertex below every vertex of greater length. This explicit order calculation identifies
the maximal chains used in the simplicial model of paths with Bruhat-ordered directions.

The proof uses the subword criterion and the inversion formula for Coxeter length from
`TauCeti.permCoxeterSystem`, rather than introducing a separate finite poset.

Reference: Björner–Brenti, *Combinatorics of Coxeter Groups*, §§1.5 and 2.2.
-/

public section

namespace TauCeti

/-- The six permutations of three letters, ordered as `1, s, t, st, ts, sts`, where
`s = (0 1)` and `t = (1 2)`. This labels the four Bruhat levels of sizes `1, 2, 2, 1`. -/
def symmetricThreeVertex (i : Fin 6) : Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 0 1, Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1,
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1] i

/-- The explicit permutation attached to each Bruhat label. -/
theorem symmetricThreeVertex_def (i : Fin 6) :
    symmetricThreeVertex i =
      ![1, Equiv.swap 0 1, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1,
        Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1] i := (rfl)

/-- The six Bruhat labels enumerate the symmetric group without repetition. -/
theorem bijective_symmetricThreeVertex : Function.Bijective symmetricThreeVertex := by
  decide

private def word (i : Fin 6) : List (Fin 2) :=
  ![[], [0], [1], [0, 1], [1, 0], [0, 1, 0]] i

private theorem wordProd_word (i : Fin 6) :
    (permCoxeterSystem 3).wordProd (word i) = symmetricThreeVertex i := by
  fin_cases i <;>
    simp [word, permCoxeterSystem_wordProd (n := 3), symmetricThreeVertex,
      BraidGroup.transposition_eq_swap_castSucc_succ, mul_assoc]

private theorem isReduced_word (i : Fin 6) :
    (permCoxeterSystem 3).IsReduced (word i) := by
  rw [CoxeterSystem.IsReduced, wordProd_word,
    permCoxeterSystem_length_eq_card_inversion]
  fin_cases i <;> decide

/-- The ranks of the six Bruhat vertices are `0, 1, 1, 2, 2, 3`. -/
@[simp]
theorem length_symmetricThreeVertex (i : Fin 6) :
    (permCoxeterSystem 3).length (symmetricThreeVertex i) = ![0, 1, 1, 2, 2, 3] i := by
  rw [permCoxeterSystem_length_eq_card_inversion]
  fin_cases i <;> decide

private theorem exists_subword (i j : Fin 6)
    (h : (word i).length < (word j).length) :
    ∃ σ ∈ (word j).sublists,
      (permCoxeterSystem 3).wordProd σ = symmetricThreeVertex i := by
  have he : (BraidGroup.transposition (n := 3)) =
      fun k : Fin 2 ↦ (![Equiv.swap 0 1, Equiv.swap 1 2] k : Equiv.Perm (Fin 3)) := by
    funext k
    fin_cases k <;> simp [BraidGroup.transposition_eq_swap_castSucc_succ]
  simp only [permCoxeterSystem_wordProd (n := 3)]
  rw [he]
  fin_cases i <;> fin_cases j <;> norm_num [word] at h <;> decide

end TauCeti

namespace Equiv.Perm

/-- On three letters, every permutation of smaller Coxeter length lies below every
permutation of greater length in Bruhat order. Distinct permutations of equal length
are incomparable. -/
theorem bruhatLE_three_iff (u v : Perm (Fin 3)) :
    (TauCeti.permCoxeterSystem 3).BruhatLE u v ↔ u = v ∨
      (TauCeti.permCoxeterSystem 3).length u < (TauCeti.permCoxeterSystem 3).length v := by
  constructor
  · intro h
    exact eq_or_ne u v |>.imp_right h.length_lt_of_ne
  · rintro (rfl | h)
    · exact (TauCeti.permCoxeterSystem 3).bruhatLE_refl _
    obtain ⟨i, rfl⟩ := TauCeti.bijective_symmetricThreeVertex.surjective u
    obtain ⟨j, rfl⟩ := TauCeti.bijective_symmetricThreeVertex.surjective v
    rw [← TauCeti.wordProd_word j,
      (TauCeti.permCoxeterSystem 3).bruhatLE_iff_exists_sublist_wordProd_eq
        (TauCeti.isReduced_word j)]
    obtain ⟨σ, hσ, he⟩ := TauCeti.exists_subword i j (by
      simpa only [← TauCeti.wordProd_word, (TauCeti.isReduced_word _).eq] using h)
    exact ⟨σ, List.mem_sublists.mp hσ, he⟩

end Equiv.Perm
