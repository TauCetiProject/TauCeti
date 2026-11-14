/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.FiniteAction
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Computable permutation words, tables, and cycles

Words use Mathlib's multiplication convention: the rightmost letter acts first.
The inverse-table construction performs a bounded search over the points.
The cycle check uses point saturation rather than an integer-power search.
-/

open Equiv Subgroup

@[expose] public section

namespace TauCeti.FinitePermutation

/-- A list of bounded generator indices and inversion bits. -/
abbrev Word (size : ℕ) := List (Fin size × Bool)

section Words

variable {G : Type*} [Group G]

/-- Interpret one generator index and inversion bit in a group. -/
def letterValue (gs : List G) (letter : Fin gs.length × Bool) : G :=
  if letter.2 then (gs.get letter.1)⁻¹ else gs.get letter.1

/-- Evaluate a signed word with the rightmost letter acting first. -/
def wordValue (gs : List G) (word : Word gs.length) : G :=
  (word.map (letterValue gs)).prod

/-- Reverse a word and toggle its inversion bits. -/
def inverseWord {size : ℕ} (word : Word size) : Word size :=
  (word.map fun letter => (letter.1, !letter.2)).reverse

theorem wordValue_mem (gs : List G) (word : Word gs.length) :
    wordValue gs word ∈ closure {g | g ∈ gs} := by
  induction word with
  | nil => exact one_mem _
  | cons letter word ih =>
    change letterValue gs letter * wordValue gs word ∈ _
    apply mul_mem _ ih
    have hmem : gs.get letter.1 ∈ closure {g | g ∈ gs} :=
      subset_closure (gs.get_mem _)
    unfold letterValue
    split
    · exact inv_mem hmem
    · exact hmem

theorem letterValue_inverse (gs : List G) (letter : Fin gs.length × Bool) :
    letterValue gs (letter.1, !letter.2) = (letterValue gs letter)⁻¹ := by
  cases letter with
  | mk i inverted => cases inverted <;> simp [letterValue]

theorem wordValue_inverseWord (gs : List G) (word : Word gs.length) :
    wordValue gs (inverseWord word) = (wordValue gs word)⁻¹ := by
  induction word with
  | nil => simp [inverseWord, wordValue]
  | cons letter word ih =>
    simp only [inverseWord, List.map_cons, List.reverse_cons, wordValue,
      List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_inv_rev]
    rw [letterValue_inverse]
    exact congrArg (· * (letterValue gs letter)⁻¹) ih

theorem wordValue_foldl (gs : List G) (word : Word gs.length) :
    word.foldl (fun value letter => value * letterValue gs letter) 1 =
      wordValue gs word := by
  rw [← List.foldl_map]
  exact List.prod_eq_foldl.symm

end Words

section Tables

variable {n : ℕ}

/-- An injective table on `Fin n`, with its inverse computed by a bounded search. -/
def permutationOfTable (table : Fin n → Fin n) (hinj : Function.Injective table) :
    Perm (Fin n) where
  toFun := table
  invFun y := Fin.find (fun x => table x = y) (Finite.surjective_of_injective hinj y)
  left_inv x := hinj (Fin.find_spec (p := fun z => table z = table x) _)
  right_inv y := Fin.find_spec (p := fun x => table x = y) _

@[simp]
theorem permutationOfTable_apply (table : Fin n → Fin n)
    (hinj : Function.Injective table) (x : Fin n) :
    permutationOfTable table hinj x = table x := rfl

theorem permutationOfTable_roundtrip (g : Perm (Fin n)) :
    permutationOfTable g g.injective = g := by
  ext x
  rfl

end Tables

section Cycles

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem mem_cycleOrbit_iff (g : Perm α) (a x : α) :
    x ∈ FiniteAction.orbit [g] a ↔ g.SameCycle a x := by
  constructor
  · have hstep : ∀ s : Finset α, (∀ x ∈ s, g.SameCycle a x) →
        ∀ x ∈ FiniteAction.orbitStep [g] s, g.SameCycle a x := by
      intro s hs x hx
      rcases (FiniteAction.mem_orbitStep _ _ _).mp hx with hx | ⟨i, hi⟩ | ⟨i, hi⟩
      · exact hs _ hx
      · have h := hs _ hi
        simpa using h
      · have h := hs _ hi
        simpa using h
    exact FiniteClosure.saturate_preserves _ (Fintype.card α)
      (fun s => ∀ x ∈ s, g.SameCycle a x) hstep (by
        intro y hy
        simp only [Finset.mem_singleton] at hy
        subst y
        exact Perm.SameCycle.refl _ _) x
  · rintro ⟨z, rfl⟩
    apply (FiniteAction.mem_orbit_iff _ _ _).mpr
    exact ⟨⟨g ^ z, (FiniteAction.ambientGroup [g]).zpow_mem
      (subset_closure (by simp)) z⟩, rfl⟩

/-- Check that the nonfixed points form one nontrivial permutation orbit. -/
def cycleCheck (g : Perm α) : Bool :=
  decide (∃ a, g a ≠ a ∧ ∀ x, g x ≠ x → x ∈ FiniteAction.orbit [g] a)

theorem cycleCheck_iff (g : Perm α) :
    cycleCheck g = true ↔ g.IsCycle := by
  simp only [cycleCheck, decide_eq_true_eq, mem_cycleOrbit_iff, Perm.IsCycle]


end Cycles

end TauCeti.FinitePermutation
