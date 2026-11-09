/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite sums and finite types

`Unit ⊕ Unit` and `Fin 2`, or `Unit ⊕ Unit ⊕ Unit` and `Fin 3`, are the two ways a small index
type arises: one variable per named slot, or one variable per numeral. Translating between them
is pure bookkeeping, needed wherever an object indexed by named slots must be presented against
an API indexed by `Fin n`.

More generally, an embedding of a type `α` into a finite type `β` identifies `β` with the sum of
`α` and a finite complementary type `Fin l`. This packages the standard splitting of a finite
type along the range of an embedding.

The two `Unit`-sum equivalences are Mathlib's own compositions — `finOneEquiv` on each summand,
then `finSumFinEquiv` — given a name and their evaluation lemmas, so that call sites reindexing a
two- or three-variable object can rewrite rather than unfold them.

## Main declarations

* `TauCeti.unitSumUnitEquivFinTwo`: the equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left
  summand to `0` and the right to `1`.
* `TauCeti.unitSumUnitSumUnitEquivFinThree`: the equivalence `Unit ⊕ Unit ⊕ Unit ≃ Fin 3`,
  sending the outer left summand to `0` and the two inner ones to `1` and `2`.
* `Function.Embedding.exists_equiv_sum_fin`: an embedding into a finite type extends to an
  equivalence from the sum with a finite complement.

## Implementation notes

The constructions are implementation details: `Mathlib.Data.Fintype.EquivFin` and
`Mathlib.Logic.Equiv.Fin.Basic` are imported privately rather than re-exported. Only the
finiteness, equivalence and embedding interfaces needed by the declaration types are public.
-/

public section

namespace Function.Embedding

/-- An embedding `s : α ↪ β` into a finite type extends to an equivalence from `α` together with
a finite complement to `β`. -/
theorem exists_equiv_sum_fin {α β : Type*} [Finite β] (s : α ↪ β) :
    ∃ (l : ℕ) (e : α ⊕ Fin l ≃ β), ∀ a, e (Sum.inl a) = s a := by
  classical
  obtain ⟨l, ⟨f⟩⟩ := Finite.exists_equiv_fin {b : β // b ∉ Set.range s}
  exact ⟨l, (Equiv.sumCongr (Equiv.ofInjective s s.injective) f.symm).trans
    (Equiv.sumCompl (· ∈ Set.range s)), fun a ↦ by simp⟩

end Function.Embedding

namespace TauCeti

/-- The equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left summand to `0` and the right to `1`.

An `Equiv` rather than a bare `Function.Embedding`: injectivity is what turns a coefficient under
a reindexing into an equality rather than a sum over a fibre, but surjectivity is what lets a
statement about *every* `Fin 2` index be pulled back, and both directions are wanted downstream. -/
def unitSumUnitEquivFinTwo : (Unit ⊕ Unit) ≃ Fin 2 :=
  (Equiv.sumCongr finOneEquiv.symm finOneEquiv.symm).trans finSumFinEquiv

@[simp]
theorem unitSumUnitEquivFinTwo_inl : unitSumUnitEquivFinTwo (Sum.inl ()) = 0 := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_inr : unitSumUnitEquivFinTwo (Sum.inr ()) = 1 := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_symm_zero :
    unitSumUnitEquivFinTwo.symm 0 = Sum.inl () := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_symm_one :
    unitSumUnitEquivFinTwo.symm 1 = Sum.inr () := by decide

/-- The equivalence `Unit ⊕ Unit ≃ Fin 2` iterated on the right, `Unit ⊕ Unit ⊕ Unit ≃ Fin 3`,
sending the outer left summand to `0` and the two inner summands to `1` and `2`.

The nesting is the one a three-variable identity meets: an outer variable together with a pair of
inner ones, matching the shape in which an associativity law names its three slots. -/
def unitSumUnitSumUnitEquivFinThree : (Unit ⊕ Unit ⊕ Unit) ≃ Fin 3 :=
  (Equiv.sumCongr finOneEquiv.symm unitSumUnitEquivFinTwo).trans finSumFinEquiv

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_inl :
    unitSumUnitSumUnitEquivFinThree (Sum.inl ()) = 0 := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_inr_inl :
    unitSumUnitSumUnitEquivFinThree (Sum.inr (Sum.inl ())) = 1 := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_inr_inr :
    unitSumUnitSumUnitEquivFinThree (Sum.inr (Sum.inr ())) = 2 := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_symm_zero :
    unitSumUnitSumUnitEquivFinThree.symm 0 = Sum.inl () := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_symm_one :
    unitSumUnitSumUnitEquivFinThree.symm 1 = Sum.inr (Sum.inl ()) := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_symm_two :
    unitSumUnitSumUnitEquivFinThree.symm 2 = Sum.inr (Sum.inr ()) := by decide

end TauCeti
