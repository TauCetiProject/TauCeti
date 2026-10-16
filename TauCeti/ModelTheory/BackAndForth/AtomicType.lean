/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic

/-!
# Atomic types of finite tuples

`AtomicIdx L n` indexes equalities of positions and relation symbols applied to positions in
an `n`-tuple. Nullary relations are included, even for the empty tuple. `SameAtomicType`
expresses agreement on these tests, the initial level of back-and-forth equivalence.

For a relational language these are all atomic formulas. `SameAtomicType` includes relationality
as a conjunct so that it cannot hold for a language with function symbols. Reflexivity requires
`[L.IsRelational]`; symmetry and transitivity preserve this restriction.

The construction follows the atomic tests in Cameron Freer's
`cameronfreer/infinitary-logic`, `InfinitaryLogic/Scott/BackAndForth.lean`.
-/

public section

universe u v w w' w''

namespace TauCeti

open FirstOrder FirstOrder.Language.Structure

/-- An equality of tuple positions or a relation symbol applied to tuple positions.
The arity of a relation may be zero. -/
inductive AtomicIdx (L : Language.{u, v}) (n : ℕ) : Type v where
  | eq (i j : Fin n)
  | rel {k : ℕ} (r : L.Relations k) (f : Fin k → Fin n)

variable {L : Language.{u, v}} {n : ℕ}
variable {M : Type w} {N : Type w'} {P : Type w''}
variable [L.Structure M] [L.Structure N] [L.Structure P]

/-- Evaluate an atomic test at a tuple. -/
def AtomicIdx.Holds : AtomicIdx L n → (Fin n → M) → Prop
  | .eq i j, a => a i = a j
  | .rel r f, a => RelMap r (a ∘ f)

@[simp]
theorem AtomicIdx.holds_eq (i j : Fin n) (a : Fin n → M) :
    (AtomicIdx.eq (L := L) i j).Holds a ↔ a i = a j := Iff.rfl

@[simp]
theorem AtomicIdx.holds_rel {k : ℕ} (r : L.Relations k) (f : Fin k → Fin n)
    (a : Fin n → M) : (AtomicIdx.rel r f).Holds a ↔ RelMap r (a ∘ f) := Iff.rfl

/-- The language is relational and the tuples agree on all atomic tests, including nullary
relations. Relationality is part of the predicate, rather than an unused instance argument. -/
def SameAtomicType (a : Fin n → M) (b : Fin n → N) : Prop :=
  L.IsRelational ∧ ∀ i : AtomicIdx L n, i.Holds a ↔ i.Holds b

section

variable [L.IsRelational]

/-- Atomic-type agreement is pointwise agreement on the atomic tests. -/
theorem sameAtomicType_def (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := L) a b ↔ ∀ i : AtomicIdx L n, i.Holds a ↔ i.Holds b :=
  ⟨And.right, fun h => ⟨inferInstance, h⟩⟩

/-- Separate the equality and relation parts of atomic-type agreement. -/
theorem sameAtomicType_iff (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := L) a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧
      (∀ {k} (r : L.Relations k) (f : Fin k → Fin n),
        RelMap r (a ∘ f) ↔ RelMap r (b ∘ f)) := by
  rw [sameAtomicType_def]
  constructor
  · intro h
    exact ⟨fun i j => h (.eq i j), fun r f => h (.rel r f)⟩
  · rintro ⟨heq, hrel⟩ i
    cases i with
    | eq i j => exact heq i j
    | rel r f => exact hrel r f

end

namespace SameAtomicType

variable {a : Fin n → M} {b : Fin n → N} {c : Fin n → P}

/-- Atomic-type agreement can hold only in a relational language. -/
theorem isRelational (h : SameAtomicType (L := L) a b) : L.IsRelational := h.1

/-- Tuples with the same atomic type have the same equality pattern. -/
theorem eq_iff (h : SameAtomicType (L := L) a b) (i j : Fin n) :
    a i = a j ↔ b i = b j := h.2 (.eq i j)

/-- Tuples with the same atomic type agree on every relation, including nullary ones. -/
theorem rel_iff (h : SameAtomicType (L := L) a b) {k : ℕ} (r : L.Relations k)
    (f : Fin k → Fin n) : RelMap r (a ∘ f) ↔ RelMap r (b ∘ f) := h.2 (.rel r f)

/-- Every tuple agrees with itself on all atomic tests. -/
@[refl, simp]
theorem refl [L.IsRelational] (a : Fin n → M) : SameAtomicType (L := L) a a :=
  ⟨inferInstance, fun _ => Iff.rfl⟩

/-- Atomic-type agreement is symmetric. -/
@[symm]
theorem symm (h : SameAtomicType (L := L) a b) : SameAtomicType (L := L) b a :=
  ⟨h.1, fun i => (h.2 i).symm⟩

/-- Atomic-type agreement is transitive across three structures. -/
@[trans]
theorem trans (hab : SameAtomicType (L := L) a b) (hbc : SameAtomicType (L := L) b c) :
    SameAtomicType (L := L) a c := ⟨hab.1, fun i => (hab.2 i).trans (hbc.2 i)⟩

end SameAtomicType

end TauCeti
