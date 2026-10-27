/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum

/-!
# Atomic types of finite tuples

`AtomicIdx L n` indexes equalities of positions and relation symbols applied to positions in
an `n`-tuple. Nullary relations are included, even for the empty tuple. `SameAtomicType`
expresses agreement on these tests, the initial level of back-and-forth equivalence.

For a relational language these are all atomic formulas. `SameAtomicType` requires a relational
language so that agreement on these tests is agreement on the full atomic type.

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

/-- A countable relation language has countably many atomic tests on a finite tuple. -/
instance [Countable (Σ k, L.Relations k)] : Countable (AtomicIdx L n) := by
  have : ∀ k, Countable (L.Relations k) := fun k =>
    (sigma_mk_injective (i := k)).countable
  let f : AtomicIdx L n → (Fin n × Fin n) ⊕ (Σ k, L.Relations k × (Fin k → Fin n))
    | .eq i j => .inl (i, j)
    | .rel r g => .inr ⟨_, r, g⟩
  apply Function.Injective.countable (f := f)
  intro i j hij
  cases i <;> cases j <;> simp_all [f]
  rcases hij with ⟨rfl, h⟩
  cases eq_of_heq h
  simp

/-- A finite relation language has finitely many atomic tests on a finite tuple. -/
instance [Finite (Σ k, L.Relations k)] : Finite (AtomicIdx L n) := by
  let f : AtomicIdx L n → (Fin n × Fin n) ⊕ (Σ r : Σ k, L.Relations k, Fin r.1 → Fin n)
    | .eq i j => .inl (i, j)
    | .rel r g => .inr ⟨⟨_, r⟩, g⟩
  apply Finite.of_injective f
  intro i j hij
  cases i <;> cases j <;> simp_all [f]

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

/-- Agreement on all atomic formulas of a relational language, including nullary relations. -/
structure SameAtomicType [L.IsRelational] (a : Fin n → M) (b : Fin n → N) : Prop where
  /-- The tuples agree on each atomic test. -/
  holds : ∀ i : AtomicIdx L n, i.Holds a ↔ i.Holds b

variable [L.IsRelational]

/-- Atomic-type agreement is pointwise agreement on the atomic tests. -/
theorem sameAtomicType_def (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := L) a b ↔ ∀ i : AtomicIdx L n, i.Holds a ↔ i.Holds b :=
  ⟨fun h => h.holds, fun h => ⟨h⟩⟩

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

namespace SameAtomicType

variable {a : Fin n → M} {b : Fin n → N} {c : Fin n → P}

/-- Tuples with the same atomic type have the same equality pattern. -/
theorem eq_iff (h : SameAtomicType (L := L) a b) (i j : Fin n) :
    a i = a j ↔ b i = b j := h.holds (.eq i j)

/-- Tuples with the same atomic type agree on every relation, including nullary ones. -/
theorem rel_iff (h : SameAtomicType (L := L) a b) {k : ℕ} (r : L.Relations k)
    (f : Fin k → Fin n) : RelMap r (a ∘ f) ↔ RelMap r (b ∘ f) := h.holds (.rel r f)

/-- Every tuple agrees with itself on all atomic tests. -/
@[refl, simp]
theorem refl (a : Fin n → M) : SameAtomicType (L := L) a a := ⟨fun _ => Iff.rfl⟩

/-- Atomic-type agreement is symmetric. -/
@[symm]
theorem symm (h : SameAtomicType (L := L) a b) : SameAtomicType (L := L) b a :=
  ⟨fun i => (h.holds i).symm⟩

/-- Atomic-type agreement is transitive across three structures. -/
@[trans]
theorem trans (hab : SameAtomicType (L := L) a b) (hbc : SameAtomicType (L := L) b c) :
    SameAtomicType (L := L) a c := ⟨fun i => (hab.holds i).trans (hbc.holds i)⟩

/-- Atomic-type agreement is preserved by reindexing both tuples along the same map of
positions, which may repeat or omit entries. -/
theorem comp (h : SameAtomicType (L := L) a b) {m : ℕ} (g : Fin m → Fin n) :
    SameAtomicType (L := L) (a ∘ g) (b ∘ g) := by
  rw [sameAtomicType_iff]
  exact ⟨fun i j => h.eq_iff (g i) (g j), fun r f => h.rel_iff r (g ∘ f)⟩

end SameAtomicType

/-- In a relational language without nullary relation symbols, the empty tuples of any two
structures have the same atomic type. -/
theorem sameAtomicType_elim0 [IsEmpty (L.Relations 0)] :
    SameAtomicType (L := L) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  refine (sameAtomicType_iff _ _).mpr ⟨fun i => i.elim0, fun {k} r f => ?_⟩
  cases k with
  | zero => exact isEmptyElim r
  | succ k => exact (f 0).elim0

end TauCeti
