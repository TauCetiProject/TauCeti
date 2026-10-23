/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finitely many dominant neutral elements

Fix a splitting Cartan subalgebra `H` in a finite-dimensional Lie algebra with nondegenerate
Killing form over a field of characteristic zero, and a base `b` of its root system.
The dominant neutral elements in `H` are the elements occurring as `h` in a nonzero
`sl₂` triple for which all simple roots take natural-number values.

`weightedDynkinDiagram` encodes such an element by a function `b.support → Fin 3`.
The encoding is injective: the simple roots form a basis of the dual of `H`, so their
values determine the element. Consequently there are at most `3 ^ finrank K H` dominant
neutral elements. This does not assert that every labeling is realized by a triple,
or that equal labels classify nilpotent orbits.

The zero element is excluded by the native nonzero `IsSl2Triple` convention.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §3.5.
-/

public section

open LieAlgebra LieModule LieAlgebra.IsKilling Module

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

/-- The neutral elements of nonzero `sl₂` triples lying in `H` and dominant for `b`.
Dominance means that every simple root takes a natural-number value. -/
def dominantNeutralElements : Set H :=
  {h | (∃ e f : L, IsSl2Triple (h : L) e f) ∧
    ∀ i ∈ b.support, ∃ n : ℕ, (i : Weight K H L) h = n}

/-- Membership is the existence of a triple together with dominance on the simple roots. -/
@[simp]
theorem mem_dominantNeutralElements_iff (h : H) :
    h ∈ dominantNeutralElements b ↔
      (∃ e f : L, IsSl2Triple (h : L) e f) ∧
        ∀ i ∈ b.support, ∃ n : ℕ, (i : Weight K H L) h = n := (Iff.rfl)

/-- Zero is not the neutral element of a native nonzero `sl₂` triple. -/
-- Simplify before the general membership rule expands the proposition inside the negation.
@[simp↓]
theorem zero_notMem_dominantNeutralElements : (0 : H) ∉ dominantNeutralElements b := by
  rintro ⟨⟨e, f, t⟩, -⟩
  exact t.h_ne_zero (by simp)

/-- The labels of the weighted Dynkin diagram of a dominant neutral element. -/
noncomputable def weightedDynkinDiagram (h : dominantNeutralElements b)
    (i : b.support) : Fin 3 := by
  classical
  exact if (i : Weight K H L) h = 0 then 0 else
    if (i : Weight K H L) h = 1 then 1 else 2

/-- A diagram label is the corresponding simple-root value, interpreted in the field. -/
@[simp]
theorem weightedDynkinDiagram_cast (h : dominantNeutralElements b) (i : b.support) :
    ((weightedDynkinDiagram b h i : ℕ) : K) = (i : Weight K H L) h := by
  obtain ⟨⟨e, f, t⟩, hh⟩ := h.property
  rcases t.root_apply_eq_zero_or_eq_one_or_eq_two hh i.property with hi | hi | hi <;>
    simp [weightedDynkinDiagram, hi]

/-- Equality of a diagram label is characterized by the corresponding simple-root value. -/
@[simp]
theorem weightedDynkinDiagram_apply_eq_iff (h : dominantNeutralElements b)
    (i : b.support) (n : Fin 3) :
    weightedDynkinDiagram b h i = n ↔ (i : Weight K H L) h = (n : ℕ) := by
  constructor
  · intro hn
    rw [← weightedDynkinDiagram_cast b h i, hn]
  · intro hn
    apply Fin.ext
    exact Nat.cast_injective ((weightedDynkinDiagram_cast b h i).trans hn)

/-- Simple-root labels determine a dominant neutral element uniquely. -/
theorem weightedDynkinDiagram_injective : Function.Injective (weightedDynkinDiagram b) := by
  intro h h' heq
  apply Subtype.ext
  apply Module.eval_apply_injective K
  apply b.toWeightBasis.ext
  intro i
  have hi := congrArg (fun d : b.support → Fin 3 => ((d i : ℕ) : K)) heq
  simpa using hi

/-- The dominant neutral elements form a finite type via their weighted Dynkin diagrams. -/
instance : Finite (dominantNeutralElements b) :=
  Finite.of_injective _ (weightedDynkinDiagram_injective b)

/-- Only finitely many neutral elements of triples can be dominant in a fixed Cartan subalgebra. -/
theorem finite_dominantNeutralElements : (dominantNeutralElements b).Finite :=
  Set.toFinite _

/-- There are at most three choices per simple root for a dominant neutral element. -/
theorem ncard_dominantNeutralElements_le :
    (dominantNeutralElements b).ncard ≤ 3 ^ finrank K H := by
  have hcard := Nat.card_le_card_of_injective _ (weightedDynkinDiagram_injective b)
  have hrank : Nat.card b.support = finrank K H := by
    simpa using (Module.finrank_eq_card_basis b.toWeightBasis).symm
  rw [Nat.card_fun, Nat.card_fin, hrank] at hcard
  exact hcard

end TauCeti
