/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Basic
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Primitivity of a permutation triple

This module supplies the primitivity predicate for permutation triples. The finite decision
procedure and its correctness theorem use this predicate to state what their test decides. A
connected triple of prime degree is primitive.
-/

public section

namespace TauCeti

namespace PermutationTriple

open MulAction

variable {n : ℕ} (t : PermutationTriple n)

/-- The monodromy action is pretransitive and has only trivial blocks of sheets.
This uses Mathlib's `IsPreprimitive`, which also holds for an empty set of sheets. -/
def IsPrimitive : Prop := IsPreprimitive t.monodromyGroup (Fin n)

/-- Primitivity of a triple is preprimitivity of its monodromy action. -/
theorem isPrimitive_iff : t.IsPrimitive ↔ IsPreprimitive t.monodromyGroup (Fin n) := Iff.rfl

/-- A connected triple of prime degree is primitive: a block of a transitive action has size
dividing the degree. -/
theorem IsConnected.isPrimitive_of_prime {t : PermutationTriple n} (ht : t.IsConnected)
    (hn : n.Prime) : t.IsPrimitive :=
  have := ht.isPretransitive
  IsPreprimitive.of_prime_card (by rwa [Nat.card_fin])

end PermutationTriple

end TauCeti
