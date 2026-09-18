/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Generators of an extension of prime degree

A field extension of prime degree has no proper intermediate field
(`IntermediateField.isSimpleOrder_of_finrank_prime`), so every element outside the base field
generates the whole extension. This file records that consequence, for the intermediate field
`F⟮x⟯` and for the subalgebra `Algebra.adjoin F {x}`.

## Main results

* `TauCeti.IntermediateField.adjoin_simple_eq_top_of_finrank_prime`: in an extension of prime
  degree, `F⟮x⟯ = ⊤` for every `x` outside the base field.
* `TauCeti.Algebra.adjoin_singleton_eq_top_of_finrank_prime`: the same conclusion for
  `Algebra.adjoin F {x}`.
-/

public section

open scoped IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- In an extension of prime degree, every element outside the base field generates the
extension. -/
theorem TauCeti.IntermediateField.adjoin_simple_eq_top_of_finrank_prime
    (hp : Nat.Prime (Module.finrank F E)) {x : E} (hx : x ∉ (⊥ : IntermediateField F E)) :
    F⟮x⟯ = ⊤ :=
  ((IntermediateField.isSimpleOrder_of_finrank_prime F E hp).eq_bot_or_eq_top F⟮x⟯).resolve_left
    fun h => hx (h ▸ IntermediateField.mem_adjoin_simple_self F x)

/-- In an extension of prime degree, every element outside the base field generates the
extension as an algebra. -/
theorem TauCeti.Algebra.adjoin_singleton_eq_top_of_finrank_prime
    (hp : Nat.Prime (Module.finrank F E))
    {x : E} (hx : x ∉ (⊥ : IntermediateField F E)) : Algebra.adjoin F {x} = ⊤ := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos hp.pos
  exact (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic fun x _ =>
    Algebra.IsAlgebraic.isAlgebraic x).mp
    (TauCeti.IntermediateField.adjoin_simple_eq_top_of_finrank_prime hp hx)
