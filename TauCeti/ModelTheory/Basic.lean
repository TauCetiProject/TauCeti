/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic

/-!
# Basic facts about first-order languages

Additions to Mathlib's `Mathlib.ModelTheory.Basic`.

## Main results

* `FirstOrder.Language.countable_functions_of_countable_sigma`,
  `FirstOrder.Language.countable_relations_of_countable_sigma`: a language with countably many
  function or relation symbols in total has countably many of each arity.
* `FirstOrder.Language.Countable.countable_relations`: a language with countably many symbols
  has countably many relation symbols in total, complementing Mathlib's function-symbol instance.
* `FirstOrder.Language.nonempty_structure_of_nonempty`,
  `FirstOrder.Language.nonempty_structure_of_isRelational`: a type carries some `L`-structure
  when it is nonempty, and over any type when `L` is relational. On the empty type a constant
  symbol has no interpretation, so some such hypothesis is needed.
-/

public section

namespace FirstOrder

namespace Language

variable {L : Language}

/-- A language with countably many function symbols has countably many of each arity. -/
instance countable_functions_of_countable_sigma [Countable (Σ n, L.Functions n)] (n : ℕ) :
    Countable (L.Functions n) :=
  (sigma_mk_injective (i := n)).countable

/-- A language with countably many relation symbols has countably many of each arity. -/
instance countable_relations_of_countable_sigma [Countable (Σ n, L.Relations n)] (n : ℕ) :
    Countable (L.Relations n) :=
  (sigma_mk_injective (i := n)).countable

/-- A language with countably many symbols has countably many relation symbols in total. -/
instance Countable.countable_relations [Countable L.Symbols] : Countable (Σ n, L.Relations n) :=
  Function.Injective.countable
    (f := (Sum.inr : (Σ n, L.Relations n) → L.Symbols)) Sum.inr_injective

/-- A nonempty type carries some `L`-structure: Mathlib's `Inhabited.trivialStructure` for a
chosen element. -/
instance nonempty_structure_of_nonempty (M : Type*) [Nonempty M] : Nonempty (L.Structure M) :=
  letI := Classical.inhabited_of_nonempty' (α := M)
  ⟨Inhabited.trivialStructure L⟩

/-- Every type, including the empty one, carries some structure for a relational language: make
every relation empty. -/
instance nonempty_structure_of_isRelational [L.IsRelational] (M : Type*) :
    Nonempty (L.Structure M) :=
  ⟨⟨fun f => isEmptyElim f, fun _ _ => False⟩⟩

end Language

end FirstOrder
