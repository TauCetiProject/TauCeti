/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
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

## Main definitions

* `FirstOrder.Language.relStructure`: the structure interpreting one binary relation symbol by a
  given relation, every other relation symbol as empty and every function symbol as a constant.
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

/-- The `L`-structure on `M` interpreting the binary relation symbol `lt` by `r`, every other
relation symbol as empty and every function symbol as the constant `m`. -/
@[instance_reducible]
def relStructure (lt : L.Relations 2) {M : Type*} (r : M → M → Prop) (m : M) :
    L.Structure M where
  funMap _ _ := m
  RelMap {n} R xs := match n, R, xs with
    | 2, R, xs => R = lt ∧ r (xs 0) (xs 1)
    | _, _, _ => False

/-- In `relStructure lt r m`, a binary relation symbol holds of a pair exactly when it is `lt` and
`r` holds of the pair. -/
@[simp]
theorem relMap_relStructure (lt R : L.Relations 2) {M : Type*} (r : M → M → Prop) (m : M)
    (xs : Fin 2 → M) :
    @Structure.RelMap L M (relStructure lt r m) 2 R xs ↔ R = lt ∧ r (xs 0) (xs 1) :=
  Iff.rfl

/-- In `relStructure lt r m`, the symbol `lt` is interpreted by `r`. -/
theorem relMap_relStructure_self (lt : L.Relations 2) {M : Type*} (r : M → M → Prop) (m : M)
    (x y : M) : @Structure.RelMap L M (relStructure lt r m) 2 lt ![x, y] ↔ r x y :=
  and_iff_right rfl

/-- In `relStructure lt r m`, every function symbol is interpreted as the constant `m`. -/
@[simp]
theorem funMap_relStructure (lt : L.Relations 2) {M : Type*} (r : M → M → Prop) (m : M) {n : ℕ}
    (f : L.Functions n) (xs : Fin n → M) :
    @Structure.funMap L M (relStructure lt r m) n f xs = m :=
  (rfl)

/-- In `relStructure lt r m`, every relation symbol of arity other than `2` is empty. -/
theorem not_relMap_relStructure_of_ne (lt : L.Relations 2) {M : Type*} (r : M → M → Prop) (m : M)
    {n : ℕ} (hn : n ≠ 2) (R : L.Relations n) (xs : Fin n → M) :
    ¬ @Structure.RelMap L M (relStructure lt r m) n R xs := by
  match n, hn with
  | 0, _ | 1, _ | _ + 3, _ => exact id
  | 2, hn => exact absurd rfl hn

end Language

end FirstOrder
