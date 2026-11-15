/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Syntax
public import Mathlib.ModelTheory.Encoding
import TauCeti.ModelTheory.Basic

/-!
# Countability of infinitary syntax

With countably many variables and countably many function and relation symbols, the atomic
infinitary formulas form a countable type, as for Mathlib's finitary terms in
`Mathlib.ModelTheory.Encoding`.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.countable_subtype_isAtomic`: there are countably many
  atomic formulas.
-/

public section

universe u v u' w

namespace FirstOrder

namespace Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type w} {α : Type u'} {n : ℕ}

/-- With countably many variables and countably many function and relation symbols, there are
countably many atomic formulas. -/
instance countable_subtype_isAtomic [Countable α] [Countable (Σ l, L.Functions l)]
    [Countable (Σ l, L.Relations l)] :
    Countable {φ : L.BoundedFormulaInf ι α n // φ.IsAtomic} := by
  refine Function.Surjective.countable
    (f := Sum.elim (fun t : L.Term (α ⊕ Fin n) × L.Term (α ⊕ Fin n) =>
        (⟨equal t.1 t.2, .equal _ _⟩ : {φ : L.BoundedFormulaInf ι α n // φ.IsAtomic}))
      fun R : Σ l, L.Relations l × (Fin l → L.Term (α ⊕ Fin n)) => ⟨rel R.2.1 R.2.2, .rel _ _⟩)
    ?_
  rintro ⟨_, ⟨t₁, t₂⟩ | ⟨R, ts⟩⟩
  exacts [⟨.inl (t₁, t₂), rfl⟩, ⟨.inr ⟨_, R, ts⟩, rfl⟩]

end BoundedFormulaInf

end Language

end FirstOrder
