/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.WellFounded

/-!
# Sorting permutations of a finite linear order

Exactly one permutation of a finite linear order sorts the values of an injective map to a linear
order (`Equiv.Perm.existsUnique_strictMono_comp`). It is obtained from the order isomorphism of
the domain with the range given by Mathlib's `Fintype.orderIsoFinOfCardEq`.
-/

public section

namespace Equiv.Perm

/-- Exactly one permutation of a finite linear order `α` sorts the values of an injective map
`f : α → β` to a linear order, that is, makes `f ∘ p` strictly increasing. -/
theorem existsUnique_strictMono_comp {α β : Type*} [LinearOrder α] [Finite α] [LinearOrder β]
    {f : α → β} (hf : Function.Injective f) : ∃! p : Perm α, StrictMono (f ∘ p) := by
  have := Fintype.ofFinite α
  classical
  -- The order isomorphism of `α` with the range of `f` gives the sorting permutation.
  let o : α ≃o Set.range f := (Fintype.orderIsoFinOfCardEq α rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq (Set.range f) (Set.card_range_of_injective hf))
  let p : Perm α := o.toEquiv.trans (Equiv.ofInjective f hf).symm
  have hp : StrictMono (f ∘ p) := fun a b hab => by
    simpa [p, Equiv.apply_ofInjective_symm hf] using o.strictMono hab
  refine ⟨p, hp, fun q hq => Equiv.ext fun a => hf ?_⟩
  -- Two sorting permutations give strictly increasing maps with the same range.
  have hrange : Set.range (f ∘ q) = Set.range (f ∘ p) := by
    rw [Set.range_comp, Set.range_comp, q.range_eq_univ, p.range_eq_univ]
  exact congrFun ((StrictMono.range_inj_of_wellFoundedLT hq hp).1 hrange) a

end Equiv.Perm
