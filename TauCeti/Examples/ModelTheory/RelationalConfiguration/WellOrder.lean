/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.WellOrder
import TauCeti.SetTheory.Descriptive.Tree.Descending
import Mathlib.ModelTheory.Order
import Mathlib.Logic.Equiv.Nat

/-!
# Regression examples: coded well-orders

In the language of orders, with its symbol read as `lt`, a coded well-order is a code whose
relation is a strict well-order of `ℕ`:

* the code of `(ℕ, <)` is a coded well-order, of order type `ω`;
* the code of `(ℤ, <)`, transported to `ℕ`, is strict but not a coded well-order:
  `0 > -1 > -2 > ⋯` is an infinite descending chain;
* the code of `(ℕ, ≤)` is not a coded well-order because it is not strict: `0 ≤ 0`, so the
  constant sequence `0, 0, …` is a branch of its descending tree.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration Descriptive Tree

-- `(ℕ, <)`: a coded well-order of order type `ω`.
example :
    let S : Language.order.Structure ℕ :=
      ⟨fun f => isEmptyElim f, fun {_} R xs => match R with | .le => xs 0 < xs 1⟩
    ∃ h : IsWellOrder ℕ (codeRel leSymb (@ofStructure Language.order ℕ S)),
      @Ordinal.type ℕ (codeRel leSymb (@ofStructure Language.order ℕ S)) h = Ordinal.omega0 := by
  intro S
  let f : codeRel leSymb (@ofStructure Language.order ℕ S) ≃r (· < · : ℕ → ℕ → Prop) :=
    ⟨Equiv.refl ℕ, fun {x y} => (@codeRel_ofStructure _ _ S leSymb x y).symm⟩
  have hwo : IsWellOrder ℕ (codeRel leSymb (@ofStructure Language.order ℕ S)) :=
    f.toRelEmbedding.isWellOrder
  exact ⟨hwo, (Ordinal.type_eq.2 ⟨f⟩).trans Ordinal.type_nat_lt⟩

-- `(ℤ, <)` transported to `ℕ`: strict, but `0 > -1 > -2 > ⋯` is an infinite descending chain.
example :
    let S : Language.order.Structure ℕ := ⟨fun f => isEmptyElim f, fun {_} R xs => match R with
      | .le => Equiv.intEquivNat.symm (xs 0) < Equiv.intEquivNat.symm (xs 1)⟩
    @ofStructure Language.order ℕ S ∉ wellOrderClass leSymb := by
  intro S h
  refine (wellFounded_iff_isEmpty_descending_chain.1 (mem_wellOrderClass.1 h).wf).false
    ⟨fun n => Equiv.intEquivNat (-(n : ℤ)), fun n => ?_⟩
  rw [@codeRel_ofStructure _ _ S]
  change Equiv.intEquivNat.symm (Equiv.intEquivNat _) < Equiv.intEquivNat.symm (Equiv.intEquivNat _)
  simp

-- `(ℕ, ≤)`: not strict, and the constant sequence `0, 0, …` is a branch of its descending tree.
example :
    let S : Language.order.Structure ℕ :=
      ⟨fun f => isEmptyElim f, fun {_} R xs => match R with | .le => xs 0 ≤ xs 1⟩
    ¬ IsWellFounded (descendingTree (codeRel leSymb (@ofStructure Language.order ℕ S))) ∧
      @ofStructure Language.order ℕ S ∉ wellOrderClass leSymb := by
  intro S
  have h0 : codeRel leSymb (@ofStructure Language.order ℕ S) 0 0 :=
    (@codeRel_ofStructure _ _ S leSymb 0 0).2 (le_refl 0)
  have hbranch := not_isWellFounded_iff.2
    ⟨fun _ => 0, (forall_ofFn_mem_descendingTree_iff _).2 fun _ => h0⟩
  exact ⟨hbranch, fun h => hbranch (isWellFounded_descendingTree_iff.2 (mem_wellOrderClass.1 h).wf)⟩
