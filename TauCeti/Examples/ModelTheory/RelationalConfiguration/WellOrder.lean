/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.WellOrder
import TauCeti.SetTheory.Descriptive.Tree.Descending
import Mathlib.ModelTheory.Order
import TauCeti.ModelTheory.Order
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
example : ∃ h : IsWellOrder ℕ
      (codeRel leSymb (@ofStructure Language.order ℕ (relStructure leSymb (· < ·) 0))),
    @Ordinal.type ℕ _ h = Ordinal.omega0 := by
  -- the code interprets the order symbol by `<`
  have hS (x y : ℕ) :
      codeRel leSymb (@ofStructure Language.order ℕ (relStructure leSymb (· < ·) 0)) x y ↔
        x < y :=
    (@codeRel_ofStructure _ _ (relStructure leSymb (· < ·) 0) leSymb x y).trans
      (relMap_relStructure_self leSymb (· < ·) 0 x y)
  let f : codeRel leSymb (@ofStructure Language.order ℕ (relStructure leSymb (· < ·) 0)) ≃r
      (· < · : ℕ → ℕ → Prop) := ⟨Equiv.refl ℕ, fun {x y} => (hS x y).symm⟩
  have hwo := f.toRelEmbedding.isWellOrder
  exact ⟨hwo, (Ordinal.type_eq.2 ⟨f⟩).trans Ordinal.type_nat_lt⟩

-- `(ℤ, <)` transported to `ℕ`: strict, but `0 > -1 > -2 > ⋯` is an infinite descending chain.
example : @ofStructure Language.order ℕ (relStructure leSymb
      (fun x y => Equiv.intEquivNat.symm x < Equiv.intEquivNat.symm y) 0) ∉
    wellOrderClass leSymb := by
  -- the code interprets the order symbol by the order of `ℤ`
  have hS (x y : ℕ) : codeRel leSymb (@ofStructure Language.order ℕ (relStructure leSymb
      (fun x y => Equiv.intEquivNat.symm x < Equiv.intEquivNat.symm y) 0)) x y ↔
        Equiv.intEquivNat.symm x < Equiv.intEquivNat.symm y :=
    (@codeRel_ofStructure _ _ (relStructure leSymb
      (fun x y => Equiv.intEquivNat.symm x < Equiv.intEquivNat.symm y) 0) leSymb x y).trans
      (relMap_relStructure_self leSymb _ 0 x y)
  intro h
  refine (wellFounded_iff_isEmpty_descending_chain.1 (mem_wellOrderClass.1 h).wf).false
    ⟨fun n => Equiv.intEquivNat (-(n : ℤ)), fun n => ?_⟩
  simp [hS]

-- `(ℕ, ≤)`: not strict, and the constant sequence `0, 0, …` is a branch of its descending tree.
example : ¬ IsWellFounded
      (descendingTree (codeRel leSymb (@ofStructure Language.order ℕ (orderStructure ℕ)))) ∧
    @ofStructure Language.order ℕ (orderStructure ℕ) ∉ wellOrderClass leSymb := by
  -- the code interprets the order symbol by `≤`, which relates `0` to itself
  have h0 : codeRel leSymb (@ofStructure Language.order ℕ (orderStructure ℕ)) 0 0 := by
    let := orderStructure ℕ
    exact (codeRel_ofStructure leSymb 0 0).2 ((relMap_leSymb ![0, 0]).2 le_rfl)
  have hbranch := not_isWellFounded_iff.2
    ⟨fun _ => 0, (forall_ofFn_mem_descendingTree_iff _).2 fun _ => h0⟩
  exact ⟨hbranch, fun h => hbranch (isWellFounded_descendingTree_iff.2 (mem_wellOrderClass.1 h).wf)⟩
