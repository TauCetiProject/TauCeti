/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.WellOrder
import Mathlib.ModelTheory.Order
import Mathlib.Logic.Equiv.Nat

/-!
# Regression examples: coded well-orders

In the language of orders, with its symbol read as `lt`, a well-order here is strict:

* the code of `(ℕ, <)` is a coded well-order, of order type `ω`;
* the code of `(ℤ, <)`, transported to `ℕ`, is not: `0 > -1 > -2 > ⋯` descends;
* the code of `(ℕ, ≤)` is not, since `0 ≤ 0`: its descending tree has the constant branch
  `0, 0, 0, …`.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration Descriptive Tree

-- The code of `(ℕ, <)` is a coded well-order of order type `ω`.
example :
    let S : Language.order.Structure ℕ :=
      ⟨fun f => isEmptyElim f, fun {_} R xs => match R with | .le => xs 0 < xs 1⟩
    ∃ h : IsWellOrder ℕ (codeRel leSymb (@ofStructure Language.order ℕ S)),
      @Ordinal.type ℕ (codeRel leSymb (@ofStructure Language.order ℕ S)) h = Ordinal.omega0 := by
  intro S
  classical
  let f : codeRel leSymb (@ofStructure Language.order ℕ S) ≃r (· < · : ℕ → ℕ → Prop) :=
    ⟨Equiv.refl ℕ, fun {x y} => by
      rw [codeRel_iff, @eval_ofStructure Language.order ℕ S, decide_eq_true_eq]; rfl⟩
  have hwo : IsWellOrder ℕ (codeRel leSymb (@ofStructure Language.order ℕ S)) :=
    f.toRelEmbedding.isWellOrder
  exact ⟨hwo, (Ordinal.type_eq.2 ⟨f⟩).trans Ordinal.type_nat_lt⟩

-- The code of `(ℤ, <)`, transported to `ℕ`, is not a coded well-order.
example :
    let S : Language.order.Structure ℕ := ⟨fun f => isEmptyElim f, fun {_} R xs => match R with
      | .le => Equiv.intEquivNat.symm (xs 0) < Equiv.intEquivNat.symm (xs 1)⟩
    @ofStructure Language.order ℕ S ∉ wellOrderClass leSymb := by
  intro S h
  classical
  refine (wellFounded_iff_isEmpty_descending_chain.1 ((mem_wellOrderClass leSymb).1 h).wf).false
    ⟨fun n => Equiv.intEquivNat (-(n : ℤ)), fun n => ?_⟩
  rw [codeRel_iff, @eval_ofStructure Language.order ℕ S, decide_eq_true_eq]
  change Equiv.intEquivNat.symm (Equiv.intEquivNat _) < Equiv.intEquivNat.symm (Equiv.intEquivNat _)
  simp

-- The code of `(ℕ, ≤)` is not a coded well-order: its descending tree has the branch `0, 0, …`.
example :
    let S : Language.order.Structure ℕ :=
      ⟨fun f => isEmptyElim f, fun {_} R xs => match R with | .le => xs 0 ≤ xs 1⟩
    ¬ IsWellFounded (descendingTree (codeRel leSymb (@ofStructure Language.order ℕ S))) ∧
      @ofStructure Language.order ℕ S ∉ wellOrderClass leSymb := by
  intro S
  classical
  have h0 : codeRel leSymb (@ofStructure Language.order ℕ S) 0 0 := by
    rw [codeRel_iff, @eval_ofStructure Language.order ℕ S, decide_eq_true_eq]
    exact le_refl 0
  have hbranch := not_isWellFounded_iff.2
    ⟨fun _ => 0, (forall_ofFn_mem_descendingTree_iff _).2 fun _ => h0⟩
  exact ⟨hbranch, fun h => hbranch
    (isWellFounded_descendingTree_iff.2 ((mem_wellOrderClass leSymb).1 h).wf)⟩
