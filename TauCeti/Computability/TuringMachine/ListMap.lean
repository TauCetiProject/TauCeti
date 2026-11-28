/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.Composition

/-!
# Finite machines for reversing and mapping lists

A transfer between two stacks computes a reversed map in `2 * n + 2` TM2 steps.
The machine has two stacks, a finite optional-letter state, and finitely many labels.
Composing two transfers computes a map in polynomial time.
-/

open Function Polynomial StateTransition Turing.TM2
open Turing.TM2.Stmt

@[expose] public section

namespace Turing

variable {α : Type} [Fintype α]

/-- A two-stack machine which maps letters while reversing its input. -/
abbrev reverseMapComputer (f : α → α) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := α
  Λ := Option (Option α)
  main := some none
  σ := Option α
  initialState := none
  m
    | none => load (fun _ => none) halt
    | some none => pop false (fun _ x => x)
        (goto fun x => (x.map f).elim none (fun y => some (some y)))
    | some (some x) => push true (fun _ => x) (goto fun _ => some none)

/-- The transfer machine empties its input and leaves the reversed map on its output stack. -/
def reverseMapOutputs (f : α → α) (input : List α) :
    TM2OutputsInTime (reverseMapComputer f) input
      (some (input.map f).reverse) (2 * input.length + 2) := by
  refine ⟨⟨2 * input.length + 2, ?_⟩, le_rfl⟩
  change (flip bind (TM2.step (reverseMapComputer f).m))^[2 * input.length + 2]
      (some (initList (reverseMapComputer f) input)) =
    some (haltList (reverseMapComputer f) (input.map f).reverse)
  have htransfer := TM2.iterate_transfer
    (M := (reverseMapComputer f).m) (k₁ := false) (k₂ := true) (get := f)
    (rd := Option.map f) (w := fun _ x => x) (L := some none) (L' := none)
    (P := fun x => some (some x)) (by decide : (false : Bool) ≠ true)
    rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (initList (reverseMapComputer f) input).stk none
  have hclear :
      update (initList (reverseMapComputer f) input).stk false [] = fun _ => [] := by
    funext k
    cases k <;> simp [initList_stk, reverseMapComputer]
  change (flip bind (TM2.step (reverseMapComputer f).m))^[2 * input.length + 1]
      (some (initList (reverseMapComputer f) input)) = _ at htransfer
  rw [hclear] at htransfer
  simp only [initList_stk, reverseMapComputer, Function.update_self,
    Function.update_of_ne (by decide : true ≠ false), List.append_nil] at htransfer
  rw [show 2 * input.length + 2 = (2 * input.length + 1) + 1 by omega,
    Function.iterate_succ_apply', htransfer]
  change some ⟨none, none, update (fun _ => []) true (input.map f).reverse⟩ =
    some (haltList (reverseMapComputer f) (input.map f).reverse)
  apply congrArg some
  exact (congrArg (TM2.Cfg.mk none none)
    (haltList_stk (reverseMapComputer f) (input.map f).reverse)).symm

/-- Reversing a mapped list has the linear time bound `2 * X + 2`. -/
noncomputable def reverseMapComputableInPolyTime (f : α → α) :
    TM2ComputableInPolyTime id id (fun input : List α => (input.map f).reverse) where
  tm := reverseMapComputer f
  inputAlphabet := Equiv.refl α
  outputAlphabet := Equiv.refl α
  time := 2 * X + 2
  outputsFun input := by
    simpa [List.map_id] using reverseMapOutputs f input

/-- A finite machine reverses lists in time `2 * X + 2`. -/
noncomputable def listReverseComputableInPolyTime :
    TM2ComputableInPolyTime id id (List.reverse : List α → List α) := by
  simpa using reverseMapComputableInPolyTime (id : α → α)

/-- Composing two finite transfer machines computes an order-preserving map in polynomial time. -/
noncomputable def listMapComputableInPolyTime (f : α → α) :
    TM2ComputableInPolyTime id id (List.map f) := by
  simpa [Function.comp_def] using
    listReverseComputableInPolyTime.comp (reverseMapComputableInPolyTime f)

end Turing
