/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import TauCeti.Computability.StateTransition.Induction

/-!
# Stack length bounds for TM2 programs

Count the pushes in a statement and bound the growth of every stack during an execution.
-/

public section

namespace Turing.TM2

open Stmt

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- The number of `push` instructions in a statement. -/
def Stmt.pushes : Stmt Γ Λ σ → ℕ
  | push _ _ q => q.pushes + 1
  | peek _ _ q | pop _ _ q | load _ q => q.pushes
  | branch _ q₁ q₂ => q₁.pushes + q₂.pushes
  | goto _ | halt => 0

variable [DecidableEq K]

/-- Running a statement adds to each stack at most as many letters as the statement has `push`
instructions. -/
theorem length_stk_stepAux_le (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((stepAux q v S).stk k).length ≤ (S k).length + q.pushes := by
  induction q generalizing v S with
  | push k' f q ih | pop k' f q ih =>
    refine (ih _ _).trans ?_
    obtain rfl | h := eq_or_ne k k' <;> simp [Stmt.pushes, *] <;> omega
  | branch f q₁ q₂ ih₁ ih₂ =>
    rw [stepAux, Stmt.pushes]
    cases f v
    · exact (ih₂ v S).trans (by omega)
    · exact (ih₁ v S).trans (by omega)
  | peek _ _ _ ih | load _ _ ih => exact ih _ S
  | goto _ | halt => exact Nat.le_add_right _ _

/-- Along a run `h` of a program whose statements have at most `c` pushes each, each stack gains
at most `c * h.steps` letters. -/
theorem length_stk_le_of_evalsTo {M : Λ → Stmt Γ Λ σ} {c : ℕ} (hM : ∀ l, (M l).pushes ≤ c)
    {a b : Cfg Γ Λ σ} (h : StateTransition.EvalsTo (step M) a (some b)) (k : K) :
    (b.stk k).length ≤ (a.stk k).length + c * h.steps := by
  refine h.induction_on (fun n x ↦ (x.stk k).length ≤ (a.stk k).length + c * n)
    (Nat.le_add_right _ _) fun n x y hx hxy ↦ ?_
  obtain ⟨_ | l, v, S⟩ := x <;> cases hxy
  grw [length_stk_stepAux_le, hx, hM, Nat.mul_add_one, Nat.add_assoc]


end Turing.TM2
