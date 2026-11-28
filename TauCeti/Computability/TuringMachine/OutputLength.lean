/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Computability.TuringMachine.Computable
public import TauCeti.Computability.TuringMachine.StackOutputLength

/-!
# Output length of a polynomial-time TM2 machine

A finite TM2 program has a uniform per-step bound on stack growth. Consequently its
output grows at most linearly in its execution time, and a polynomial-time machine
has polynomially bounded output length.
-/

public section

namespace Turing

namespace FinTM2

variable (tm : FinTM2)

attribute [local instance] ΛFin

/-- The largest number of `push` instructions in a statement of this TM. -/
def maxPushes : ℕ :=
  Finset.univ.sup fun l ↦ (tm.m l).pushes

/-- Every statement of this TM has at most `tm.maxPushes` `push` instructions. -/
theorem pushes_le_maxPushes (l : tm.Λ) : (tm.m l).pushes ≤ tm.maxPushes :=
  Finset.le_sup (f := fun l ↦ (tm.m l).pushes) (Finset.mem_univ l)

end FinTM2

/-- The initial configuration stores the input on its designated stack and empties the rest. -/
@[simp]
theorem initList_stk (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk = Function.update (fun _ ↦ []) tm.k₀ s := by
  funext k
  by_cases h : k = tm.k₀
  · subst k
    simp [initList, Function.update]
  · simp [initList, Function.update, h]

/-- The halting configuration stores the output on its designated stack and empties the rest. -/
@[simp]
theorem haltList_stk (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk = Function.update (fun _ ↦ []) tm.k₁ s := by
  funext k
  by_cases h : k = tm.k₁
  · subst k
    simp [haltList, Function.update]
  · simp [haltList, Function.update, h]

/-- If `h` is a run of `tm` from `l` to `l'`, then `l'` is at most `tm.maxPushes * h.steps`
letters longer than `l`. -/
theorem TM2Outputs.length_le {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)}
    (h : TM2Outputs tm l (some l')) : l'.length ≤ l.length + tm.maxPushes * h.steps := by
  have := TM2.length_stk_le_of_evalsTo tm.pushes_le_maxPushes (b := haltList tm l') h tm.k₁
  simp only [haltList_stk, initList_stk, Function.update_self] at this
  refine this.trans (Nat.add_le_add_right ?_ _)
  by_cases hk : tm.k₁ = tm.k₀
  · rw [hk, Function.update_self]
  · simp [Function.update_of_ne hk]

/-- The output of a polynomial-time machine has polynomial length: the encoding of `f a` is at most
`h.tm.maxPushes * h.time.eval n` letters longer than the encoding of `a`, of length `n`. -/
theorem TM2ComputableInPolyTime.length_le {α β αΓ βΓ : Type} {ea : α → List αΓ}
    {eb : β → List βΓ} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + h.tm.maxPushes * h.time.eval (ea a).length := by
  have := (h.outputsFun a).toTM2Outputs.length_le
  simp only [List.length_map] at this
  exact this.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (h.outputsFun a).steps_le_m) _)

end Turing
