/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Partrec

/-!
# Computable list operations

Mathlib proves that folding, mapping and flat-mapping over lists are primitive recursive
(`Primrec.list_foldl`, `Primrec.list_map`, `Primrec.list_flatMap`), but for computable functions
it provides only a few fixed list operations. This file proves the computable counterparts: a left
fold with a computable step is computable, and so are mapping a computable function over a
computably given list and concatenating the images of a computable list-valued function. The
statements have the same shape as the primitive recursive ones, uniformly in a parameter.
-/

public section

namespace Computable

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

/-- A left fold over a computably given list, with a computable initial value and a computable
step, is computable. -/
theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} (hf : Computable f)
    (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  -- the fold over the first `n` entries of `f a`, by recursion on `n`
  have hstep : Computable fun p : α × (ℕ × σ) =>
      ((f p.1)[p.2.1]?).elim p.2.2 fun b => h p.1 (p.2.2, b) :=
    (option_casesOn (list_getElem?.comp (hf.comp fst) (fst.comp snd)) (snd.comp snd)
      (hh.comp (fst.comp fst) (pair (snd.comp (snd.comp fst)) snd)).to₂).of_eq fun p => by
        cases (f p.1)[p.2.1]? <;> rfl
  refine (nat_rec (list_length.comp hf) hg hstep.to₂).of_eq fun a => ?_
  suffices ∀ n, Nat.rec (motive := fun _ => σ) (g a)
      (fun n s => ((f a)[n]?).elim s fun b => h a (s, b)) n =
      ((f a).take n).foldl (fun s b => h a (s, b)) (g a) by
    simpa using this (f a).length
  intro n
  induction n with
  | zero => simp
  | succ n ih => cases hn : (f a)[n]? <;> simp [ih, List.take_add_one, hn]

/-- Concatenating the images of the entries of a computably given list under a computable
list-valued function is computable. -/
theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).flatMap (g a) :=
  (list_foldl hf (const []) (list_append.comp (fst.comp snd)
    (hg.comp fst (snd.comp snd))).to₂).of_eq fun _ => by rw [List.flatMap_eq_foldl]

/-- Mapping a computable function over a computably given list is computable. -/
theorem list_map {f : α → List β} {g : α → β → σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) :=
  (list_flatMap hf (list_cons.comp hg (const [])).to₂).of_eq fun _ => List.map_eq_flatMap.symm

end Computable
