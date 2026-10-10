/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Computability.Partrec

/-!
# Computable list operations

Computability of left and right folds, list recursion, and list mapping.
-/

public section

namespace Computable

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

/-- A left fold of computable data by a computable step is computable. -/
theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} (hf : Computable f)
    (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  have : Computable₂ fun a (p : ℕ × σ) =>
      Option.casesOn (motive := fun _ => σ) (f a)[p.1]? p.2 fun b => h a (p.2, b) :=
    option_casesOn (list_getElem?.comp (hf.comp fst) (fst.comp snd)) (snd.comp snd)
      (hh.comp (fst.comp fst) (pair ((snd.comp snd).comp fst) snd)).to₂
  refine (nat_rec (list_length.comp hf) hg this).of_eq fun a => ?_
  conv_rhs => rw [← List.take_length (l := f a)]
  induction (f a).length with
  | zero => rfl
  | succ n IH => cases e : (f a)[n]? <;> simp [IH, List.take_add_one, e]

/-- A right fold of computable data by a computable step is computable. -/
theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Computable f)
    (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]

/-- Primitive recursion over a computable list is computable. -/
theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : Computable f)
    (hg : Computable g) (hh : Computable₂ h) :
    @Computable _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Computable F :=
    list_foldr hf (pair (const []) hg) <|
      to₂ <| pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    dsimp [F]
    induction f a <;> simp [*]

/-- Mapping a computable function over a computable list is computable. -/
theorem list_map {f : α → List β} {g : α → β → σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]


end Computable
