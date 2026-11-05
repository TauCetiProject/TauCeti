/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Primitive-recursive evaluation of free-group words

If a primitively encoded group has primitive-recursive multiplication and inversion,
evaluating signed-letter words is primitive recursive. The assignment of generators may
vary in a primitive-recursive family. In particular, evaluation is primitive recursive
jointly in a finite table `Fin n → G` and the input word, using Mathlib's standard encoding
of finite functions.

The value is `FreeGroup.lift` applied to the element represented by the word, not an
alternative evaluation operation or free-group carrier. Inputs need not be reduced, and
both empty words and an empty generator table are allowed. This provides evaluation on
finite descriptions of equations over encoded groups.

The proof uses Mathlib's `FreeGroup.lift_mk` and `Primrec.list_foldr`.
-/

public section

namespace FreeGroup

variable {P α G : Type*} [Primcodable P] [Primcodable α] [Primcodable G] [Group G]

/-- Evaluation of words under a primitive-recursive family of generator assignments is
primitive recursive jointly in the family parameter and the word. -/
theorem primrec₂_lift_mk (hmul : Primrec₂ ((· * ·) : G → G → G))
    (hinv : Primrec (Inv.inv : G → G)) {f : P → α → G} (hf : Primrec₂ f) :
    Primrec₂ fun p (w : List (α × Bool)) => lift (f p) (mk w) := by
  have letter : Primrec₂ fun p (a : α × Bool) =>
      cond a.2 (f p a.1) (f p a.1)⁻¹ := by
    exact (Primrec.cond (Primrec.snd.comp Primrec.snd)
      (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (hinv.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))).to₂
  apply Primrec₂.mk
  refine (Primrec.list_foldr Primrec.snd (Primrec.const (1 : G))
    (hmul.comp (letter.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun p => ?_
  simp only [lift_mk, List.prod_eq_foldr, List.foldr_map]

/-- For a finite basis, word evaluation is primitive recursive uniformly in the entire
assignment table, including rank zero. The table uses Mathlib's finite-function encoding. -/
theorem primrec₂_lift_mk_fin (hmul : Primrec₂ ((· * ·) : G → G → G))
    (hinv : Primrec (Inv.inv : G → G)) (n : ℕ) :
    Primrec₂ fun (f : Fin n → G) (w : List (Fin n × Bool)) => lift f (mk w) :=
  primrec₂_lift_mk hmul hinv Primrec.fin_app

end FreeGroup
