/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Computability

/-!
# Primitive-recursive substitution of free-group words

A substitution specified by a primitive-recursive table of words is primitive recursive on
the standard signed-letter list codes. The result is reduced after substitution, so it is
the canonical representative of the value of `FreeGroup.lift`. This supplies the word
substitutions used when evaluating finite systems of equations over free groups.

Substitution without free reduction is also recorded, for words in variables and constant
letters (`FreeGroup.substituteVars`): it is the substitution in Makanin's generalised equations,
where both sides must agree letter by letter.
-/

public section

namespace FreeGroup

variable {α β : Type*}

/-- Replace a signed letter by the word assigned to its generator, reversing and inverting
the assigned word for a negative letter. -/
@[expose] def substituteLetter (f : α → List (β × Bool)) (a : α × Bool) : List (β × Bool) :=
  bif a.2 then f a.1 else invRev (f a.1)

/-- A positive letter is replaced by its assigned word. -/
@[simp] theorem substituteLetter_true (f : α → List (β × Bool)) (a : α) :
    substituteLetter f (a, true) = f a := by simp [substituteLetter]

/-- A negative letter is replaced by the inverse of its assigned word. -/
@[simp] theorem substituteLetter_false (f : α → List (β × Bool)) (a : α) :
    substituteLetter f (a, false) = invRev (f a) := by simp [substituteLetter]

/-- Substitution without free reduction commutes with formal inverses. -/
theorem flatMap_substituteLetter_invRev (f : α → List (β × Bool)) (w : List (α × Bool)) :
    (invRev w).flatMap (substituteLetter f) = invRev (w.flatMap (substituteLetter f)) := by
  induction w with
  | nil => simp [invRev_empty]
  | cons a w ih =>
    rw [invRev_cons, List.flatMap_append, ih, List.flatMap_cons, invRev_append]
    congr 1
    have hs : invRev [a] = [(a.1, !a.2)] := by simp [invRev]
    obtain ⟨x, _ | _⟩ := a <;> simp [hs, invRev_invRev]

/-- Substitution without free reduction agrees with the universal homomorphism from the free
group. -/
theorem mk_flatMap_substituteLetter (f : α → List (β × Bool)) (w : List (α × Bool)) :
    mk (w.flatMap (substituteLetter f)) = lift (fun a => mk (f a)) (mk w) := by
  induction w with
  | nil => simp only [List.flatMap_nil, ← one_eq_mk, _root_.map_one]
  | cons a w ih =>
    rw [List.flatMap_cons, ← mul_mk, ih]
    have h : mk (a :: w) = mk [a] * mk w := by simp only [mul_mk, List.singleton_append]
    rw [h, _root_.map_mul]
    cases a with
    | mk x b =>
      cases b <;> simp [substituteLetter, inv_mk, lift_mk]

/-- Substitute words for the generators of a word and freely reduce the result. -/
def substituteWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) : List (β × Bool) :=
  reduce (w.flatMap (substituteLetter f))

/-- Substitution agrees with the universal homomorphism from the free group. -/
theorem mk_substituteWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) :
    mk (substituteWord f w) = lift (fun a => mk (f a)) (mk w) := by
  rw [substituteWord, reduce.self, mk_flatMap_substituteLetter]

/-- Substitution computes the reduced word of the induced free-group homomorphism. -/
@[simp] theorem substituteWord_eq_toWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) :
    substituteWord f w = (lift (fun a => mk (f a)) (mk w)).toWord := by
  rw [← mk_substituteWord, toWord_mk]
  exact (reduce.idem).symm

section Vars

variable {X A : Type*}

/-- Substitute words over `A^{±1}` for the variables of a word in variables `X` and letters of
`A`, without free reduction: a variable `x` becomes `U x`, its inverse becomes the formal inverse
of `U x`, and a letter of `A^{±1}` is kept. -/
@[expose] def substituteVars (U : X → List (A × Bool)) (w : List ((X ⊕ A) × Bool)) :
    List (A × Bool) :=
  w.flatMap (substituteLetter (Sum.elim U fun a => [(a, true)]))

@[simp]
theorem substituteVars_nil (U : X → List (A × Bool)) : substituteVars U [] = [] :=
  List.flatMap_nil

/-- Substitution proceeds letter by letter. -/
theorem substituteVars_cons (U : X → List (A × Bool)) (y : (X ⊕ A) × Bool)
    (w : List ((X ⊕ A) × Bool)) :
    substituteVars U (y :: w) = substituteVars U [y] ++ substituteVars U w := by
  simp [substituteVars]

@[simp]
theorem substituteVars_append (U : X → List (A × Bool)) (w w' : List ((X ⊕ A) × Bool)) :
    substituteVars U (w ++ w') = substituteVars U w ++ substituteVars U w' :=
  List.flatMap_append

/-- A positive variable is replaced by its assigned word. -/
@[simp]
theorem substituteVars_singleton_inl (U : X → List (A × Bool)) (x : X) :
    substituteVars U [(Sum.inl x, true)] = U x := by
  simp [substituteVars]

/-- A negative variable is replaced by the formal inverse of its assigned word. -/
@[simp]
theorem substituteVars_singleton_inl_false (U : X → List (A × Bool)) (x : X) :
    substituteVars U [(Sum.inl x, false)] = invRev (U x) := by
  simp [substituteVars]

/-- A letter of `A^{±1}` is kept. -/
@[simp]
theorem substituteVars_singleton_inr (U : X → List (A × Bool)) (a : A) (b : Bool) :
    substituteVars U [(Sum.inr a, b)] = [(a, b)] := by
  cases b <;> simp [substituteVars, invRev]

/-- A word of positive variables is replaced by the concatenation of their assigned words. -/
theorem substituteVars_map_inl (U : X → List (A × Bool)) (l : List X) :
    substituteVars U (l.map fun x => (Sum.inl x, true)) = l.flatMap U := by
  simp [substituteVars, List.flatMap_map]

/-- Substitution without free reduction commutes with formal inverses. -/
theorem substituteVars_invRev (U : X → List (A × Bool)) (w : List ((X ⊕ A) × Bool)) :
    substituteVars U (invRev w) = invRev (substituteVars U w) :=
  flatMap_substituteLetter_invRev _ w

/-- Substitution followed by free reduction is evaluation in the free group. -/
theorem mk_substituteVars (U : X → List (A × Bool)) (w : List ((X ⊕ A) × Bool)) :
    mk (substituteVars U w) = lift (Sum.elim (fun x => mk (U x)) of) (mk w) := by
  rw [substituteVars, mk_flatMap_substituteLetter]
  congr 2
  funext y
  -- `of a` is the one-letter word `mk [(a, true)]` by definition.
  cases y <;> rfl

end Vars

variable [Primcodable α] [Primcodable β]

/-- The signed-letter substitution determined by a primitive-recursive word table is
primitive recursive. -/
theorem primrec_substituteLetter (f : α → List (β × Bool)) (hf : Primrec f) :
    Primrec (substituteLetter f) := by
  unfold substituteLetter
  exact Primrec.cond (Primrec.snd)
    (hf.comp Primrec.fst) (primrec_invRev.comp (hf.comp Primrec.fst))

/-- Substitution followed by free reduction is primitive recursive on word codes. -/
theorem primrec_substituteWord [DecidableEq β] (f : α → List (β × Bool))
    (hf : Primrec f) : Primrec (substituteWord f) := by
  unfold substituteWord
  exact primrec_reduce.comp
    (Primrec.list_flatMap Primrec.id
      ((primrec_substituteLetter f hf).comp Primrec.snd).to₂)

/-- Evaluating a word under a primitive-recursive assignment of words is
primitive recursive, with the reduced word of the value as output. -/
theorem primrec_toWord_lift_mk [DecidableEq β] (f : α → List (β × Bool))
    (hf : Primrec f) :
    Primrec fun w : List (α × Bool) => (lift (fun a => mk (f a)) (mk w)).toWord := by
  simpa only [← substituteWord_eq_toWord] using primrec_substituteWord f hf

/-- A primitive-recursive map of alphabets induces a primitive-recursive map on reduced
representatives of free-group elements. -/
theorem primrec_toWord_map_mk [DecidableEq β] (g : α → β) (hg : Primrec g) :
    Primrec fun w : List (α × Bool) => (map g (mk w)).toWord := by
  have htable : Primrec fun a : α => ([(g a, true)] : List (β × Bool)) :=
    Primrec.list_cons.comp (Primrec.pair hg (Primrec.const true)) (Primrec.const [])
  simpa only [map_eq_lift, Function.comp_def, of] using
    (primrec_toWord_lift_mk (fun a : α => [(g a, true)]) htable)

end FreeGroup
