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
-/

public section

namespace FreeGroup

variable {α β : Type*}

/-- Replace a signed letter by the word assigned to its generator, reversing and inverting
the assigned word for a negative letter. -/
def substituteLetter (f : α → List (β × Bool)) (a : α × Bool) : List (β × Bool) :=
  bif a.2 then f a.1 else invRev (f a.1)

/-- A positive letter is replaced by its assigned word. -/
@[simp] theorem substituteLetter_true (f : α → List (β × Bool)) (a : α) :
    substituteLetter f (a, true) = f a := by simp [substituteLetter]

/-- A negative letter is replaced by the inverse of its assigned word. -/
@[simp] theorem substituteLetter_false (f : α → List (β × Bool)) (a : α) :
    substituteLetter f (a, false) = invRev (f a) := by simp [substituteLetter]

/-- Substitute words for the generators of a word and freely reduce the result. -/
def substituteWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) : List (β × Bool) :=
  reduce (w.flatMap (substituteLetter f))

/-- Substitution agrees with the universal homomorphism from the free group. -/
theorem mk_substituteWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) :
    mk (substituteWord f w) = lift (fun a => mk (f a)) (mk w) := by
  simp only [substituteWord, reduce.self]
  induction w with
  | nil => simp only [List.flatMap_nil, ← one_eq_mk, _root_.map_one]
  | cons a w ih =>
    rw [List.flatMap_cons, ← mul_mk, ih]
    have h : mk (a :: w) = mk [a] * mk w := by simp only [mul_mk, List.singleton_append]
    rw [h, _root_.map_mul]
    cases a with
    | mk x b =>
      cases b <;> simp [substituteLetter, inv_mk, lift_mk]

/-- Substitution computes the reduced word of the induced free-group homomorphism. -/
@[simp] theorem substituteWord_eq_toWord [DecidableEq β] (f : α → List (β × Bool))
    (w : List (α × Bool)) :
    substituteWord f w = (lift (fun a => mk (f a)) (mk w)).toWord := by
  rw [← mk_substituteWord, toWord_mk]
  exact (reduce.idem).symm

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
