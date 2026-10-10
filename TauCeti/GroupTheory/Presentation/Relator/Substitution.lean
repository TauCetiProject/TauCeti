/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Relator

/-!
# Substitution in relator expressions

Published presentations often abbreviate a word by a new generator name. `Relator.substitute`
expands such abbreviations while retaining the expression's powers and commutators.
`Relator.toWord_substitute` proves that expansion agrees with signed-word substitution;
`Relator.toFreeGroup_substitute` identifies the induced free-group homomorphism.

Substitution does not perform free reduction. In particular, the length formula counts all letters
of the expanded word, including letters that might subsequently cancel.
-/

public section

namespace TauCeti.Relator

variable {α β γ : Type*}

/-- Replace each generator by a relator expression, preserving the surrounding operations. -/
def substitute (f : α → Relator β) : Relator α → Relator β
  | .gen a => f a
  | .inv r => .inv (substitute f r)
  | .mul r s => .mul (substitute f r) (substitute f s)
  | .pow r n => .pow (substitute f r) n
  | .comm r s => .comm (substitute f r) (substitute f s)

/-- Substitution at a generator uses its assigned expression. -/
@[simp]
theorem substitute_gen (f : α → Relator β) (a : α) :
    substitute f (.gen a) = f a := by
  rw [substitute]

/-- Substitution commutes with inversion. -/
@[simp]
theorem substitute_inv (f : α → Relator β) (r : Relator α) :
    substitute f (.inv r) = .inv (substitute f r) := by
  rw [substitute]

/-- Substitution commutes with multiplication. -/
@[simp]
theorem substitute_mul (f : α → Relator β) (r s : Relator α) :
    substitute f (.mul r s) = .mul (substitute f r) (substitute f s) := by
  rw [substitute]

/-- Substitution commutes with natural powers. -/
@[simp]
theorem substitute_pow (f : α → Relator β) (r : Relator α) (n : ℕ) :
    substitute f (.pow r n) = .pow (substitute f r) n := by
  rw [substitute]

/-- Substitution commutes with commutators. -/
@[simp]
theorem substitute_comm (f : α → Relator β) (r s : Relator α) :
    substitute f (.comm r s) = .comm (substitute f r) (substitute f s) := by
  rw [substitute]

/-- Replacing each generator by itself leaves the expression unchanged. -/
@[simp]
theorem substitute_id (r : Relator α) : substitute .gen r = r := by
  induction r <;> simp_all

/-- Successive substitutions compose by substituting in each assigned expression. -/
@[simp]
theorem substitute_substitute (g : β → Relator γ) (f : α → Relator β) (r : Relator α) :
    substitute g (substitute f r) = substitute (fun a => substitute g (f a)) r := by
  induction r <;> simp_all

private theorem flatMap_invRev (f : α → PresentationWord β) (w : PresentationWord α) :
    (FreeGroup.invRev w).flatMap (fun p => if p.2 then f p.1 else FreeGroup.invRev (f p.1)) =
      FreeGroup.invRev
        (w.flatMap (fun p => if p.2 then f p.1 else FreeGroup.invRev (f p.1))) := by
  induction w with
  | nil => simp
  | cons p w ih =>
    obtain ⟨a, b⟩ := p
    rw [FreeGroup.invRev_cons, List.flatMap_append, ih, List.flatMap_cons,
      FreeGroup.invRev_append]
    have hs : FreeGroup.invRev [(a, b)] = [(a, !b)] := rfl
    rw [hs]
    cases b <;> simp

/-- Compiling a substitution replaces positive letters by the assigned words and negative letters
by their reversed inverses. The equality is of literal words, before free reduction. -/
theorem toWord_substitute (f : α → Relator β) (r : Relator α) :
    (substitute f r).toWord =
      r.toWord.flatMap (fun p => if p.2 then (f p.1).toWord
        else FreeGroup.invRev (f p.1).toWord) := by
  induction r with
  | gen a => simp
  | inv r ih => simp [ih, flatMap_invRev (fun a => (f a).toWord)]
  | mul r s ihr ihs => simp [ihr, ihs, List.flatMap_append]
  | pow r n ih =>
    simp only [substitute_pow, toWord_pow, ih]
    induction n with
    | zero => simp
    | succ n ihn => simp [List.replicate_succ, List.flatMap_append, ihn]
  | comm r s ihr ihs => simp [ihr, ihs, List.flatMap_append, flatMap_invRev (fun a => (f a).toWord)]

/-- Interpreting a substitution applies the free-group homomorphism determined by its generator
assignments. No injectivity or relations on those assignments are required. -/
@[simp]
theorem toFreeGroup_substitute (f : α → Relator β) (r : Relator α) :
    (substitute f r).toFreeGroup =
      FreeGroup.lift (fun a => (f a).toFreeGroup) r.toFreeGroup := by
  induction r <;> simp_all [commutatorElement_def]

/-- The expanded length is the sum of the assigned expression lengths over all signed letters of
the original compiled word. This counts unreduced letters, regardless of their signs. -/
theorem length_substitute (f : α → Relator β) (r : Relator α) :
    (substitute f r).length = (r.toWord.map (fun p => (f p.1).length)).sum := by
  rw [← length_toWord, toWord_substitute, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro p _
  cases p.2 <;> simp

end TauCeti.Relator
