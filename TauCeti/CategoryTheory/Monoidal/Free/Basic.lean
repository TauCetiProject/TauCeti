/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic

/-!
# Interpreting tensor words by tensor words

Mathlib's `FreeMonoidalCategory.projectObj f` interprets a formal tensor word by the images `f`
of its letters. Taking the images to be tensor words themselves, this is substitution into tensor
words, and it is unital and associative:

* `FreeMonoidalCategory.projectObj_of`: interpreting a word by its own letters recovers the word.
* `FreeMonoidalCategory.projectObj_projectObj`: interpreting a word after replacing its letters
  by words is interpreting it by the interpretations of those words.
-/

public section

universe u u' u'' v''

namespace CategoryTheory.FreeMonoidalCategory

open MonoidalCategory

variable {C : Type u}

/-- Interpreting a tensor word by its own letters recovers the word. -/
@[simp]
theorem projectObj_of (X : FreeMonoidalCategory C) : projectObj of X = X := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY => exact congrArg₂ tensor hX hY

/-- Interpreting a tensor word after replacing its letters by tensor words `h` is interpreting it
by the interpretations of those words. -/
theorem projectObj_projectObj {C' : Type u'} {D : Type u''} [Category.{v''} D]
    [MonoidalCategory D] (f : C' → D) (h : C → FreeMonoidalCategory C')
    (X : FreeMonoidalCategory C) :
    projectObj f (projectObj h X) = projectObj (fun a ↦ projectObj f (h a)) X := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY => exact congrArg₂ (· ⊗ ·) hX hY

end CategoryTheory.FreeMonoidalCategory
