/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.PresentedMonoid.Basic

/-!
# Words in a presented monoid

The class in `PresentedMonoid rels` of the word `FreeMonoid.ofList l` is the product of the
generators listed by `l` (`PresentedMonoid.mk_ofList`). A function on words that is constant on
the classes of the congruence `conGen rels` descends to `PresentedMonoid rels`
(`PresentedMonoid.liftOn`), and its value on the class of a word is its value on the word
(`PresentedMonoid.liftOn_mk`).
-/

public section

namespace PresentedMonoid

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop}

/-- The class of the word of a list is the product of the generators it lists. -/
theorem mk_ofList (l : List α) : mk rels (FreeMonoid.ofList l) = (l.map (of rels)).prod := by
  rw [show mk rels = FreeMonoid.lift (of rels) from
    FreeMonoid.hom_eq fun _ ↦ by rw [FreeMonoid.lift_eval_of, of], FreeMonoid.lift_ofList]

/-- Descend a function on words that is constant on the classes of `conGen rels` to the presented
monoid. This is `Con.liftOn` for `conGen rels`, since `PresentedMonoid rels` is defined to be the
quotient of `FreeMonoid α` by `conGen rels`. -/
protected def liftOn {β : Sort*} (x : PresentedMonoid rels) (f : FreeMonoid α → β)
    (h : ∀ w v, conGen rels w v → f w = f v) : β :=
  Con.liftOn (c := conGen rels) x f h

/-- A function descended with `PresentedMonoid.liftOn` takes its value on the class of a word to
its value on the word. -/
@[simp]
theorem liftOn_mk {β : Sort*} (w : FreeMonoid α) (f : FreeMonoid α → β)
    (h : ∀ w v, conGen rels w v → f w = f v) : (mk rels w).liftOn f h = f w :=
  Con.liftOn_coe (conGen rels) f h w

end PresentedMonoid
