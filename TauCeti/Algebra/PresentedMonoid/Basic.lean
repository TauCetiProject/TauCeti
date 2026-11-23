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
generators listed by `l` (`PresentedMonoid.mk_ofList`). Since `PresentedMonoid rels` is defined
as the quotient of `FreeMonoid α` by the congruence `conGen rels`, the class of a word is also
its coercion into that quotient (`PresentedMonoid.mk_eq_coe`), which lets functions on words
constant on `conGen rels` descend with `Con.liftOn`.
-/

public section

namespace PresentedMonoid

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop}

/-- The class of the word of a list is the product of the generators it lists. -/
theorem mk_ofList (l : List α) : mk rels (FreeMonoid.ofList l) = (l.map (of rels)).prod := by
  rw [show mk rels = FreeMonoid.lift (of rels) from
    FreeMonoid.hom_eq fun _ ↦ by rw [FreeMonoid.lift_eval_of, of], FreeMonoid.lift_ofList]

/-- The class of a word in `PresentedMonoid rels` is its coercion into the quotient by
`conGen rels`, the type that `PresentedMonoid rels` is defined to be. -/
theorem mk_eq_coe (w : FreeMonoid α) : @Eq (conGen rels).Quotient (mk rels w) w :=
  rfl

end PresentedMonoid
