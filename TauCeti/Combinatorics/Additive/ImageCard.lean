/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Set.Card

/-!
# Counting images of a finite set under two homomorphisms

Let `S` be a finite subset of an additive group `A`, and let `f` and `g` be additive
homomorphisms out of `A`. Two elements of `S` with the same image under `g` differ by an element
of `(S - S) ∩ ker g`. So `f '' S` is covered by the right translates of
`f '' ((S - S) ∩ ker g)` by the images under `f` of one representative of each fibre of `g` on
`S`, and

`#(f '' S) ≤ #(g '' S) · #(f '' ((S - S) ∩ ker g))`.

For quotient maps `f = π_{V'}` and `g = π_V` modulo subspaces `V'` and `V`, this bounds the
number of classes of the differences of `S` lying in `V` from below by `#π_{V'}(S) / #π_V(S)`.

## Main results

* `AddMonoidHom.ncard_image_le_mul_ncard_image_sub_inter_ker`: the inequality above.
-/

public section

open Set
open scoped Pointwise

namespace AddMonoidHom

variable {A B C : Type*} [AddGroup A] [AddZeroClass B] [AddZeroClass C]

/-- The image of a finite set `S` under `f` has at most `#(g '' S) · #(f '' ((S - S) ∩ ker g))`
elements: each element of `S` is a difference of elements of `S` lying in `ker g` plus a
representative of its fibre under `g`. -/
theorem ncard_image_le_mul_ncard_image_sub_inter_ker (f : A →+ B) (g : A →+ C) {S : Set A}
    (hS : S.Finite) :
    (f '' S).ncard ≤ (g '' S).ncard * (f '' ((S - S) ∩ g.ker)).ncard := by
  have hfin : ((g '' S) ×ˢ (f '' ((S - S) ∩ g.ker))).Finite :=
    (hS.image g).prod (((hS.sub hS).inter_of_left _).image f)
  calc (f '' S).ncard
      ≤ ((fun p : C × B ↦ p.2 + f (Function.invFunOn g S p.1)) ''
          ((g '' S) ×ˢ (f '' ((S - S) ∩ g.ker)))).ncard := by
        refine ncard_le_ncard ?_ (hfin.image _)
        rintro _ ⟨s, hs, rfl⟩
        have hex : ∃ r ∈ S, g r = g s := ⟨s, hs, rfl⟩
        set r := Function.invFunOn g S (g s)
        have hker : s - r ∈ g.ker := by
          rw [mem_ker, sub_eq_add_neg, map_add, ← Function.invFunOn_eq hex, ← map_add,
            add_neg_cancel, map_zero]
        exact ⟨(g s, f (s - r)), ⟨⟨s, hs, rfl⟩, _, ⟨sub_mem_sub hs (Function.invFunOn_mem hex),
          hker⟩, rfl⟩, (map_add f _ _).symm.trans (congrArg f (sub_add_cancel _ _))⟩
    _ ≤ ((g '' S) ×ˢ (f '' ((S - S) ∩ g.ker))).ncard := ncard_image_le hfin
    _ = (g '' S).ncard * (f '' ((S - S) ∩ g.ker)).ncard := ncard_prod

end AddMonoidHom
