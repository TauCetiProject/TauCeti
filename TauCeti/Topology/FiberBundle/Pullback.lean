/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Pullbacks of fibre bundles

Two facts about Mathlib's pullback bundle `f *ᵖ E`, whose fibre over `x` is the fibre of `E` over
`f x`, needed to pull back bundles with extra structure on their fibres or on their atlas.

* The fibres of `f *ᵖ E` carry the actions of a monoid on the fibres of `E`
  (`Bundle.Pullback.instMulAction`), as Mathlib already does for module structures. This is what
  makes the pullback of a principal bundle again carry a right action on its fibres.
* The coordinate change between the pullbacks `e.pullback f` and `e'.pullback f` of two
  trivializations, over a point `x` with `f x` in the base set of `e`, is the coordinate change
  between `e` and `e'` over `f x` (`Bundle.Trivialization.coordChange_pullback`). This transfers
  regularity of the coordinate changes of `E` to those of `f *ᵖ E`.
-/

public section

open Bundle

variable {B B' : Type*}

/-- The fibres of a pullback bundle `f *ᵖ E` carry the actions on the fibres of `E`: the fibre over
`x` is the fibre of `E` over `f x`. -/
instance Bundle.Pullback.instMulAction {M : Type*} [Monoid M] {E : B → Type*}
    [i : ∀ b, MulAction M (E b)] (f : B' → B) (x : B') : MulAction M ((f *ᵖ E) x) :=
  i (f x)

variable {F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, Nonempty (E b)] {K : Type*} [FunLike K B' B]
  [ContinuousMapClass K B' B]

/-- The coordinate change between the pullbacks of two trivializations, over a point `x` whose
image `f x` lies in the base set of the first, is the coordinate change between the
trivializations over `f x`. -/
theorem Bundle.Trivialization.coordChange_pullback (e e' : Trivialization F (π F E)) (f : K)
    {x : B'} (hx : f x ∈ e.baseSet) (v : F) :
    (e.pullback f).coordChange (e'.pullback f) x v = e.coordChange e' (f x) v := by
  rw [Trivialization.coordChange, Trivialization.coordChange, Trivialization.pullback_apply,
    ← e.mk_symm hx]
  -- By construction, the inverse of `e.pullback f` sends `(x, v)` to the point `e.symm (f x) v` of
  -- the fibre over `x`, and `Pullback.lift f` sends that point to `⟨f x, e.symm (f x) v⟩`.
  rfl
