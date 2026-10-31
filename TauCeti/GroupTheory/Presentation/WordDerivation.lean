/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Relator
import Mathlib.Data.List.Rotate

/-!
# Checked derivations of signed-word relations

Words are evaluated through a homomorphism from the free group. Rotations, inverses,
products and conjugates preserve the identity relation. Comparing free reductions
therefore certifies consequence steps and rewrites of rotated target words.
The homomorphism can be the quotient map of an exact presentation; no finiteness
or injectivity hypothesis is needed.
-/

public section

namespace TauCeti.PresentationWord

variable {α G : Type*} [Group G]

/-- Evaluate a signed word through a homomorphism from its free group. -/
@[expose]
def eval (f : FreeGroup α →* G) (w : PresentationWord α) : G :=
  f (FreeGroup.mk w)

/-- Concatenation evaluates to multiplication in the target group. -/
theorem eval_append (f : FreeGroup α →* G) (u v : PresentationWord α) :
    eval f (u ++ v) = eval f u * eval f v := by
  simp only [eval, ← FreeGroup.mul_mk, map_mul]

/-- Reversing a word and inverting its letters evaluates to inversion. -/
theorem eval_invRev (f : FreeGroup α →* G) (w : PresentationWord α) :
    eval f (FreeGroup.invRev w) = (eval f w)⁻¹ := by
  simp only [eval, ← FreeGroup.inv_mk, map_inv]

/-- Equal free reductions have equal evaluations under any group homomorphism. -/
theorem eval_eq_of_reduce_eq [DecidableEq α] (f : FreeGroup α →* G)
    {u v : PresentationWord α} (h : FreeGroup.reduce u = FreeGroup.reduce v) :
    eval f u = eval f v :=
  congrArg f (FreeGroup.reduce.exact h)

/-- Cyclic rotation preserves and reflects the identity relation. -/
theorem eval_rotate_eq_one_iff (f : FreeGroup α →* G) (w : PresentationWord α) (n : ℕ) :
    eval f (w.rotate n) = 1 ↔ eval f w = 1 := by
  rw [List.rotate_eq_drop_append_take_mod, eval_append, mul_eq_one_comm,
    ← eval_append, List.take_append_drop]

/-- Optionally invert a word, then rotate it to the left by the given number of letters. -/
@[expose]
def variant (w : PresentationWord α) (invert : Bool) (shift : ℕ) : PresentationWord α :=
  (if invert then FreeGroup.invRev w else w).rotate shift

/-- Inversion followed by rotation preserves and reflects the identity relation. -/
theorem eval_variant_eq_one_iff (f : FreeGroup α →* G) (w : PresentationWord α)
    (invert : Bool) (shift : ℕ) :
    eval f (variant w invert shift) = 1 ↔ eval f w = 1 := by
  cases invert <;> simp [variant, eval_rotate_eq_one_iff, eval_invRev]

/-- A free-reduction comparison with a conjugate transports the identity relation. -/
theorem eval_eq_one_of_reduced_conjugate [DecidableEq α] (f : FreeGroup α →* G)
    {w core : PresentationWord α} (q : PresentationWord α) (hw : eval f w = 1)
    (hred : FreeGroup.reduce w =
      FreeGroup.reduce (q ++ core ++ FreeGroup.invRev q)) : eval f core = 1 := by
  have heq := eval_eq_of_reduce_eq f hred
  rw [eval_append, eval_append, eval_invRev] at heq
  exact conj_eq_one_iff.mp (heq.symm.trans hw)

/-- A checked product of variants derives an output relation from two known relations. -/
theorem eval_variant_product_eq_one [DecidableEq α] (f : FreeGroup α →* G)
    {u v w : PresentationWord α} (hu : eval f u = 1) (hv : eval f v = 1)
    (left right result : Bool × ℕ) (q : PresentationWord α)
    (hred : FreeGroup.reduce (variant u left.1 left.2 ++ variant v right.1 right.2) =
      FreeGroup.reduce (q ++ variant w result.1 result.2 ++ FreeGroup.invRev q)) :
    eval f w = 1 := by
  apply (eval_variant_eq_one_iff f w result.1 result.2).mp
  apply eval_eq_one_of_reduced_conjugate f q ?_ hred
  rw [eval_append, (eval_variant_eq_one_iff f u left.1 left.2).mpr hu,
    (eval_variant_eq_one_iff f v right.1 right.2).mpr hv, mul_one]

end TauCeti.PresentationWord
