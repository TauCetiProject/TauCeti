/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# Realization of first-order terms depends only on their left variables

`FirstOrder.Language.Term.realize_congr_varFinsetLeft` says that a term over `α ⊕ β` has the same
realization under two valuations of `α` that agree on the variables `Term.varFinsetLeft` it
mentions. It is derived from Mathlib's `Term.realize_restrictVarLeft'`, since Mathlib has no
direct congruence lemma of this form.
-/

public section

namespace FirstOrder

namespace Language

namespace Term

variable {L : Language} {α β M : Type*} [L.Structure M]

/-- A term over `α ⊕ β` has the same realization under two valuations of `α` that agree on the
variables `Term.varFinsetLeft` of `α` it mentions. -/
theorem realize_congr_varFinsetLeft [DecidableEq α] {t : L.Term (α ⊕ β)} {v v' : α → M}
    (h : Set.EqOn v v' t.varFinsetLeft) (xs : β → M) :
    t.realize (Sum.elim v xs) = t.realize (Sum.elim v' xs) := by
  rw [← realize_restrictVarLeft' subset_rfl (v := v),
    ← realize_restrictVarLeft' subset_rfl (v := v'), ← Set.domRestrict_eq, ← Set.domRestrict_eq,
    Set.domRestrict_eq_domRestrict_iff.2 h]

end Term

end Language

end FirstOrder
