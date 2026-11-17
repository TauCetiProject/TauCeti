/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Sym2

/-!
# Ordering unordered pairs

In a linear order, an unordered pair `s : Sym2 α` is reconstructed from its infimum and supremum via
`Sym2.sortEquiv`.

## Main results

* `Sym2.mk_inf_sup`: `s(s.inf, s.sup) = s` for `s : Sym2 α` in a linear order.
-/

public section

namespace Sym2

variable {α : Type*}

/-- In a linear order, an unordered pair is reconstructed from its infimum and supremum. -/
@[simp, grind =]
theorem mk_inf_sup [LinearOrder α] (s : Sym2 α) : s(s.inf, s.sup) = s := by
  simpa only [sortEquiv_symm_apply, sortEquiv_apply_coe] using sortEquiv.symm_apply_apply s

end Sym2
