/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.LanguageMap

/-!
# Language maps for adjoining constants

The relation map of `lhomWithConstants` inverts the elimination of the empty summand of
`L[[γ]].Relations n` by `Equiv.sumEmpty`.
-/

public section

namespace FirstOrder.Language

variable {L : Language} {γ : Type*}

theorem lhomWithConstants_onRelation_sumEmpty {l : ℕ} (R : L[[γ]].Relations l) :
    (L.lhomWithConstants γ).onRelation ((Equiv.sumEmpty _ _) R) = R := by
  -- lhomWithConstants is sumInl, so its relation map restores the left summand.
  cases R with
  | inl R => rfl
  | inr R => exact R.elim

end FirstOrder.Language
