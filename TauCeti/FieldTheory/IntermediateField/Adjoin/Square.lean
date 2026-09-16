/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Ring.Commute

/-!
# Adjoining elements with matching squares

Two sets of elements generate the same intermediate field if every element of either set has
the same square as some element of the other. This makes square-root composita independent of
the choices of signs, as needed to identify explicit genus fields with their canonical
prime-discriminant composita. No restriction on the characteristic is needed.
-/

public section

open IntermediateField

namespace TauCeti.IntermediateField

/-- Two sets with square-matching witnesses in both directions generate the same intermediate
field. The sets need not be finite, and the field may have any characteristic. -/
theorem adjoin_eq_adjoin_of_forall_sq_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    {s t : Set L} (hst : ∀ x ∈ s, ∃ y ∈ t, x ^ 2 = y ^ 2)
    (hts : ∀ y ∈ t, ∃ x ∈ s, y ^ 2 = x ^ 2) : adjoin K s = adjoin K t := by
  have le_of {s t : Set L} (h : ∀ x ∈ s, ∃ y ∈ t, x ^ 2 = y ^ 2) :
      adjoin K s ≤ adjoin K t := by
    rw [adjoin_le_iff]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h x hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with rfl | rfl
    · exact subset_adjoin K t hy
    · exact neg_mem (subset_adjoin K t hy)
  exact le_antisymm (le_of hst) (le_of hts)

end TauCeti.IntermediateField
