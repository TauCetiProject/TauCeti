/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Inequivalence and disjointness of infinite and finite places

Because an infinite place is never equivalent to a nonarchimedean absolute value
(`NumberField.InfinitePlace.not_isEquiv_of_isNonarchimedean`), an infinite place of a number field
is never equivalent or equal to a finite place (`NumberField.InfinitePlace.not_isEquiv_finitePlace`,
`NumberField.FinitePlace.not_isEquiv_infinitePlace`,
`NumberField.InfinitePlace.val_ne_finitePlace_val`,
`NumberField.FinitePlace.val_ne_infinitePlace_val`).

Thus the predicates `NumberField.IsInfinitePlace` and `NumberField.IsFinitePlace` are disjoint
(`NumberField.not_isInfinitePlace_and_isFinitePlace`), and among places of a number field the
finite ones are precisely the nonarchimedean ones
(`NumberField.isNonarchimedean_iff_isFinitePlace`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §§1.2–1.3.
-/

public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- An infinite place and a finite place of a number field have inequivalent underlying absolute
values. -/
@[simp]
theorem InfinitePlace.not_isEquiv_finitePlace (v : InfinitePlace K) (u : FinitePlace K) :
    ¬ v.val.IsEquiv u.val :=
  v.not_isEquiv_of_isNonarchimedean u.add_le

/-- A finite place and an infinite place of a number field have inequivalent underlying absolute
values. -/
@[simp]
theorem FinitePlace.not_isEquiv_infinitePlace (u : FinitePlace K) (v : InfinitePlace K) :
    ¬ u.val.IsEquiv v.val :=
  fun h ↦ v.not_isEquiv_finitePlace u h.symm

/-- An infinite place and a finite place of a number field never have the same underlying absolute
value. -/
@[simp]
theorem InfinitePlace.val_ne_finitePlace_val (v : InfinitePlace K) (u : FinitePlace K) :
    v.val ≠ u.val :=
  fun h ↦ v.not_isEquiv_finitePlace u (h ▸ .rfl)

/-- A finite place and an infinite place of a number field never have the same underlying absolute
value. -/
@[simp]
theorem FinitePlace.val_ne_infinitePlace_val (u : FinitePlace K) (v : InfinitePlace K) :
    u.val ≠ v.val :=
  (v.val_ne_finitePlace_val u).symm

/-- The underlying absolute value of an infinite place is not a finite place. -/
@[simp]
theorem InfinitePlace.not_isFinitePlace (v : InfinitePlace K) : ¬ IsFinitePlace v.val := by
  rintro ⟨𝔭, h𝔭⟩
  exact v.val_ne_finitePlace_val (FinitePlace.mk 𝔭) h𝔭.symm

/-- The underlying absolute value of a finite place is not an infinite place. -/
@[simp]
theorem FinitePlace.not_isInfinitePlace (u : FinitePlace K) : ¬ IsInfinitePlace u.val := by
  rintro ⟨φ, hφ⟩
  exact (InfinitePlace.mk φ).val_ne_finitePlace_val u hφ

/-- No absolute value on a number field is simultaneously an infinite place and a finite place. -/
theorem not_isInfinitePlace_and_isFinitePlace (w : AbsoluteValue K ℝ) :
    ¬ (IsInfinitePlace w ∧ IsFinitePlace w) := by
  rintro ⟨hinf, hfin⟩
  obtain ⟨v, rfl⟩ := (isInfinitePlace_iff w).mp hinf
  exact v.not_isFinitePlace hfin

/-- Among the places of a number field, the finite places are precisely the nonarchimedean ones. -/
theorem isNonarchimedean_iff_isFinitePlace {w : AbsoluteValue K ℝ}
    (hw : IsInfinitePlace w ∨ IsFinitePlace w) :
    IsNonarchimedean w ↔ IsFinitePlace w := by
  refine ⟨fun hna ↦ hw.resolve_left fun hinf ↦ ?_, fun hfin ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := (isInfinitePlace_iff w).mp hinf
    exact v.not_isNonarchimedean hna
  · obtain ⟨u, rfl⟩ := (isFinitePlace_iff w).mp hfin
    exact u.add_le

end NumberField
