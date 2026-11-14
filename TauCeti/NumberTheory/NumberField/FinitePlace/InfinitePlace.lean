/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Inequivalence and disjointness of infinite and finite places

An infinite place of a field is archimedean (`NumberField.InfinitePlace.not_isNonarchimedean`),
whereas every positive real power of a nonarchimedean absolute value remains nonarchimedean
(`AbsoluteValue.isNonarchimedean_nonarchRpow`). Consequently an infinite place is never equivalent
to a nonarchimedean absolute value (`NumberField.InfinitePlace.not_isEquiv_of_isNonarchimedean`),
and in particular never equivalent or equal to a finite place of a number field
(`NumberField.InfinitePlace.not_isEquiv_finitePlace`,
`NumberField.InfinitePlace.val_ne_finitePlace_val`).

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

section Field

variable {K : Type*} [Field K]

/-- An infinite place is never equivalent to a nonarchimedean absolute value. -/
theorem InfinitePlace.not_isEquiv_of_isNonarchimedean (v : InfinitePlace K)
    {w : AbsoluteValue K ℝ} (hw : IsNonarchimedean w) : ¬ v.1.IsEquiv w := by
  intro h
  obtain ⟨c, hc, hcw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp h.symm
  have hv : v.1 = w.nonarchRpow hw hc :=
    AbsoluteValue.ext fun x ↦ by rw [w.nonarchRpow_apply, ← congrFun hcw x]
  exact v.not_isNonarchimedean (hv ▸ w.isNonarchimedean_nonarchRpow hw hc)

end Field

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- An infinite place and a finite place of a number field have inequivalent underlying absolute
values. -/
theorem InfinitePlace.not_isEquiv_finitePlace (v : InfinitePlace K) (u : FinitePlace K) :
    ¬ v.1.IsEquiv u.1 :=
  v.not_isEquiv_of_isNonarchimedean u.add_le

/-- A finite place and an infinite place of a number field have inequivalent underlying absolute
values. -/
theorem FinitePlace.not_isEquiv_infinitePlace (u : FinitePlace K) (v : InfinitePlace K) :
    ¬ u.1.IsEquiv v.1 :=
  fun h ↦ v.not_isEquiv_finitePlace u h.symm

/-- An infinite place and a finite place of a number field never have the same underlying absolute
value. -/
theorem InfinitePlace.val_ne_finitePlace_val (v : InfinitePlace K) (u : FinitePlace K) :
    v.1 ≠ u.1 :=
  fun h ↦ v.not_isEquiv_finitePlace u (h ▸ .rfl)

/-- The underlying absolute value of an infinite place is not a finite place. -/
theorem InfinitePlace.not_isFinitePlace (v : InfinitePlace K) : ¬ IsFinitePlace v.1 := by
  rintro ⟨𝔭, h𝔭⟩
  exact v.val_ne_finitePlace_val (FinitePlace.mk 𝔭) h𝔭.symm

/-- The underlying absolute value of a finite place is not an infinite place. -/
theorem FinitePlace.not_isInfinitePlace (u : FinitePlace K) : ¬ IsInfinitePlace u.1 := by
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

end NumberField
