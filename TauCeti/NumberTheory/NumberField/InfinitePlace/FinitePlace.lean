/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Separation of infinite and finite places

Infinite places of a number field are archimedean
(`NumberField.InfinitePlace.not_isNonarchimedean`), whereas finite places satisfy the ultrametric
inequality (`NumberField.FinitePlace.add_le`). Hence an infinite place and a finite place never
share the same underlying `AbsoluteValue K ℝ` (`NumberField.InfinitePlace.val_ne_finitePlace_val`),
and among absolute values arising from places, nonarchimedean ones are precisely the finite places
(`NumberField.isNonarchimedean_iff_isFinitePlace`).

This disjointness allows constructions indexed by `AbsoluteValue K ℝ` to prescribe data
independently on a set of infinite places and a set of finite places without collision.

## Main results

* `NumberField.InfinitePlace.val_ne_finitePlace_val` and
  `NumberField.FinitePlace.val_ne_infinitePlace_val`: an infinite place and a finite place have
  distinct underlying absolute values.
* `NumberField.IsInfinitePlace.not_isNonarchimedean` and
  `NumberField.IsFinitePlace.isNonarchimedean`: archimedean vs nonarchimedean character of place
  predicates.
* `NumberField.IsInfinitePlace.not_isFinitePlace`, `NumberField.IsFinitePlace.not_isInfinitePlace`
  and `NumberField.disjoint_isInfinitePlace_isFinitePlace`: disjointness of `IsInfinitePlace` and
  `IsFinitePlace`.
* `NumberField.isNonarchimedean_iff_isFinitePlace` and
  `NumberField.not_isNonarchimedean_iff_isInfinitePlace`: among places, nonarchimedean character
  characterizes finite places.
-/

public section

namespace NumberField

section Field

variable {K : Type*} [Field K]

/-- An absolute value arising from an infinite place is archimedean. -/
theorem IsInfinitePlace.not_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v) :
    ¬ IsNonarchimedean ⇑v := by
  obtain ⟨w, rfl⟩ := (isInfinitePlace_iff v).mp hv
  exact w.not_isNonarchimedean

end Field

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- An absolute value arising from a finite place is nonarchimedean. -/
theorem IsFinitePlace.isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsFinitePlace v) :
    IsNonarchimedean ⇑v := by
  obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp hv
  exact u.add_le

/-- An infinite place and a finite place never have the same underlying absolute value. -/
theorem InfinitePlace.val_ne_finitePlace_val (v : InfinitePlace K) (u : FinitePlace K) :
    v.1 ≠ u.1 := fun h ↦
  v.not_isNonarchimedean (h ▸ u.add_le)

/-- A finite place and an infinite place never have the same underlying absolute value. -/
theorem FinitePlace.val_ne_infinitePlace_val (u : FinitePlace K) (v : InfinitePlace K) :
    u.1 ≠ v.1 :=
  (v.val_ne_finitePlace_val u).symm

/-- No absolute value is simultaneously an infinite place and a finite place. -/
theorem IsInfinitePlace.not_isFinitePlace {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v) :
    ¬ IsFinitePlace v := fun hfin ↦
  hv.not_isNonarchimedean hfin.isNonarchimedean

/-- No absolute value is simultaneously a finite place and an infinite place. -/
theorem IsFinitePlace.not_isInfinitePlace {v : AbsoluteValue K ℝ} (hv : IsFinitePlace v) :
    ¬ IsInfinitePlace v := fun hinf ↦
  hinf.not_isFinitePlace hv

variable (K) in
/-- The sets of infinite-place and finite-place absolute values on `K` are disjoint. -/
theorem disjoint_isInfinitePlace_isFinitePlace :
    Disjoint {v : AbsoluteValue K ℝ | IsInfinitePlace v}
      {v : AbsoluteValue K ℝ | IsFinitePlace v} :=
  Set.disjoint_left.mpr fun _ hv ↦ hv.not_isFinitePlace

/-- Among places of a number field, an absolute value is nonarchimedean if and only if it is a
finite place. -/
theorem isNonarchimedean_iff_isFinitePlace {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    IsNonarchimedean ⇑v ↔ IsFinitePlace v := by
  refine ⟨fun hna ↦ ?_, IsFinitePlace.isNonarchimedean⟩
  exact hv.resolve_left fun hinf ↦ hinf.not_isNonarchimedean hna

/-- Among places of a number field, an absolute value is archimedean if and only if it is an
infinite place. -/
theorem not_isNonarchimedean_iff_isInfinitePlace {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    ¬ IsNonarchimedean ⇑v ↔ IsInfinitePlace v := by
  rw [isNonarchimedean_iff_isFinitePlace hv]
  exact ⟨hv.resolve_right, IsInfinitePlace.not_isFinitePlace⟩

end NumberField

end NumberField
