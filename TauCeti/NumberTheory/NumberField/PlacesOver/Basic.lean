/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Unified properties of absolute values lying over a place of a number field

Let `F / K` be an extension of number fields and `v : AbsoluteValue K ℝ` the underlying absolute
value of either an infinite place or a finite place of `K` (`IsInfinitePlace v ∨ IsFinitePlace v`).
Combining the archimedean (`TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace`) and
nonarchimedean (`TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace`) classifications, this
file records the properties shared by both kinds of places and the dichotomy separating them:

* `NumberField.InfinitePlace.val_ne_finitePlace_val`: an infinite place and a finite place never
  have the same underlying absolute value, since one is archimedean and the other is not.
* `NumberField.finite_setOf_liesOver`, `NumberField.nonempty_setOf_liesOver`, and
  `NumberField.finite_nonempty_setOf_liesOver`: the fibre `{w : AbsoluteValue F ℝ | w.LiesOver v}`
  above any place `v` of `K` is finite and nonempty.
* `NumberField.isNonarchimedean_of_liesOver_iff`: an absolute value `w` lying over a place `v` of
  `K` is nonarchimedean if and only if `v` is a finite place (and archimedean if and only if `v` is
  an infinite place, `NumberField.not_isNonarchimedean_of_liesOver_iff`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

section Disjoint

variable {K : Type*} [Field K] [NumberField K]

/-- An infinite place and a finite place of a number field never have the same underlying absolute
value: an infinite place is archimedean whereas a finite place is nonarchimedean. -/
theorem InfinitePlace.val_ne_finitePlace_val (v : InfinitePlace K) (u : FinitePlace K) :
    v.1 ≠ u.1 :=
  fun h ↦ v.not_isNonarchimedean (h ▸ fun x y ↦ u.add_le x y)

/-- Symmetric form of `NumberField.InfinitePlace.val_ne_finitePlace_val`. -/
theorem FinitePlace.val_ne_infinitePlace_val (u : FinitePlace K) (v : InfinitePlace K) :
    u.1 ≠ v.1 :=
  (v.val_ne_finitePlace_val u).symm

/-- The underlying absolute value of an infinite place is not a finite place. -/
theorem IsInfinitePlace.not_isFinitePlace {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v) :
    ¬IsFinitePlace v := by
  obtain ⟨w, rfl⟩ := (isInfinitePlace_iff v).mp hv
  intro hfin
  obtain ⟨u, hu⟩ := (isFinitePlace_iff w.1).mp hfin
  exact w.val_ne_finitePlace_val u hu.symm

/-- The underlying absolute value of a finite place is not an infinite place. -/
theorem IsFinitePlace.not_isInfinitePlace {v : AbsoluteValue K ℝ} (hv : IsFinitePlace v) :
    ¬IsInfinitePlace v :=
  fun h ↦ h.not_isFinitePlace hv

end Disjoint

section Dichotomy

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]

/-- An absolute value `w` of a field extension `F / K` lying over a place `v` of `K` is
nonarchimedean if and only if `v` is a finite place. -/
theorem isNonarchimedean_of_liesOver_iff {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    IsNonarchimedean w ↔ IsFinitePlace v := by
  refine ⟨fun hna ↦ hv.resolve_left fun hinf ↦ ?_, fun hfin ↦ ?_⟩
  · obtain ⟨u, rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact not_isNonarchimedean_of_liesOver_infinitePlace u w hna
  · obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact isNonarchimedean_of_liesOver u.add_le

/-- An absolute value `w` of a field extension `F / K` lying over a place `v` of `K` is archimedean
if and only if `v` is an infinite place. -/
theorem not_isNonarchimedean_of_liesOver_iff {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    ¬IsNonarchimedean w ↔ IsInfinitePlace v := by
  rw [isNonarchimedean_of_liesOver_iff hv w]
  exact ⟨hv.resolve_right, IsInfinitePlace.not_isFinitePlace⟩

end Dichotomy

section Fibre

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

variable (F) in
/-- A finite extension of number fields has only finitely many absolute values lying over a given
finite place of the base. -/
theorem finite_setOf_liesOver_finitePlace (v : FinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  simpa only [v.mk_maximalIdeal] using finite_setOf_liesOver_finitePlace_mk F v.maximalIdeal

variable (F) in
/-- Every finite place of the base extends to an absolute value of a finite extension of number
fields. -/
theorem nonempty_setOf_liesOver_finitePlace (v : FinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  simpa only [v.mk_maximalIdeal] using nonempty_setOf_liesOver_finitePlace_mk F v.maximalIdeal

variable (F) in
/-- Above any infinite or finite place of `K`, there are only finitely many absolute values of
`F`. -/
theorem finite_setOf_liesOver {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite := by
  rcases hv with h | h
  · obtain ⟨u, rfl⟩ := (isInfinitePlace_iff v).mp h
    exact finite_setOf_liesOver_infinitePlace F u
  · obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp h
    exact finite_setOf_liesOver_finitePlace F u

variable (F) in
/-- Above any infinite or finite place of `K`, there is at least one absolute value of `F`. -/
theorem nonempty_setOf_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty := by
  rcases hv with h | h
  · obtain ⟨u, rfl⟩ := (isInfinitePlace_iff v).mp h
    exact nonempty_setOf_liesOver_infinitePlace_of_numberField F u
  · obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp h
    exact nonempty_setOf_liesOver_finitePlace F u

variable (F) in
/-- Above every place of `K`, the set of absolute values of `F` lying over it is finite and
nonempty. -/
theorem finite_nonempty_setOf_liesOver (v : AbsoluteValue K ℝ)
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite ∧
      {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty :=
  ⟨finite_setOf_liesOver F hv, nonempty_setOf_liesOver F hv⟩

end Fibre

end NumberField
