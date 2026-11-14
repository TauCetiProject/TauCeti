/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Absolute values lying over an infinite or finite place

For an extension `F / K` of number fields and an absolute value `v : AbsoluteValue K ℝ` coming from
either an infinite place or a finite place of `K` (`IsInfinitePlace v ∨ IsFinitePlace v`), this
file combines the archimedean classification
(`TauCeti/NumberTheory/NumberField/PlacesOver/InfinitePlace.lean`) and the nonarchimedean
classification (`TauCeti/NumberTheory/NumberField/PlacesOver/FinitePlace.lean`) to record the
uniform properties of the fibre `{w : AbsoluteValue F ℝ | w.LiesOver v}`:

* the fibre is finite (`NumberField.finite_setOf_liesOver`) and nonempty
  (`NumberField.nonempty_setOf_liesOver`);
* an absolute value `w` lying over `v` is nonarchimedean if and only if `v` is a finite place
  (`NumberField.isNonarchimedean_of_liesOver_iff`), and archimedean if and only if `v` is an
  infinite place (`NumberField.not_isNonarchimedean_of_liesOver_iff`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

section FieldExtension

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]

/-- An absolute value `w` of an extension field `F` lying over a place `v` of a number field `K` is
nonarchimedean if and only if `v` is a finite place. -/
theorem isNonarchimedean_of_liesOver_iff {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    IsNonarchimedean ⇑w ↔ IsFinitePlace v := by
  refine ⟨fun hna ↦ hv.resolve_left fun hinf ↦ ?_, fun hfin ↦ ?_⟩
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact not_isNonarchimedean_of_liesOver_infinitePlace v' w hna
  · exact isNonarchimedean_of_liesOver hfin.isNonarchimedean

/-- An absolute value `w` of an extension field `F` lying over a place `v` of a number field `K` is
archimedean if and only if `v` is an infinite place. -/
theorem not_isNonarchimedean_of_liesOver_iff {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    ¬ IsNonarchimedean ⇑w ↔ IsInfinitePlace v := by
  rw [isNonarchimedean_of_liesOver_iff hv w]
  exact ⟨hv.resolve_right, IsInfinitePlace.not_isFinitePlace⟩

end FieldExtension

section NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

variable (F) in
/-- Above any infinite or finite place of `K`, a number field extension `F / K` has only finitely
many absolute values lying over it. -/
theorem finite_setOf_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact finite_setOf_liesOver_infinitePlace F v'
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    rw [← v'.mk_maximalIdeal]
    exact finite_setOf_liesOver_finitePlace_mk F v'.maximalIdeal

variable (F) in
/-- Above any infinite or finite place of `K`, a number field extension `F / K` has at least one
absolute value lying over it. -/
theorem nonempty_setOf_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
    have : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
    exact nonempty_setOf_liesOver_infinitePlace F v'
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    rw [← v'.mk_maximalIdeal]
    exact nonempty_setOf_liesOver_finitePlace_mk F v'.maximalIdeal

end NumberField

end NumberField
