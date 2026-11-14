/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.FinitePlace.InfinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Fibres of absolute values above a place of a number field

For an extension `F / K` of number fields and an absolute value `v` on `K` that is either an
infinite place or a finite place (`IsInfinitePlace v ∨ IsFinitePlace v`), this file combines the
archimedean (`PlacesOver.InfinitePlace`) and nonarchimedean (`PlacesOver.FinitePlace`)
classifications into uniform statements on the fibre `{w : AbsoluteValue F ℝ | w.LiesOver v}`:

* the fibre is finite (`NumberField.finite_setOf_liesOver`) and nonempty
  (`NumberField.nonempty_setOf_liesOver`);
* no absolute value on `F` can simultaneously lie over an infinite place and a finite place of `K`
  (`NumberField.not_liesOver_infinitePlace_and_finitePlace`), and an absolute value `w` in the
  fibre over `v` is nonarchimedean if and only if `v` is a finite place
  (`NumberField.isNonarchimedean_iff_isFinitePlace_of_liesOver`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

namespace NumberField

section Field

variable {K F : Type*} [Field K] [Field F] [NumberField K] [Algebra K F]

/-- No absolute value on `F` can simultaneously lie over an infinite place and a finite place of
`K`. -/
theorem not_liesOver_infinitePlace_and_finitePlace (v : InfinitePlace K) (u : FinitePlace K)
    (w : AbsoluteValue F ℝ) : ¬ (w.LiesOver v.1 ∧ w.LiesOver u.1) := by
  rintro ⟨_, _⟩
  exact v.val_ne_finitePlace_val u
    ((AbsoluteValue.LiesOver.under_eq w v.1).symm.trans (AbsoluteValue.LiesOver.under_eq w u.1))

/-- An absolute value `w` on `F` lying over an infinite or finite place `v` of `K` is
nonarchimedean if and only if `v` is a finite place. -/
theorem isNonarchimedean_iff_isFinitePlace_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    IsNonarchimedean w ↔ IsFinitePlace v := by
  refine ⟨fun hna ↦ hv.resolve_left fun hinf ↦ ?_, fun hfin ↦ ?_⟩
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact not_isNonarchimedean_of_liesOver_infinitePlace v' w hna
  · obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact AbsoluteValue.isNonarchimedean_of_liesOver u.add_le

end Field

section NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

variable (F) in
/-- Over a finite place `v` of `K`, only finitely many absolute values of `F` lie over `v`. -/
theorem finite_setOf_liesOver_finitePlace (v : FinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  have hv : (FinitePlace.mk v.maximalIdeal).1 = v.1 :=
    congrArg Subtype.val v.mk_maximalIdeal
  simpa only [hv] using finite_setOf_liesOver_finitePlace_mk F v.maximalIdeal

variable (F) in
/-- Every finite place `v` of `K` has an absolute value of `F` lying over it. -/
theorem nonempty_setOf_liesOver_finitePlace (v : FinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  have hv : (FinitePlace.mk v.maximalIdeal).1 = v.1 :=
    congrArg Subtype.val v.mk_maximalIdeal
  simpa only [hv] using nonempty_setOf_liesOver_finitePlace_mk F v.maximalIdeal

variable (F) in
/-- Above any infinite or finite place of `K`, the extension `F` has only finitely many absolute
values restricting to it. -/
theorem finite_setOf_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact finite_setOf_liesOver_infinitePlace F v'
  · obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact finite_setOf_liesOver_finitePlace F u

variable (F) in
/-- Above any infinite or finite place of `K`, there exists at least one absolute value of `F`
restricting to it. -/
theorem nonempty_setOf_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
    exact nonempty_setOf_liesOver_infinitePlace F v'
  · obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact nonempty_setOf_liesOver_finitePlace F u

end NumberField

end NumberField
