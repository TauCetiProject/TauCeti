/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.Basic
public import Mathlib.Analysis.AbsoluteValue.Equivalence
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Extending absolute values above places

An absolute value of a field extension `F / K` lying over a place of `K` extends to further
extensions `E / F`, restricting to the given absolute value on `F` on the nose rather than merely up
to equivalence:

* `NumberField.InfinitePlace.exists_liesOver_of_liesOver`: an absolute value of `F` lying over an
  infinite place of `K` extends to every algebraic extension `E / F`.
* `NumberField.FinitePlace.exists_liesOver_of_isEquiv` and
  `NumberField.FinitePlace.exists_liesOver_of_liesOver`: over number fields, an absolute value
  equivalent to a finite place of `F` — and in particular any absolute value of `F` lying over a
  finite place of `K`, including its root-of-place normalization — extends to every number field `E`
  over `F`.
* `NumberField.exists_liesOver_of_liesOver`: over number fields, an absolute value of `F` lying over
  any `v : AbsoluteValue K ℝ` satisfying `IsInfinitePlace v ∨ IsFinitePlace v` extends to `E`.

## Implementation notes

Above an infinite place, `NumberField.existsUnique_infinitePlace_of_liesOver` identifies `w` with an
infinite place of `F`, which extends to any algebraic extension. Above a finite place, `w` is a
positive real power of a finite place of `F`; extending that finite place to `E` and raising to the
same power via `AbsoluteValue.nonarchRpow` preserves `w` exactly on `F`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

section InfinitePlace

/-- An absolute value of a field `F` lying over an infinite place of a subfield `K` extends to
every algebraic extension `E` of `F`. -/
theorem InfinitePlace.exists_liesOver_of_liesOver {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra.IsAlgebraic F E] (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  obtain ⟨w', -, rfl⟩ := (existsUnique_infinitePlace_of_liesOver v w).exists
  exact nonempty_setOf_liesOver_infinitePlace E w'

end InfinitePlace

section NumberField

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- An absolute value equivalent to a finite place extends to every further number field,
with equality on the base, not merely equivalence. -/
theorem FinitePlace.exists_liesOver_of_isEquiv (v : FinitePlace F) {w : AbsoluteValue F ℝ}
    (hw : v.1.IsEquiv w) : ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  obtain ⟨t, ht, htw⟩ := isEquiv_iff_exists_rpow_eq.mp hw
  obtain ⟨u, hu⟩ := nonempty_setOf_liesOver_finitePlace_mk E v.maximalIdeal
  have hu' : u.LiesOver v.1 := by
    simpa only [Set.mem_ofPred_eq, v.mk_maximalIdeal] using hu
  have huNA : IsNonarchimedean u := isNonarchimedean_of_liesOver v.add_le
  refine ⟨u.nonarchRpow huNA ht, ⟨AbsoluteValue.ext fun x ↦ ?_⟩⟩
  rw [under_def, comp_apply, nonarchRpow_apply, LiesOver.apply_algebraMap v.1]
  exact congrFun htw x

/-- An absolute value of a number field lying over a finite place of a smaller number field
extends to every further number field. The extension restricts to the given absolute value
exactly, including its root-of-place normalization. -/
theorem FinitePlace.exists_liesOver_of_liesOver {K : Type*} [Field K] [NumberField K]
    [Algebra K F] (v : FinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  obtain ⟨𝔓, t, ht, -, hw⟩ := exists_finitePlace_rpow_inv_eq_of_liesOver w v
  apply (FinitePlace.mk 𝔓).exists_liesOver_of_isEquiv
  exact isEquiv_iff_exists_rpow_eq.mpr ⟨t, ht, funext hw |>.symm⟩

/-- An absolute value of a number field lying over an infinite or finite place of a smaller number
field extends to every further number field. -/
theorem exists_liesOver_of_liesOver {K : Type*} [Field K] [NumberField K] [Algebra K F]
    {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
    exact v'.exists_liesOver_of_liesOver w
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact v'.exists_liesOver_of_liesOver w

end NumberField

end NumberField
