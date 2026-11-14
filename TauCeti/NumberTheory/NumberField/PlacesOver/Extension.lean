/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace

/-!
# Extending absolute values above places

An absolute value `w` on an intermediate extension `F / K` lying over a place `v` of `K` extends to
further extensions `E / F`, with its normalization on `F` preserved:

* Above an infinite place `v : InfinitePlace K`, `w` is itself an infinite place of `F`
  (`NumberField.isInfinitePlace_of_liesOver`) and extends to every algebraic field extension `E / F`
  (`NumberField.InfinitePlace.exists_liesOver_of_liesOver`), without assuming `K`, `F`, or `E` to be
  number fields.
* Above a finite place `v : FinitePlace K` in a tower of number fields, `w` is typically a proper
  root of a finite place of `F` at ramified or inert primes rather than a finite place itself; it is
  extended by extending the underlying finite place of `F` and raising to the same positive real
  power via `AbsoluteValue.nonarchRpow` (`NumberField.FinitePlace.exists_liesOver_of_isEquiv`,
  `NumberField.FinitePlace.exists_liesOver_of_liesOver`).
* Combining the two cases yields `NumberField.exists_liesOver_of_liesOver` for any infinite or
  finite place `v` of `K` (`IsInfinitePlace v ∨ IsFinitePlace v`) in a tower of number fields.

## Main results

* `NumberField.InfinitePlace.exists_liesOver_of_liesOver`: an absolute value of a field extension
  `F / K` lying over an infinite place of `K` extends to every algebraic field extension `E / F`.
* `NumberField.FinitePlace.exists_liesOver_of_isEquiv` and
  `NumberField.FinitePlace.exists_liesOver_of_liesOver`: an absolute value of a number field `F`
  equivalent to a finite place of `F`, or lying over a finite place of a smaller number field `K`,
  extends to every further number field `E / F`.
* `NumberField.exists_liesOver_of_liesOver`: an absolute value of a number field `F` lying over an
  infinite or finite place of a number field `K` extends to every further number field `E / F`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

/-- An absolute value of a field extension `F / K` lying over an infinite place `v` of `K` extends
to every algebraic field extension `E / F`. -/
theorem InfinitePlace.exists_liesOver_of_liesOver {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra.IsAlgebraic F E] (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  obtain ⟨w', -, rfl⟩ := (existsUnique_infinitePlace_eq_of_liesOver v w).exists
  exact nonempty_setOf_liesOver_infinitePlace E w'

section NumberFieldExtension

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

/-- An absolute value of a number field `F` lying over an infinite or finite place `v` of a number
field `K` extends to every further number field `E / F`. -/
theorem exists_liesOver_of_liesOver {K : Type*} [Field K] [NumberField K] [Algebra K F]
    {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  rcases hv.imp (isInfinitePlace_iff v).mp (isFinitePlace_iff v).mp with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact v.exists_liesOver_of_liesOver w
  · exact v.exists_liesOver_of_liesOver w

end NumberFieldExtension

end NumberField
