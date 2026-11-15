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
# Extending absolute values above places of a base field

An absolute value of a field extension `F / K` lying over a place `v` of `K` extends to every
further extension `E / F` (`NumberField.exists_liesOver_of_liesOver`), with its normalization
preserved on `F` on the nose.

* Above an infinite place `v : InfinitePlace K`, `w` is itself an infinite place of `F`
  (`NumberField.exists_infinitePlace_eq_of_liesOver`), so it extends to every algebraic extension
  `E / F` (`NumberField.InfinitePlace.exists_liesOver_of_liesOver`).
* Above a finite place `v : FinitePlace K`, `w` is in general a root of a finite place of `F`
  rather than a finite place itself (`NumberField.exists_finitePlace_rpow_inv_eq_of_liesOver`).
  The extension to a further number field `E / F` is obtained by extending that finite place and
  taking the same positive real power via `AbsoluteValue.nonarchRpow`
  (`NumberField.FinitePlace.exists_liesOver_of_liesOver`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

section Infinite

variable {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra F E]

/-- An absolute value of a field `F` lying over an infinite place of `K` extends to every further
algebraic extension `E / F`. -/
theorem InfinitePlace.exists_liesOver_of_liesOver [Algebra.IsAlgebraic F E] (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] : ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  obtain ⟨w', -, rfl⟩ := exists_infinitePlace_eq_of_liesOver v w
  exact nonempty_setOf_liesOver_infinitePlace E w'

/-- An absolute value of a field `F` lying over an infinite place of `K` extends to every number
field `E` over `F`. -/
theorem InfinitePlace.exists_liesOver_of_liesOver_of_numberField [NumberField E]
    (v : InfinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  have : CharZero F := (algebraMap F E).charZero
  have := Algebra.IsAlgebraic.tower_top (K := ℚ) (L := F) (A := E)
  exact v.exists_liesOver_of_liesOver w

end Infinite

section FiniteAndUnified

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

/-- An absolute value of a number field `F` lying over any infinite or finite place of a base
number field `K` extends to every further number field `E` over `F`. -/
theorem exists_liesOver_of_liesOver {K : Type*} [Field K] [NumberField K] [Algebra K F]
    {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ)
    [w.LiesOver v] : ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  rcases hv with h | h
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp h
    exact v'.exists_liesOver_of_liesOver_of_numberField w
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp h
    exact v'.exists_liesOver_of_liesOver w

end FiniteAndUnified

end NumberField
