/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace
public import Mathlib.Analysis.AbsoluteValue.Equivalence
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Extending absolute values above places

An absolute value of an extension field lying over a place of the base extends to every further
algebraic or number-field extension, with its normalization preserved on the nose:

* Above an infinite place `v` of an arbitrary field `K`, an absolute value `w` of `F` is itself an
  infinite place (`NumberField.isInfinitePlace_of_liesOver`), and extends along any algebraic
  extension `E / F` via `NumberField.InfinitePlace.comap_surjective`
  (`NumberField.InfinitePlace.exists_liesOver_of_liesOver`).
* Above a finite place of a number field, an absolute value `w` of `F` is in general a positive root
  of a finite place (`NumberField.exists_finitePlace_rpow_inv_eq_of_liesOver`). More generally, any
  absolute value equivalent to a finite place extends to every further number field by extending the
  finite place and taking the same positive real power (`AbsoluteValue.nonarchRpow`); the exponent
  may exceed one because finite-place absolute values are nonarchimedean
  (`NumberField.FinitePlace.exists_liesOver_of_isEquiv`,
  `NumberField.FinitePlace.exists_liesOver_of_liesOver`).
* Combining the two cases gives extension above any infinite or finite place of a number field
  (`NumberField.exists_liesOver_of_liesOver`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

/-- An absolute value of a field `F` lying over an infinite place of a subfield `K` extends to every
algebraic extension `E` of `F`. -/
theorem InfinitePlace.exists_liesOver_of_liesOver {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra.IsAlgebraic F E] (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] : ∃ u : AbsoluteValue E ℝ, u.LiesOver w :=
  nonempty_setOf_liesOver_infinitePlace E ⟨w, isInfinitePlace_of_liesOver v w⟩

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- An absolute value equivalent to a finite place extends to every further number field,
with equality on the base, not merely equivalence. -/
theorem FinitePlace.exists_liesOver_of_isEquiv (v : FinitePlace F) {w : AbsoluteValue F ℝ}
    (hw : v.1.IsEquiv w) : ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  obtain ⟨t, ht, htw⟩ := isEquiv_iff_exists_rpow_eq.mp hw
  obtain ⟨u, hu⟩ := nonempty_setOf_liesOver_finitePlace E v
  let : u.LiesOver v.1 := hu
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

/-- An absolute value of a number field lying over a place (infinite or finite) of a smaller number
field extends to every further number field. -/
theorem exists_liesOver_of_liesOver {K : Type*} [Field K] [NumberField K] [Algebra K F]
    {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ)
    [w.LiesOver v] : ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact v'.exists_liesOver_of_liesOver w
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact v'.exists_liesOver_of_liesOver w

end NumberField
