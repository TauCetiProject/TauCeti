/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import Mathlib.Analysis.AbsoluteValue.Equivalence
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Extending absolute values above finite places

An absolute value of a number field equivalent to a finite place extends to every further
number field. In particular, an absolute value lying over a finite place of a smaller number
field extends further, with its normalization preserved exactly.

This distinction matters at ramified primes: an absolute value lying over a base place is
usually a root of a finite place, rather than a finite place itself. The extension is obtained
by extending the finite place and taking the same positive real power. The exponent is allowed
to exceed one, because finite-place absolute values are nonarchimedean.

The proof uses the finite-place classification and nonemptiness of the fibres from
`NumberField.exists_finitePlace_rpow_inv_eq_of_liesOver` and
`NumberField.nonempty_setOf_liesOver_finitePlace_mk`, together with
`AbsoluteValue.nonarchRpow`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

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

end NumberField
