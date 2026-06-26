/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.EffectiveBounds.HermiteCountMonotone

/-!
# Threshold-monotone forms of the effective Hermite--Minkowski count

The exact effective Hermite--Minkowski bound in
`TauCeti.NumberField.ncard_setOf_finiteDimensional_abs_discr_le_le` counts number fields in a fixed
ambient extension whose discriminant is at most a chosen threshold `N`. The monotone wrappers in
`TauCeti.NumberTheory.EffectiveBounds.HermiteCountMonotone` allow the degree and coefficient-height
constants for that same threshold to be replaced by larger constants.

This file records the other monotonicity that later effective estimates need: a field family cut
out by `|d_K| ≤ N` may be counted using the explicit constants attached to any larger threshold
`M`. This keeps downstream arithmetic free to round the discriminant threshold upward first and then
use the Hermite-count constants for the rounded bound.

## Main results

* `TauCeti.NumberField.ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_le`: if
  `N ≤ M`, then the fields with `|d_K| ≤ N` are bounded by the exact Hermite count at `M`.
* `TauCeti.NumberField.ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_bounds`: the
  same statement with the degree and coefficient-height constants at `M` replaced by any larger
  explicit bounds.

No formal code is vendored. The proof reuses Mathlib's qualitative
`NumberField.finite_of_discr_bdd` for the finite target set, and Tau Ceti's existing explicit
Hermite-count API.
-/

public section

open Module NumberField NumberField.hermiteTheorem

namespace TauCeti.NumberField

variable (A : Type*) [Field A] [CharZero A]

/-- The bounded-discriminant subfields at threshold `N` form a subset of those at threshold `M`
whenever `N ≤ M`. -/
private theorem setOf_finiteDimensional_abs_discr_le_subset_of_le {N M : ℕ} (hNM : N ≤ M) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)} ⊆
      {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (M : ℤ)} := by
  intro K hK
  haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
  exact @le_trans ℤ _ |discr K| (N : ℤ) (M : ℤ) hK (by exact_mod_cast hNM)

/-- **Threshold-monotone effective Hermite--Minkowski.** If `N ≤ M`, then the number of
finite-dimensional subfields of an ambient extension `A / ℚ` with discriminant at most `N` is
bounded by the explicit Hermite-count expression attached to the larger threshold `M`. -/
theorem ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_le {N M : ℕ}
    (hNM : N ≤ M) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)}.ncard ≤
      hermiteCountBound (rankOfDiscrBdd M) (coeffBoundOfDiscrBdd M) :=
  (Set.ncard_le_ncard (setOf_finiteDimensional_abs_discr_le_subset_of_le (A := A) hNM)
      (NumberField.finite_of_discr_bdd A M)).trans
    (ncard_setOf_finiteDimensional_abs_discr_le_le_hermiteCountBound (A := A) M)

/-- **Threshold-monotone effective Hermite--Minkowski with coarser constants.** If `N ≤ M`, and
`D` and `C` bound the degree and coefficient-height constants attached to `M`, then the number of
finite-dimensional subfields of an ambient extension `A / ℚ` with discriminant at most `N` is at
most `hermiteCountBound D C`. -/
theorem ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_bounds {N M D C : ℕ}
    (hNM : N ≤ M) (hD : rankOfDiscrBdd M ≤ D) (hC : coeffBoundOfDiscrBdd M ≤ C) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)}.ncard ≤ hermiteCountBound D C :=
  (ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_le (A := A) hNM).trans
    (hermiteCountBound_mono hD hC)

end TauCeti.NumberField
