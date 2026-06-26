/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.HermiteCountThreshold

/-!
# Natural-discriminant forms of the effective Hermite--Minkowski count

The effective Hermite--Minkowski count in `TauCeti.NumberTheory.EffectiveBounds.HermiteCount`
counts finite-dimensional subfields of a fixed ambient extension `A / ℚ` satisfying
`|NumberField.discr K| ≤ (N : ℤ)`. That spelling matches Mathlib's
`NumberField.finite_of_discr_bdd`, but later explicit estimates often carry natural-number
absolute discriminants, namely `(NumberField.discr K).natAbs ≤ N`.

This file records the corresponding consumer forms. They do not change the constants or re-run the
Hermite--Minkowski proof; they only bridge the natural-number discriminant inequality to the
existing integer-absolute-value API, and then reuse the threshold and monotone wrappers.

## Main results

* `TauCeti.NumberField.ncard_setOf_finiteDimensional_natAbs_discr_le_le_hermiteCountBound`:
  the `natAbs` version with the exact constants attached to the same threshold.
* `TauCeti.NumberField.ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_le`:
  the `natAbs` version counted using a larger discriminant threshold.
* `TauCeti.NumberField.ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_bounds`:
  the same form with separate larger degree and coefficient-height bounds.

No formal code is vendored. This is a direct API layer over the existing effective
Hermite--Minkowski count and Mathlib's `NumberField.finite_of_discr_bdd` target shape.
-/

public section

open Module NumberField NumberField.hermiteTheorem

namespace TauCeti.NumberField

variable (A : Type*) [Field A] [CharZero A]

/-- The subfields whose discriminant has natural absolute value at most `N` are contained in the
integer-absolute-value family used by Mathlib's Hermite theorem. -/
private theorem setOf_finiteDimensional_natAbs_discr_le_subset_abs_discr_le (N : ℕ) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N} ⊆
      {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)} := by
  intro K hK
  haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
  -- The set predicate elaborates its own `haveI`; normalize the target to the local instance
  -- before rewriting `Int.natAbs`.
  change |discr K| ≤ (N : ℤ)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hK

/-- **Threshold-monotone effective Hermite--Minkowski, natural-discriminant form.** If `N ≤ M`,
then the number of finite-dimensional subfields of an ambient extension `A / ℚ` whose
discriminant has natural absolute value at most `N` is bounded by the explicit Hermite-count
expression attached to the larger threshold `M`. -/
theorem ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_le {N M : ℕ}
    (hNM : N ≤ M) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N}.ncard ≤
      hermiteCountBound (rankOfDiscrBdd M) (coeffBoundOfDiscrBdd M) :=
  (Set.ncard_le_ncard
      (setOf_finiteDimensional_natAbs_discr_le_subset_abs_discr_le (A := A) N)
      (NumberField.finite_of_discr_bdd A N)).trans
    (ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_le (A := A) hNM)

/-- **Effective Hermite--Minkowski, natural-discriminant form.** Inside a fixed extension
`A / ℚ`, the number of finite-dimensional subfields whose discriminant has natural absolute value
at most `N` is bounded by the explicit Hermite-count expression attached to `N`. -/
theorem ncard_setOf_finiteDimensional_natAbs_discr_le_le_hermiteCountBound (N : ℕ) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N}.ncard ≤
      hermiteCountBound (rankOfDiscrBdd N) (coeffBoundOfDiscrBdd N) :=
  ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_le (A := A) le_rfl

/-- **Threshold-monotone effective Hermite--Minkowski with coarser constants,
natural-discriminant form.** If `N ≤ M`, and `D` and `C` bound the degree and coefficient-height
constants attached to `M`, then the number of finite-dimensional subfields of an ambient extension
`A / ℚ` whose discriminant has natural absolute value at most `N` is at most
`hermiteCountBound D C`. -/
theorem ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_bounds {N M D C : ℕ}
    (hNM : N ≤ M) (hD : rankOfDiscrBdd M ≤ D) (hC : coeffBoundOfDiscrBdd M ≤ C) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N}.ncard ≤ hermiteCountBound D C :=
  (ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_le (A := A) hNM).trans
    (hermiteCountBound_mono hD hC)

/-- **Monotone effective Hermite--Minkowski, natural-discriminant form.** If `D` and `C` bound the
degree and coefficient-height constants attached to `N`, then the number of finite-dimensional
subfields of an ambient extension `A / ℚ` whose discriminant has natural absolute value at most
`N` is at most `hermiteCountBound D C`. -/
theorem ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_bounds (N D C : ℕ)
    (hD : rankOfDiscrBdd N ≤ D) (hC : coeffBoundOfDiscrBdd N ≤ C) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N}.ncard ≤ hermiteCountBound D C :=
  ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_bounds
    (A := A) le_rfl hD hC

end TauCeti.NumberField
