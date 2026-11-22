/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Discriminants of quadratic number fields

For an imaginary quadratic field `K`, `NumberField.discr_lt_zero_of_isTotallyComplex`
gives `discr K < 0`, and combined with Stickelberger's congruence `discr K ≡ 0, 1 (mod 4)`
(`TauCeti.NumberField.discr_emod_four_eq_zero_or_one`) this shows `discr K < -4` holds
precisely away from `-4` and `-3`.

## Main results

* `TauCeti.NumberField.discr_lt_neg_four_iff`: for an imaginary quadratic field, `discr K < -4`
  iff `discr K ≠ -4 ∧ discr K ≠ -3`.
-/

public section

open NumberField

namespace TauCeti.NumberField

/-- For an imaginary quadratic field, `discr K < -4` holds precisely away from `-4` and `-3`. -/
theorem discr_lt_neg_four_iff {K : Type*} [Field K] [NumberField K]
    [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) :
    discr K < -4 ↔ discr K ≠ -4 ∧ discr K ≠ -3 := by
  have hlt := discr_lt_zero_of_isTotallyComplex hK
  have h4 := discr_emod_four_eq_zero_or_one K
  omega

end TauCeti.NumberField
