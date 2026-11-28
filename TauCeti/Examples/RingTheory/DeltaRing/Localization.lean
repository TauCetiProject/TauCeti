/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.DeltaRing.Localization

/-!
# Checks for the `δ`-structure on a localization

The Frobenius lift of `ℤ` is the identity, so every localization of `ℤ` carries a unique
compatible `δ`-structure. For `p = 2` on the rationals, `δ 3 = (3 - 9) / 2 = -3` in `ℤ` and the
fraction formula `3 ^ 2 * 3 * δ (1 / 3) = 3 ^ 2 * δ 1 - 1 ^ 2 * δ 3 = 3` gives `δ (1 / 3) = 1 / 9`.
-/

public section

namespace TauCeti.Examples

open DeltaRing

variable (p : ℕ) [Fact p.Prime]

/-- The Frobenius lift of `ℤ` is the identity, so it maps `nonZeroDivisors ℤ` into itself. -/
theorem isUnit_algebraMap_frobenius_int_rat (s : nonZeroDivisors ℤ) :
    IsUnit (algebraMap ℤ ℚ (frobenius p ℤ s)) :=
  isUnit_algebraMap_frobenius_of_forall_mem (fun _ hs => by rwa [frobenius_int, RingHom.id_apply])
    s

/-- The `δ`-structure on `ℚ` extending that of `ℤ`. -/
noncomputable local instance : DeltaRing p ℚ := localization (isUnit_algebraMap_frobenius_int_rat p)

-- The inclusion `ℤ → ℚ` is a `δ`-map.
example : IsDeltaMap p (algebraMap ℤ ℚ) :=
  isDeltaMap_algebraMap_localization _

-- It is the only `δ`-structure on `ℚ` with this property.
example (d : DeltaRing p ℚ) (hd : IsDeltaMap p (algebraMap ℤ ℚ)) :
    d = localization (isUnit_algebraMap_frobenius_int_rat p) :=
  eq_localization _ d hd

-- With `p = 2`, `δ (1 / 3) = 1 / 9`.
example : delta 2 (1 / 3 : ℚ) = 1 / 9 := by
  have h3 : (3 : ℤ) ∈ nonZeroDivisors ℤ := mem_nonZeroDivisors_of_ne_zero (by norm_num)
  have h := algebraMap_pow_mul_frobenius_mul_delta_mk' (isDeltaMap_algebraMap_localization
    (isUnit_algebraMap_frobenius_int_rat 2)) (1 : ℤ) ⟨3, h3⟩
  rw [IsFractionRing.mk'_eq_div, frobenius_int, delta_int, delta_int] at h
  norm_num at h
  linarith

end TauCeti.Examples
