/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs

/-!
# Zero-sum-freeness of localizations of commutative semirings

Localizing a zero-sum-free commutative semiring `R` (`Subsingleton (AddUnits R)`) at any submonoid
`M` produces a zero-sum-free semiring (`IsLocalization.subsingleton_addUnits`). No regularity or
non-zero-divisor assumption on `M` is needed, so this applies uniformly to `Localization M`,
`Localization.Away`, and fraction semirings.
-/

public section

/-- Any localization of a zero-sum-free commutative semiring is zero-sum-free. -/
theorem IsLocalization.subsingleton_addUnits {R : Type*} [CommSemiring R]
    [Subsingleton (AddUnits R)] (M : Submonoid R) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization M S] : Subsingleton (AddUnits S) := by
  refine .addUnits_of_isAddUnit fun x ⟨u, hu⟩ => ?_
  subst hu
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj M (u : S)
  obtain ⟨⟨b, n⟩, hn⟩ := IsLocalization.surj M ((-u : AddUnits S) : S)
  have hsum : algebraMap R S (a * n + b * m) = 0 := by
    calc algebraMap R S (a * n + b * m)
        = algebraMap R S a * algebraMap R S n + algebraMap R S b * algebraMap R S m := by
          simp [map_add, map_mul]
      _ = ((u : S) + (-u : AddUnits S)) * (algebraMap R S m * algebraMap R S n) := by
          rw [← hm, ← hn]; ring
      _ = 0 := by simp
  obtain ⟨c, hc⟩ := (IsLocalization.toLocalizationMap M S).map_eq_zero_iff.mp hsum
  have hca : ((c * n : M) : R) * a = 0 := by
    have hmul : (c : R) * (a * n) + (c : R) * (b * m) = 0 := by
      simpa [mul_add] using hc
    simpa [Submonoid.coe_mul, mul_assoc, mul_left_comm, mul_comm] using (add_eq_zero.mp hmul).1
  have ha0 : algebraMap R S a = 0 :=
    (IsLocalization.toLocalizationMap M S).map_eq_zero_iff.mpr ⟨c * n, hca⟩
  exact (IsLocalization.map_units S m).mul_left_eq_zero.mp (hm.trans ha0)

namespace TauCeti

instance instSubsingletonAddUnitsLocalization {R : Type*} [CommSemiring R]
    [Subsingleton (AddUnits R)] {M : Submonoid R} :
    Subsingleton (AddUnits (Localization M)) :=
  IsLocalization.subsingleton_addUnits M (Localization M)

end TauCeti
