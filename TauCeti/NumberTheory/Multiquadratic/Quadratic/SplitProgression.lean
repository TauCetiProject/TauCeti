/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic

/-!
# The class of one modulo a quadratic discriminant

In a quadratic number field, a rational prime congruent to one modulo the absolute
value of the discriminant splits. In particular it is the absolute norm of a prime ideal.
This is the progression form of `fundamentalDiscriminantChar_discr_eq_one_iff`.
-/

public section

open Module
open scoped NumberField

namespace NumberField

/-- A prime congruent to `1` modulo the absolute discriminant of a quadratic number
field occurs as the absolute norm of a prime ideal above it. -/
theorem exists_isPrime_and_absNorm_eq_of_modEq_one_discr {K : Type*} [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (h : p ≡ 1 [MOD (discr K).natAbs]) :
    ∃ I : Ideal (𝓞 K), I.IsPrime ∧ I.LiesOver (Ideal.span {(p : ℤ)}) ∧ Ideal.absNorm I = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpD := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have hval : TauCeti.Multiquadratic.fundamentalDiscriminantChar (discr K)
      (TauCeti.Multiquadratic.isFundamentalDiscr_discr hK) p = 1 := by
    rw [hpD, Nat.cast_one, map_one]
  have hsplit := (TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_one_iff hK p).mp hval
  rw [← hK] at hsplit
  obtain ⟨⟨I, hI, hover⟩⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)))
  exact ⟨I, hI, hover, @Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank K _ _ p I hI hover hsplit⟩

end NumberField
