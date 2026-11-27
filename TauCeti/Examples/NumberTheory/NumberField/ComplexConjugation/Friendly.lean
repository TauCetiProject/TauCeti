/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Friendly.Basic

/-!
# Tests of friendly places

* `ℚ(i)`, here any `4`-th cyclotomic extension of `ℚ`: the place above `3` is friendly, neither
  place above `5` is, and the place above `2` is ramified over `ℚ` (ramification index `2`), so
  not friendly.
* `ℚ(2^(1/3))`, here any cubic field: every place unramified over `ℚ` is friendly.
-/

public section

open NumberField IsDedekindDomain HeightOneSpectrum

namespace TauCeti.Examples.Friendly

section GaussianRationals

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- `ℚ(i)`: the place above `3` is friendly. -/
theorem isFriendly_of_liesOver_three (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(3 : ℤ)})] : IsFriendly v :=
  (isFriendly_iff_mod_four_eq_three v 3).mpr rfl

/-- `ℚ(i)`: neither place above `5` is friendly. -/
theorem not_isFriendly_of_liesOver_five (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(5 : ℤ)})] : ¬IsFriendly v :=
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  fun h ↦ absurd ((isFriendly_iff_mod_four_eq_three v 5).mp h) (by decide)

/-- `ℚ(i)`: the place above `2` is ramified over `ℚ`, with ramification index `2`, and is not
friendly. -/
theorem ramificationIdx_eq_two_and_not_isFriendly_of_liesOver_two (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})] :
    v.asIdeal.ramificationIdx ℤ = 2 ∧ ¬IsFriendly v := by
  refine ⟨?_, fun h ↦ absurd ((isFriendly_iff_mod_four_eq_three v 2).mp h) (by decide)⟩
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq 4 K v.asIdeal (p := 2) (k := 1) (m := 1)
    rfl (by decide)

end GaussianRationals

/-- `ℚ(2^(1/3))`, here any cubic field: every place unramified over `ℚ` is friendly. -/
theorem isFriendly_of_finrank_eq_three {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal.ramificationIdx ℤ = 1) : IsFriendly v :=
  (isFriendly_iff_of_odd_finrank (hK ▸ by decide) v).mpr hv

end TauCeti.Examples.Friendly
