/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Signature
public import TauCeti.NumberTheory.Multiquadratic.Three.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# The units of `ℚ(√3)` miss a sign pattern

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² - 3`, the prime
`3 ≡ 3 (mod 4)` divides the radicand, so no algebraic integer of `K` has norm `-1`
(`TauCeti.NumberField.norm_ne_neg_one_of_prime_dvd`). Hence no unit of `𝓞 K` is positive at one
real place and negative at the other: the signature map on the units is not surjective, although
every sign pattern is the signature of an element of `Kˣ`. This is the narrow-class obstruction in
its simplest form: `ℚ(√3)` has class number `1` but narrow class number `2`
(`TauCeti.Multiquadratic.natCard_narrowClassGroup_eq_two_of_minpoly_eq_X_sq_sub_three`).

`ℚ(√3)` is the first real quadratic field with this property, since `1 + √2` has norm `-1`.

## Main results

* `TauCeti.NumberField.Sqrt3.not_surjective_unitSignature`: the units of `ℚ(√3)` miss a sign
  pattern.
* `TauCeti.NumberField.Sqrt3.not_surjective_unitSignature_adjoinRoot`: the same for the concrete
  model `AdjoinRoot (X² - 3)`.

## References

* H. Cohn, *A Classical Invitation to Algebraic Numbers and Class Fields*, Chapter 8.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField.Sqrt3

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The units of `ℚ(√3)` miss a sign pattern.** No unit of `𝓞 K` is positive at one real
place and negative at the other, since no unit has norm `-1`. -/
theorem not_surjective_unitSignature (hmin : minpoly ℤ θ = X ^ 2 - C (3 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ¬ Function.Surjective (unitSignature (K := K)) := by
  rw [unitSignature_surjective_iff_exists_norm_eq_neg_one hmin hgen (by norm_num)]
  rintro ⟨u, hu⟩
  exact norm_ne_neg_one_of_prime_dvd (p := 3) hmin hgen Int.prime_three.squarefree (by norm_num)
    dvd_rfl (u : 𝓞 K) hu

/-- **Worked example.** The units of the concrete number field `AdjoinRoot (X² - 3)`, modelling
`ℚ(√3)`, miss a sign pattern. -/
theorem not_surjective_unitSignature_adjoinRoot :
    ¬ Function.Surjective (unitSignature (K := AdjoinRoot (X ^ 2 - C (3 : ℚ)))) := by
  obtain ⟨θ, hmin, hgen⟩ := exists_minpoly_eq_X_sq_sub_three_and_adjoin_eq_top
  exact not_surjective_unitSignature hmin hgen

end TauCeti.NumberField.Sqrt3
