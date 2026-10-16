/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.UnitSignature
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.NarrowClassGroup

/-!
# Real quadratic fields whose units miss a sign pattern

Every sign pattern at the real places of a number field is the signature of an element of `Kˣ`
(`NumberField.fieldUnitSignature_surjective`), but the signature map on the units of `𝓞 K`
need not be surjective. This file shows how this happens for real quadratic fields.

For a real quadratic field the units of `𝓞 K` realize every sign pattern exactly when some unit has
norm `-1`, since both conditions say that `Cl⁺(K) → Cl(K)` is injective
(`TauCeti.NumberField.NarrowClassGroup.toClassGroup_injective_iff_unitSignature_surjective` and
`NumberField.NarrowClassGroup.toClassGroup_injective_iff_exists_norm_eq_neg_one`). When there is
no such unit the narrow class number is exactly twice the class number
(`TauCeti.NumberField.NarrowClassGroup.card_eq_two_mul_card_classGroup_of_forall_norm_ne_neg_one`).
No unit has norm `-1` when a prime `p ≡ 3 (mod 4)` divides the radicand
(`TauCeti.NumberField.norm_ne_neg_one_of_prime_dvd`); the simplest instance is `ℚ(√3)`
(`TauCeti.NumberField.Sqrt3.not_surjective_unitSignature`).

## Main results

* `TauCeti.NumberField.unitSignature_surjective_iff_exists_norm_eq_neg_one`: for a real quadratic
  field the units realize every sign pattern exactly when some unit has norm `-1`.

## References

* H. Cohn, *A Classical Invitation to Algebraic Numbers and Class Fields*, Chapter 8.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open Polynomial NumberField NumberField.NarrowClassGroup

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The units of a real quadratic field realize every sign pattern exactly when some unit has
norm `-1`.** Both conditions are equivalent to injectivity of `Cl⁺(K) → Cl(K)`. -/
theorem unitSignature_surjective_iff_exists_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : 0 < d) :
    Function.Surjective (unitSignature (K := K)) ↔
      ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 :=
  NarrowClassGroup.toClassGroup_injective_iff_unitSignature_surjective.symm.trans
    (toClassGroup_injective_iff_exists_norm_eq_neg_one hmin hgen hd)

end TauCeti.NumberField
