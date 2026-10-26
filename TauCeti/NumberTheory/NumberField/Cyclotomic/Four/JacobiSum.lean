/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.JacobiSum.Quartic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary

/-!
# The Jacobi sum of a quartic character is primary up to sign

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`. If `χ` is a multiplicative character with `χ ^ 4 = 1` on a finite field with
`q ≡ 1 (mod 4)` elements, with values in `𝓞 K`, then `-χ (-1) J(χ, χ)` is primary: it is
congruent to `1` modulo `(1 + i) ^ 3`. This applies to the quartic residue symbol
`χ = (· / P)_4` at a prime `P` of `𝓞 K` of odd norm, a character of order `4`
(`Ideal.orderOf_powerResidueSymbol`) on a residue field with `N P ≡ 1 (mod 4)` elements
(`NumberField.dvd_absNorm_sub_one`). For a primary prime `π` of norm `p ≡ 1 (mod 4)` it is the
normalisation that singles out `π` among the associates of `-χ (-1) J(χ, χ)` in the
identification `-χ (-1) J(χ, χ) = π` used in the proof of biquadratic reciprocity.

## Main results

* `TauCeti.isPrimaryGaussian_neg_apply_neg_one_mul_jacobiSum`: `-χ (-1) J(χ, χ)` is primary for
  every character `χ` with `χ ^ 4 = 1` on a finite field with `q ≡ 1 (mod 4)` elements, with values
  in `𝓞 K`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §9.
* N. Xu, *Reciprocity Laws*, §5, Proposition 5.9.
-/

public section

open NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
  {F : Type*} [Field F] [Fintype F]

/-- **The Jacobi sum of a quartic character is primary up to sign.** If `χ` is a multiplicative
character with `χ ^ 4 = 1` on a finite field `F` with `#F ≡ 1 (mod 4)`, such as a character of
order `4`, with values in `𝓞 K = ℤ[i]`, then `-χ (-1) J(χ, χ)` is primary. -/
theorem isPrimaryGaussian_neg_apply_neg_one_mul_jacobiSum {χ : MulChar F (𝓞 K)}
    (hχ : χ ^ 4 = 1) (hq : 4 ∣ Fintype.card F - 1) :
    IsPrimaryGaussian (-χ (-1) * jacobiSum χ χ) := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  rw [hζ.isPrimaryGaussian_iff,
    show -χ (-1) * jacobiSum χ χ - 1 = -(χ (-1) * jacobiSum χ χ + 1) by ring, dvd_neg]
  exact one_add_pow_three_dvd_apply_neg_one_mul_jacobiSum_add_one hχ hq
    hζ.toInteger_isPrimitiveRoot

end TauCeti
