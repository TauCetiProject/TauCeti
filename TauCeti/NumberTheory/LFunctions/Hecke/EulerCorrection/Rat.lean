/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.EulerCorrection.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Primitive.Rat
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight.Rat
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Deleted Euler factors for rational ray class characters

Mapping height-one primes of `𝓞 ℚ` to their absolute norms identifies `𝔪.support` with
`(Ideal.absNorm 𝔪.finitePart).primeFactors`, expressing `RayClassCharacter.eulerCorrection` over
`ℚ` in terms of `Nat.primeFactors` and `DirichletCharacter` values.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.eulerCorrection_eq_prod_primeFactors` and
  `eulerCorrection_eq_prod_sdiff_primeFactors`: rational deleted Euler factors in terms of prime
  factors of modulus norms.
* `TauCeti.GlobalNumberFields.RayClassCharacter.eulerCorrection_ratDirichletEquiv_symm`,
  `TauCeti.LFunctions.PrimitiveRayClassCharacter.eulerCorrection_character_of`, and
  `TauCeti.LFunctions.PrimitiveRayClassCharacter.eulerCorrection_ofDirichletCharacter`: Euler
  corrections for `(ratDirichletEquiv m hm).symm χ` and primitive ray class characters over `ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti

open GlobalNumberFields

namespace GlobalNumberFields.RayClassCharacter

variable {𝔪 : Modulus ℚ}

/-- **Over `ℚ`, the deleted Euler correction of `η` at `𝔫` is the product over all prime factors of
`Ideal.absNorm 𝔫.finitePart`** (primes dividing `𝔪` contribute `1` because `η.toDirichletCharacter`
vanishes there). -/
theorem eulerCorrection_eq_prod_primeFactors (η : RayClassCharacter 𝔪) (𝔫 : Modulus ℚ) (s : ℂ) :
    η.eulerCorrection 𝔫 s = ∏ p ∈ (Ideal.absNorm 𝔫.finitePart).primeFactors,
      (1 - η.toDirichletCharacter p * (p : ℂ) ^ (-s)) := by
  rw [← image_absNorm_support 𝔫,
    Finset.prod_image Rat.HeightOneSpectrum.absNorm_asIdeal_injective.injOn,
    eulerCorrection_eq_prod_support]
  exact Finset.prod_congr rfl fun 𝔭 _ ↦ by
    rw [toMultiplicativeIdealWeight_eq_toDirichletCharacter_absNorm η 𝔭.ne_bot]

/-- **Over `ℚ`, the deleted Euler correction of `η` at `𝔫` is the product over prime factors of
`Ideal.absNorm 𝔫.finitePart` not dividing `Ideal.absNorm 𝔪.finitePart`.** -/
theorem eulerCorrection_eq_prod_sdiff_primeFactors (η : RayClassCharacter 𝔪) (𝔫 : Modulus ℚ)
    (s : ℂ) :
    η.eulerCorrection 𝔫 s =
      ∏ p ∈ (Ideal.absNorm 𝔫.finitePart).primeFactors \ (Ideal.absNorm 𝔪.finitePart).primeFactors,
        (1 - η.toDirichletCharacter p * (p : ℂ) ^ (-s)) := by
  classical
  rw [eulerCorrection_def, ← image_absNorm_support 𝔫, ← image_absNorm_support 𝔪,
    ← Finset.image_sdiff 𝔫.support 𝔪.support Rat.HeightOneSpectrum.absNorm_asIdeal_injective,
    Finset.prod_image Rat.HeightOneSpectrum.absNorm_asIdeal_injective.injOn]
  exact Finset.prod_congr rfl fun 𝔭 _ ↦ by
    rw [toMultiplicativeIdealWeight_eq_toDirichletCharacter_absNorm η 𝔭.ne_bot]

/-- For `χ : DirichletCharacter ℂ m`, the deleted Euler correction of
`(ratDirichletEquiv m hm).symm χ` at `(n)·∞` is
`∏ p ∈ n.primeFactors \ m.primeFactors, (1 - χ p * p ^ (-s))`. -/
theorem eulerCorrection_ratDirichletEquiv_symm {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (χ : DirichletCharacter ℂ m) (s : ℂ) :
    ((ratDirichletEquiv m hm).symm χ).eulerCorrection (ratModulus n hn) s =
      ∏ p ∈ n.primeFactors \ m.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) := by
  rw [eulerCorrection_eq_prod_sdiff_primeFactors]
  refine Finset.prod_congr ?_ fun p _ ↦ by simp
  rw [absNorm_ratModulus_finitePart, absNorm_ratModulus_finitePart]

end GlobalNumberFields.RayClassCharacter

namespace LFunctions.PrimitiveRayClassCharacter

/-- Over `ℚ`, the deleted Euler correction from the primitive character `of η` to `𝔪` is the
product over primes dividing `Ideal.absNorm 𝔪.finitePart` and not dividing the Dirichlet conductor
of `η`. -/
theorem eulerCorrection_character_of {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) (s : ℂ) :
    (of η).character.eulerCorrection 𝔪 s =
      ∏ p ∈ (Ideal.absNorm 𝔪.finitePart).primeFactors \
          η.toDirichletCharacter.conductor.primeFactors,
        (1 - η.toDirichletCharacter.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  rw [RayClassCharacter.eulerCorrection_eq_prod_sdiff_primeFactors]
  refine Finset.prod_congr ?_ fun p _ ↦ by
    rw [← toDirichletCharacter_def, toDirichletCharacter_of_natCast]
  rw [conductor_of, ← RayClassCharacter.conductor_toDirichletCharacter]

/-- For `χ : DirichletCharacter ℂ N`, the deleted Euler correction from `ofDirichletCharacter χ`
to `(N)·∞` is the product of `1 - χ.primitiveCharacter p * p ^ (-s)` over
`p ∈ N.primeFactors \ χ.conductor.primeFactors`. -/
theorem eulerCorrection_ofDirichletCharacter {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) :
    (ofDirichletCharacter χ).character.eulerCorrection (ratModulus N (NeZero.ne N)) s =
      ∏ p ∈ N.primeFactors \ χ.conductor.primeFactors,
        (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  rw [RayClassCharacter.eulerCorrection_eq_prod_sdiff_primeFactors]
  refine Finset.prod_congr ?_ fun p _ ↦ by
    rw [← toDirichletCharacter_def, toDirichletCharacter_ofDirichletCharacter_natCast]
  rw [absNorm_ratModulus_finitePart, absNorm_conductor_ofDirichletCharacter]

end LFunctions.PrimitiveRayClassCharacter

end TauCeti
