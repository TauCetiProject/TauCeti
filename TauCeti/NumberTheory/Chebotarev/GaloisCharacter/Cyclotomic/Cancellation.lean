/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Basic
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation

/-!
# Cancellation for the ideal weight of a cyclotomic Galois character

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K` and `χ` a character of
`Gal(F/K)` whose ray class character `χ ∘ cyclotomicArtin K F m` of `cyclotomicModulus K m` is
nontrivial. This file provides cancellation for the ideal weight `galoisCharacterUnitaryWeight χ`
with its Euler factors at the primes dividing `m` deleted: its ideal partial sums are
`O(x ^ (1 - 1 / [K : ℚ]))`. At such a prime the weight can be a root of unity rather than `0` (the
prime may be unramified in `F`), so the restricted weight is the one that agrees with the ray class
character.

## Main results

* `MonoidHom.hasCancellation_restrictAway_galoisCharacterUnitaryWeight`: the weight restricted away
  from the primes dividing `m` has cancellation.
-/

public section

open IsDedekindDomain TauCeti TauCeti.GlobalNumberFields NumberField.Chebotarev
open scoped nonZeroDivisors NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- The Galois weight with the Euler factors at the primes dividing `m` deleted is the unitary
-- weight of the ray class character `χ ∘ cyclotomicArtin K F m`.
private theorem restrictAway_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ) :
    (galoisCharacterUnitaryWeight (L := F) χ).restrictAway
        ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
        (cyclotomicModulus K m).support.finite_toSet =
      RayClassCharacter.toUnitaryIdealWeight (χ.comp (cyclotomicArtin K F m)) := by
  classical
  apply Subtype.ext
  ext I
  rw [UnitaryIdealWeight.val_restrictAway, MultiplicativeIdealWeight.restrictAway_apply,
    val_galoisCharacterUnitaryWeight, RayClassCharacter.val_toUnitaryIdealWeight]
  by_cases hI : Ideal.IsPrimeTo I (cyclotomicModulus K m).support
  · simp only [hI, ite_true]
    rw [RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo _ hI]
    exact galoisCharacterWeight_eq_onIdeals_cyclotomicArtin χ
      ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr hI⟩
  · simp only [hI, ite_false]
    rw [RayClassCharacter.toMultiplicativeIdealWeight_apply_of_not_isPrimeTo _ hI]

/-- **Cancellation for a cyclotomic Galois character, away from the level.** For `F = K(μ_m)`
and a character `χ` of `Gal(F/K)` whose ray class character `χ ∘ cyclotomicArtin K F m` is
nontrivial, the ideal weight of `χ` with the Euler factors at the primes dividing `m` deleted has
cancellation. -/
theorem hasCancellation_restrictAway_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) :
    HasCancellation ((galoisCharacterUnitaryWeight (L := F) χ).restrictAway
      ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
      (cyclotomicModulus K m).support.finite_toSet) := by
  rw [restrictAway_galoisCharacterUnitaryWeight]
  exact RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ

end MonoidHom
