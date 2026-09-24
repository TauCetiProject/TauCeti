/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Basic
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.PartialSums

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

* `MonoidHom.hasCancellation_restrict_galoisCharacterUnitaryWeight`: the weight restricted away
  from the primes dividing `m` has cancellation.
-/

public section

open IsDedekindDomain TauCeti TauCeti.GlobalNumberFields NumberField.Chebotarev
open scoped nonZeroDivisors NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- The ideal partial sums of the Galois weight with the Euler factors at the primes dividing `m`
-- deleted are the partial sums of the ray class character `χ ∘ cyclotomicArtin K F m`.
private theorem idealSummatory_restrict_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (x : ℝ) :
    idealSummatory K ((galoisCharacterUnitaryWeight (L := F) χ).restrict
        ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
        (cyclotomicModulus K m).support.finite_toSet).toIdealArithmeticFunction x =
      rayClassCharacterPartialSum (cyclotomicModulus K m) (χ.comp (cyclotomicArtin K F m)) x := by
  classical
  set 𝔪 := cyclotomicModulus K m
  have hmem (J : Ideal (𝓞 K)) : J ∈ integralIdealsPrimeTo 𝔪 ↔ J.IsPrimeTo 𝔪.support :=
    NumberFieldArithmetic.mem_integralIdealsAway_iff.trans Ideal.isPrimeTo_iff.symm
  let e : integralIdealsPrimeTo 𝔪 → (Ideal (𝓞 K))⁰ := fun I ↦
    ⟨I, mem_nonZeroDivisors_of_ne_zero ((hmem I).mp I.2).ne_bot⟩
  have hsum : rayClassCharacterPartialSum 𝔪 (χ.comp (cyclotomicArtin K F m)) x =
      ∑ I ∈ normLE (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x,
        (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ) := by
    rw [rayClassCharacterPartialSum_def, ← finsum_mem_coe_finset, coe_normLE]
    exact finsum_set_coe_eq_finsum_mem
      (f := fun I ↦ (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ)) _
  rw [hsum, idealSummatory_apply]
  refine (Finset.sum_of_injOn e (fun I _ J _ h ↦ Subtype.ext (by simpa [e] using h))
    (fun I hI ↦ by simpa [e] using hI) (fun J hJ hJe ↦ ?_) (fun I _ ↦ ?_)).symm
  · simpa using fun hJ𝔪 ↦ absurd ⟨⟨J, (hmem J).mpr hJ𝔪⟩, by simpa using hJ, rfl⟩ hJe
  · simpa [e, 𝔪, (hmem I).mp I.2] using (galoisCharacterWeight_eq_onIdeals_cyclotomicArtin χ I).symm

/-- **Cancellation for a cyclotomic Galois character, away from the level.** For `F = K(μ_m)`
and a character `χ` of `Gal(F/K)` whose ray class character `χ ∘ cyclotomicArtin K F m` is
nontrivial, the ideal weight of `χ` with the Euler factors at the primes dividing `m` deleted has
cancellation. -/
theorem hasCancellation_restrict_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) :
    HasCancellation ((galoisCharacterUnitaryWeight (L := F) χ).restrict
      ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
      (cyclotomicModulus K m).support.finite_toSet) := by
  simpa [hasCancellation_iff_isBigO, idealSummatory_restrict_galoisCharacterUnitaryWeight] using
    isBigO_rayClassCharacterPartialSum _ _ hχ

end MonoidHom
