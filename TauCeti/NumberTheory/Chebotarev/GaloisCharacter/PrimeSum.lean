/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.PrimeSum
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Orthogonality
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum

/-!
# Prime sums of Galois characters

For a finite Galois extension `L / K` of number fields and a character `χ` of `Gal(L/K)`, the
prime sum `P_χ(t) = ∑_𝔭 χ(Frob 𝔭) N𝔭^{-t}` of the ideal weight `MonoidHom.galoisCharacterWeight χ`
is the input to character-sum proofs of Chebotarev density. This file records how these prime sums
combine. When `Gal(L/K)` is abelian, character orthogonality turns `∑_χ χ(σ)⁻¹ P_χ(t)` into
`#Gal(L/K)` times the prime zeta sum over the Frobenius fibre of `σ`. The trivial character
contributes the prime zeta sum over the unramified primes.

## Main results

* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_eq_ite`: character orthogonality at every
  height-one prime, ramified or not.
* `MonoidHom.primeSum_galoisCharacterWeight_one`: the prime sum of the trivial character is the
  prime zeta sum over the unramified primes.
* `AlgEquiv.natCard_mul_primeIdealZetaSum_frobeniusPrimeSet`: for `t > 1`, `#Gal(L/K)` times the
  prime zeta sum over the Frobenius fibre of `σ` is `∑_χ χ(σ)⁻¹ P_χ(t)`.
-/

public section

open IsDedekindDomain NumberField NumberField.Chebotarev TauCeti
open scoped NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

namespace MonoidHom

variable (K L) in
/-- The prime sum of the trivial character is the prime zeta sum over the unramified primes. -/
theorem primeSum_galoisCharacterWeight_one (t : ℝ) :
    (galoisCharacterWeight (L := L) (1 : (L ≃ₐ[K] L) →* ℂˣ)).primeSum t =
      ((↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ.primeIdealZetaSum t : ℂ) := by
  classical
  simp [Set.ofReal_primeIdealZetaSum, MultiplicativeIdealWeight.primeSum_def,
    Ideal.isPrimeTo_asIdeal_iff]

end MonoidHom

namespace AlgEquiv

open scoped Classical IsMulCommutative in
/-- **Character orthogonality at every prime.** For `L / K` abelian, the sum of
`χ(σ)⁻¹ · galoisCharacterWeight χ 𝔭` over the characters `χ` of `Gal(L/K)` is `#Gal(L/K)` when
`𝔭` lies in the Frobenius fibre of `σ`, and `0` otherwise, ramified primes included. -/
theorem sum_inv_mul_galoisCharacterWeight_apply_eq_ite [IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) (P : HeightOneSpectrum (𝓞 K)) :
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := L) χ P.asIdeal =
      if P ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) then (Nat.card (L ≃ₐ[K] L) : ℂ) else 0 := by
  by_cases hP : P ∈ ramifiedPrimes K L
  · rw [σ.sum_inv_mul_galoisCharacterWeight_apply_eq_zero_of_mem_ramifiedPrimes P hP,
      ite_eq_right fun h ↦ frobeniusPrimeSet_subset_compl_ramifiedPrimes _ h hP]
  · rw [mem_ramifiedPrimes_iff, not_not] at hP
    rw [σ.sum_inv_mul_galoisCharacterWeight_apply_of_unramified P hP,
      mem_frobeniusPrimeSet_iff_artinSymbol_eq hP]
    generalize artinSymbol P.asIdeal hP = c
    -- In an abelian group a conjugacy class is the class of its representative alone.
    congr 1
    have hc : ConjClasses.mk c.out = c := Quotient.out_eq c
    rw [← ConjClasses.mk_injective.eq_iff (a := c.out), hc]

/-- **The Frobenius fibre by orthogonality.** For `L / K` abelian and `t > 1`, `#Gal(L/K)` times
the prime zeta sum over the Frobenius fibre of `σ` is `∑_χ χ(σ)⁻¹ P_χ(t)`. -/
theorem natCard_mul_primeIdealZetaSum_frobeniusPrimeSet [IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) {t : ℝ} (ht : 1 < t) :
    (Nat.card (L ≃ₐ[K] L) : ℂ) *
        ((frobeniusPrimeSet K L (ConjClasses.mk σ)).primeIdealZetaSum t : ℂ) =
      ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * (MonoidHom.galoisCharacterWeight (L := L) χ).primeSum t := by
  simp only [MultiplicativeIdealWeight.primeSum_def, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun χ _ ↦
      ((MonoidHom.galoisCharacterWeight χ).summable_div_of_summable_idealTerm
        (χ.summable_idealTerm_galoisCharacterWeight (by simpa using ht))).mul_left _,
    Set.ofReal_primeIdealZetaSum, ← tsum_mul_left]
  refine tsum_congr fun P ↦ ?_
  simp only [mul_div_assoc', ← Finset.sum_div, sum_inv_mul_galoisCharacterWeight_apply_eq_ite]
  simp

end AlgEquiv
