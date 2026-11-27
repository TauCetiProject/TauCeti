/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Cyclotomic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction

/-!
# Odd-order Frobenius after complex conjugation

In a Galois extension of number fields `L/K` with a primitive `2 ^ n`-th root `ζ` in `L`, let
`E` be a normal subfield containing `ζ + ζ⁻¹`. An odd-order product of arithmetic Frobenius
and complex conjugation on `E` forces the norm of the prime of `K` to be `1` or `-1` modulo
`2 ^ n`; over `K = ℚ` this norm is the rational prime itself. The real cyclotomic subfield is
specified by its generator `ζ + ζ⁻¹`, so `E` need not contain `ζ` itself. This restricts the
residue classes that can contribute when prime sums are indexed by the order of conjugated
Frobenius.

The cyclotomic description of the real subfield is classical; see Washington,
*Introduction to Cyclotomic Fields*, Chapter 3. In a normal tower the specified Frobenius
lifts by `IsArithFrobAt.exists_isArithFrobAt_restrictNormal_eq`, even when it is not unique.
-/

public section

open scoped NumberField

namespace IsPrimitiveRoot

/-- If an automorphism restricts to odd order on a normal subfield containing `ζ + ζ⁻¹`, its
cyclotomic exponent on the primitive dyadic root `ζ` is a sign. -/
theorem autToPow_eq_one_or_neg_one_of_odd_orderOf_restrictNormal
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (E : IntermediateField K L) [Normal K E]
    (hreal : ζ + ζ⁻¹ ∈ E) {τ : L ≃ₐ[K] L} (hodd : Odd (orderOf (τ.restrictNormal E))) :
    hζ.autToPow K τ = 1 ∨ hζ.autToPow K τ = -1 := by
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
  -- `restrictNormalHom` packages `restrictNormal` as a monoid hom, to rewrite powers.
  have hr (σ : L ≃ₐ[K] L) : r σ = σ.restrictNormal E := rfl
  let d := orderOf (τ.restrictNormal E)
  have hd : Odd d := hodd
  have hres : (τ ^ d).restrictNormal E = 1 := by rw [← hr, map_pow, hr, pow_orderOf_eq_one]
  have hfix : (τ ^ d) (ζ + ζ⁻¹) = ζ + ζ⁻¹ :=
    (AlgEquiv.restrictNormal_eq_one_iff E (τ ^ d)).mp hres (ζ + ζ⁻¹) hreal
  have hpow := (hζ.autToPow_eq_one_or_neg_one_iff (τ ^ d)).mpr hfix
  rw [map_pow] at hpow
  -- An odd power acts injectively on the entire dyadic unit group and fixes both signs.
  have hcard : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by
    cases n with
    | zero => simp [Nat.card_eq_fintype_card]
    | succ n => simp [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow_succ Nat.prime_two]
  have hcop : (Nat.card (ZMod (2 ^ n))ˣ).Coprime d := by
    rw [hcard]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hd.not_two_dvd_nat).pow_left _
  exact hpow.imp (fun h ↦ (powCoprime hcop).injective (h.trans (one_pow d).symm))
    (fun h ↦ (powCoprime hcop).injective (h.trans hd.neg_one_pow.symm))

open NumberField NumberField.InfinitePlace Ideal

/-- Let `L/K` be a Galois extension of number fields, `ζ` a primitive `2 ^ n`-th root in `L`,
and `E` a normal subfield containing `ζ + ζ⁻¹`. If the product of complex conjugation and
arithmetic Frobenius on `E` at a prime `𝔭` of `K` not dividing `2 ^ n` has odd order, then the
norm of `𝔭` is congruent to `1` or `-1` modulo `2 ^ n`. The conjugation on `E` is the restriction
of the conjugation attached to the chosen infinite place of `L`, ramified over `K`. For `K = ℚ`
the norm is the rational prime. -/
theorem natCast_absNorm_eq_one_or_neg_one_of_odd_orderOf_complexConjugation_mul
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {n : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ n))
    (E : IntermediateField K L) [Normal K E] (hreal : ζ + ζ⁻¹ ∈ E)
    (w : InfinitePlace L) (hw : w.IsRamified K)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hm : ((2 ^ n : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal]
    {σ : E ≃ₐ[K] E} (hσ : IsArithFrobAt (𝓞 K) σ P)
    (hodd : Odd (orderOf
      ((TauCeti.NumberField.complexConjugationAt K w hw).restrictNormal E * σ))) :
    (absNorm 𝔭.asIdeal : ZMod (2 ^ n)) = 1 ∨ (absNorm 𝔭.asIdeal : ZMod (2 ^ n)) = -1 := by
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  let : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP inferInstance
  obtain ⟨Q, hQmax, hQP⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) P
  let : Q.IsPrime := hQmax.isPrime
  let : Q.LiesOver 𝔭.asIdeal := hQP.trans Q P 𝔭.asIdeal
  -- Lift the specified Frobenius, not just an arbitrary representative at `Q`.
  obtain ⟨τ, hτ, hres⟩ := hσ.exists_isArithFrobAt_restrictNormal_eq E Q
    (ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
  let c := TauCeti.NumberField.complexConjugationAt K w hw
  have hmul : (c * τ).restrictNormal E = c.restrictNormal E * τ.restrictNormal E :=
    AlgEquiv.restrictNormal_trans τ c E
  have hcτ : Odd (orderOf ((c * τ).restrictNormal E)) := by rwa [hmul, hres]
  have hsign := hζ.autToPow_eq_one_or_neg_one_of_odd_orderOf_restrictNormal E hreal hcτ
  rw [map_mul, hζ.autToPow_complexConjugationAt w hw] at hsign
  have hval := hτ.autToPow_eq_absNorm hζ 𝔭 hm Q
  rcases hsign with h | h
  · right
    simpa [hval] using congrArg (fun u : (ZMod (2 ^ n))ˣ ↦ -(u : ZMod (2 ^ n))) h
  · left
    simpa [hval] using congrArg (fun u : (ZMod (2 ^ n))ˣ ↦ -(u : ZMod (2 ^ n))) h

end IsPrimitiveRoot
