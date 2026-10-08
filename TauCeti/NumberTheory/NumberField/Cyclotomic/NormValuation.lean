/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RamificationInertia.Inertia
import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Frobenius.Tower
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Norms from subfields of a cyclotomic field at primes not dividing the level

Let `K` be a subfield of the `n`-th cyclotomic field `F` over `ℚ` and `p` a prime not dividing `n`.
The automorphism `ζ ↦ ζ ^ p` of `F` is an arithmetic Frobenius at every prime above `p`, so its
`f`-th power fixes `K`, where `f` is the residue degree of a prime of `K` above `p`. The `p`-adic
valuation of the absolute norm of an ideal of `K`, and hence of the norm `N_{K/ℚ}(x)` of an element
of `K`, is a sum of such residue degrees. So `ζ ↦ ζ ^ (p ^ v_p(N_{K/ℚ} x))` fixes `K`.

This is the contribution of the primes not dividing `n` to the product formula for the explicit
cyclotomic symbols, applied to the norm of an element of `K`.

## Main results

* `TauCeti.NumberField.galEquivZMod_symm_pow_inertiaDeg_mem_fixingSubgroup`: `ζ ↦ ζ ^ (p ^ f)`
  fixes `K`, for `f` the residue degree of a prime of `K` above `p`.
* `TauCeti.NumberField.galEquivZMod_symm_pow_padicValNat_absNorm_mem_fixingSubgroup`: the same for
  the exponent `p ^ v_p(𝔑 I)`, for an ideal `I` of `K`.
* `TauCeti.NumberField.galEquivZMod_symm_zpow_padicValRat_norm_mem_fixingSubgroup`: the same for
  the exponent `p ^ v_p(N_{K/ℚ} x)`, for `x ∈ K`.
-/

public section

open Ideal IsCyclotomicExtension NumberField

open scoped NumberField

namespace TauCeti.NumberField

variable {n : ℕ} [NeZero n] {F : Type*} [Field F] [NumberField F]
  [IsCyclotomicExtension {n} ℚ F] {p : ℕ} [Fact p.Prime]

/-- **A residue-degree power of `p` fixes the subfield.** Let `K` be a subfield of the `n`-th
cyclotomic field `F` and `P` a prime of `K` above `p ∤ n`. Raising roots of unity to the power
`p ^ f(P/p)` fixes `K`. -/
theorem galEquivZMod_symm_pow_inertiaDeg_mem_fixingSubgroup (hp : p.Coprime n)
    (K : IntermediateField ℚ F) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})] :
    (Rat.galEquivZMod n F).symm (ZMod.unitOfCoprime p hp ^ P.inertiaDeg ℤ) ∈
      K.fixingSubgroup := by
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {n} ℚ F
  obtain ⟨Q, -, hQ, hQP⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 F))
    (by simp [comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 F))])
  have : Q.LiesOver P := ⟨hQP.symm⟩
  have : Q.LiesOver (span {(p : ℤ)}) := LiesOver.trans Q P _
  set σ := (Rat.galEquivZMod n F).symm (ZMod.unitOfCoprime p hp)
  have hσ : IsArithFrobAt (𝓞 ℚ) σ Q := by
    rw [isArithFrobAt_ringOfIntegers_rat_iff,
      isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime hp Q σ, MulEquiv.apply_symm_apply]
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
    have : Q.LiesOver (Q.under (𝓞 ℚ)) := ⟨rfl⟩
    refine isUnramifiedAt_of_natCast_notMem F n (p := Q.under (𝓞 ℚ)) (fun hn ↦ ?_) Q
    have hnQ : ((n : ℤ) : 𝓞 F) ∈ Q := by simpa using hn
    have hdvd : (p : ℤ) ∣ n := by
      rw [← mem_span_singleton, Q.over_def (span {(p : ℤ)}), mem_comap]
      simpa using hnQ
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hp (by exact_mod_cast hdvd)
  rw [map_pow, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h := pow_inertiaDeg_apply_algebraMap hσ (⟨x, hx⟩ : K)
  rwa [hQP, inertiaDeg_ringOfIntegers_rat_eq_int] at h

/-- Raising roots of unity to the power `p ^ v_p(𝔑 I)` fixes `K`, for every ideal `I` of a subfield
`K` of the `n`-th cyclotomic field and `p ∤ n`. -/
theorem galEquivZMod_symm_pow_padicValNat_absNorm_mem_fixingSubgroup (hp : p.Coprime n)
    (K : IntermediateField ℚ F) (I : Ideal (𝓞 K)) :
    (Rat.galEquivZMod n F).symm (ZMod.unitOfCoprime p hp ^ padicValNat p (absNorm I)) ∈
      K.fixingSubgroup := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Submodule.zero_eq_bot, absNorm_bot, padicValNat_zero_right, pow_zero, map_one]
    exact one_mem _
  | h₂ I hI =>
    rw [Ideal.isUnit_iff.mp hI, absNorm_top, padicValNat_one_right, pow_zero, map_one]
    exact one_mem _
  | h₃ I P hI hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have : P.IsPrime := (Ideal.prime_iff_isPrime hP0).mp hP
    rw [map_mul, padicValNat.mul (absNorm_eq_zero_iff.not.mpr hP0)
      (absNorm_eq_zero_iff.not.mpr hI), pow_add, map_mul]
    refine mul_mem ?_ ih
    -- `P` lies over the rational prime `q = 𝔑 (P ∩ ℤ)`, and `𝔑 P = q ^ f(P/q)`.
    have hq : (absNorm (P.under ℤ)).Prime := by
      rw [Int.prime_absNorm, Ideal.prime_iff_isPrime
        (Ideal.IsIntegral.under_ne_bot ℤ hP0)]
      infer_instance
    have : P.LiesOver (span {((absNorm (P.under ℤ) : ℕ) : ℤ)}) :=
      ⟨by rw [Int.ideal_span_absNorm_eq_self]⟩
    rw [← pow_inertiaDeg (absNorm (P.under ℤ)) P]
    by_cases hqp : absNorm (P.under ℤ) = p
    · have : P.LiesOver (span {(p : ℤ)}) := hqp ▸ this
      rw [hqp, padicValNat.prime_pow]
      exact galEquivZMod_symm_pow_inertiaDeg_mem_fixingSubgroup hp K P
    · have : Fact (absNorm (P.under ℤ)).Prime := ⟨hq⟩
      rw [padicValNat.pow, padicValNat_primes (Ne.symm hqp), mul_zero, pow_zero,
        map_one]
      exact one_mem _

/-- **Norms from a cyclotomic subfield at a prime not dividing the level.** For `K` a subfield of
the `n`-th cyclotomic field, `x ∈ K` and `p ∤ n`, raising roots of unity to the power
`p ^ v_p(N_{K/ℚ} x)` fixes `K`. -/
theorem galEquivZMod_symm_zpow_padicValRat_norm_mem_fixingSubgroup (hp : p.Coprime n)
    (K : IntermediateField ℚ F) (x : K) :
    (Rat.galEquivZMod n F).symm (ZMod.unitOfCoprime p hp ^ padicValRat p (Algebra.norm ℚ x)) ∈
      K.fixingSubgroup := by
  -- On integers the valuation of the norm is that of the absolute norm of the principal ideal.
  have hint (z : 𝓞 K) : padicValRat p (Algebra.norm ℚ (z : K)) =
      padicValNat p (absNorm (span {z})) := by
    rw [← Algebra.coe_norm_int, padicValRat.of_int, absNorm_span_singleton, padicValInt]
  have hmem (z : 𝓞 K) : (Rat.galEquivZMod n F).symm
      (ZMod.unitOfCoprime p hp ^ padicValRat p (Algebra.norm ℚ (z : K))) ∈ K.fixingSubgroup := by
    rw [hint, zpow_natCast]
    exact galEquivZMod_symm_pow_padicValNat_absNorm_mem_fixingSubgroup hp K _
  obtain ⟨⟨d, hd⟩, r, hr⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) x
  by_cases hx : x = 0
  · rw [hx, Algebra.norm_zero, padicValRat.zero, zpow_zero, map_one]
    exact one_mem _
  have hd0 : Algebra.norm ℚ (d : K) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr (by simpa using nonZeroDivisors.ne_zero hd)
  have hnorm : Algebra.norm ℚ (r : K) = Algebra.norm ℚ (d : K) * Algebra.norm ℚ x := by
    rw [RingOfIntegers.coe_eq_algebraMap, hr, Algebra.smul_def, map_mul]
  have hval : padicValRat p (Algebra.norm ℚ x) =
      padicValRat p (Algebra.norm ℚ (r : K)) - padicValRat p (Algebra.norm ℚ (d : K)) := by
    rw [hnorm, padicValRat.mul hd0 (Algebra.norm_ne_zero_iff.mpr hx)]
    ring
  rw [hval, zpow_sub, ← div_eq_mul_inv, map_div]
  exact div_mem (hmem r) (hmem d)

end TauCeti.NumberField
