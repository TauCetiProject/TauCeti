/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Roots of unity modulo a prime of a ring of integers

Let `K` be a number field whose ring of integers contains a primitive `n`-th root of unity, and
let `P` be a prime of `𝓞 K` whose absolute norm `N P` is prime to `n`. Then reduction modulo `P`
identifies the `n`-th roots of unity of `𝓞 K` with those of the residue field `𝓞 K ⧸ P`, and in
particular `N P ≡ 1 (mod n)`.

This is the input needed to define the `n`-th power residue symbol at `P`: an `n`-th root of
unity of the residue field, such as `x ^ ((N P - 1) / n)`, lifts uniquely to `𝓞 K`.

## Main results

* `NumberField.dvd_absNorm_sub_one`: `n ∣ N P - 1`.
* `Ideal.eq_of_pow_eq_one_of_mk_eq`: two `n`-th roots of unity of `𝓞 K` congruent modulo a
  proper ideal `P` with `N P` prime to `n` are equal.
* `Ideal.rootsOfUnityEquivQuot`: reduction modulo `P` as an isomorphism between the `n`-th roots
  of unity of `𝓞 K` and those of `𝓞 K ⧸ P`.
* `Ideal.pow_absNorm_sub_one_div_mem_rootsOfUnity`: `u ^ ((N P - 1) / n)` is an `n`-th root of
  unity for every unit `u` of `𝓞 K ⧸ P`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2.
-/

public section

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The norm of a prime not dividing `n` is one modulo `n`.** If `𝓞 K` contains a primitive
`n`-th root of unity and the absolute norm of the prime `P` is prime to `n`, then
`n ∣ N P - 1`. The proof adapts Mathlib's `NumberField.torsionOrder_dvd_absNorm_sub_one`, with `n`
in place of the torsion order. -/
theorem NumberField.dvd_absNorm_sub_one {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity (𝓞 K) n]
    {P : Ideal (𝓞 K)} [P.IsPrime]
    (hP : (Ideal.absNorm P).Coprime n) : n ∣ Ideal.absNorm P - 1 := by
  obtain rfl | hP₀ := eq_or_ne P ⊥
  · rw [Ideal.absNorm_bot, Nat.coprime_zero_left] at hP
    subst hP
    exact one_dvd _
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ ‹_›
  let _ := Ideal.Quotient.field P
  have h := Subgroup.card_dvd_of_injective _ (Ideal.rootsOfUnityMapQuot_injective n
    (Ideal.absNorm_eq_one_iff.not.mpr Ideal.IsPrime.ne_top') hP)
  rwa [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_units,
    ← Ideal.absNorm_eq_natCard] at h

namespace Ideal

/-- Two `n`-th roots of unity of `𝓞 K` that are congruent modulo a proper ideal `P` with `N P`
prime to `n` are equal. -/
theorem eq_of_pow_eq_one_of_mk_eq {n : ℕ} [NeZero n] {P : Ideal (𝓞 K)} (hP₁ : P ≠ ⊤)
    (hP : (absNorm P).Coprime n) {μ ν : 𝓞 K} (hμ : μ ^ n = 1) (hν : ν ^ n = 1)
    (h : Ideal.Quotient.mk P μ = Ideal.Quotient.mk P ν) : μ = ν := by
  have := rootsOfUnityMapQuot_injective (I := P) n (absNorm_eq_one_iff.not.mpr hP₁) hP
    (a₁ := rootsOfUnity.mkOfPowEq μ hμ) (a₂ := rootsOfUnity.mkOfPowEq ν hν) (by ext; simpa)
  simpa using congrArg (fun z : rootsOfUnity n (𝓞 K) ↦ ((z : (𝓞 K)ˣ) : 𝓞 K)) this

variable (P : Ideal (𝓞 K)) [P.IsMaximal]

/-- Every unit of the residue field `𝓞 K ⧸ P` has order dividing `N P - 1`. -/
theorem pow_absNorm_sub_one_eq_one (u : (𝓞 K ⧸ P)ˣ) : u ^ (absNorm P - 1) = 1 := by
  let _ := Ideal.Quotient.field P
  rw [absNorm_eq_natCard, ← Nat.card_units]
  exact pow_card_eq_one'

/-- **Reduction of roots of unity modulo a prime not dividing `n`.** If `𝓞 K` contains a
primitive `n`-th root of unity and `N P` is prime to `n`, then reduction modulo `P` is an
isomorphism from the `n`-th roots of unity of `𝓞 K` onto those of the residue field. -/
noncomputable def rootsOfUnityEquivQuot (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity (𝓞 K) n]
    (hP : (absNorm P).Coprime n) : rootsOfUnity n (𝓞 K) ≃* rootsOfUnity n (𝓞 K ⧸ P) :=
  MulEquiv.ofBijective (restrictRootsOfUnity (Ideal.Quotient.mk P) n) <| by
    refine Function.Injective.bijective_of_nat_card_le (fun x y hxy ↦ ?_) ?_
    · obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      refine rootsOfUnityMapQuot_injective n (absNorm_eq_one_iff.not.mpr IsPrime.ne_top') hP ?_
      ext
      simpa [restrictRootsOfUnity_coe_apply] using
        congrArg (fun z : rootsOfUnity n (𝓞 K ⧸ P) ↦ ((z : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) hxy
    · rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity (𝓞 K) n]
      exact card_rootsOfUnity _ _

variable {P} {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity (𝓞 K) n]

/-- The isomorphism `rootsOfUnityEquivQuot` is reduction modulo `P`. -/
@[simp]
theorem coe_rootsOfUnityEquivQuot_apply (hP : (absNorm P).Coprime n) (ζ : rootsOfUnity n (𝓞 K)) :
    ((rootsOfUnityEquivQuot P n hP ζ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) =
      Ideal.Quotient.mk P ((ζ : (𝓞 K)ˣ) : 𝓞 K) :=
  restrictRootsOfUnity_coe_apply _ ζ

/-- The inverse of `rootsOfUnityEquivQuot` lifts a root of unity of the residue field to the
unique root of unity of `𝓞 K` reducing to it. -/
@[simp]
theorem mk_coe_rootsOfUnityEquivQuot_symm_apply (hP : (absNorm P).Coprime n)
    (ζ : rootsOfUnity n (𝓞 K ⧸ P)) :
    Ideal.Quotient.mk P (((rootsOfUnityEquivQuot P n hP).symm ζ : (𝓞 K)ˣ) : 𝓞 K) =
      ((ζ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) := by
  rw [← coe_rootsOfUnityEquivQuot_apply hP, MulEquiv.apply_symm_apply]

/-- If `N P` is prime to `n` and `𝓞 K` contains a primitive `n`-th root of unity, then the
`(N P - 1) / n`-th power of a unit of the residue field is an `n`-th root of unity. -/
theorem pow_absNorm_sub_one_div_mem_rootsOfUnity (hP : (absNorm P).Coprime n)
    (u : (𝓞 K ⧸ P)ˣ) : u ^ ((absNorm P - 1) / n) ∈ rootsOfUnity n (𝓞 K ⧸ P) := by
  rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel (dvd_absNorm_sub_one hP),
    pow_absNorm_sub_one_eq_one]

end Ideal
