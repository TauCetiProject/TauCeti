/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.FieldTheory.Finite.Basic

/-!
# Roots of unity modulo a prime of a ring of integers

Let `K` be a number field whose ring of integers contains a primitive `n`-th root of unity, and
let `P` be a prime of `𝓞 K` whose absolute norm `N P` is prime to `n`. Then reduction modulo `P`
identifies the `n`-th roots of unity of `𝓞 K` with those of the residue field `𝓞 K ⧸ P`, and in
particular `N P ≡ 1 (mod n)`.

This is the input needed to define the `n`-th power residue symbol at `P`: an `n`-th root of
unity of the residue field, such as `x ^ ((N P - 1) / n)`, lifts uniquely to `𝓞 K`. Applied to
all of the units of a finite field `F` with `q` elements mapping to `𝓞 K ⧸ P`, which are
`(q - 1)`-th roots of unity, it gives the Teichmüller character `ω : F → 𝓞 K` lifting the map to
the residue field; this is the character whose powers Stickelberger's congruence evaluates.

## Main results

* `NumberField.dvd_absNorm_sub_one`: `n ∣ N P - 1`.
* `NumberField.absNorm_modEq_one`: more generally, `N 𝔞 ≡ 1 (mod n)` for every ideal `𝔞` whose
  norm is prime to `n`.
* `Ideal.eq_of_pow_eq_one_of_mk_eq`: two `n`-th roots of unity of `𝓞 K` congruent modulo a
  proper ideal `P` with `N P` prime to `n` are equal.
* `Ideal.rootsOfUnityEquivQuot`: reduction modulo `P` as an isomorphism between the `n`-th roots
  of unity of `𝓞 K` and those of `𝓞 K ⧸ P`.
* `Ideal.pow_absNorm_sub_one_div_mem_rootsOfUnity`: `u ^ ((N P - 1) / n)` is an `n`-th root of
  unity for every unit `u` of `𝓞 K ⧸ P`.
* `Ideal.exists_mulChar_mk_eq`: a ring homomorphism from a finite field with `q` elements to
  `𝓞 K ⧸ P` lifts to a multiplicative character with values in `𝓞 K`, the Teichmüller character,
  when `𝓞 K` contains a primitive `(q - 1)`-th root of unity.

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
theorem NumberField.dvd_absNorm_sub_one {n : ℕ} [HasEnoughRootsOfUnity (𝓞 K) n]
    {P : Ideal (𝓞 K)} [P.IsPrime]
    (hP : (Ideal.absNorm P).Coprime n) : n ∣ Ideal.absNorm P - 1 := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [Nat.coprime_zero_right, Ideal.absNorm_eq_one_iff] at hP
    exact absurd hP Ideal.IsPrime.ne_top'
  have : NeZero n := ⟨hn⟩
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

/-- **The norm of an ideal prime to `n` is one modulo `n`.** If `𝓞 K` contains a primitive
`n`-th root of unity and the absolute norm of the ideal `𝔞` is prime to `n`, then
`N 𝔞 ≡ 1 (mod n)`. For a prime `𝔞` this is `NumberField.dvd_absNorm_sub_one`. -/
theorem NumberField.absNorm_modEq_one {n : ℕ} [HasEnoughRootsOfUnity (𝓞 K) n]
    {𝔞 : Ideal (𝓞 K)} (h𝔞 : (Ideal.absNorm 𝔞).Coprime n) : Ideal.absNorm 𝔞 ≡ 1 [MOD n] := by
  -- Induct on the factorisation of `𝔞` into primes; the norm is multiplicative.
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Ideal.zero_eq_bot, Ideal.absNorm_bot, Nat.coprime_zero_left] at h𝔞
    rw [h𝔞]
    exact Nat.modEq_one
  | h₂ 𝔞 h => rw [Ideal.isUnit_iff.mp h, Ideal.absNorm_top]
  | h₃ 𝔞 P _ hP ih =>
    have := Ideal.isPrime_of_prime hP
    rw [map_mul, Nat.coprime_mul_iff_left] at h𝔞
    rw [map_mul]
    have hP₀ : 1 ≤ Ideal.absNorm P :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
    simpa using ((Nat.modEq_iff_dvd' hP₀).mpr (dvd_absNorm_sub_one h𝔞.1)).symm.mul (ih h𝔞.2)

namespace Ideal

/-- Two `n`-th roots of unity of `𝓞 K` that are congruent modulo a proper ideal `P` with `N P`
prime to `n` are equal. -/
theorem eq_of_pow_eq_one_of_mk_eq {n : ℕ} {P : Ideal (𝓞 K)} (hP₁ : P ≠ ⊤)
    (hP : (absNorm P).Coprime n) {μ ν : 𝓞 K} (hμ : μ ^ n = 1) (hν : ν ^ n = 1)
    (h : Ideal.Quotient.mk P μ = Ideal.Quotient.mk P ν) : μ = ν := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [Nat.coprime_zero_right, absNorm_eq_one_iff] at hP
    exact absurd hP hP₁
  have : NeZero n := ⟨hn⟩
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

omit [NeZero n] in
/-- If `N P` is prime to `n` and `𝓞 K` contains a primitive `n`-th root of unity, then the
`(N P - 1) / n`-th power of a unit of the residue field is an `n`-th root of unity. -/
theorem pow_absNorm_sub_one_div_mem_rootsOfUnity (hP : (absNorm P).Coprime n)
    (u : (𝓞 K ⧸ P)ˣ) : u ^ ((absNorm P - 1) / n) ∈ rootsOfUnity n (𝓞 K ⧸ P) := by
  rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel (dvd_absNorm_sub_one hP),
    pow_absNorm_sub_one_eq_one]

variable (P) in
/-- **The Teichmüller character.** Let `F` be a finite field with `q` elements and
`f : F →+* 𝓞 K ⧸ P`. If `𝓞 K` contains a primitive `(q - 1)`-th root of unity, then `f` lifts
to a multiplicative character `ω` of `F` with values in `𝓞 K`: `ω x ≡ f x (mod P)` for every `x`.
On `x ≠ 0`, `ω x` is the unique `(q - 1)`-th root of unity of `𝓞 K` reducing to `f x`. -/
theorem exists_mulChar_mk_eq {F : Type*} [Field F] [Fintype F] (f : F →+* 𝓞 K ⧸ P)
    [HasEnoughRootsOfUnity (𝓞 K) (Fintype.card F - 1)] :
    ∃ ω : MulChar F (𝓞 K), ∀ x, Ideal.Quotient.mk P (ω x) = f x := by
  have : NeZero (Fintype.card F - 1) := ⟨by have := Fintype.one_lt_card (α := F); omega⟩
  -- `F` and `𝓞 K ⧸ P` have the same characteristic `p`, so `N P` and `q` are powers of `p`, and
  -- `N P` is prime to `q - 1`.
  have hP : (absNorm P).Coprime (Fintype.card F - 1) := by
    let _ := Ideal.Quotient.field P
    let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
    have : CharP (𝓞 K ⧸ P) (ringChar F) := (f.charP_iff f.injective _).1 (ringChar.charP F)
    obtain ⟨a, hp, ha⟩ := FiniteField.card F (ringChar F)
    obtain ⟨b, -, hb⟩ := FiniteField.card (𝓞 K ⧸ P) (ringChar F)
    rw [absNorm_eq_natCard, Nat.card_eq_fintype_card, hb, ha]
    refine Nat.Coprime.pow_left _ (((Nat.coprime_self_sub_right ?_).2
      (Nat.coprime_one_right _)).coprime_dvd_left (dvd_pow_self _ a.ne_zero))
    exact Nat.one_le_pow _ _ hp.pos
  -- Every unit of `F` is a `(q - 1)`-th root of unity, and so is its image under `f`.
  let φ : Fˣ →* rootsOfUnity (Fintype.card F - 1) (𝓞 K ⧸ P) :=
    (Units.map f.toMonoidHom).codRestrict _ fun u ↦ by
      have hu : u ^ (Fintype.card F - 1) = 1 :=
        Units.ext (by simpa using FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero)
      rw [mem_rootsOfUnity, ← map_pow, hu, map_one]
  refine ⟨MulChar.ofUnitHom ((rootsOfUnity _ _).subtype.comp
    ((rootsOfUnityEquivQuot P _ hP).symm.toMonoidHom.comp φ)), fun x ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · rw [MulChar.map_zero, map_zero, map_zero]
  lift x to Fˣ using hx.isUnit
  rw [MulChar.ofUnitHom_coe]
  simp [φ]

end Ideal
