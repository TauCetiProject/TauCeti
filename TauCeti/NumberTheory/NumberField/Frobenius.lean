/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import TauCeti.RingTheory.Frobenius
public import TauCeti.NumberTheory.LegendreSymbol.Frobenius
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.IntegralSqrt
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# Frobenius elements of number fields and their action on square roots

For an extension `L/K` of number fields and a prime `Q` of `𝓞 L`, an arithmetic Frobenius
at `Q` is an automorphism `σ : L ≃ₐ[K] L` satisfying
`σ x ≡ x ^ #(𝓞 K ⧸ Q ∩ 𝓞 K) (mod Q)` for every `x : 𝓞 L`. The exponent is the
cardinality of the *base* residue ring, not the absolute norm of `Q`.

This file specializes Mathlib's Frobenius API to number fields:

* Frobenius elements exist at every nonzero prime in a Galois extension. The rational-prime
  form uses the base ring `ℤ`, with exponent `p`, whereas the relative form at `K = ℚ` uses
  the carrier `𝓞 ℚ`.
* At an unramified prime, two Frobenius automorphisms coincide. This conditional uniqueness
  requires no Galois hypothesis on the extension.
* An isomorphism of extensions transports the Frobenius condition to the matching ideal.

The square-root formulas work in any characteristic-zero field. At an ideal above an odd
prime `p`, a Frobenius sends a square root of an integer `d` with `p ∤ d` to
`legendreSym p d` times that root. At an ideal above `2`, for `d ≡ 1 (mod 4)`, it fixes the
root exactly when `d ≡ 1 (mod 8)` and negates it otherwise. These formulas describe Frobenius
on every generator of a multiquadratic field.

## Main results

* `NumberField.exists_isArithFrobAt`: a relative Frobenius exists at every nonzero prime in
  a Galois extension of number fields.
* `NumberField.exists_isArithFrobAt_int_of_liesOver`: a `ℤ`-carrier Frobenius exists at
  every prime above a rational prime.
* `AlgEquiv.isArithFrobAt_autCongr`: an isomorphism of extensions transports Frobenius.
* `NumberField.isArithFrobAt_eq_of_isUnramifiedAt` and
  `NumberField.subsingleton_isArithFrobAt`: uniqueness at an unramified prime.
* `NumberField.isArithFrobAt_apply_sqrt` and
  `NumberField.isArithFrobAt_apply_sqrt_eq_self_iff`: the odd-prime square-root action and
  its fixing criterion.
* `TauCeti.isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight` and
  `TauCeti.isArithFrobAt_apply_sqrt_two`: the square-root action at `2`.
-/

public section

open Ideal

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

variable (K) in
/-- **Relative Frobenius elements exist.** For a finite Galois extension `L/K` of number fields
and a nonzero prime `Q` of `𝓞 L`, some `σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`. -/
theorem exists_isArithFrobAt {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ Q := by
  let _ : Finite (𝓞 L ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQ
  exact IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) Q

/-- A Frobenius relative to the base ring `ℤ` exists at every prime of `𝓞 K` lying over the
rational prime `(p)`; its exponent is therefore `p`. This is distinct from
`exists_isArithFrobAt ℚ`, whose base-ring carrier is `𝓞 ℚ` rather than `ℤ`. -/
theorem exists_isArithFrobAt_int_of_liesOver [IsGalois ℚ K] {p : ℕ} [Fact p.Prime]
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q := by
  have hp : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  let _ : Finite (𝓞 K ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp Q)
  exact IsArithFrobAt.exists_of_isInvariant ℤ (K ≃ₐ[ℚ] K) Q

end NumberField

namespace AlgEquiv

variable {K L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']

/-- **A Frobenius travels along an isomorphism of extensions.** If `σ` is an arithmetic Frobenius
at `Q`, then `AlgEquiv.autCongr e σ` is one at the prime of `𝓞 L'` matching `Q`. -/
theorem isArithFrobAt_autCongr (e : L ≃ₐ[K] L') {Q : Ideal (𝓞 L)} {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    IsArithFrobAt (𝓞 K) (autCongr e σ)
      (Q.comap (NumberField.RingOfIntegers.mapAlgEquiv e).symm) := by
  have hunder : (Q.comap (NumberField.RingOfIntegers.mapAlgEquiv e).symm).under (𝓞 K) =
      Q.under (𝓞 K) :=
    (Ideal.LiesOver.over (p := Q.under (𝓞 K))
      (P := Q.comap (NumberField.RingOfIntegers.mapAlgEquiv e).symm)).symm
  intro x
  rw [MulSemiringAction.toAlgHom_apply, Ideal.mem_comap, hunder, map_sub, map_pow,
    e.mapAlgEquiv_symm_autCongr_smul, ← MulSemiringAction.toAlgHom_apply (𝓞 K)]
  exact hσ _

end AlgEquiv

namespace NumberField

/-! ### Uniqueness at unramified primes -/

/-- At an unramified prime of `𝓞 L`, two arithmetic Frobenius automorphisms of an extension
`L/K` of number fields coincide. No normality hypothesis is needed.

This is a conditional uniqueness statement and makes no existence assertion, so `Q` need not be
assumed nonzero. -/
theorem isArithFrobAt_eq_of_isUnramifiedAt {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L]
    {σ τ : L ≃ₐ[K] L} {Q : Ideal (𝓞 L)} [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (hτ : IsArithFrobAt (𝓞 K) τ Q) : σ = τ := by
  have h := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ hτ
    (Ideal.primeCompl_le_nonZeroDivisors Q)
  apply AlgEquiv.toRingEquiv_injective
  apply RingEquiv.toRingHom_injective
  -- A number field is the fraction field of its integers, so their images determine the maps.
  apply IsFractionRing.ringHom_ext (A := 𝓞 L)
  intro x
  simpa only [MulSemiringAction.toAlgHom_apply, algebraMap_smul_eq_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv] using
    congrArg (algebraMap (𝓞 L) L) (DFunLike.congr_fun h x)

/-- The Frobenius elements at an unramified prime form a subsingleton. -/
instance subsingleton_isArithFrobAt {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L]
    {Q : Ideal (𝓞 L)} [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    Subsingleton {σ : L ≃ₐ[K] L // IsArithFrobAt (𝓞 K) σ Q} where
  allEq σ τ := Subtype.ext (isArithFrobAt_eq_of_isUnramifiedAt σ.property τ.property)

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime]

/-- **A Frobenius acts on square roots by the Legendre symbol.** Let `K` be a characteristic-zero
field, `p` an odd prime, and `σ : K ≃ₐ[ℚ] K` an arithmetic Frobenius at an ideal `Q` of `𝓞 K` above
`p`. If `x ∈ K` satisfies `x² = d` for an integer `d` with `p ∤ d`, then

`σ x = legendreSym p d • x`:

the Frobenius fixes `√d` when `d` is a quadratic residue mod `p` and negates it otherwise. -/
theorem isArithFrobAt_apply_sqrt (hodd : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K d) (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = legendreSym p d • x := by
  -- Apply the `𝓞 K`-level computation to the packaged square root and push down along `𝓞 K ↪ K`.
  have hsmul : σ • integralSqrt hx = legendreSym p d • integralSqrt hx :=
    IsArithFrobAt.smul_sqrt hσ hodd hd (integralSqrt_sq hx)
  simpa only [map_zsmul, algebraMap_integralSqrt, algebraMap_smul_eq_apply] using
    congrArg (algebraMap (𝓞 K) K) hsmul

/-- **A Frobenius fixes `√d` iff `d` is a quadratic residue mod `p`.** Under the hypotheses of
`NumberField.isArithFrobAt_apply_sqrt`, `σ x = x` exactly when `legendreSym p d = 1`
(the other case being `σ x = -x`, `legendreSym p d = -1`). The ambient field only needs
characteristic zero. -/
theorem isArithFrobAt_apply_sqrt_eq_self_iff (hodd : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K d) (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = x ↔ legendreSym p d = 1 := by
  have hxne : x ≠ 0 := by
    intro h
    have hd0 : (d : K) = 0 := by simpa [h] using hx.symm
    exact hd (by simp [Int.cast_eq_zero.mp hd0])
  rw [isArithFrobAt_apply_sqrt hodd hd hx Q hσ]
  simpa only [one_smul] using
    (smul_left_inj (R := ℤ) hxne (r₁ := legendreSym p d) (r₂ := 1))

end NumberField

/-! ### Frobenius on square roots at 2

For `d ≡ 1 (mod 4)`, an arithmetic Frobenius at a prime above `2` fixes a square root of
`d` exactly when `d ≡ 1 (mod 8)`, and negates it when `d ≡ 5 (mod 8)`. The ambient field
need not be quadratic, so the result applies to each generator of a multiquadratic field.

The two roots have identical reductions in characteristic two. Instead one uses the algebraic
integer `(1 + √d) / 2`, whose conjugate is `1 - (1 + √d) / 2`; their difference has odd square
and hence is nonzero modulo the prime. This is the dyadic counterpart of the Legendre-symbol
formula for Frobenius at odd primes, and supplies its missing local input at an odd discriminant.

The classical quadratic splitting criterion is described in D. A. Cox,
*Primes of the Form x² + ny²*, §5.A.
-/

open NumberField

namespace TauCeti

/-- At a prime above `2`, Frobenius fixes `√d` exactly when `d ≡ 1 (mod 8)`, provided
`d ≡ 1 (mod 4)`. This works in any characteristic-zero field containing the chosen square root. -/
theorem isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight
    {K : Type*} [Field K] [CharZero K] {d : ℤ} {x : K}
    (hx : x ^ 2 = algebraMap ℤ K d) (hd : d % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(2 : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = x ↔ d % 8 = 1 := by
  -- Pass to the integral half-generator before reducing modulo 2.
  let w : 𝓞 K := ⟨(1 + x) / 2, isIntegral_one_add_div_two_of_sq_eq hx hd⟩
  have hw : algebraMap (𝓞 K) K w = (1 + x) / 2 := RingOfIntegers.map_mk _ _
  have hwsq : w ^ 2 - w = algebraMap ℤ (𝓞 K) (d / 4) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simpa only [map_sub, map_pow, hw, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K] using
      sq_one_add_div_two_sub_self hx hd
  have hcong : σ • w - w ^ 2 ∈ Q := by
    have h := hσ w
    rwa [natCard_quotient_under_of_liesOver (p := 2) Q,
      MulSemiringAction.toAlgHom_apply] at h
  have hfix : σ • w = w ↔ σ x = x := by
    rw [← (FaithfulSMul.algebraMap_injective (𝓞 K) K).eq_iff,
      algebraMap_smul_eq_apply, hw]
    simp only [map_div₀, map_add, map_one, map_ofNat, div_left_inj' (two_ne_zero : (2 : K) ≠ 0),
      add_right_inj]
  -- Its conjugates are `w` and `1 - w`, even when the ambient field is larger.
  have hpm : σ • w = w ∨ σ • w = 1 - w := by
    have hxsq : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxsq with h | h
    · exact Or.inl (hfix.mpr h)
    · right
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_sub, map_one, algebraMap_smul_eq_apply, hw]
      simp only [map_div₀, map_add, map_one, map_ofNat, h]
      ring
  -- The Frobenius congruence distinguishes these conjugates by the parity of `(d - 1) / 4`.
  have heven : σ • w = w ↔ (2 : ℤ) ∣ d / 4 := by
    constructor
    · intro h
      rw [h] at hcong
      have hmem := Q.neg_mem hcong
      rw [neg_sub, hwsq] at hmem
      exact (algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp hmem
    · intro h
      rcases hpm with hfix | hneg
      · exact hfix
      · have hemem := (algebraMap_int_mem_iff_dvd_of_liesOver Q (d / 4)).mpr h
        have htwo : (2 : 𝓞 K) ∈ Q := by
          simpa using (algebraMap_int_mem_iff_dvd_of_liesOver Q 2).mpr (dvd_refl 2)
        have hone : (1 : 𝓞 K) ∈ Q := by
          have hsum := Q.add_mem (Q.add_mem hcong hemem) (Q.mul_mem_right w htwo)
          rw [hneg] at hsum
          convert hsum using 1
          linear_combination hwsq
        have hbad : (2 : ℤ) ∣ 1 :=
          (algebraMap_int_mem_iff_dvd_of_liesOver Q 1).mp (by simpa using hone)
        norm_num at hbad
  rw [← hfix, heven, Int.dvd_iff_emod_eq_zero]
  omega

/-- At a prime above `2`, Frobenius fixes square roots of integers congruent to `1` modulo `8`
and negates square roots of integers congruent to `5` modulo `8`. -/
theorem isArithFrobAt_apply_sqrt_two
    {K : Type*} [Field K] [CharZero K] {d : ℤ} {x : K}
    (hx : x ^ 2 = algebraMap ℤ K d) (hd : d % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(2 : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = if d % 8 = 1 then x else -x := by
  have hfix := isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight hx hd Q hσ
  split_ifs with h
  · exact hfix.mpr h
  · have hsq : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx]; simp
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_left (fun h' ↦ h (hfix.mp h'))

end TauCeti
