/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
import TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Wild
import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# Extensions of bounded degree unramified outside a finite set

Let `K` be a number field and `S` a finite set of finite places of `K`. This file proves Hermite's
finiteness theorem (often called the Hermite–Minkowski theorem) in the form used for Galois
cohomology unramified outside `S`: inside any field `A` containing `K`, there are only finitely
many extensions `L / K` of degree at most `d` whose ramified places all lie in `S`. Finiteness
theorems for Galois cohomology groups unramified outside `S`, such as the finiteness of Selmer
groups over number fields, reduce to this statement.

The proof bounds the discriminant and applies Hermite's theorem
`NumberField.finite_of_discr_bdd`. The bound comes from the different. At a prime `P` of `𝓞 L`
with ramification index `e` over `K`, the wild bound says the different exponent is at most
`e - 1 + v_P(e)`, and `e ≤ [L : K]`. Now `e` divides `[L : K]!`, and `v_P(𝔭) = e` for the prime
`𝔭` of `K` below `P`. So the different divides `[L : K]! · ∏ 𝔭`, the product over the ramified
primes `𝔭` of `K`. Taking norms,

  `|d_L| ∣ (N([L : K]! · ∏ 𝔭) · |d_K|) ^ [L : K]`.

The factor `[L : K]!` is crude, but this bound depends only on `[L : K]` and the ramified primes,
which is all the finiteness argument needs.

## Main results

* `TauCeti.NumberField.differentIdeal_dvd_map_span_factorial_mul_prod_ramifiedSupport`: the
  different of `L / K` divides `[L : K]!` times the product of the ramified primes of `K`.
* `natAbs_discr_dvd_absNorm_factorial_mul_prod_ramifiedSupport_mul_natAbs_discr_pow` (in
  `TauCeti.NumberField`): the resulting divisibility of the absolute discriminant of `L`.
* `TauCeti.NumberField.finite_of_finrank_le_of_ramifiedSupport_subset`: there are finitely many
  extensions of `K` in `A` of degree at most `d` and ramified only at places in `S`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
-/

public section

open scoped NumberField
open IsDedekindDomain Module NumberField

namespace TauCeti.NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The different divides `[L : K]!` times the product of the ramified primes.** The different
of `L / K` divides the extension to `𝓞 L` of `[L : K]! · ∏ 𝔭`, where `𝔭` runs over the primes of
`𝓞 K` ramified in `L`. -/
theorem differentIdeal_dvd_map_span_factorial_mul_prod_ramifiedSupport :
    differentIdeal (𝓞 K) (𝓞 L) ∣
      (Ideal.span {((finrank K L).factorial : 𝓞 K)} *
        ∏ v ∈ ramifiedSupport K L, v.asIdeal).map (algebraMap (𝓞 K) (𝓞 L)) := by
  classical
  set n := finrank K L
  set 𝔯 := ∏ v ∈ ramifiedSupport K L, v.asIdeal
  have h𝔯 : 𝔯.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := by
    refine Ideal.map_ne_bot_of_ne_bot ?_
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun v _ ↦ v.ne_bot
  have hfac : Ideal.span {((n.factorial : ℕ) : 𝓞 L)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast n.factorial_ne_zero
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_natCast,
    UniqueFactorizationMonoid.dvd_iff_emultiplicity_le differentIdeal_ne_bot]
  intro P hP
  have : P.IsPrime := Ideal.isPrime_of_prime hP
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, inferInstance, hP.ne_zero⟩
  let v := w.under (𝓞 K)
  have : P.LiesOver v.asIdeal := ⟨rfl⟩
  have hfin := FiniteMultiplicity.of_prime_left hP (mul_ne_zero hfac h𝔯)
  rw [(FiniteMultiplicity.of_prime_left hP differentIdeal_ne_bot).emultiplicity_eq_multiplicity,
    hfin.emultiplicity_eq_multiplicity, Nat.cast_le, multiplicity_mul hP hfin]
  -- Above a ramified `𝔭`, the wild bound `e - 1 + v_P(e)` is less than `v_P(n!) + e`, and `e` is
  -- at most `v_P(𝔯)`. Above an unramified `𝔭`, `P` does not divide the different.
  by_cases hv : v ∈ ramifiedSupport K L
  · set e := P.ramificationIdx (𝓞 K) with he
    have hen : e ≤ n := by
      have := RamificationInertia.ramificationIdx_le_finrank v.asIdeal P
      rwa [← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at this
    have hwild : multiplicity P (differentIdeal (𝓞 K) (𝓞 L)) ≤
        e - 1 + multiplicity P (Ideal.span {((e : ℕ) : 𝓞 L)}) :=
      HeightOneSpectrum.multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span
        v w
    -- `v_P(e) ≤ v_P(n!)`, since `e ∣ n!`
    have hen' : multiplicity P (Ideal.span {((e : ℕ) : 𝓞 L)}) ≤
        multiplicity P (Ideal.span {((n.factorial : ℕ) : 𝓞 L)}) := by
      refine (FiniteMultiplicity.of_prime_left hP hfac).le_multiplicity_of_pow_dvd
        ((pow_multiplicity_dvd _ _).trans ?_)
      rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
      exact Nat.cast_dvd_cast (Nat.dvd_factorial (P.ramificationIdx_pos (𝓞 K)) hen)
    -- `e ≤ v_P(𝔯)`, since `𝔯 ≤ 𝔭` and `𝔭 𝓞_L ≤ P ^ e`
    have he𝔯 : e ≤ multiplicity P (𝔯.map (algebraMap (𝓞 K) (𝓞 L))) := by
      refine (FiniteMultiplicity.of_prime_left hP h𝔯).le_multiplicity_of_pow_dvd ?_
      rw [Ideal.dvd_iff_le, he,
        ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P v.ne_bot]
      exact (Ideal.map_mono (Ideal.prod_le_inf.trans
        (Finset.inf_le (f := HeightOneSpectrum.asIdeal) hv))).trans Ideal.le_pow_ramificationIdx'
    omega
  · rw [multiplicity_eq_zero_of_not_dvd
      (not_dvd_differentIdeal_iff.mpr (isUnramifiedAway_ramifiedSupport v hv P))]
    exact Nat.zero_le _

/-- **A bound on the discriminant from the ramified primes.** The absolute discriminant of `L`
divides `(N([L : K]! · ∏ 𝔭) · |d_K|) ^ [L : K]`, the product over the primes `𝔭` of `K`
ramified in `L`. -/
theorem natAbs_discr_dvd_absNorm_factorial_mul_prod_ramifiedSupport_mul_natAbs_discr_pow :
    (discr L).natAbs ∣
      (Ideal.absNorm (Ideal.span {((finrank K L).factorial : 𝓞 K)} *
        ∏ v ∈ ramifiedSupport K L, v.asIdeal) * (discr K).natAbs) ^ finrank K L := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L), mul_pow]
  refine mul_dvd_mul_right ?_ _
  have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd
    (differentIdeal_dvd_map_span_factorial_mul_prod_ramifiedSupport (K := K) (L := L)))
  rwa [Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at this

/-- **Hermite's theorem: finitely many extensions of bounded degree are unramified outside a finite
set.** Inside a field `A` containing the number field `K`, only finitely many finite extensions
`L / K` have degree at most `d` and are ramified only at places in the finite set `S`. -/
theorem finite_of_finrank_le_of_ramifiedSupport_subset (A : Type*) [Field A] [Algebra K A]
    (d : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    {L : {F : IntermediateField K A // FiniteDimensional K F} |
      haveI : NumberField L := haveI := L.2; NumberField.of_module_finite K L
      finrank K L ≤ d ∧ ramifiedSupport K L ⊆ S}.Finite := by
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  set B := Ideal.absNorm (Ideal.span {(d.factorial : 𝓞 K)} * ∏ v ∈ S, v.asIdeal) *
    (discr K).natAbs
  have hB : 0 < B := by
    refine Nat.mul_pos (Nat.pos_of_ne_zero ?_) (Int.natAbs_pos.mpr (discr_ne_zero K))
    rw [Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot, mul_eq_zero, not_or,
      Finset.prod_eq_zero_iff, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ⟨by exact_mod_cast d.factorial_ne_zero, fun ⟨v, _, hv⟩ ↦ v.ne_bot hv⟩
  let φ : {F : IntermediateField K A // FiniteDimensional K F} →
      {F : IntermediateField ℚ A // FiniteDimensional ℚ F} := fun L ↦
    ⟨L.1.restrictScalars ℚ, haveI := L.2; (NumberField.of_module_finite K L.1).to_finiteDimensional⟩
  have hφ : Function.Injective φ := fun L₁ L₂ h ↦
    Subtype.ext (IntermediateField.restrictScalars_injective ℚ (congrArg Subtype.val h))
  refine ((finite_of_discr_bdd A (B ^ d)).preimage hφ.injOn).subset ?_
  rintro ⟨L, hL⟩ ⟨hd, hS⟩
  have : NumberField L := NumberField.of_module_finite K L
  -- `L.restrictScalars ℚ` and `L` have the same underlying subfield of `A`
  let e : L.restrictScalars ℚ ≃+* L :=
    .subfieldCongr (IntermediateField.restrictScalars_toSubfield ℚ)
  have : NumberField (L.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance (φ ⟨L, hL⟩).2
  rw [Set.mem_preimage, Set.mem_ofPred_eq, discr_eq_discr_of_ringEquiv _ e, Int.abs_eq_natAbs,
    Nat.cast_le]
  refine (Nat.le_of_dvd (pow_pos hB _)
    (natAbs_discr_dvd_absNorm_factorial_mul_prod_ramifiedSupport_mul_natAbs_discr_pow.trans
      (pow_dvd_pow_of_dvd ?_ _))).trans (Nat.pow_le_pow_right hB hd)
  refine Nat.mul_dvd_mul_right (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd ?_)) _
  refine mul_dvd_mul ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hS)
  rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
  exact Nat.cast_dvd_cast (Nat.factorial_dvd_factorial hd)

end TauCeti.NumberField
