/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Discriminant
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import TauCeti.Algebra.Algebra.Subalgebra.Adjoin
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow

/-!
# Integral closures in prime-power cyclotomic extensions

Let `R` be an integrally closed domain with fraction field `K` in which the rational prime `p` is
a prime element, for instance `ℤ`, `ℤ_p`, or the ring of integers of a finite unramified extension
of `ℚ_p`. Let `L` be a `p ^ k`-th cyclotomic extension of `K` and `ζ ∈ L` a primitive
`p ^ k`-th root of unity. This file shows that the integral closure of `R` in `L` is
`R[ζ] = R[ζ - 1]`, and that it is free over `R` with power basis
`1, ζ - 1, …, (ζ - 1) ^ (φ(p ^ k) - 1)`.
The minimal polynomial of `ζ - 1` over `R` is `Φ_{p ^ k}(X + 1)`, which for `k ≥ 1` is Eisenstein
at `(p)`.

Mathlib proves the case `R = ℤ`
(`IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow` and
`IsPrimitiveRoot.subOneIntegralPowerBasisOfPrimePow`); the argument here follows it. The
discriminant of the power basis of `ζ` is `± p ^ m`, so it clears every denominator of an integral
element up to a power of `p`, and the Eisenstein property of the minimal polynomial of `ζ - 1`
removes that power of `p`. Over `ℤ_p` this computes the integers of the local cyclotomic fields
`ℚ_p(ζ_{p ^ k})`.

## Main results

* `IsPrimitiveRoot.minpoly_sub_one_eq_cyclotomic_comp_of_prime`: the minimal polynomial of
  `ζ - 1` over `R` is `Φ_{p ^ k}(X + 1)`.
* `IsPrimitiveRoot.isEisensteinAt_minpoly_sub_one`: for `k ≥ 1` it is Eisenstein at `(p)`.
* `IsPrimitiveRoot.integralClosure_eq_adjoin_sub_one` and
  `IsPrimitiveRoot.integralClosure_eq_adjoin`: the integral closure of `R` in `L` is
  `R[ζ - 1] = R[ζ]`.
* `IsPrimitiveRoot.subOneIntegralClosurePowerBasis`: the power basis of `integralClosure R L`
  over `R` with generator `ζ - 1` and dimension `φ(p ^ k)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 10.2 (the case `R = ℤ`), and
  Chapter II, Proposition 7.13 (the case `R = ℤ_p`).
-/

public section

open Polynomial

namespace IsPrimitiveRoot

/-- If `ζ` is a primitive `n`-th root of unity with `0 < n`, then `ζ - 1` is integral over any
ring `R`. -/
theorem isIntegral_sub_one {n : ℕ} (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ζ : A} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) : IsIntegral R (ζ - 1) :=
  (hζ.isIntegral hn).tower_top.sub isIntegral_one

variable {p k : ℕ} [Fact p.Prime] (R : Type*) {L : Type*} [CommRing R] [IsIntegrallyClosed R]
  [Field L] [Algebra R L] {ζ : L}

section Minpoly

variable [FaithfulSMul R L]

/-- Let `R` be an integrally closed domain in which `p` is prime, and let `ζ` be a primitive
`p ^ k`-th root of unity in a field containing `R`. The minimal polynomial of `ζ - 1` over `R` is
`Φ_{p ^ k}(X + 1)`. -/
theorem minpoly_sub_one_eq_cyclotomic_comp_of_prime (hζ : IsPrimitiveRoot ζ (p ^ k))
    (hpR : Prime (p : R)) : minpoly R (ζ - 1) = (cyclotomic (p ^ k) R).comp (X + 1) := by
  have := IsDomain.of_faithfulSMul R L
  let := FractionRing.liftAlgebra R L
  have hint := hζ.isIntegral_sub_one R (NeZero.pos _)
  have : NeZero ((p ^ k : ℕ) : FractionRing R) := ⟨by
    rw [Nat.cast_pow, ← map_natCast (algebraMap R (FractionRing R))]
    exact pow_ne_zero _
      ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hpR.ne_zero)⟩
  have hK : minpoly (FractionRing R) (ζ - 1) =
      (cyclotomic (p ^ k) (FractionRing R)).comp (X + 1) := by
    rw [show ζ - 1 = ζ + algebraMap (FractionRing R) L (-1) by simp [sub_eq_add_neg],
      minpoly.add_algebraMap ζ, ← hζ.minpoly_eq_cyclotomic_of_irreducible
        (irreducible_cyclotomic_prime_pow_of_prime (FractionRing R) hpR k)]
    simp
  apply map_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing R) hint, hK, map_comp,
    map_cyclotomic]
  simp

/-- For `k ≥ 1`, the minimal polynomial `Φ_{p ^ k}(X + 1)` of `ζ - 1` over `R` is Eisenstein at
`(p)`. -/
theorem isEisensteinAt_minpoly_sub_one (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hpR : Prime (p : R)) : (minpoly R (ζ - 1)).IsEisensteinAt (Ideal.span {(p : R)}) := by
  have := IsDomain.of_faithfulSMul R L
  rw [hζ.minpoly_sub_one_eq_cyclotomic_comp_of_prime R hpR]
  exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_of_prime p hpR k

end Minpoly

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K L]
  [IsScalarTower R K L]

/-- **The integral closure in a prime-power cyclotomic extension.** If `R` is an integrally closed
domain with fraction field `K` in which `p` is prime, `L` is a `p ^ k`-th cyclotomic extension of
`K` and `ζ ∈ L` is a primitive `p ^ k`-th root of unity, then the integral closure of `R` in `L`
is `R[ζ - 1]`. -/
theorem integralClosure_eq_adjoin_sub_one [IsCyclotomicExtension {p ^ k} K L]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hpR : Prime (p : R)) :
    integralClosure R L = Algebra.adjoin R {ζ - 1} := by
  have := (IsFractionRing.isDomain_iff_isField (R := R) (K := K)).2 (Field.toIsField K)
  have := FaithfulSMul.of_field_isFractionRing R L K L
  have hint := hζ.isIntegral_sub_one R (NeZero.pos _)
  refine le_antisymm (fun z hz ↦ ?_) (adjoin_le_integralClosure hint)
  replace hz := (mem_integralClosure_iff R L).1 hz
  have hirr := irreducible_cyclotomic_prime_pow_of_prime K hpR k
  have := IsCyclotomicExtension.isSeparable {p ^ k} K L
  have := IsCyclotomicExtension.finiteDimensional {p ^ k} K L
  -- The discriminant `± p ^ m` of the power basis of `ζ` multiplies `z` into `R[ζ] = R[ζ - 1]`.
  have H := (TauCeti.Algebra.adjoin_sub_one_eq_adjoin ζ).ge
    (Algebra.discr_mul_isIntegral_mem_adjoin K (B := hζ.powerBasis K)
      (by simpa using (hζ.isIntegral (NeZero.pos _)).tower_top) hz)
  obtain ⟨u, m, hum⟩ := IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow hζ hirr
  -- Multiplying the discriminant `u * p ^ m` by the unit `u` leaves `p ^ m`, as `u * u = 1`.
  have hu : ((u : ℤ) : K) * (u * (p : K) ^ m) = algebraMap R K ((p : R) ^ m) := by
    obtain rfl | rfl := Int.units_eq_one_or u <;> simp
  have hpm : (p : R) ^ m • z ∈ Algebra.adjoin R {ζ - 1} := by
    convert Subalgebra.zsmul_mem _ H (u : ℤ) using 1
    rw [hum, ← smul_assoc, zsmul_eq_mul, hu, algebraMap_smul]
  rcases k with - | k
  · -- For `k = 0` we have `L = K`, and `z` comes from the integrally closed `R`.
    have : IsCyclotomicExtension {1} K L := by simpa using ‹IsCyclotomicExtension {p ^ 0} K L›
    obtain ⟨y, rfl⟩ := Algebra.mem_bot.1
      (IsCyclotomicExtension.singleton_one K L ▸ Algebra.mem_top : z ∈ (⊥ : Subalgebra K L))
    obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (isIntegral_algebraMap_iff.1 hz)
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  · rw [← hζ.subOnePowerBasis_gen K] at hint hpm ⊢
    exact mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt hpR hint hz hpm
      (by rw [hζ.subOnePowerBasis_gen K]; exact hζ.isEisensteinAt_minpoly_sub_one R hpR)

/-- The integral closure of `R` in a `p ^ k`-th cyclotomic extension `L` of `K` is `R[ζ]`, for any
primitive `p ^ k`-th root of unity `ζ ∈ L`. -/
theorem integralClosure_eq_adjoin [IsCyclotomicExtension {p ^ k} K L]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hpR : Prime (p : R)) :
    integralClosure R L = Algebra.adjoin R {ζ} :=
  (hζ.integralClosure_eq_adjoin_sub_one R K hpR).trans (TauCeti.Algebra.adjoin_sub_one_eq_adjoin ζ)

/-- The power basis `1, ζ - 1, …, (ζ - 1) ^ (φ(p ^ k) - 1)` of the integral closure of `R` in a
`p ^ k`-th cyclotomic extension `L` of `K`, where `ζ ∈ L` is a primitive `p ^ k`-th root of
unity. -/
noncomputable def subOneIntegralClosurePowerBasis [IsCyclotomicExtension {p ^ k} K L]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hpR : Prime (p : R)) : PowerBasis R (integralClosure R L) :=
  haveI := FaithfulSMul.of_field_isFractionRing R L K L
  haveI := IsDomain.of_faithfulSMul R L
  haveI := Module.IsTorsionFree.trans_faithfulSMul R K L
  (Algebra.adjoin.powerBasis' (hζ.isIntegral_sub_one R (NeZero.pos _))).map
    (Subalgebra.equivOfEq _ _ (hζ.integralClosure_eq_adjoin_sub_one R K hpR).symm)

@[simp]
theorem coe_subOneIntegralClosurePowerBasis_gen [IsCyclotomicExtension {p ^ k} K L]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hpR : Prime (p : R)) :
    ((hζ.subOneIntegralClosurePowerBasis R K hpR).gen : L) = ζ - 1 := by
  simp [subOneIntegralClosurePowerBasis]

/-- The minimal polynomial over `R` of the generator `ζ - 1` of the integral closure is
`Φ_{p ^ k}(X + 1)`. -/
theorem minpoly_subOneIntegralClosurePowerBasis_gen [IsCyclotomicExtension {p ^ k} K L]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hpR : Prime (p : R)) :
    minpoly R (hζ.subOneIntegralClosurePowerBasis R K hpR).gen =
      (cyclotomic (p ^ k) R).comp (X + 1) := by
  have := FaithfulSMul.of_field_isFractionRing R L K L
  rw [← minpoly.algebraMap_eq (B' := L) Subtype.val_injective]
  simpa using hζ.minpoly_sub_one_eq_cyclotomic_comp_of_prime R hpR

@[simp]
theorem subOneIntegralClosurePowerBasis_dim [IsCyclotomicExtension {p ^ k} K L]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hpR : Prime (p : R)) :
    (hζ.subOneIntegralClosurePowerBasis R K hpR).dim = (p ^ k).totient := by
  have := (IsFractionRing.isDomain_iff_isField (R := R) (K := K)).2 (Field.toIsField K)
  rw [← PowerBasis.natDegree_minpoly, minpoly_subOneIntegralClosurePowerBasis_gen,
    natDegree_cyclotomic_comp_X_add_one]

end IsPrimitiveRoot
