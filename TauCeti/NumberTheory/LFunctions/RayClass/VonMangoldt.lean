/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta

import TauCeti.Analysis.SpecialFunctions.LogIntegral

/-!
# Chebyshev's `ψ`, `ϑ`, and `π` restricted to a ray class

For a modulus `𝔪` of a number field `K` and a ray class `c ∈ Cl_𝔪`, this file defines the
ray-class prime-counting functions `rayClassPsi 𝔪 c`, `rayClassTheta 𝔪 c`, and
`rayClassPrimeCount 𝔪 c`, together with the regrouped von Mangoldt arithmetic function
`rayClassVonMangoldtCoeff 𝔪 c`.

An integral prime power `A = 𝔭 ^ k` prime to `𝔪` contributes `log N(𝔭)` to `rayClassPsi 𝔪 c` when
`idealClass 𝔪 A = c`, equivalently `(idealClass 𝔪 𝔭) ^ k = c`. Thus a prime `𝔭` outside `c` can
contribute through a higher power, matching the ideal-level von Mangoldt transform of the ray-class
indicator `rayClassCoeff 𝔪 c`. At exponent one the condition reduces to `idealClass 𝔪 𝔭 = c`, giving
`rayClassTheta 𝔪 c` and the unweighted prime count `rayClassPrimeCount 𝔪 c`.

## Main definitions

* `TauCeti.LFunctions.rayClassPrimeSet 𝔪 c`: height-one primes coprime to `𝔪` of ray class `c`.
* `TauCeti.LFunctions.rayClassPrimePowerSet 𝔪 c`: prime-power ideals coprime to `𝔪` of ray class
  `c`.
* `TauCeti.LFunctions.rayClassPrimeCount 𝔪 c x`: number of prime ideals in `integralIdealsPrimeTo 𝔪`
  of norm at most `x` and ray class `c`.
* `TauCeti.LFunctions.rayClassTheta 𝔪 c x` and `TauCeti.LFunctions.rayClassPsi 𝔪 c x`: the
  logarithmically weighted prime and prime-power counts in the ray class `c`.
* `TauCeti.LFunctions.rayClassVonMangoldtCoeff 𝔪 c`: the nonnegative `ArithmeticFunction ℝ`
  obtained by regrouping `(rayClassCoeff 𝔪 c).vonMangoldtTransform` by absolute norm.

## Main results

* `TauCeti.LFunctions.natCast_rayClassPrimeCount`: identifies `rayClassPrimeCount 𝔪 c` with
  `TauCeti.primeCount K (rayClassPrimeSet 𝔪 c)`.
* `TauCeti.LFunctions.idealSummatory_vonMangoldtTransform_rayClassCoeff`: identifies
  `rayClassPsi 𝔪 c` with the ideal summatory function of `(rayClassCoeff 𝔪 c).vonMangoldtTransform`.
* `TauCeti.LFunctions.rayClassPsi_sub_rayClassTheta_le_higherPrimePowerTheta`,
  `TauCeti.LFunctions.rayClassPsi_sub_rayClassTheta_isBigO`, and
  `TauCeti.LFunctions.rayClassPsi_sub_rayClassTheta_isLittleO_mul_exp_neg_mul_sqrt_log`: the
  higher-prime-power contribution to `rayClassPsi 𝔪 c` is at most `higherPrimePowerTheta K`, hence
  `O(√x log² x)` and `o(x exp (-c₀ √log x))` for every real `c₀`.
* `TauCeti.LFunctions.sum_rayClassPsi_add_primePsi_support` and
  `TauCeti.LFunctions.primePsi_univ_sub_sum_rayClassPsi_le`: summing `rayClassPsi 𝔪 c` over
  `c : RayClassGroup 𝔪` recovers `ψ_K(x)` up to the bad-prime sum over `𝔪.support`, which is at
  most `𝔪.support.card * log x` for `x ≥ 1`.
* `TauCeti.LFunctions.sum_rayClassPsi_classMap` and
  `TauCeti.LFunctions.rayClassPsi_sub_sum_rayClassPsi_classMap_isBigO_log`: behaviour of
  `rayClassPsi` across a change of modulus `𝔪 ∣ 𝔫`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§8 and 13.
* H. Davenport, *Multiplicative Number Theory*, Chapters 4 and 20.
-/

public section

namespace TauCeti.LFunctions

open Asymptotics Filter NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K]

/-! ### Prime and prime-power fibres of a ray class -/

/-- The height-one primes of `𝓞 K` coprime to the finite part of `𝔪` whose ray class is `c`. -/
def rayClassPrimeSet (𝔪 : Modulus K) (c : RayClassGroup 𝔪) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | ∃ h𝔭 : 𝔪.IsCoprimeTo 𝔭.asIdeal,
    idealClass 𝔪 ⟨𝔭.asIdeal, Modulus.mem_integralIdealsPrimeTo.mpr h𝔭⟩ = c}

/-- Membership in `rayClassPrimeSet`, unfolded. -/
@[simp]
theorem mem_rayClassPrimeSet_iff {𝔪 : Modulus K} {c : RayClassGroup 𝔪}
    {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ rayClassPrimeSet 𝔪 c ↔
      ∃ h𝔭 : 𝔪.IsCoprimeTo 𝔭.asIdeal,
        idealClass 𝔪 ⟨𝔭.asIdeal, Modulus.mem_integralIdealsPrimeTo.mpr h𝔭⟩ = c :=
  Iff.rfl

/-- At a height-one prime coprime to `𝔪`, membership in `rayClassPrimeSet 𝔪 c` tests its ray
class. -/
theorem mem_rayClassPrimeSet_iff_of_isCoprimeTo {𝔪 : Modulus K} {c : RayClassGroup 𝔪}
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔪.IsCoprimeTo 𝔭.asIdeal) :
    𝔭 ∈ rayClassPrimeSet 𝔪 c ↔
      idealClass 𝔪 ⟨𝔭.asIdeal, Modulus.mem_integralIdealsPrimeTo.mpr h𝔭⟩ = c :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨h𝔭, h⟩⟩

/-- A height-one prime is coprime to `𝔪` iff it does not lie in `𝔪.support`. -/
theorem isCoprimeTo_asIdeal_iff {𝔪 : Modulus K} {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔪.IsCoprimeTo 𝔭.asIdeal ↔ 𝔭 ∉ 𝔪.support :=
  (Modulus.isCoprimeTo_iff.trans Ideal.isPrimeTo_iff.symm).trans Ideal.isPrimeTo_asIdeal_iff

/-- The prime-power ideals of `𝓞 K` coprime to the finite part of `𝔪` whose ray class is `c`. -/
def rayClassPrimePowerSet (𝔪 : Modulus K) (c : RayClassGroup 𝔪) : Set (IdealPrimePower K) :=
  {A | ∃ hA : 𝔪.IsCoprimeTo (A : Ideal (𝓞 K)),
    idealClass 𝔪 ⟨(A : Ideal (𝓞 K)), Modulus.mem_integralIdealsPrimeTo.mpr hA⟩ = c}

/-- Membership in `rayClassPrimePowerSet`, unfolded. -/
@[simp]
theorem mem_rayClassPrimePowerSet_iff {𝔪 : Modulus K} {c : RayClassGroup 𝔪}
    {A : IdealPrimePower K} :
    A ∈ rayClassPrimePowerSet 𝔪 c ↔
      ∃ hA : 𝔪.IsCoprimeTo (A : Ideal (𝓞 K)),
        idealClass 𝔪 ⟨(A : Ideal (𝓞 K)), Modulus.mem_integralIdealsPrimeTo.mpr hA⟩ = c :=
  Iff.rfl

/-- A prime-power ideal is coprime to `𝔪` iff its prime base is coprime to `𝔪`, i.e., outside
`𝔪.support`. -/
theorem isCoprimeTo_idealPrimePower_iff {𝔪 : Modulus K} {A : IdealPrimePower K} :
    𝔪.IsCoprimeTo (A : Ideal (𝓞 K)) ↔ primePowerBase A ∉ 𝔪.support := by
  rw [← primePowerBase_pow_primePowerExponent A]
  exact (Modulus.isCoprimeTo_iff.trans Ideal.isPrimeTo_iff.symm).trans
    ((Ideal.isPrimeTo_pow_iff (primePowerExponent_pos A).ne').trans Ideal.isPrimeTo_asIdeal_iff)

/-- A prime power `A = 𝔭 ^ m` with `𝔭` coprime to `𝔪` belongs to `rayClassPrimePowerSet 𝔪 c` iff
`(idealClass 𝔪 𝔭) ^ m = c`. -/
theorem mem_rayClassPrimePowerSet_iff_idealClass_pow_eq {𝔪 : Modulus K} {c : RayClassGroup 𝔪}
    {A : IdealPrimePower K} (h𝔭 : 𝔪.IsCoprimeTo (primePowerBase A).asIdeal) :
    A ∈ rayClassPrimePowerSet 𝔪 c ↔
      idealClass 𝔪 ⟨(primePowerBase A).asIdeal, Modulus.mem_integralIdealsPrimeTo.mpr h𝔭⟩ ^
        primePowerExponent A = c := by
  have hA : 𝔪.IsCoprimeTo (A : Ideal (𝓞 K)) :=
    isCoprimeTo_idealPrimePower_iff.mpr (isCoprimeTo_asIdeal_iff.mp h𝔭)
  have hpow : (⟨(primePowerBase A).asIdeal, Modulus.mem_integralIdealsPrimeTo.mpr h𝔭⟩ :
      integralIdealsPrimeTo 𝔪) ^ primePowerExponent A =
        ⟨(A : Ideal (𝓞 K)), Modulus.mem_integralIdealsPrimeTo.mpr hA⟩ :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow, primePowerBase_pow_primePowerExponent])
  rw [mem_rayClassPrimePowerSet_iff, ← map_pow, hpow]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hA, h⟩⟩

/-- At exponent one, the prime-power ray-class fibre agrees with `rayClassPrimeSet`. -/
theorem ofPrime_mem_rayClassPrimePowerSet_iff {𝔪 : Modulus K} {c : RayClassGroup 𝔪}
    {𝔭 : HeightOneSpectrum (𝓞 K)} :
    IdealPrimePower.ofPrime 𝔭 ∈ rayClassPrimePowerSet 𝔪 c ↔ 𝔭 ∈ rayClassPrimeSet 𝔪 c := by
  simp only [mem_rayClassPrimePowerSet_iff, mem_rayClassPrimeSet_iff, IdealPrimePower.coe_ofPrime]

/-! ### Ray-class prime-counting functions `π`, `ϑ`, and `ψ` -/

/-- **Unweighted prime count in a ray class**: the number of prime ideals in
`integralIdealsPrimeTo 𝔪` of absolute norm at most `x` whose ray class is `c`. -/
noncomputable def rayClassPrimeCount (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) : ℕ :=
  Set.ncard {I : integralIdealsPrimeTo 𝔪 |
    (I : Ideal (𝓞 K)).IsPrime ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x ∧ idealClass 𝔪 I = c}

/-- Defining equation of `TauCeti.LFunctions.rayClassPrimeCount`. -/
theorem rayClassPrimeCount_def (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassPrimeCount 𝔪 c x =
      Set.ncard {I : integralIdealsPrimeTo 𝔪 |
        (I : Ideal (𝓞 K)).IsPrime ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x ∧
          idealClass 𝔪 I = c} :=
  (rfl)

/-- `rayClassPrimeCount 𝔪 c x` equals the cardinality of the primes in `primesLE K x` belonging to
`rayClassPrimeSet 𝔪 c`. -/
theorem rayClassPrimeCount_eq_card_filter (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassPrimeCount 𝔪 c x =
      by classical exact ((primesLE K x).filter (· ∈ rayClassPrimeSet 𝔪 c)).card := by
  classical
  rw [rayClassPrimeCount_def, ← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun I hI ↦ ⟨(I : Ideal (𝓞 K)), hI.1,
      (Modulus.isCoprimeTo_iff.mp (Modulus.mem_integralIdealsPrimeTo.mp I.2)).1⟩) ?_ ?_ ?_
  · intro I hI
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨(mem_normLE (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)).mpr hI.2.1,
        Modulus.mem_integralIdealsPrimeTo.mp I.2, hI.2.2⟩)
  · intro I J _ _ hIJ
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal hIJ)
  · intro 𝔭 h𝔭
    obtain ⟨hnorm, hcop, hcl⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp h𝔭)
    exact ⟨⟨𝔭.asIdeal, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩,
      ⟨𝔭.isPrime,
        (mem_normLE (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)).mp hnorm, hcl⟩,
      HeightOneSpectrum.ext rfl⟩

/-- Cast to `ℝ`, `rayClassPrimeCount 𝔪 c` is the generic prime count of `rayClassPrimeSet 𝔪 c`. -/
@[simp]
theorem natCast_rayClassPrimeCount (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    (rayClassPrimeCount 𝔪 c x : ℝ) = primeCount K (rayClassPrimeSet 𝔪 c) x := by
  classical
  rw [rayClassPrimeCount_eq_card_filter, primeCount_eq_card]

/-- `rayClassPrimeCount 𝔪 c` is monotone in the cutoff. -/
theorem rayClassPrimeCount_mono (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    Monotone (rayClassPrimeCount 𝔪 c) := fun x y hxy ↦ by
  have h := primeCount_mono (rayClassPrimeSet 𝔪 c) hxy
  rw [← natCast_rayClassPrimeCount, ← natCast_rayClassPrimeCount] at h
  exact Nat.cast_le.mp h

/-- Below `2` there are no prime ideals in any ray class. -/
theorem rayClassPrimeCount_eq_zero_of_lt_two (𝔪 : Modulus K) (c : RayClassGroup 𝔪) {x : ℝ}
    (hx : x < 2) : rayClassPrimeCount 𝔪 c x = 0 := by
  exact_mod_cast (natCast_rayClassPrimeCount 𝔪 c x).trans
    (primeCount_eq_zero_of_lt_two (rayClassPrimeSet 𝔪 c) hx)

/-- **Chebyshev's `ϑ` restricted to a ray class**: the sum of `log N(𝔭)` over primes `𝔭` prime to
`𝔪` of norm at most `x` with `idealClass 𝔪 𝔭 = c`. -/
noncomputable def rayClassTheta (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) : ℝ :=
  primeTheta K (rayClassPrimeSet 𝔪 c) x

/-- Defining equation of `TauCeti.LFunctions.rayClassTheta`. -/
theorem rayClassTheta_def (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassTheta 𝔪 c x = primeTheta K (rayClassPrimeSet 𝔪 c) x :=
  (rfl)

/-- `rayClassTheta` is nonnegative. -/
theorem rayClassTheta_nonneg (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    0 ≤ rayClassTheta 𝔪 c x :=
  primeTheta_nonneg (rayClassPrimeSet 𝔪 c) x

/-- `rayClassTheta` is monotone in the cutoff. -/
theorem rayClassTheta_mono (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    Monotone (rayClassTheta 𝔪 c) :=
  primeTheta_mono (rayClassPrimeSet 𝔪 c)

/-- Below `2`, `rayClassTheta` vanishes. -/
theorem rayClassTheta_eq_zero_of_lt_two (𝔪 : Modulus K) (c : RayClassGroup 𝔪) {x : ℝ}
    (hx : x < 2) : rayClassTheta 𝔪 c x = 0 :=
  primeTheta_eq_zero_of_lt_two (rayClassPrimeSet 𝔪 c) hx

/-- **Chebyshev's `ψ` restricted to a ray class**: the inclusive sum of `log N(𝔭)` over prime
powers `A = 𝔭 ^ k` prime to `𝔪` of norm at most `x` with `idealClass 𝔪 A = c`. -/
noncomputable def rayClassPsi (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) : ℝ :=
  primePowerSummatory K ((rayClassPrimePowerSet 𝔪 c).indicator primePowerWeight) x

/-- Explicit sum presentation of `rayClassPsi` over `primePowersLE K x`. -/
theorem rayClassPsi_apply (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassPsi 𝔪 c x = ∑ A ∈ primePowersLE K x,
      (rayClassPrimePowerSet 𝔪 c).indicator primePowerWeight A := by
  rw [rayClassPsi, primePowerSummatory_apply]

/-- `rayClassPsi` is nonnegative. -/
theorem rayClassPsi_nonneg (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    0 ≤ rayClassPsi 𝔪 c x :=
  primePowerSummatory_nonneg K _
    (fun A ↦ Set.indicator_nonneg (fun _ _ ↦ primePowerWeight_nonneg _) A) x

/-- `rayClassPsi` is monotone in the cutoff. -/
theorem rayClassPsi_mono (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    Monotone (rayClassPsi 𝔪 c) :=
  primePowerSummatory_mono K _
    fun A ↦ Set.indicator_nonneg (fun _ _ ↦ primePowerWeight_nonneg _) A

/-- Below `2`, `rayClassPsi` vanishes. -/
theorem rayClassPsi_eq_zero_of_lt_two (𝔪 : Modulus K) (c : RayClassGroup 𝔪) {x : ℝ}
    (hx : x < 2) : rayClassPsi 𝔪 c x = 0 := by
  rw [rayClassPsi_apply, primePowersLE_eq_empty_of_lt_two hx, Finset.sum_empty]

/-! ### Agreement with the von Mangoldt transform of `rayClassCoeff` -/

/-- On a prime-power ideal, `(rayClassCoeff 𝔪 c).vonMangoldtTransform` agrees with the indicator
of `rayClassPrimePowerSet 𝔪 c` against `primePowerWeight`. -/
theorem vonMangoldtTransform_rayClassCoeff_idealPrimePower (𝔪 : Modulus K) (c : RayClassGroup 𝔪)
    (A : IdealPrimePower K) :
    (rayClassCoeff 𝔪 c).vonMangoldtTransform (A : (Ideal (𝓞 K))⁰) =
      (((rayClassPrimePowerSet 𝔪 c).indicator (primePowerWeight (K := K)) A : ℝ) : ℂ) := by
  classical
  rw [IdealArithmeticFunction.vonMangoldtTransform_apply, vonMangoldt_eq_primePowerWeight,
    rayClassCoeff_apply]
  by_cases hA : A ∈ rayClassPrimePowerSet 𝔪 c
  · rw [Set.indicator_of_mem hA, ite_eq_left (mem_rayClassPrimePowerSet_iff.mp hA), one_mul]
  · rw [Set.indicator_of_notMem hA, ite_eq_right (mt mem_rayClassPrimePowerSet_iff.mpr hA),
      zero_mul, Complex.ofReal_zero]

/-- **Ideal-summatory presentation of `rayClassPsi`.** Summing the von Mangoldt transform of the
class indicator `rayClassCoeff 𝔪 c` over all nonzero ideals of norm at most `x` produces
`rayClassPsi 𝔪 c x`. -/
theorem idealSummatory_vonMangoldtTransform_rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪)
    (x : ℝ) :
    idealSummatory K (rayClassCoeff 𝔪 c).vonMangoldtTransform x = (rayClassPsi 𝔪 c x : ℂ) := by
  rw [idealSummatory_eq_primePowerSummatory K (rayClassCoeff 𝔪 c).vonMangoldtTransform
    (fun A ↦ (((rayClassPrimePowerSet 𝔪 c).indicator (primePowerWeight (K := K)) A : ℝ) : ℂ))
    (vonMangoldtTransform_rayClassCoeff_idealPrimePower 𝔪 c)
    (fun I hI ↦ by
      rw [IdealArithmeticFunction.vonMangoldtTransform_apply,
        IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hI, mul_zero]),
    rayClassPsi_apply, primePowerSummatory_apply, Complex.ofReal_sum]

/-- Real-part form of `idealSummatory_vonMangoldtTransform_rayClassCoeff`. -/
theorem re_idealSummatory_vonMangoldtTransform_rayClassCoeff (𝔪 : Modulus K)
    (c : RayClassGroup 𝔪) (x : ℝ) :
    (idealSummatory K (rayClassCoeff 𝔪 c).vonMangoldtTransform x).re = rayClassPsi 𝔪 c x := by
  rw [idealSummatory_vonMangoldtTransform_rayClassCoeff, Complex.ofReal_re]

/-- **Regrouped von Mangoldt arithmetic function of a ray class**: the total logarithmic weight of
prime-power ideals of absolute norm `n` coprime to `𝔪` in the ray class `c`. -/
noncomputable def rayClassVonMangoldtCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    ArithmeticFunction ℝ where
  toFun n := (normCoeff K (rayClassCoeff 𝔪 c).vonMangoldtTransform n).re
  map_zero' := by simp

/-- Value of `rayClassVonMangoldtCoeff` at `n`. -/
theorem rayClassVonMangoldtCoeff_apply (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (n : ℕ) :
    rayClassVonMangoldtCoeff 𝔪 c n =
      (normCoeff K (rayClassCoeff 𝔪 c).vonMangoldtTransform n).re :=
  (rfl)

/-- Every value of `(rayClassCoeff 𝔪 c).vonMangoldtTransform` is real and nonnegative. -/
private theorem vonMangoldtTransform_rayClassCoeff_im_and_re_nonneg (𝔪 : Modulus K)
    (c : RayClassGroup 𝔪) (I : (Ideal (𝓞 K))⁰) :
    ((rayClassCoeff 𝔪 c).vonMangoldtTransform I).im = 0 ∧
      0 ≤ ((rayClassCoeff 𝔪 c).vonMangoldtTransform I).re := by
  by_cases hI : IsPrimePow (I : Ideal (𝓞 K))
  · set A : IdealPrimePower K := ⟨I, hI⟩
    have hA : (A : (Ideal (𝓞 K))⁰) = I := rfl
    rw [← hA, vonMangoldtTransform_rayClassCoeff_idealPrimePower, Complex.ofReal_im,
      Complex.ofReal_re]
    exact ⟨rfl, Set.indicator_nonneg (fun _ _ ↦ primePowerWeight_nonneg _) A⟩
  · simp [IdealArithmeticFunction.vonMangoldtTransform_apply,
      IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hI]

/-- Cast to `ℂ`, `rayClassVonMangoldtCoeff 𝔪 c` is the norm regrouping of
`(rayClassCoeff 𝔪 c).vonMangoldtTransform`. -/
@[simp]
theorem ofReal_rayClassVonMangoldtCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (n : ℕ) :
    (rayClassVonMangoldtCoeff 𝔪 c n : ℂ) =
      normCoeff K (rayClassCoeff 𝔪 c).vonMangoldtTransform n := by
  refine Complex.ext (by rw [Complex.ofReal_re, rayClassVonMangoldtCoeff_apply]) ?_
  rw [Complex.ofReal_im, normCoeff_eq_sum_normFiber, Complex.im_sum]
  exact (Finset.sum_eq_zero fun I _ ↦
    (vonMangoldtTransform_rayClassCoeff_im_and_re_nonneg 𝔪 c I).1).symm

/-- `rayClassVonMangoldtCoeff` is nonnegative. -/
theorem rayClassVonMangoldtCoeff_nonneg (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (n : ℕ) :
    0 ≤ rayClassVonMangoldtCoeff 𝔪 c n := by
  rw [rayClassVonMangoldtCoeff_apply, normCoeff_eq_sum_normFiber, Complex.re_sum]
  exact Finset.sum_nonneg fun I _ ↦
    (vonMangoldtTransform_rayClassCoeff_im_and_re_nonneg 𝔪 c I).2

/-- `rayClassVonMangoldtCoeff` vanishes outside natural prime powers. -/
theorem rayClassVonMangoldtCoeff_eq_zero_of_not_isPrimePow (𝔪 : Modulus K) (c : RayClassGroup 𝔪)
    {n : ℕ} (hn : ¬ IsPrimePow n) : rayClassVonMangoldtCoeff 𝔪 c n = 0 := by
  rw [rayClassVonMangoldtCoeff_apply, normCoeff_eq_sum_normFiber, Complex.re_sum]
  refine Finset.sum_eq_zero fun I hI ↦ ?_
  have hnot : ¬ IsPrimePow (I : Ideal (𝓞 K)) := fun h ↦ by
    rw [← (mem_normFiber K).mp hI] at hn
    exact hn (isPrimePow_absNorm ⟨I, h⟩)
  simp [IdealArithmeticFunction.vonMangoldtTransform_apply,
    IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hnot]

/-- `rayClassPsi` is the inclusive partial sum of `rayClassVonMangoldtCoeff`. -/
theorem rayClassPsi_eq_sum_Icc (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassPsi 𝔪 c x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, rayClassVonMangoldtCoeff 𝔪 c n := by
  have h := congrArg Complex.re (idealSummatory_vonMangoldtTransform_rayClassCoeff 𝔪 c x)
  rw [Complex.ofReal_re, idealSummatory_eq_sum_Icc_normCoeff, Complex.re_sum] at h
  exact h.symm.trans (Finset.sum_congr rfl fun n _ ↦ (rayClassVonMangoldtCoeff_apply 𝔪 c n).symm)

/-! ### Removal of higher prime powers -/

/-- The difference `rayClassPsi 𝔪 c - rayClassTheta 𝔪 c` is the higher-prime-power sum restricted
to `rayClassPrimePowerSet 𝔪 c`. -/
theorem rayClassPsi_sub_rayClassTheta_eq_primePowerSummatory (𝔪 : Modulus K) (c : RayClassGroup 𝔪)
    (x : ℝ) :
    rayClassPsi 𝔪 c x - rayClassTheta 𝔪 c x =
      primePowerSummatory K ((rayClassPrimePowerSet 𝔪 c).indicator higherPrimePowerWeight) x :=
  primePowerSummatory_indicator_sub_primeTheta (rayClassPrimePowerSet 𝔪 c) (rayClassPrimeSet 𝔪 c)
    (fun _ ↦ ofPrime_mem_rayClassPrimePowerSet_iff) x

/-- `rayClassTheta` never exceeds `rayClassPsi`. -/
theorem rayClassTheta_le_rayClassPsi (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassTheta 𝔪 c x ≤ rayClassPsi 𝔪 c x := by
  rw [← sub_nonneg, rayClassPsi_sub_rayClassTheta_eq_primePowerSummatory]
  exact primePowerSummatory_nonneg K _
    (fun A ↦ Set.indicator_nonneg (fun _ _ ↦ higherPrimePowerWeight_nonneg _) A) x

/-- **Higher-prime-power domination.** The gap `rayClassPsi 𝔪 c x - rayClassTheta 𝔪 c x` is bounded
by the unrestricted higher-prime-power tail `higherPrimePowerTheta K x`. -/
theorem rayClassPsi_sub_rayClassTheta_le_higherPrimePowerTheta (𝔪 : Modulus K)
    (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassPsi 𝔪 c x - rayClassTheta 𝔪 c x ≤ higherPrimePowerTheta K x := by
  rw [rayClassPsi_sub_rayClassTheta_eq_primePowerSummatory, higherPrimePowerTheta_apply,
    primePowerSummatory_apply, primePowerSummatory_apply]
  exact Finset.sum_le_sum fun A _ ↦
    Set.indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ higherPrimePowerWeight_nonneg A

/-- The higher-prime-power contribution to `rayClassPsi` is `O(√x log² x)`. -/
theorem rayClassPsi_sub_rayClassTheta_isBigO (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    (fun x ↦ rayClassPsi 𝔪 c x - rayClassTheta 𝔪 c x) =O[atTop]
      fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2 := by
  simpa only [rayClassPsi_sub_rayClassTheta_eq_primePowerSummatory] using
    primePowerSummatory_isBigO_of_le_higherPrimePowerWeight K zero_le_one fun A ↦ by
      rw [one_mul, Real.norm_of_nonneg
        (Set.indicator_nonneg (fun _ _ ↦ higherPrimePowerWeight_nonneg _) A)]
      exact Set.indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ higherPrimePowerWeight_nonneg A

/-- The higher-prime-power contribution to `rayClassPsi` is `o(x)`. -/
theorem rayClassPsi_sub_rayClassTheta_isLittleO (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    (fun x ↦ rayClassPsi 𝔪 c x - rayClassTheta 𝔪 c x) =o[atTop] fun x : ℝ ↦ x :=
  (rayClassPsi_sub_rayClassTheta_isBigO 𝔪 c).trans_isLittleO isLittleO_sqrt_mul_log_sq

/-- The higher-prime-power contribution to `rayClassPsi` is `o(x exp (-c₀ √log x))` for every real
`c₀`. -/
theorem rayClassPsi_sub_rayClassTheta_isLittleO_mul_exp_neg_mul_sqrt_log (𝔪 : Modulus K)
    (c : RayClassGroup 𝔪) (c₀ : ℝ) :
    (fun x ↦ rayClassPsi 𝔪 c x - rayClassTheta 𝔪 c x) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x)) := by
  have hlog : (fun x : ℝ ↦ Real.log x ^ 2) =o[atTop] fun x : ℝ ↦ x ^ (1 / 4 : ℝ) := by
    refine (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 4)).congr' ?_
      EventuallyEq.rfl
    filter_upwards with x
    exact Real.rpow_two (Real.log x)
  have hsqrt : (fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2) =o[atTop]
      fun x : ℝ ↦ x ^ (3 / 4 : ℝ) := by
    refine ((isBigO_refl (fun x : ℝ ↦ Real.sqrt x) atTop).mul_isLittleO hlog).congr'
      EventuallyEq.rfl ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)]
    norm_num
  exact ((rayClassPsi_sub_rayClassTheta_isBigO 𝔪 c).trans_isLittleO hsqrt).trans
    (Real.isLittleO_rpow_mul_exp_neg_mul_sqrt_log (by norm_num : (3 / 4 : ℝ) < 1) c₀)

/-! ### Partition across the ray class group and bad-prime bound -/

/-- At a prime power `A`, summing the indicators of `rayClassPrimePowerSet 𝔪 c` over all ray
classes gives `log N(𝔭)` if `primePowerBase A ∉ 𝔪.support` and `0` otherwise. -/
theorem sum_indicator_rayClassPrimePowerSet (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)]
    (A : IdealPrimePower K) :
    ∑ c : RayClassGroup 𝔪, (rayClassPrimePowerSet 𝔪 c).indicator primePowerWeight A =
      {B : IdealPrimePower K | primePowerBase B ∉ 𝔪.support}.indicator primePowerWeight A := by
  classical
  by_cases hA : primePowerBase A ∈ 𝔪.support
  · rw [Set.indicator_of_notMem (by simpa using hA)]
    exact Finset.sum_eq_zero fun c _ ↦ Set.indicator_of_notMem
      (fun h ↦ isCoprimeTo_idealPrimePower_iff.mp (mem_rayClassPrimePowerSet_iff.mp h).1 hA) _
  · rw [Set.indicator_of_mem (by simpa using hA)]
    have hcop : 𝔪.IsCoprimeTo (A : Ideal (𝓞 K)) := isCoprimeTo_idealPrimePower_iff.mpr hA
    set c₀ := idealClass 𝔪 ⟨(A : Ideal (𝓞 K)), Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩
    rw [Finset.sum_eq_single c₀
      (fun c _ hc ↦ Set.indicator_of_notMem
        (fun h ↦ hc (mem_rayClassPrimePowerSet_iff.mp h).2.symm) _)
      (fun h ↦ absurd (Finset.mem_univ c₀) h)]
    exact Set.indicator_of_mem (mem_rayClassPrimePowerSet_iff.mpr ⟨hcop, rfl⟩) _

/-- **Partition of `ψ_K` by ray classes.** Summing `rayClassPsi 𝔪 c` over all ray classes and
adding `primePsi` of the finite bad-prime set `𝔪.support` recovers `primePsi K Set.univ`. -/
theorem sum_rayClassPsi_add_primePsi_support (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)]
    (x : ℝ) :
    ∑ c : RayClassGroup 𝔪, rayClassPsi 𝔪 c x +
        primePsi K (𝔪.support : Set (HeightOneSpectrum (𝓞 K))) x =
      primePsi K Set.univ x := by
  simp only [rayClassPsi_apply, primePsi_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [sum_indicator_rayClassPrimePowerSet]
  have huniv : {A : IdealPrimePower K | primePowerBase A ∈ Set.univ}.indicator primePowerWeight A =
      primePowerWeight A := Set.indicator_of_mem (Set.mem_univ _) _
  by_cases hA : primePowerBase A ∈ 𝔪.support
  · rw [Set.indicator_of_notMem (by simpa using hA), Set.indicator_of_mem (by simpa using hA),
      huniv, zero_add]
  · rw [Set.indicator_of_mem (by simpa using hA), Set.indicator_of_notMem (by simpa using hA),
      huniv, add_zero]

/-- At the trivial modulus `Modulus.one K`, the ray-class `ψ` functions sum to `ψ_K`. -/
@[simp]
theorem sum_rayClassPsi_one [Fintype (RayClassGroup (Modulus.one K))] (x : ℝ) :
    ∑ c : RayClassGroup (Modulus.one K), rayClassPsi (Modulus.one K) c x =
      primePsi K Set.univ x := by
  simpa [Modulus.support_one] using sum_rayClassPsi_add_primePsi_support (Modulus.one K) x

/-- **Explicit bad-prime bound.** For `x ≥ 1`, the prime powers sharing a prime with `𝔪` contribute
at most `𝔪.support.card * log x` between `ψ_K(x)` and `∑_c rayClassPsi 𝔪 c x`. -/
theorem primePsi_univ_sub_sum_rayClassPsi_le (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)]
    {x : ℝ} (hx : 1 ≤ x) :
    primePsi K Set.univ x - ∑ c : RayClassGroup 𝔪, rayClassPsi 𝔪 c x ≤
      𝔪.support.card * Real.log x := by
  rw [← sum_rayClassPsi_add_primePsi_support 𝔪 x, add_sub_cancel_left]
  simpa only [Set.ncard_coe_finset] using primePsi_le_ncard_mul_log 𝔪.support.finite_toSet hx

/-- The prime powers sharing a prime with `𝔪` contribute `O(log x)` between `ψ_K` and the sum of
`rayClassPsi 𝔪 c`. -/
theorem primePsi_univ_sub_sum_rayClassPsi_isBigO_log (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)] :
    (fun x : ℝ ↦ primePsi K Set.univ x - ∑ c : RayClassGroup 𝔪, rayClassPsi 𝔪 c x)
      =O[atTop] Real.log := by
  refine (primePsi_isBigO_log_of_finite 𝔪.support.finite_toSet).congr_left fun x ↦ ?_
  rw [← sum_rayClassPsi_add_primePsi_support 𝔪 x, add_sub_cancel_left]

/-- **Partition of `π_K` by ray classes.** Summing `rayClassPrimeCount 𝔪 c` over all ray classes
and adding the primes in `𝔪.support` of norm at most `x` recovers `primeCount K Set.univ`. -/
theorem sum_natCast_rayClassPrimeCount_add_primeCount_support (𝔪 : Modulus K)
    [Fintype (RayClassGroup 𝔪)] (x : ℝ) :
    ∑ c : RayClassGroup 𝔪, (rayClassPrimeCount 𝔪 c x : ℝ) +
        primeCount K (𝔪.support : Set (HeightOneSpectrum (𝓞 K))) x =
      primeCount K Set.univ x := by
  classical
  simp only [natCast_rayClassPrimeCount, primeCount_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun 𝔭 _ ↦ ?_
  by_cases h𝔭 : 𝔭 ∈ 𝔪.support
  · have hnot : ∀ c : RayClassGroup 𝔪, 𝔭 ∉ rayClassPrimeSet 𝔪 c :=
      fun _ h ↦ isCoprimeTo_asIdeal_iff.mp (mem_rayClassPrimeSet_iff.mp h).1 h𝔭
    simp [h𝔭, hnot]
  · have hcop : 𝔪.IsCoprimeTo 𝔭.asIdeal := isCoprimeTo_asIdeal_iff.mpr h𝔭
    set c₀ := idealClass 𝔪 ⟨𝔭.asIdeal, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩
    rw [Finset.sum_eq_single c₀
      (fun c _ hc ↦ Set.indicator_of_notMem (fun h ↦ hc (mem_rayClassPrimeSet_iff.mp h).2.symm) _)
      (fun h ↦ absurd (Finset.mem_univ c₀) h)]
    have hmem : 𝔭 ∈ rayClassPrimeSet 𝔪 c₀ := ⟨hcop, rfl⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem (by simpa using h𝔭),
      Set.indicator_of_mem (Set.mem_univ _), add_zero]

/-! ### Change of modulus -/

open scoped Classical in
/-- For `𝔪 ∣ 𝔫` and a prime power `A`, summing the prime-power weights of the ray classes of `𝔫`
lying over `c` gives the weight of `c` if `A` is coprime to `𝔫`, and `0` otherwise. -/
theorem sum_indicator_rayClassPrimePowerSet_classMap {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Fintype (RayClassGroup 𝔫)] [DecidableEq (RayClassGroup 𝔪)] (c : RayClassGroup 𝔪)
    (A : IdealPrimePower K) :
    ∑ c' with classMap h c' = c, (rayClassPrimePowerSet 𝔫 c').indicator primePowerWeight A =
      if 𝔫.IsCoprimeTo (A : Ideal (𝓞 K)) then
        (rayClassPrimePowerSet 𝔪 c).indicator primePowerWeight A
      else 0 := by
  by_cases hA : 𝔫.IsCoprimeTo (A : Ideal (𝓞 K))
  · rw [ite_eq_left hA]
    have hAm : 𝔪.IsCoprimeTo (A : Ideal (𝓞 K)) := Modulus.mem_integralIdealsPrimeTo.mp
      (integralIdealsPrimeTo_antitone h (Modulus.mem_integralIdealsPrimeTo.mpr hA))
    set J𝔫 : integralIdealsPrimeTo 𝔫 :=
      ⟨(A : Ideal (𝓞 K)), Modulus.mem_integralIdealsPrimeTo.mpr hA⟩
    set J𝔪 : integralIdealsPrimeTo 𝔪 :=
      ⟨(A : Ideal (𝓞 K)), Modulus.mem_integralIdealsPrimeTo.mpr hAm⟩
    have hcl : classMap h (idealClass 𝔫 J𝔫) = idealClass 𝔪 J𝔪 := by
      rw [classMap_idealClass]
      exact congrArg (idealClass 𝔪) (Subtype.ext (coe_integralIdealsPrimeToInclusion h J𝔫))
    by_cases hc : idealClass 𝔪 J𝔪 = c
    · rw [Set.indicator_of_mem (mem_rayClassPrimePowerSet_iff.mpr ⟨hAm, hc⟩),
        Finset.sum_eq_single (idealClass 𝔫 J𝔫)
          (fun c' _ hc' ↦ Set.indicator_of_notMem
            (fun hmem ↦ hc' (mem_rayClassPrimePowerSet_iff.mp hmem).2.symm) _)
          (fun hnot ↦ absurd (Finset.mem_filter.mpr
            ⟨Finset.mem_univ (idealClass 𝔫 J𝔫), hcl.trans hc⟩) hnot)]
      exact Set.indicator_of_mem (mem_rayClassPrimePowerSet_iff.mpr ⟨hA, rfl⟩) _
    · rw [Set.indicator_of_notMem (fun hmem ↦ hc (mem_rayClassPrimePowerSet_iff.mp hmem).2)]
      refine Finset.sum_eq_zero fun c' hc' ↦ Set.indicator_of_notMem (fun hmem ↦ hc ?_) _
      rw [← hcl, (mem_rayClassPrimePowerSet_iff.mp hmem).2, (Finset.mem_filter.mp hc').2]
  · rw [ite_eq_right hA]
    exact Finset.sum_eq_zero fun c' _ ↦ Set.indicator_of_notMem
      (fun hmem ↦ hA (mem_rayClassPrimePowerSet_iff.mp hmem).1) _

/-- **Change of modulus for `rayClassPsi` without new primes.** If `𝔪 ∣ 𝔫` and
`𝔫.support ⊆ 𝔪.support`, summing `rayClassPsi 𝔫 c'` over `classMap h c' = c` gives
`rayClassPsi 𝔪 c`. -/
theorem sum_rayClassPsi_classMap {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) (h' : 𝔫.support ⊆ 𝔪.support)
    [Fintype (RayClassGroup 𝔫)] [DecidableEq (RayClassGroup 𝔪)] (c : RayClassGroup 𝔪) (x : ℝ) :
    ∑ c' with classMap h c' = c, rayClassPsi 𝔫 c' x = rayClassPsi 𝔪 c x := by
  classical
  simp only [rayClassPsi_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [sum_indicator_rayClassPrimePowerSet_classMap h c A]
  split_ifs with hA
  · rfl
  · symm
    refine Set.indicator_of_notMem (fun hAm ↦ hA ?_) _
    exact isCoprimeTo_idealPrimePower_iff.mpr fun hv ↦
      isCoprimeTo_idealPrimePower_iff.mp (mem_rayClassPrimePowerSet_iff.mp hAm).1 (h' hv)

/-- **General change of modulus for `rayClassPsi`.** For any `h : 𝔪 ∣ 𝔫`, `rayClassPsi 𝔪 c x`
exceeds the fibre sum `∑_{classMap h c' = c} rayClassPsi 𝔫 c' x` only on prime powers based at
primes in `𝔫.support \ 𝔪.support`, hence by `O(log x)`. -/
theorem rayClassPsi_sub_sum_rayClassPsi_classMap_isBigO_log {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    [Fintype (RayClassGroup 𝔫)] [DecidableEq (RayClassGroup 𝔪)] (c : RayClassGroup 𝔪) :
    (fun x : ℝ ↦ rayClassPsi 𝔪 c x - ∑ c' with classMap h c' = c, rayClassPsi 𝔫 c' x)
      =O[atTop] Real.log := by
  classical
  set S : Set (HeightOneSpectrum (𝓞 K)) :=
    (𝔫.support : Set (HeightOneSpectrum (𝓞 K))) \ (𝔪.support : Set (HeightOneSpectrum (𝓞 K)))
  have hS : S.Finite := 𝔫.support.finite_toSet.sdiff
  have hdom : ∀ x : ℝ, 0 ≤ rayClassPsi 𝔪 c x - ∑ c' with classMap h c' = c, rayClassPsi 𝔫 c' x ∧
      rayClassPsi 𝔪 c x - ∑ c' with classMap h c' = c, rayClassPsi 𝔫 c' x ≤ primePsi K S x :=
    fun x ↦ by
      simp only [rayClassPsi_apply, primePsi_apply]
      rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
      refine ⟨Finset.sum_nonneg fun A _ ↦ ?_, Finset.sum_le_sum fun A _ ↦ ?_⟩
      · rw [sum_indicator_rayClassPrimePowerSet_classMap h c A]
        split_ifs
        · rw [sub_self]
        · rw [sub_zero]
          exact Set.indicator_nonneg (fun _ _ ↦ primePowerWeight_nonneg _) A
      · rw [sum_indicator_rayClassPrimePowerSet_classMap h c A]
        split_ifs with hA
        · rw [sub_self]
          exact Set.indicator_nonneg (fun _ _ ↦ primePowerWeight_nonneg _) A
        · rw [sub_zero]
          by_cases hAm : A ∈ rayClassPrimePowerSet 𝔪 c
          · have hmem : primePowerBase A ∈ S :=
              ⟨not_not.mp (mt isCoprimeTo_idealPrimePower_iff.mpr hA),
                isCoprimeTo_idealPrimePower_iff.mp (mem_rayClassPrimePowerSet_iff.mp hAm).1⟩
            rw [Set.indicator_of_mem hAm,
              Set.indicator_of_mem (s := {B : IdealPrimePower K | primePowerBase B ∈ S}) hmem]
          · rw [Set.indicator_of_notMem hAm]
            exact Set.indicator_nonneg (fun _ _ ↦ primePowerWeight_nonneg _) A
  refine IsBigO.trans ?_ (primePsi_isBigO_log_of_finite hS)
  refine IsBigO.of_bound 1 (Eventually.of_forall fun x ↦ ?_)
  rw [one_mul, Real.norm_of_nonneg (hdom x).1, Real.norm_of_nonneg (primePsi_nonneg _ _)]
  exact (hdom x).2

end TauCeti.LFunctions
