/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import TauCeti.NumberTheory.LFunctions.RayClass.CharacterExpansion
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Rat

import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.SubgroupConductor.Rat
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Specialization of `rayClassPsi` and `rayClassPrimeCount` to `ℚ`

Over `ℚ`, the general number-field ray-class prime-counting functions of `RayClass/VonMangoldt.lean`
and `RayClass/CharacterExpansion.lean` specialize directly to classical prime counting and
arithmetic progressions:

* For `S = Set.univ`, `primeVonMangoldtCoeff ℚ Set.univ` agrees termwise with Mathlib's
  `ArithmeticFunction.vonMangoldt`, so `primePsi ℚ Set.univ = Chebyshev.psi`. Since
  `RayClassGroup (Modulus.one ℚ)` is trivial, `rayClassPsi (Modulus.one ℚ) c = Chebyshev.psi` as
  well.
* For the modulus `ratModulus q hq` (`(q)·∞` of `ℚ`) and a unit `u : (ZMod q)ˣ`,
  `rayClassVonMangoldtCoeff (ratModulus q hq) ((ratModulusEquivZMod q hq).symm u)` agrees at *every*
  natural number (including higher prime powers) with Mathlib's
  `ArithmeticFunction.vonMangoldt.residueClass (u : ZMod q)`.
* For `q ≠ 0`, `a.Coprime q`, and *every* real cutoff `x`, `rayClassPrimeCount (ratModulus q hq)` at
  the class of `a` equals `((Nat.primesBelow (⌊x⌋₊ + 1)).filter (· ≡ a [MOD q])).card`: a rational
  prime congruent to `a` modulo `q` is automatically coprime to `q`, and below `x < 0` both counts
  vanish. Consequently the effective number-field transfer theorems specialize directly to primes in
  arithmetic progressions modulo `q` with main term `Real.logIntegral x / q.totient`.

## Main results

* `TauCeti.LFunctions.primeVonMangoldtCoeff_rat_univ` and `TauCeti.LFunctions.primePsi_rat_univ`:
  over `ℚ`, `primePsi ℚ Set.univ = Chebyshev.psi`.
* `TauCeti.LFunctions.rayClassPsi_rat_one`: for `Modulus.one ℚ`, `rayClassPsi` is `Chebyshev.psi`.
* `TauCeti.LFunctions.rayClassVonMangoldtCoeff_ratModulus` and
  `TauCeti.LFunctions.rayClassPsi_ratModulus`: exact agreement with
  `ArithmeticFunction.vonMangoldt.residueClass`.
* `TauCeti.LFunctions.rayClassPrimeCount_ratModulus_of_coprime`: exact identification of
  `rayClassPrimeCount` for `ratModulus q hq` with
  `((Nat.primesBelow (⌊x⌋₊ + 1)).filter (· ≡ a [MOD q])).card`.
* `primeCounting_progression_sub_div_totient_isLittleO_of_rayClassPsi_sub_sum_isBigO` and
  `primeCounting_progression_sub_div_totient_isLittleO_of_rayClassPsi_isBigO`: effective transfer
  for primes in arithmetic progressions over `ℚ`.
-/

public section

namespace TauCeti.LFunctions

open Asymptotics Filter NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

/-! ### All primes of `ℚ` and the trivial modulus -/

/-- Over `ℚ`, `primeVonMangoldtCoeff ℚ Set.univ` agrees with `ArithmeticFunction.vonMangoldt` at
every natural number. -/
@[simp]
theorem primeVonMangoldtCoeff_rat_univ (n : ℕ) :
    primeVonMangoldtCoeff ℚ Set.univ n = ArithmeticFunction.vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hv
    rw [← hv, primeVonMangoldtCoeff_rat_natGenerator_pow Set.univ v hk,
      ite_eq_left (Set.mem_univ v), hv, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  · rw [primeVonMangoldtCoeff_eq_zero_of_not_isPrimePow _ hn,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]

/-- Over `ℚ`, `primePsi ℚ Set.univ` is Mathlib's `Chebyshev.psi`. -/
@[simp]
theorem primePsi_rat_univ (x : ℝ) : primePsi ℚ Set.univ x = Chebyshev.psi x := by
  rw [primePsi_eq_sum_range, Chebyshev.psi]
  simp_rw [primeVonMangoldtCoeff_rat_univ]
  refine (Finset.sum_subset (fun n hn ↦ Finset.mem_range.mpr (by
    have := Finset.mem_Ioc.mp hn; omega)) fun n hn hnot ↦ ?_).symm
  have hn0 : n = 0 := by
    have := Finset.mem_range.mp hn
    rw [Finset.mem_Ioc] at hnot
    omega
  rw [hn0, ArithmeticFunction.map_zero]

/-- `RayClassGroup (Modulus.one ℚ)` is a subsingleton, as the surjective image under `classMap` of
`RayClassGroup (ratModulus 1 one_ne_zero)` of order `φ(1) = 1`. -/
private theorem subsingleton_rayClassGroup_one_rat :
    Subsingleton (RayClassGroup (Modulus.one ℚ)) := by
  have : Subsingleton (RayClassGroup (ratModulus 1 one_ne_zero)) :=
    Finite.card_le_one_iff_subsingleton.mp (by rw [card_rayClassGroup_ratModulus, Nat.totient_one])
  exact (classMap_surjective (Modulus.one_dvd (ratModulus 1 one_ne_zero))).subsingleton

/-- At the trivial modulus `Modulus.one ℚ`, `rayClassPsi` equals `Chebyshev.psi`. -/
@[simp]
theorem rayClassPsi_rat_one (c : RayClassGroup (Modulus.one ℚ)) (x : ℝ) :
    rayClassPsi (Modulus.one ℚ) c x = Chebyshev.psi x := by
  have := Fintype.ofFinite (RayClassGroup (Modulus.one ℚ))
  have := subsingleton_rayClassGroup_one_rat
  rw [← primePsi_rat_univ, ← sum_rayClassPsi_one, Fintype.sum_subsingleton _ c]

/-! ### Ray classes modulo `(q)·∞` and residue classes modulo `q` -/

/-- Over `ℚ`, at a prime power `p ^ (m + 1)` generated by `v : HeightOneSpectrum (𝓞 ℚ)`,
`rayClassVonMangoldtCoeff 𝔪 c` is the indicator of membership in `rayClassPrimePowerSet 𝔪 c` at
`v.idealPrimePowerOf m` against `primePowerWeight`. -/
theorem rayClassVonMangoldtCoeff_rat_natGenerator_pow (𝔪 : Modulus ℚ) (c : RayClassGroup 𝔪)
    (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) :
    rayClassVonMangoldtCoeff 𝔪 c (Rat.HeightOneSpectrum.natGenerator v ^ (m + 1)) =
      (rayClassPrimePowerSet 𝔪 c).indicator primePowerWeight (v.idealPrimePowerOf m) := by
  rw [← Rat.HeightOneSpectrum.absNorm_asIdeal, ← map_pow, rayClassVonMangoldtCoeff_apply,
    normCoeff_eq_sum_normFiber, ← HeightOneSpectrum.coe_idealPrimePowerOf,
    normFiber_rat_absNorm ((v.idealPrimePowerOf m : IdealPrimePower ℚ) : (Ideal (𝓞 ℚ))⁰),
    Finset.sum_singleton, vonMangoldtTransform_rayClassCoeff_idealPrimePower, Complex.ofReal_re]

/-- **Agreement with `ArithmeticFunction.vonMangoldt.residueClass`.** For `q ≠ 0` and a unit
`u : (ZMod q)ˣ`, the ray-class von Mangoldt coefficient of `(ratModulusEquivZMod q hq).symm u`
equals Mathlib's `ArithmeticFunction.vonMangoldt.residueClass (u : ZMod q)` at *every* natural
number `n`. -/
theorem rayClassVonMangoldtCoeff_ratModulus {q : ℕ} (hq : q ≠ 0) (u : (ZMod q)ˣ) (n : ℕ) :
    rayClassVonMangoldtCoeff (ratModulus q hq) ((ratModulusEquivZMod q hq).symm u) n =
      ArithmeticFunction.vonMangoldt.residueClass (u : ZMod q) n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    have hgen : Rat.HeightOneSpectrum.natGenerator v = p := by
      rwa [Rat.HeightOneSpectrum.absNorm_asIdeal] at hv
    set A : IdealPrimePower ℚ := v.idealPrimePowerOf m
    have hAnorm : Ideal.absNorm (A : Ideal (𝓞 ℚ)) = p ^ (m + 1) := by
      rw [HeightOneSpectrum.coe_idealPrimePowerOf, map_pow, hv]
    have hweight : primePowerWeight A = ArithmeticFunction.vonMangoldt (p ^ (m + 1)) := by
      rw [primePowerWeight_eq_vonMangoldt_re,
        IdealArithmeticFunction.vonMangoldt_apply_of_eq_prime_pow
          (Ideal.prime_of_isPrime v.ne_bot v.isPrime) hk
          (HeightOneSpectrum.coe_idealPrimePowerOf v m).symm,
        Complex.ofReal_re, hv, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hmem_iff : A ∈ rayClassPrimePowerSet (ratModulus q hq)
          ((ratModulusEquivZMod q hq).symm u) ↔
        ((p ^ (m + 1) : ℕ) : ZMod q) = (u : ZMod q) := by
      rw [mem_rayClassPrimePowerSet_iff]
      constructor
      · rintro ⟨hcop, hcl⟩
        have hval := congrArg (fun d ↦ ((ratModulusEquivZMod q hq d : (ZMod q)ˣ) : ZMod q)) hcl
        rwa [coe_ratModulusEquivZMod_idealClass, MulEquiv.apply_symm_apply, hAnorm] at hval
      · intro hu
        have hpq : p.Coprime q := (Nat.coprime_pow_left_iff hk p q).mp
          ((ZMod.isUnit_iff_coprime (p ^ (m + 1)) q).mp (hu.symm ▸ u.isUnit))
        have hv_not : v ∉ (ratModulus q hq).support := by
          rw [mem_ratModulus_support_iff, Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd,
            hv]
          exact fun hdvd ↦ hp.not_dvd_one (hpq.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hdvd)
        have hcop : (ratModulus q hq).IsCoprimeTo (A : Ideal (𝓞 ℚ)) := by
          rw [isCoprimeTo_idealPrimePower_iff, HeightOneSpectrum.primePowerBase_idealPrimePowerOf]
          exact hv_not
        refine ⟨hcop, (MulEquiv.eq_symm_apply _).mpr (Units.ext ?_)⟩
        rw [coe_ratModulusEquivZMod_idealClass, hAnorm, hu]
    rw [← hgen, rayClassVonMangoldtCoeff_rat_natGenerator_pow, hgen,
      ArithmeticFunction.vonMangoldt.residueClass]
    by_cases hu : ((p ^ (m + 1) : ℕ) : ZMod q) = (u : ZMod q)
    · rw [Set.indicator_of_mem (hmem_iff.mpr hu), Set.indicator_of_mem hu, hweight]
    · rw [Set.indicator_of_notMem (mt hmem_iff.mp hu), Set.indicator_of_notMem hu]
  · rw [rayClassVonMangoldtCoeff_eq_zero_of_not_isPrimePow _ _ hn]
    exact (Set.indicator_apply_eq_zero.mpr fun _ ↦
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn).symm

/-- For `q ≠ 0` and `u : (ZMod q)ˣ`, `rayClassPsi` of `(ratModulusEquivZMod q hq).symm u` is the
partial sum of `ArithmeticFunction.vonMangoldt.residueClass (u : ZMod q)`. -/
theorem rayClassPsi_ratModulus {q : ℕ} (hq : q ≠ 0) (u : (ZMod q)ˣ) (x : ℝ) :
    rayClassPsi (ratModulus q hq) ((ratModulusEquivZMod q hq).symm u) x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt.residueClass (u : ZMod q) n := by
  rw [rayClassPsi_eq_sum_Icc]
  exact Finset.sum_congr rfl fun n _ ↦ rayClassVonMangoldtCoeff_ratModulus hq u n

/-! ### Prime counts in arithmetic progressions over `ℚ` -/

/-- For `q ≠ 0` and `a.Coprime q`, a prime ideal `v` of `𝓞 ℚ` lies in `rayClassPrimeSet` for the
ray class of `a` modulo `q` if and only if `Ideal.absNorm v.asIdeal ≡ a [MOD q]`. -/
theorem mem_rayClassPrimeSet_ratModulus_iff_modEq {q a : ℕ} (hq : q ≠ 0) (haq : a.Coprime q)
    {v : HeightOneSpectrum (𝓞 ℚ)} :
    v ∈ rayClassPrimeSet (ratModulus q hq)
        ((ratModulusEquivZMod q hq).symm (ZMod.unitOfCoprime a haq)) ↔
      Ideal.absNorm v.asIdeal ≡ a [MOD q] := by
  rw [mem_rayClassPrimeSet_iff]
  constructor
  · rintro ⟨_, hcl⟩
    have hval := congrArg (fun d ↦ ((ratModulusEquivZMod q hq d : (ZMod q)ˣ) : ZMod q)) hcl
    rwa [coe_ratModulusEquivZMod_idealClass, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime,
      ZMod.natCast_eq_natCast_iff] at hval
  · intro hpa
    have hp : (Ideal.absNorm v.asIdeal).Prime :=
      Rat.HeightOneSpectrum.absNorm_asIdeal v ▸ Rat.HeightOneSpectrum.prime_natGenerator v
    have hpz : ((Ideal.absNorm v.asIdeal : ℕ) : ZMod q) = (ZMod.unitOfCoprime a haq : ZMod q) := by
      rwa [ZMod.coe_unitOfCoprime, ZMod.natCast_eq_natCast_iff]
    have hpq : (Ideal.absNorm v.asIdeal).Coprime q :=
      (ZMod.isUnit_iff_coprime _ q).mp (hpz.symm ▸ (ZMod.unitOfCoprime a haq).isUnit)
    have hcop : (ratModulus q hq).IsCoprimeTo v.asIdeal := by
      rw [isCoprimeTo_asIdeal_iff, mem_ratModulus_support_iff,
        Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd]
      exact fun hdvd ↦ hp.not_dvd_one (hpq.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hdvd)
    refine ⟨hcop, (MulEquiv.eq_symm_apply _).mpr (Units.ext ?_)⟩
    rw [coe_ratModulusEquivZMod_idealClass, hpz]

/-- **Identification of `rayClassPrimeCount` over `ℚ` with primes in an arithmetic progression.**
For `q ≠ 0`, `a.Coprime q`, and *every* real cutoff `x`, `rayClassPrimeCount` for `ratModulus q hq`
at the class of `a` equals `((Nat.primesBelow (⌊x⌋₊ + 1)).filter (· ≡ a [MOD q])).card`. -/
theorem rayClassPrimeCount_ratModulus_of_coprime {q a : ℕ} (hq : q ≠ 0) (haq : a.Coprime q)
    (x : ℝ) :
    rayClassPrimeCount (ratModulus q hq)
        ((ratModulusEquivZMod q hq).symm (ZMod.unitOfCoprime a haq)) x =
      ((Nat.primesBelow (⌊x⌋₊ + 1)).filter (· ≡ a [MOD q])).card := by
  classical
  rw [rayClassPrimeCount_eq_card_filter]
  refine Finset.card_bij (fun v _ ↦ Ideal.absNorm v.asIdeal) ?_ ?_ ?_
  · intro v hv
    obtain ⟨hvLE, hmem⟩ := Finset.mem_filter.mp hv
    have hvx : (Ideal.absNorm v.asIdeal : ℝ) ≤ x :=
      (mem_normLE (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ Ideal.absNorm w.asIdeal)).mp hvLE
    have hp : (Ideal.absNorm v.asIdeal).Prime :=
      Rat.HeightOneSpectrum.absNorm_asIdeal v ▸ Rat.HeightOneSpectrum.prime_natGenerator v
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le (Nat.le_floor hvx), hp⟩,
      (mem_rayClassPrimeSet_ratModulus_iff_modEq hq haq).mp hmem⟩
  · intro v₁ _ v₂ _ hnorm
    refine HeightOneSpectrum.ext ?_
    rw [← Rat.RingOfIntegers.ideal_span_absNorm_eq_self v₁.asIdeal,
      ← Rat.RingOfIntegers.ideal_span_absNorm_eq_self v₂.asIdeal, hnorm]
  · intro p hp_mem
    obtain ⟨hp_below, hpa⟩ := Finset.mem_filter.mp hp_mem
    obtain ⟨hpx, hp⟩ := Nat.mem_primesBelow.mp hp_below
    have hx0 : 0 ≤ x := by
      by_contra! hxneg
      rw [Nat.floor_of_nonpos hxneg.le] at hpx
      exact not_lt_of_gt hp.one_lt hpx
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    have hvLE : v ∈ primesLE ℚ x := by
      rw [primesLE, mem_normLE, hv]
      exact (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hpx)).trans (Nat.floor_le hx0)
    exact ⟨v, Finset.mem_filter.mpr ⟨hvLE,
      (mem_rayClassPrimeSet_ratModulus_iff_modEq hq haq).mpr (hv.symm ▸ hpa)⟩, hv⟩

/-- **Effective progression prime-count transfer over `ℚ` absorbing sublinear secondary terms.** -/
theorem primeCounting_progression_sub_div_totient_isLittleO_of_rayClassPsi_sub_sum_isBigO
    {ι : Type*} {q a : ℕ} (hq : q ≠ 0) (haq : a.Coprime q) (s : Finset ι) (coeff β : ι → ℝ)
    {c₀ : ℝ} (hβ : ∀ i ∈ s, β i < 1)
    (h : (fun x ↦ rayClassPsi (ratModulus q hq)
          ((ratModulusEquivZMod q hq).symm (ZMod.unitOfCoprime a haq)) x -
        x / q.totient - ∑ i ∈ s, coeff i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x))) :
    (fun x : ℝ ↦ (((Nat.primesBelow (⌊x⌋₊ + 1)).filter (· ≡ a [MOD q])).card : ℝ) -
      Real.logIntegral x / q.totient) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x)) := by
  have hmain := rayClassPrimeCount_sub_div_card_isLittleO_of_rayClassPsi_sub_sum_isBigO
    (ratModulus q hq) ((ratModulusEquivZMod q hq).symm (ZMod.unitOfCoprime a haq))
    s coeff β hβ (by rwa [card_rayClassGroup_ratModulus])
  refine hmain.congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
  dsimp only
  rw [rayClassPrimeCount_ratModulus_of_coprime hq haq x, card_rayClassGroup_ratModulus]

/-- **Direct effective progression prime-count transfer over `ℚ`.** -/
theorem primeCounting_progression_sub_div_totient_isLittleO_of_rayClassPsi_isBigO {q a : ℕ}
    (hq : q ≠ 0) (haq : a.Coprime q) {c₀ : ℝ}
    (h : (fun x ↦ rayClassPsi (ratModulus q hq)
          ((ratModulusEquivZMod q hq).symm (ZMod.unitOfCoprime a haq)) x -
        x / q.totient) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x))) :
    (fun x : ℝ ↦ (((Nat.primesBelow (⌊x⌋₊ + 1)).filter (· ≡ a [MOD q])).card : ℝ) -
      Real.logIntegral x / q.totient) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x)) := by
  refine primeCounting_progression_sub_div_totient_isLittleO_of_rayClassPsi_sub_sum_isBigO
    hq haq (∅ : Finset Unit) 0 0 (by simp) ?_
  simpa only [Finset.sum_empty, sub_zero] using h

end TauCeti.LFunctions
