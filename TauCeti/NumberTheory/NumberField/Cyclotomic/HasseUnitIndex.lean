/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.NumberTheory.Cyclotomic.OddLevel
import TauCeti.NumberTheory.NumberField.CMField
import TauCeti.NumberTheory.RamificationInertia.Tower
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The Hasse unit index of a cyclotomic field

This file determines the Hasse unit index `NumberField.IsCMField.indexRealUnits K` for every
cyclotomic extension `K` of `ℚ` of positive level `n` (Washington, Corollary 4.13; Sharifi,
Lemma 4.2.17):

* When `n = p ^ a` is a prime power (including `a = 0` and `p ^ a = 2`, where `K ≃ ℚ` is totally
  real), `indexRealUnits K = 1`. For `p ^ a > 2`, the unique prime ideal `(ζ - 1)` above `p` has
  ramification index `2` over the maximal real subfield `K⁺` and satisfies
  `conj (ζ - 1) = (-ζ⁻¹) * (ζ - 1)`, so the odd-multiplicity criterion from
  `TauCeti.NumberTheory.NumberField.CMField` forces `indexRealUnits K = 1`.
* When `n > 2` with `n % 4 ≠ 2` is not a prime power (for instance `n = 12`), `ζ - 1` is an
  integral unit whose conjugate quotient `(ζ - 1) / conj (ζ - 1) = -ζ` generates the full torsion
  subgroup `torsion K`, forcing `indexRealUnits K = 2`.
* For a general level `n ≠ 0`, reducing `n ≡ 2 mod 4` to `n / 2` yields the complete dichotomy:
  `indexRealUnits K = 1` if and only if `n = 1`, `IsPrimePow n`, or
  `n % 4 = 2 ∧ IsPrimePow (n / 2)`, and `indexRealUnits K = 2` otherwise.

## Main results

* `TauCeti.IsCyclotomicExtension.Rat.isPrimitiveRoot_neg_torsionOrder`: for `n % 4 ≠ 2`, `-ζ` is a
  primitive `torsionOrder K`-th root of unity.
* `TauCeti.IsCyclotomicExtension.Rat.zpowers_eq_top_of_coe_eq_neg_isPrimitiveRoot`: for `n % 4 ≠ 2`,
  the torsion unit `-ζ` generates `NumberField.Units.torsion K`.
* `TauCeti.IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one_maximalRealSubfield`: for a
  prime power `p ^ a > 2`, the prime ideal `(ζ - 1)` has ramification index `2` over `𝓞 K⁺`.
* `TauCeti.IsCyclotomicExtension.Rat.indexRealUnits_eq_one_of_prime_pow`: every prime-power
  cyclotomic field `ℚ(ζ_{p^a})` (`a ≥ 0`) has Hasse unit index `1`.
* `TauCeti.IsCyclotomicExtension.Rat.indexRealUnits_eq_two_of_not_isPrimePow`: every cyclotomic
  field of non-prime-power conductor `n > 2` with `n % 4 ≠ 2` has Hasse unit index `2`.
* `TauCeti.IsCyclotomicExtension.Rat.indexRealUnits_eq`: full classification of the Hasse unit
  index of `ℚ(ζ_n)` for every `n ≠ 0`.

## References

* R. Sharifi, *Iwasawa theory*, Lemma 4.2.17.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.12 and Corollary 4.13.
-/

public section

open NumberField NumberField.IsCMField NumberField.Units

open scoped NumberField

namespace TauCeti.IsCyclotomicExtension.Rat

/-- **When `n % 4 ≠ 2`, `-ζ` is a primitive `torsionOrder K`-th root of unity.** If `n` is odd,
then `torsionOrder K = 2 * n` and `-ζ` has order `2 * n`; if `4 ∣ n`, then `torsionOrder K = n`
and `-ζ = ζ ^ (n / 2 + 1)` has order `n` because `gcd (n / 2 + 1) n = 1`. -/
theorem isPrimitiveRoot_neg_torsionOrder (n : ℕ) [NeZero n] (hn : n % 4 ≠ 2)
    {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (-ζ) (torsionOrder K) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  rw [_root_.IsCyclotomicExtension.Rat.torsionOrder_eq (n := n) (K := K)]
  rcases Nat.even_or_odd n with heven | hodd
  · rw [ite_eq_left heven]
    have h4 : 4 ∣ n := by
      obtain ⟨m, rfl⟩ := heven
      omega
    have hhalf : ζ ^ (n / 2) = -1 :=
      (hζ.pow (NeZero.pos n) (by omega : n = n / 2 * 2)).eq_neg_one_of_two_right
    have hneg : -ζ = ζ ^ (n / 2 + 1) := by rw [pow_succ, hhalf, neg_one_mul]
    rw [hneg]
    refine hζ.pow_of_coprime (n / 2 + 1) ?_
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hgcd
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hgcd
    have hq1 : q ∣ n / 2 + 1 := hqdvd.trans (Nat.gcd_dvd_left _ _)
    have hq2 : q ∣ n := hqdvd.trans (Nat.gcd_dvd_right _ _)
    have hqtwo : q ∣ 2 := by
      have hsub : 2 * (n / 2 + 1) = n + 2 := by omega
      have h21 : q ∣ n + 2 := hsub ▸ dvd_mul_of_dvd_right hq1 2
      exact (Nat.dvd_add_right hq2).mp h21
    have hqeq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hqtwo
    subst hqeq
    omega
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hodd)]
    exact hζ.neg_of_odd hodd (by norm_num)

/-- **The torsion unit `-ζ` generates the roots of unity of `ℚ(ζ_n)` when `n % 4 ≠ 2`.** For any
`n`-th cyclotomic extension `K` of `ℚ` with `n % 4 ≠ 2` and any primitive `n`-th root of unity
`ζ ∈ K`, the torsion unit with field value `-ζ` generates `NumberField.Units.torsion K`. -/
theorem zpowers_eq_top_of_coe_eq_neg_isPrimitiveRoot (n : ℕ) (hn : n % 4 ≠ 2)
    {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {η : torsion K}
    (hη : ((η : (𝓞 K)ˣ) : K) = -ζ) :
    Subgroup.zpowers η = ⊤ := by
  have hn0 : n ≠ 0 := by
    have hfin : IsOfFinOrder (η : (𝓞 K)ˣ) := (CommGroup.mem_torsion _).mp η.2
    have hpos : 0 < orderOf (η : (𝓞 K)ˣ) := hfin.orderOf_pos
    have hpow : ζ ^ (2 * orderOf (η : (𝓞 K)ˣ)) = 1 := by
      have h1 : ((η : (𝓞 K)ˣ) : K) ^ orderOf (η : (𝓞 K)ˣ) = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
      calc
        ζ ^ (2 * orderOf (η : (𝓞 K)ˣ))
            = ((-ζ) ^ 2) ^ orderOf (η : (𝓞 K)ˣ) := by rw [pow_mul, neg_sq]
        _ = (((η : (𝓞 K)ˣ) : K) ^ orderOf (η : (𝓞 K)ˣ)) ^ 2 := by
            rw [hη, ← pow_mul, mul_comm, pow_mul]
        _ = 1 := by rw [h1, one_pow]
    exact fun h0 ↦ by
      have hdvd := hζ.dvd_of_pow_eq_one (2 * orderOf (η : (𝓞 K)ˣ)) hpow
      rw [h0, zero_dvd_iff] at hdvd
      omega
  have : NeZero n := ⟨hn0⟩
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  have hprim : IsPrimitiveRoot (-ζ) (torsionOrder K) := isPrimitiveRoot_neg_torsionOrder n hn hζ
  let f : torsion K →* K :=
    (algebraMap (𝓞 K) K).toMonoidHom.comp ((Units.coeHom (𝓞 K)).comp (torsion K).subtype)
  have hf_inj : Function.Injective f := fun x y hxy ↦
    Subtype.ext (Units.ext (RingOfIntegers.coe_injective hxy))
  have hord : orderOf η = torsionOrder K := by
    rw [← orderOf_injective f hf_inj η]
    have hfη : f η = -ζ := hη
    rw [hfη, hprim.eq_orderOf]
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_zpowers, hord, torsionOrder]

/-- **The prime `(ζ - 1)` ramifies quadratically over `K⁺` for prime powers `p ^ a > 2`.** In a
`p ^ a`-th cyclotomic extension `K` of `ℚ` with `p` prime and `2 < p ^ a`, the unique prime ideal
`(ζ - 1)` above `p` has ramification index `2` over the maximal real subfield `K⁺`. -/
theorem ramificationIdx_span_zeta_sub_one_maximalRealSubfield
    (p a : ℕ) [Fact p.Prime] (hgt : 2 < p ^ a)
    {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p ^ a} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ a)) :
    (Ideal.span {hζ.toInteger - 1}).ramificationIdx (𝓞 (maximalRealSubfield K)) = 2 := by
  have ha : a ≠ 0 := by rintro rfl; simp at hgt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  have : IsCMField K :=
    _root_.IsCyclotomicExtension.Rat.isCMField K (S := {p ^ (k + 1)}) ⟨p ^ (k + 1), rfl, hgt⟩
  set F := maximalRealSubfield K
  set P : Ideal (𝓞 K) := Ideal.span {hζ.toInteger - 1}
  set q : Ideal (𝓞 F) := P.under (𝓞 F)
  have : P.IsPrime := _root_.IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one p k hζ
  have : Module.Finite (𝓞 F) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 K)
  have htower : P.ramificationIdx ℤ = q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) :=
    Ideal.ramificationIdx_tower q P
  have hPZ : P.ramificationIdx ℤ = Module.finrank ℚ F * 2 := by
    rw [_root_.IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one p k hζ,
      ← Nat.totient_prime_pow_succ Fact.out,
      ← _root_.IsCyclotomicExtension.Rat.finrank (p ^ (k + 1)) K,
      ← Module.finrank_mul_finrank ℚ F K, Algebra.IsQuadraticExtension.finrank_eq_two F K]
  have hq_le : q.ramificationIdx ℤ ≤ Module.finrank ℚ F := by
    simpa [RingOfIntegers.rank] using RamificationInertia.ramificationIdx_le_finrank ℤ q
  have hP_le : P.ramificationIdx (𝓞 F) ≤ 2 := by
    have hle := RamificationInertia.ramificationIdx_le_finrank (𝓞 F) P
    rwa [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K,
      Algebra.IsQuadraticExtension.finrank_eq_two F K] at hle
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  nlinarith

/-- **Every prime-power cyclotomic field has Hasse unit index one (Sharifi, Lemma 4.2.17).** For
every prime `p` and every exponent `a : ℕ` (including `a = 0` and `p ^ a = 2`, where `K ≃ ℚ` is
totally real), a `p ^ a`-th cyclotomic extension `K` of `ℚ` has `indexRealUnits K = 1`. -/
theorem indexRealUnits_eq_one_of_prime_pow (p a : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharZero K] [IsCyclotomicExtension {p ^ a} ℚ K] :
    indexRealUnits K = 1 := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ a} ℚ K
  by_cases hgt : 2 < p ^ a
  · have : IsCMField K :=
      _root_.IsCyclotomicExtension.Rat.isCMField K (S := {p ^ a}) ⟨p ^ a, rfl, hgt⟩
    have ha : a ≠ 0 := by rintro rfl; simp at hgt
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
    let ζ := IsCyclotomicExtension.zeta (p ^ (k + 1)) ℚ K
    have hζ : IsPrimitiveRoot ζ (p ^ (k + 1)) :=
      IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K
    set P : Ideal (𝓞 K) := Ideal.span {hζ.toInteger - 1}
    have hPprime : P.IsPrime := _root_.IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one p k hζ
    have he : Even (P.ramificationIdx (𝓞 (maximalRealSubfield K))) := by
      rw [ramificationIdx_span_zeta_sub_one_maximalRealSubfield p (k + 1) hgt hζ]
      exact even_two
    let uζ : torsion K := ⟨(hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne _)).unit,
      (CommGroup.mem_torsion _).mpr <| isOfFinOrder_iff_pow_eq_one.mpr
        ⟨p ^ (k + 1), NeZero.pos _, Units.ext (by
          simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one)⟩⟩
    have hη_mem : -(uζ : (𝓞 K)ˣ)⁻¹ ∈ torsion K := by
      rw [neg_eq_neg_one_mul]
      exact mul_mem neg_one_mem_torsion (inv_mem uζ.2)
    have hcoe : ((uζ : (𝓞 K)ˣ) : 𝓞 K) = hζ.toInteger := IsUnit.unit_spec _
    have hconj : ringOfIntegersComplexConj K (hζ.toInteger - 1) =
        ((-(uζ : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (hζ.toInteger - 1) := by
      rw [← hcoe]
      exact TauCeti.NumberField.IsCMField.ringOfIntegersComplexConj_torsion_sub_one K uζ
    have hodd : Odd (multiplicity P P) := by
      have hm : multiplicity P (P ^ 1) = 1 :=
        multiplicity_pow_self (_root_.IsCyclotomicExtension.Rat.span_zeta_sub_one_ne_bot p k hζ)
          (Ideal.isUnit_iff.not.mpr hPprime.ne_top) 1
      rw [pow_one] at hm
      rw [hm]
      exact odd_one
    exact TauCeti.NumberField.IsCMField.indexRealUnits_eq_one_of_odd_multiplicity K (P := P) he
      (η := ⟨-(uζ : (𝓞 K)ˣ)⁻¹, hη_mem⟩) hconj hodd
  · have htot : (p ^ a).totient = 1 := by
      have hppos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
      have hcases : p ^ a = 1 ∨ p ^ a = 2 := by omega
      rcases hcases with h | h <;> simp [h]
    have hfin : Module.finrank ℚ K = 1 := by
      rw [_root_.IsCyclotomicExtension.Rat.finrank (p ^ a) K, htot]
    have : IsTotallyReal K :=
      NumberField.nrComplexPlaces_eq_zero_iff.mp
        (NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hfin)
    exact TauCeti.NumberField.IsCMField.indexRealUnits_eq_one_of_isTotallyReal K

/-- **Non-prime-power cyclotomic fields have Hasse unit index two.** For `2 < n` with `n % 4 ≠ 2`
and `¬ IsPrimePow n` (for instance `n = 12`), the element `ζ - 1` is an integral unit whose
conjugate quotient `(ζ - 1) / conj (ζ - 1) = -ζ` generates `torsion K`, so `indexRealUnits K = 2`.
-/
theorem indexRealUnits_eq_two_of_not_isPrimePow (n : ℕ) (hgt : 2 < n) (hn4 : n % 4 ≠ 2)
    (hnp : ¬ IsPrimePow n) (K : Type*) [Field K] [CharZero K]
    [IsCyclotomicExtension {n} ℚ K] :
    indexRealUnits K = 2 := by
  have : NeZero n := NeZero.of_gt hgt
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  have : IsCMField K := _root_.IsCyclotomicExtension.Rat.isCMField K (S := {n}) ⟨n, rfl, hgt⟩
  rw [indexRealUnits_eq_two_iff]
  let ζ := IsCyclotomicExtension.zeta n ℚ K
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n ℚ K
  have hnorm : Algebra.norm ℤ (hζ.toInteger - 1) = 1 := by
    refine hζ.norm_toInteger_sub_one_eq_one hgt fun {p} hp k hpk ↦ hnp ?_
    have hk : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      simp at hpk
      omega
    exact ⟨p, k, hp.prime, hk, hpk⟩
  have hu : IsUnit (hζ.toInteger - 1) := by
    rw [NumberField.isUnit_iff_norm, NumberField.RingOfIntegers.coe_norm, ← Algebra.coe_norm_int,
      hnorm]
    simp
  refine ⟨hu.unit, ?_⟩
  let uζ : torsion K := ⟨(hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne n)).unit,
    (CommGroup.mem_torsion _).mpr <| isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, NeZero.pos n, Units.ext (by simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one)⟩⟩
  have hcoe : ((uζ : (𝓞 K)ˣ) : 𝓞 K) = hζ.toInteger := IsUnit.unit_spec _
  have hconj : unitsComplexConj K hu.unit = -(uζ : (𝓞 K)ˣ)⁻¹ * hu.unit := by
    apply Units.ext
    rw [TauCeti.NumberField.IsCMField.coe_unitsComplexConj, Units.val_mul, hu.unit_spec, ← hcoe]
    exact TauCeti.NumberField.IsCMField.ringOfIntegersComplexConj_torsion_sub_one K uζ
  have hval : ((unitsMulComplexConjInv K hu.unit : (𝓞 K)ˣ) : K) = -ζ := by
    have hmul : (unitsMulComplexConjInv K hu.unit : (𝓞 K)ˣ) = -(uζ : (𝓞 K)ˣ) := by
      rw [unitsMulComplexConjInv_apply, hconj, mul_inv_rev, inv_neg, inv_inv,
        mul_inv_cancel_left]
    rw [hmul, Units.val_neg, map_neg, hcoe]
    rfl
  exact zpowers_eq_top_of_coe_eq_neg_isPrimitiveRoot n hn4 hζ hval

private theorem indexRealUnits_eq_of_mod_four_ne_two {m : ℕ} [NeZero m] (hm4 : m % 4 ≠ 2)
    (K : Type*) [Field K] [CharZero K] [IsCyclotomicExtension {m} ℚ K] :
    indexRealUnits K = if m = 1 ∨ IsPrimePow m then 1 else 2 := by
  by_cases h1 : m = 1
  · subst h1
    rw [ite_eq_left (Or.inl rfl)]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclotomicExtension {2 ^ 0} ℚ K := by simpa using ‹IsCyclotomicExtension {1} ℚ K›
    exact indexRealUnits_eq_one_of_prime_pow 2 0 K
  · by_cases hpp : IsPrimePow m
    · rw [ite_eq_left (Or.inr hpp)]
      obtain ⟨p, a, hp, -, hpa⟩ := hpp
      have : Fact p.Prime := ⟨hp.nat_prime⟩
      have : IsCyclotomicExtension {p ^ a} ℚ K := hpa ▸ ‹IsCyclotomicExtension {m} ℚ K›
      exact indexRealUnits_eq_one_of_prime_pow p a K
    · rw [ite_eq_right (by push Not; exact ⟨h1, hpp⟩)]
      have hgt : 2 < m := by
        have := NeZero.pos m
        omega
      exact indexRealUnits_eq_two_of_not_isPrimePow m hgt hm4 hpp K

/-- **Complete classification of the cyclotomic Hasse unit index (Washington, Corollary 4.13).**
For every positive level `n` and every `n`-th cyclotomic extension `K` of `ℚ`,
`indexRealUnits K = 1` when `n = 1`, `n` is a prime power, or `n ≡ 2 mod 4` with `n / 2` a prime
power, and `indexRealUnits K = 2` otherwise. -/
theorem indexRealUnits_eq (n : ℕ) [NeZero n] (K : Type*) [Field K] [CharZero K]
    [IsCyclotomicExtension {n} ℚ K] :
    indexRealUnits K =
      if n = 1 ∨ IsPrimePow n ∨ (n % 4 = 2 ∧ IsPrimePow (n / 2)) then 1 else 2 := by
  by_cases hn4 : n % 4 = 2
  · have : NeZero (n / 2) := ⟨by omega⟩
    have : IsCyclotomicExtension {n / 2} ℚ K :=
      IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two hn4
    rw [indexRealUnits_eq_of_mod_four_ne_two (m := n / 2) (by omega) K]
    refine if_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ rfl rfl
    · rcases h with h1 | hpp
      · have hn2 : n = 2 := by omega
        exact Or.inr (Or.inl (hn2 ▸ Nat.prime_two.isPrimePow))
      · exact Or.inr (Or.inr ⟨hn4, hpp⟩)
    · rcases h with h1 | hpp | ⟨-, hpp⟩
      · omega
      · obtain ⟨p, a, hp, ha, hpa⟩ := hpp
        have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.nat_prime).mp
          (Nat.Prime.dvd_of_dvd_pow Nat.prime_two (by omega : 2 ∣ p ^ a))).symm
        subst hp2
        have ha1 : a = 1 := by
          by_contra ha1
          have : 4 ∣ 2 ^ a := pow_dvd_pow 2 (by omega : 2 ≤ a)
          omega
        subst ha1
        exact Or.inl (by omega)
      · exact Or.inr hpp
  · rw [indexRealUnits_eq_of_mod_four_ne_two hn4 K]
    refine if_congr ?_ rfl rfl
    simp [hn4]

end TauCeti.IsCyclotomicExtension.Rat
