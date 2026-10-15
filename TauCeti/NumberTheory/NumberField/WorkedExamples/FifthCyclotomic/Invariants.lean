/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.IntrinsicLabel
public import TauCeti.NumberTheory.NumberField.Monogenic
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# Invariants of `ℚ(ζ₅)`

For a fifth cyclotomic field `K`, that is `[IsCyclotomicExtension {5} ℚ K]`:

* the degree is `φ(5) = 4`, the discriminant is `(−1)^2 · 5^3 = 125`, and there are no real
  places, so the signature is `(0, 2)` and the intrinsic label prefix is `4.0.125`;
* the ring of integers is `ℤ[ζ₅]`, a principal ideal domain: `K` is monogenic and its class
  number is `1`;
* the unit group has rank `1` and torsion of order `10`;
* `5` is totally ramified: the prime `𝔭 = (ζ₅ − 1)` is the only prime of `𝓞 K` above `5`,
  with `e = 4`, `f = 1` and `5 𝓞 K = 𝔭⁴`.

Every value is read off Mathlib's general theory of cyclotomic fields at `n = 5`; the splitting
of the small unramified primes is in `TauCeti.NumberTheory.NumberField.Cyclotomic.FiveSplitting`
and the subfield lattice in `TauCeti.NumberTheory.NumberField.Cyclotomic.Subfields`.

## Main results

* `TauCeti.NumberField.FifthCyclotomic.finrank_eq_four`, `discr_eq_one_hundred_twenty_five`,
  `nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_two`: degree `4`, discriminant `125`, signature
  `(0, 2)`; `hasLMFDBIntrinsicLabel`: the intrinsic label prefix is `4.0.125`.
* `TauCeti.NumberField.FifthCyclotomic.isMonogenic`, `classNumber_eq_one`: `𝓞 K = ℤ[ζ₅]` is a
  principal ideal domain.
* `TauCeti.NumberField.FifthCyclotomic.units_rank_eq_one`, `torsionOrder_eq_ten`: the unit
  group has rank `1` and torsion of order `10`.
* `TauCeti.NumberField.FifthCyclotomic.five_mem_ramifiedPrimes`, `ncard_primesOver_five_eq_one`,
  `eq_span_zeta_sub_one`, `ramificationIdx_eq_four`, `inertiaDeg_eq_one`,
  `map_span_five_eq_pow_four`: `5` is totally ramified through `(ζ₅ − 1)⁴`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapters 1 and 2.
-/

public section

open Ideal NumberField NumberField.InfinitePlace NumberField.Units TauCeti.NumberField
open scoped NumberField

namespace TauCeti.NumberField.FifthCyclotomic

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

/-- The degree of a fifth cyclotomic field is `φ(5) = 4`. -/
@[simp] theorem finrank_eq_four : Module.finrank ℚ K = 4 := by
  rw [IsCyclotomicExtension.Rat.finrank 5 K, Nat.totient_prime Nat.prime_five]

/-- The discriminant of a fifth cyclotomic field is `(−1)^2 · 5^3 = 125`. -/
@[simp] theorem discr_eq_one_hundred_twenty_five : discr K = 125 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [IsCyclotomicExtension.Rat.discr_prime 5 K]
  norm_num

/-- A fifth cyclotomic field has no real place. -/
@[simp] theorem nrRealPlaces_eq_zero : nrRealPlaces K = 0 :=
  IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 5) K (by norm_num)

/-- A fifth cyclotomic field is totally complex. -/
theorem isTotallyComplex : IsTotallyComplex K :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 5) K (by norm_num)

/-- A fifth cyclotomic field has two complex places: `φ(5) / 2 = 2`. -/
@[simp] theorem nrComplexPlaces_eq_two : nrComplexPlaces K = 2 := by
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 5 K,
    Nat.totient_prime Nat.prime_five]

/-- The intrinsic label prefix is `4.0.125`. -/
theorem hasLMFDBIntrinsicLabel : HasLMFDBIntrinsicLabel K 4 0 125 := by
  rw [hasLMFDBIntrinsicLabel_iff, discr_eq_one_hundred_twenty_five K]
  exact ⟨finrank_eq_four K, nrRealPlaces_eq_zero K, rfl⟩

/-- A fifth cyclotomic field is monogenic: `𝓞 K = ℤ[ζ₅]`. -/
theorem isMonogenic : IsMonogenic K :=
  isMonogenic_of_isCyclotomicExtension 5

/-- The class number of a fifth cyclotomic field is `1`: `ℤ[ζ₅]` is a principal ideal domain. -/
@[simp] theorem classNumber_eq_one : classNumber K = 1 :=
  classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.five_pid K)

/-- The unit group of a fifth cyclotomic field has rank `r₁ + r₂ − 1 = 1`. -/
@[simp] theorem units_rank_eq_one : Units.rank K = 1 := by
  rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_zero K,
    nrComplexPlaces_eq_two K]

/-- The torsion subgroup of the unit group of a fifth cyclotomic field has order `10`: `5` is
odd, so the field contains `2 · 5` roots of unity. -/
@[simp] theorem torsionOrder_eq_ten : torsionOrder K = 10 := by
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 5)]
  decide

/-- `5` ramifies in a fifth cyclotomic field: it divides the discriminant `125`. -/
theorem five_mem_ramifiedPrimes : 5 ∈ ramifiedPrimes K := by
  rw [mem_ramifiedPrimes_iff_dvd_discr Nat.prime_five, discr_eq_one_hundred_twenty_five K]
  norm_num

/-- There is a single prime of `𝓞 K` above `5`. -/
@[simp] theorem ncard_primesOver_five_eq_one : (primesOver (span {(5 : ℤ)}) (𝓞 K)).ncard = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 5 K

variable {K} (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] [𝔭.LiesOver (span {(5 : ℤ)})]

/-- The prime of `𝓞 K` above `5` is `(ζ₅ − 1)`, for any primitive fifth root of unity `ζ₅`. -/
theorem eq_span_zeta_sub_one {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    𝔭 = span {hζ.toInteger - 1} := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' 5 K hζ 𝔭

/-- The prime above `5` has ramification index `φ(5) = 4`. -/
@[simp] theorem ramificationIdx_eq_four : 𝔭.ramificationIdx ℤ = 4 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime 5 K 𝔭

/-- The prime above `5` has residue degree `1`. -/
@[simp] theorem inertiaDeg_eq_one : 𝔭.inertiaDeg ℤ = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime 5 K 𝔭

/-- `5` is totally ramified: `5 𝓞 K = 𝔭⁴`. -/
theorem map_span_five_eq_pow_four :
    (span {(5 : ℤ)}).map (algebraMap ℤ (𝓞 K)) = 𝔭 ^ 4 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  -- the canonical primitive fifth root of unity of the cyclotomic extension
  have hzeta := IsCyclotomicExtension.zeta_spec 5 ℚ K
  have hK : IsCyclotomicExtension {5 ^ (0 + 1)} ℚ K := by
    rw [zero_add, pow_one]
    infer_instance
  have hzeta' : IsPrimitiveRoot (IsCyclotomicExtension.zeta 5 ℚ K) (5 ^ (0 + 1)) := by
    rw [zero_add, pow_one]
    exact hzeta
  have h := IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow 5 0 hzeta'
  rw [Nat.cast_ofNat] at h
  rw [eq_span_zeta_sub_one 𝔭 hzeta, h, finrank_eq_four K]

end TauCeti.NumberField.FifthCyclotomic
