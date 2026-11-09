/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# Teichmüller coordinates of Witt vectors over a perfect ring

Let `R` be a perfect ring of characteristic `p`. Every Witt vector `x : 𝕎 R` is the `p`-adic sum
`x = ∑ₙ [xₙ] pⁿ` of Teichmüller representatives, where `xₙ` is the `p ^ n`-th root of the `n`-th
Witt coordinate of `x` (`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`). This file
names `xₙ` the `n`-th *Teichmüller coordinate* `x.teichmullerCoeff n` and records how it behaves:
it is determined by `x` modulo `p ^ (n + 1)`, it reads off the coefficients of a finite
Teichmüller sum, and multiplication by `[c]` multiplies every Teichmüller coordinate by `c`, while
multiplication by `p` shifts them. The coordinates determine `x`, so divisibility by `[c]` and
regularity of `[c]` can be read off coordinatewise. These coordinates are the input to the Gauss
valuations on `A_inf = W(𝒪_F)`.

## Main definitions

* `WittVector.teichmullerCoeff` : the Teichmüller coordinates of a Witt vector.

## Main results

* `WittVector.pow_dvd_sub_sum_teichmullerCoeff` : the Teichmüller expansion modulo `p ^ (n + 1)`.
* `WittVector.exists_eq_sum_teichmullerCoeff_add_pow_mul` : the splitting
  `x = ∑_{i < m} [xᵢ] pⁱ + pᵐ b` of the Teichmüller expansion.
* `WittVector.teichmullerCoeff_sum_teichmuller_mul_pow` : the Teichmüller coordinates of a finite
  Teichmüller sum `∑_{j ∈ s} [aⱼ] pʲ` are the `aᵢ` for `i ∈ s`, and vanish off `s`.
* `WittVector.teichmullerCoeff_eq_of_dvd_sub` : the first `n + 1` Teichmüller coordinates only
  depend on the residue modulo `p ^ (n + 1)`.
* `WittVector.teichmullerCoeff_teichmuller_mul` : `[c] x` has Teichmüller coordinates `c xₙ`.
* `WittVector.teichmullerCoeff_injective` : a Witt vector is determined by its Teichmüller
  coordinates.
* `WittVector.teichmullerCoeff_mul_natCast_pow_add` : `x pᵐ` has Teichmüller coordinates `xₙ` in
  position `n + m`, and `0` below `m` (`WittVector.teichmullerCoeff_mul_natCast_pow_of_lt`).
* `WittVector.teichmuller_dvd_iff` : `[c]` divides `x` iff `c` divides every `xₙ`; hence `[c]`
  divides `x pᵐ` only if it divides `x` (`WittVector.teichmuller_dvd_mul_natCast_pow_iff`).
* `WittVector.teichmuller_mem_nonZeroDivisors_iff` : `[c]` is a nonzerodivisor iff `c` is.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
-/

public section

namespace WittVector

open scoped nonZeroDivisors

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

local notation "𝕎" => WittVector p

variable (p) in
omit [CharP R p] [PerfectRing R p] in
/-- The Teichmüller representative `[a]` of `a ≠ 0` is nonzero, as its `0`-th coordinate is `a`. -/
theorem teichmuller_ne_zero {a : R} (ha : a ≠ 0) : teichmuller p a ≠ 0 := fun h ↦
  ha (by simpa using congrArg (coeff · 0) h)

/-- The `n`-th **Teichmüller coordinate** of a Witt vector `x` over a perfect ring of
characteristic `p`: the `p ^ n`-th root of the `n`-th Witt coordinate of `x`. These are the
coefficients of the Teichmüller expansion `x = ∑ₙ [xₙ] pⁿ`. -/
noncomputable def teichmullerCoeff (x : 𝕎 R) (n : ℕ) : R :=
  (iterateFrobeniusEquiv R p n).symm (x.coeff n)

/-- The `n`-th Teichmüller coordinate is a `p ^ n`-th root of the `n`-th Witt coordinate. -/
@[simp]
theorem teichmullerCoeff_pow (x : 𝕎 R) (n : ℕ) : x.teichmullerCoeff n ^ p ^ n = x.coeff n :=
  (iterateFrobeniusEquiv R p n).apply_symm_apply _

/-- The Teichmüller coordinate is characterised by its `p ^ n`-th power. -/
theorem teichmullerCoeff_eq_iff {x : 𝕎 R} {n : ℕ} {a : R} :
    x.teichmullerCoeff n = a ↔ x.coeff n = a ^ p ^ n := by
  rw [teichmullerCoeff, RingEquiv.symm_apply_eq, iterateFrobeniusEquiv_def]

/-- The `0`-th Teichmüller coordinate is the `0`-th Witt coordinate. -/
@[simp]
theorem teichmullerCoeff_zero (x : 𝕎 R) : x.teichmullerCoeff 0 = x.coeff 0 := by
  simp [teichmullerCoeff_eq_iff]

/-- The Teichmüller coordinates of `0` vanish. -/
@[simp]
theorem zero_teichmullerCoeff (n : ℕ) : (0 : 𝕎 R).teichmullerCoeff n = 0 := by
  simp [teichmullerCoeff]

/-- The Teichmüller coordinates of a finite Teichmüller sum `∑_{j ∈ s} [aⱼ] pʲ` are the `aᵢ` for
`i ∈ s`, and vanish off `s`. -/
@[simp]
theorem teichmullerCoeff_sum_teichmuller_mul_pow (a : ℕ → R) (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s, teichmuller p (a j) * (p : 𝕎 R) ^ j).teichmullerCoeff i =
      if i ∈ s then a i else 0 := by
  have hcoeff (j k : ℕ) : (teichmuller p (a j) * (p : 𝕎 R) ^ j).coeff k =
      if k = j then a j ^ p ^ j else 0 := by
    split_ifs with h
    · rw [h, teichmuller_mul_pow_coeff]
    · exact teichmuller_mul_pow_coeff_of_ne _ h
  rw [teichmullerCoeff_eq_iff, sum_coeff_eq_coeff_sum]
  · simp only [hcoeff, Finset.sum_ite_eq]
    split_ifs <;> simp [hp.out.ne_zero]
  · refine fun k ↦ ⟨fun ⟨j, _, hj⟩ ⟨l, _, hl⟩ ↦ Subtype.ext ?_⟩
    simp only [hcoeff, ne_eq, ite_eq_right_iff, not_forall] at hj hl
    exact hj.1.symm.trans hl.1

/-- The Teichmüller coordinates of `[a] p ^ m`: `a` in position `m` and `0` elsewhere. -/
theorem teichmullerCoeff_teichmuller_mul_pow (a : R) (m n : ℕ) :
    (teichmuller p a * (p : 𝕎 R) ^ m).teichmullerCoeff n = if n = m then a else 0 := by
  simpa using teichmullerCoeff_sum_teichmuller_mul_pow (fun _ ↦ a) {m} n

/-- The Teichmüller coordinates of `p ^ m`: `1` in position `m` and `0` elsewhere. -/
@[simp]
theorem teichmullerCoeff_natCast_pow (m n : ℕ) :
    ((p : 𝕎 R) ^ m).teichmullerCoeff n = if n = m then 1 else 0 := by
  simpa using teichmullerCoeff_teichmuller_mul_pow (p := p) (1 : R) m n

/-- The Teichmüller coordinates of `[a]`: `a` in position `0` and `0` elsewhere. -/
@[simp]
theorem teichmullerCoeff_teichmuller (a : R) (n : ℕ) :
    (teichmuller p a).teichmullerCoeff n = if n = 0 then a else 0 := by
  simpa using teichmullerCoeff_teichmuller_mul_pow (p := p) a 0 n

/-- The Teichmüller coordinates of a finite Teichmüller sum `∑_{j < n} [aⱼ] pʲ` are the `aᵢ` for
`i < n`, and vanish from `n` on. -/
theorem teichmullerCoeff_sum_range_teichmuller_mul_pow (a : ℕ → R) (n i : ℕ) :
    (∑ j ∈ Finset.range n, teichmuller p (a j) * (p : 𝕎 R) ^ j).teichmullerCoeff i =
      if i < n then a i else 0 := by
  simp

/-- **The Teichmüller expansion**: `x` is congruent to `∑_{i ≤ n} [xᵢ] pⁱ` modulo `p ^ (n + 1)`. -/
theorem pow_dvd_sub_sum_teichmullerCoeff (x : 𝕎 R) (n : ℕ) :
    (p : 𝕎 R) ^ (n + 1) ∣ x - ∑ i ≤ n, teichmuller p (x.teichmullerCoeff i) * (p : 𝕎 R) ^ i := by
  simpa [teichmullerCoeff, iterateFrobeniusEquiv_symm] using
    dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n

/-- Splitting the Teichmüller expansion of `x` after `m` terms: `x = ∑_{i < m} [xᵢ] pⁱ + pᵐ b`. -/
theorem exists_eq_sum_teichmullerCoeff_add_pow_mul (x : 𝕎 R) (m : ℕ) :
    ∃ b : 𝕎 R, x = ∑ i ∈ Finset.range m, teichmuller p (x.teichmullerCoeff i) * (p : 𝕎 R) ^ i +
      (p : 𝕎 R) ^ m * b := by
  cases m with
  | zero => exact ⟨x, by simp⟩
  | succ n =>
    obtain ⟨b, hb⟩ := pow_dvd_sub_sum_teichmullerCoeff x n
    exact ⟨b, by rw [Nat.range_succ_eq_Iic, ← hb, add_sub_cancel]⟩

/-- The first `n + 1` Teichmüller coordinates only depend on the residue modulo `p ^ (n + 1)`. -/
theorem teichmullerCoeff_eq_of_dvd_sub {x y : 𝕎 R} {n : ℕ} (h : (p : 𝕎 R) ^ (n + 1) ∣ x - y)
    {i : ℕ} (hi : i ≤ n) : x.teichmullerCoeff i = y.teichmullerCoeff i := by
  rw [← Ideal.mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero,
    ← le_coeff_eq_iff_le_sub_coeff_eq_zero] at h
  rw [teichmullerCoeff, h i (Nat.lt_succ_of_le hi), teichmullerCoeff]

/-- Multiplication by a Teichmüller representative `[c]` multiplies every Teichmüller coordinate
by `c`. -/
@[simp]
theorem teichmullerCoeff_teichmuller_mul (c : R) (x : 𝕎 R) (n : ℕ) :
    (teichmuller p c * x).teichmullerCoeff n = c * x.teichmullerCoeff n := by
  have h : (p : 𝕎 R) ^ (n + 1) ∣ teichmuller p c * x -
      ∑ i ≤ n, teichmuller p (c * x.teichmullerCoeff i) * (p : 𝕎 R) ^ i := by
    convert (pow_dvd_sub_sum_teichmullerCoeff x n).mul_left (teichmuller p c) using 1
    simp only [mul_sub, Finset.mul_sum, map_mul, mul_assoc]
  rw [teichmullerCoeff_eq_of_dvd_sub h le_rfl, teichmullerCoeff_sum_teichmuller_mul_pow]
  simp

/-- A Witt vector over a perfect ring is determined by its Teichmüller coordinates. -/
theorem teichmullerCoeff_injective : Function.Injective (teichmullerCoeff : 𝕎 R → ℕ → R) :=
  fun x y h ↦ ext fun n ↦ by rw [← teichmullerCoeff_pow, ← teichmullerCoeff_pow, congrFun h n]

/-- Multiplication by `p ^ m` shifts the Teichmüller coordinates up by `m`. -/
@[simp]
theorem teichmullerCoeff_mul_natCast_pow_add (x : 𝕎 R) (m n : ℕ) :
    (x * (p : 𝕎 R) ^ m).teichmullerCoeff (n + m) = x.teichmullerCoeff n := by
  rw [teichmullerCoeff_eq_iff, mul_pow_charP_coeff_succ, ← teichmullerCoeff_pow, ← pow_mul,
    ← pow_add]

/-- The first `m` Teichmüller coordinates of `x * p ^ m` vanish. -/
theorem teichmullerCoeff_mul_natCast_pow_of_lt (x : 𝕎 R) {m n : ℕ} (h : n < m) :
    (x * (p : 𝕎 R) ^ m).teichmullerCoeff n = 0 := by
  rw [teichmullerCoeff_eq_iff, mul_pow_charP_coeff_zero _ h,
    zero_pow (pow_ne_zero n hp.out.ne_zero)]

/-- The Teichmüller representative `[c]` divides `x` exactly when `c` divides every Teichmüller
coordinate of `x`. -/
theorem teichmuller_dvd_iff {c : R} {x : 𝕎 R} :
    teichmuller p c ∣ x ↔ ∀ n, c ∣ x.teichmullerCoeff n := by
  refine ⟨fun ⟨y, hy⟩ n ↦ ⟨y.teichmullerCoeff n, by rw [hy, teichmullerCoeff_teichmuller_mul]⟩,
    fun h ↦ ?_⟩
  choose y hy using h
  have hmk (n : ℕ) : (mk p fun n ↦ y n ^ p ^ n).teichmullerCoeff n = y n :=
    teichmullerCoeff_eq_iff.mpr (congrFun (coeff_mk p _) n)
  exact ⟨_, teichmullerCoeff_injective <| funext fun n ↦ by
    rw [teichmullerCoeff_teichmuller_mul, hmk, hy]⟩

/-- Over a perfect ring, `[c]` divides `x * p ^ m` only if it divides `x`: the factor `p ^ m`
merely shifts the Teichmüller coordinates. -/
@[simp]
theorem teichmuller_dvd_mul_natCast_pow_iff {c : R} {x : 𝕎 R} {m : ℕ} :
    teichmuller p c ∣ x * (p : 𝕎 R) ^ m ↔ teichmuller p c ∣ x :=
  ⟨fun h ↦ teichmuller_dvd_iff.mpr fun n ↦ by
    simpa using teichmuller_dvd_iff.mp h (n + m), (Dvd.dvd.mul_right · _)⟩

/-- The Teichmüller representative `[c]` is a nonzerodivisor of `𝕎 R` exactly when `c` is a
nonzerodivisor of `R`. -/
@[simp]
theorem teichmuller_mem_nonZeroDivisors_iff {c : R} :
    teichmuller p c ∈ (𝕎 R)⁰ ↔ c ∈ R⁰ := by
  simp only [mem_nonZeroDivisors_iff_left]
  refine ⟨fun h a ha ↦ ?_, fun h x hx ↦ teichmullerCoeff_injective <| funext fun n ↦ ?_⟩
  · simpa using congrArg (coeff · 0) (h (teichmuller p a) (by rw [← map_mul, ha, teichmuller_zero]))
  · rw [zero_teichmullerCoeff]
    exact h _ (by rw [← teichmullerCoeff_teichmuller_mul, hx, zero_teichmullerCoeff])

end WittVector
