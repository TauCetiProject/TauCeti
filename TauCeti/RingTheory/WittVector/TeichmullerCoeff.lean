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
Teichmüller sum, and multiplication by `[c]` multiplies every Teichmüller coordinate by `c`.
These coordinates are the input to the Gauss valuations on `A_inf = W(𝒪_F)`.

## Main definitions

* `WittVector.teichmullerCoeff` : the Teichmüller coordinates of a Witt vector.

## Main results

* `WittVector.pow_dvd_sub_sum_teichmullerCoeff` : the Teichmüller expansion modulo `p ^ (n + 1)`.
* `WittVector.teichmullerCoeff_sum_teichmuller_mul_pow` : the Teichmüller coordinates of a finite
  Teichmüller sum `∑_{j ≤ n} [aⱼ] pʲ` are the `aⱼ`.
* `WittVector.teichmullerCoeff_eq_of_dvd_sub` : the first `n + 1` Teichmüller coordinates only
  depend on the residue modulo `p ^ (n + 1)`.
* `WittVector.teichmullerCoeff_teichmuller_mul` : `[c] x` has Teichmüller coordinates `c xₙ`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
-/

public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

local notation "𝕎" => WittVector p

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
  simp [teichmullerCoeff_eq_iff, zero_pow (pow_ne_zero n hp.out.ne_zero)]

/-- The Teichmüller coordinates of `[a] p ^ m`: `a` in position `m` and `0` elsewhere. -/
theorem teichmullerCoeff_teichmuller_mul_pow (a : R) (m n : ℕ) :
    (teichmuller p a * (p : 𝕎 R) ^ m).teichmullerCoeff n = if n = m then a else 0 := by
  split_ifs with h
  · subst h
    rw [teichmullerCoeff_eq_iff, teichmuller_mul_pow_coeff]
  · rw [teichmullerCoeff_eq_iff, teichmuller_mul_pow_coeff_of_ne _ h,
      zero_pow (pow_ne_zero n hp.out.ne_zero)]

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

/-- The Teichmüller coordinates of a finite Teichmüller sum `∑_{j ≤ n} [aⱼ] pʲ` are the `aⱼ`. -/
theorem teichmullerCoeff_sum_teichmuller_mul_pow (a : ℕ → R) {i n : ℕ} (hi : i ≤ n) :
    (∑ j ≤ n, teichmuller p (a j) * (p : 𝕎 R) ^ j).teichmullerCoeff i = a i := by
  rw [teichmullerCoeff_eq_iff, sum_coeff_eq_coeff_sum, Finset.sum_eq_single_of_mem i
    (Finset.mem_Iic.mpr hi) fun j _ hj ↦ teichmuller_mul_pow_coeff_of_ne _ (Ne.symm hj),
    teichmuller_mul_pow_coeff]
  refine fun k ↦ ⟨fun ⟨j, _, hj⟩ ⟨l, _, hl⟩ ↦ Subtype.ext ?_⟩
  by_contra h
  exact (if hk : k = j then hl (teichmuller_mul_pow_coeff_of_ne _ (hk ▸ h)) else
    hj (teichmuller_mul_pow_coeff_of_ne _ hk))

/-- **The Teichmüller expansion**: `x` is congruent to `∑_{i ≤ n} [xᵢ] pⁱ` modulo `p ^ (n + 1)`. -/
theorem pow_dvd_sub_sum_teichmullerCoeff (x : 𝕎 R) (n : ℕ) :
    (p : 𝕎 R) ^ (n + 1) ∣ x - ∑ i ≤ n, teichmuller p (x.teichmullerCoeff i) * (p : 𝕎 R) ^ i := by
  simpa [teichmullerCoeff, iterateFrobeniusEquiv_symm] using
    dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n

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
  rw [teichmullerCoeff_eq_of_dvd_sub h le_rfl,
    teichmullerCoeff_sum_teichmuller_mul_pow (fun i ↦ c * x.teichmullerCoeff i) le_rfl]

end WittVector
