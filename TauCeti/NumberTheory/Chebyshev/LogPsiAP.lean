/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.ResidueClass
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.SumPrimePow

/-!
# The logarithmic von Mangoldt sum in arithmetic progressions

The sum `logPsiAP q a x` weights each prime power in the class `a` up to and including `x`
by `Λ(n) / n`. Abel summation expresses it in terms of the unweighted progression sum
`psiAP q a`. This is the finite identity underlying Mertens' theorem in progressions.

For a positive modulus the non-unit classes together account for a bounded correction.
Each prime divisor `p` of the modulus contributes a term tending to `log p / (p - 1)`.

## References

* O. Ramaré, *Sur un théorème de Mertens*, Manuscripta Math. 108 (2002), Corollaire 1.
-/

public section

open Finset ArithmeticFunction Filter
open scoped Topology

namespace Chebyshev

/-- The logarithmic progression sum `∑_{n ≤ x, n ≡ a (mod q)} Λ(n)/n`. -/
noncomputable def logPsiAP (q : ℕ) (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊ with ((n : ℕ) : ZMod q) = a, Λ n / n

variable {q : ℕ} {a : ZMod q} {x : ℝ}

/-- The defining finite sum, with inclusive upper endpoint. -/
theorem logPsiAP_def (q : ℕ) (a : ZMod q) (x : ℝ) :
    logPsiAP q a x = ∑ n ∈ Ioc 0 ⌊x⌋₊ with ((n : ℕ) : ZMod q) = a, Λ n / n := (rfl)

/-- The same sum in terms of Mathlib's restriction of `Λ` to a residue class. -/
theorem logPsiAP_eq_sum_residueClass_div (q : ℕ) (a : ZMod q) (x : ℝ) :
    logPsiAP q a x = ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt.residueClass a n / n := by
  simp [logPsiAP_def, sum_filter, Set.indicator_apply, ite_div]

/-- The logarithmic sum in each class is nonnegative. -/
theorem logPsiAP_nonneg (q : ℕ) (a : ZMod q) (x : ℝ) : 0 ≤ logPsiAP q a x :=
  sum_nonneg fun n _ ↦ div_nonneg vonMangoldt_nonneg n.cast_nonneg

/-- Enlarging the cutoff can only increase the sum. -/
theorem logPsiAP_mono (q : ℕ) (a : ZMod q) : Monotone (logPsiAP q a) := fun _ _ h ↦
  sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Ioc_subset_Ioc_right (Nat.floor_mono h)))
    fun n _ _ ↦ div_nonneg vonMangoldt_nonneg n.cast_nonneg

/-- No prime power contributes below two. -/
theorem logPsiAP_eq_zero_of_lt_two (hx : x < 2) : logPsiAP q a x = 0 := by
  refine sum_eq_zero fun n hn ↦ ?_
  have hn' := mem_Ioc.mp (mem_filter.mp hn).1
  have h : ⌊x⌋₊ < 2 := (Nat.floor_lt' two_ne_zero).2 (by exact_mod_cast hx)
  obtain rfl : n = 1 := by omega
  simp

/-- Level one gives the unrestricted sum of `Λ(n)/n`. -/
@[simp]
theorem logPsiAP_one (a : ZMod 1) (x : ℝ) :
    logPsiAP 1 a x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n := by
  rw [logPsiAP_def, filter_true_of_mem fun _ _ ↦ Subsingleton.elim _ _]

/-- Summing over every class recovers the unrestricted logarithmic von Mangoldt sum. -/
theorem sum_logPsiAP [NeZero q] (x : ℝ) :
    ∑ a : ZMod q, logPsiAP q a x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n :=
  sum_fiberwise _ _ _

/-- Abel summation for the logarithmic progression sum. The oriented integral also gives the
identity below `1`, where the Chebyshev function vanishes. -/
theorem logPsiAP_eq_psiAP_div_add_integral (q : ℕ) (a : ZMod q) (x : ℝ) :
    logPsiAP q a x = psiAP q a x / x + ∫ t in (1 : ℝ)..x, psiAP q a t / t ^ 2 := by
  simp_rw [logPsiAP_eq_sum_residueClass_div, psiAP_eq_sum_residueClass,
    ← Icc_add_one_left_eq_Ioc, zero_add]
  have he : (-1 : ℝ) - 1 = -2 := by norm_num
  simpa [he, Real.rpow_neg_one, div_eq_mul_inv, mul_comm] using
    TauCeti.sum_Icc_rpow_mul_eq (vonMangoldt.residueClass a) (-1) x

/-- Character expansion of the logarithmic sum in a reduced residue class. -/
theorem logPsiAP_eq_sum_char [NeZero q] (ha : IsUnit a) (x : ℝ) :
    (logPsiAP q a x : ℂ) = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      χ a⁻¹ * ∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * Λ n / n := by
  rw [logPsiAP_eq_sum_residueClass_div]
  push_cast
  simp_rw [vonMangoldt.residueClass_apply ha, mul_div_assoc, sum_div]
  rw [← mul_sum, sum_comm]
  simp [mul_sum, mul_assoc, mul_div_assoc]

/-! ## The correction at the primes dividing the modulus -/

/-- The non-unit classes consist, on the support of `Λ`, of powers of the prime divisors
of the modulus. Each such prime contributes a finite geometric sum. -/
theorem sum_logPsiAP_not_isUnit [NeZero q] (x : ℝ) :
    ∑ a : ZMod q with ¬IsUnit a, logPsiAP q a x =
      ∑ p ∈ q.primeFactors, Real.log p / (p - 1) * (1 - (p : ℝ)⁻¹ ^ p.log ⌊x⌋₊) := by
  classical
  let f (n : ℕ) := if n.Coprime q then 0 else Λ n / n
  have hsum : ∑ a : ZMod q with ¬IsUnit a, logPsiAP q a x = ∑ n ∈ Icc 1 ⌊x⌋₊, f n := by
    simp_rw [logPsiAP_def]
    rw [sum_fiberwise_eq_sum_filter, sum_filter, ← Icc_add_one_left_eq_Ioc, zero_add]
    simp [f, ZMod.isUnit_iff_coprime]
  rw [hsum, Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (f := f)
    (fun n hn ↦ by simp [f, vonMangoldt_eq_zero_iff.2 hn])]
  have hterm (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
      f (p ^ k) = if p ∣ q then Real.log p * (p : ℝ)⁻¹ ^ k else 0 := by
    simp [f, Nat.coprime_pow_left_iff hk, hp.coprime_iff_not_dvd, vonMangoldt_apply_pow hk.ne',
      vonMangoldt_apply_prime hp, div_eq_mul_inv]
  calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, ∑ k ∈ Icc 1 (p.log ⌊x⌋₊), f (p ^ k)
      = ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (· ∣ q),
          ∑ k ∈ Icc 1 (p.log ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹ ^ k := by
        rw [sum_filter]
        refine sum_congr rfl fun p hp ↦ ?_
        rw [ite_sum_zero]
        exact sum_congr rfl fun k hk ↦ hterm p (Nat.prime_of_mem_primesLE hp) k (mem_Icc.mp hk).1
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ Icc 1 (p.log ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹ ^ k := by
      apply sum_subset
      · intro p hp
        obtain ⟨hp, hd⟩ := mem_filter.mp hp
        exact (Nat.prime_of_mem_primesLE hp).mem_primeFactors' hd
      · intro p hp hmem
        have hlt : ⌊x⌋₊ < p := by
          simpa [Nat.mem_primesLE, Nat.prime_of_mem_primeFactors hp,
            Nat.dvd_of_mem_primeFactors hp] using hmem
        simp [Nat.log_of_lt hlt]
    _ = _ := by
      refine sum_congr rfl fun p hp ↦ ?_
      have h : (1 : ℝ) < p := mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      rw [← mul_sum, ← Ico_add_one_right_eq_Icc,
        geom_sum_Ico' (inv_lt_one_of_one_lt₀ h).ne (by omega), pow_one, pow_succ]
      field_simp [(zero_lt_one.trans h).ne', sub_ne_zero.mpr h.ne', (inv_lt_one_of_one_lt₀ h).ne]

/-- The limiting correction from all the non-unit classes. It is exactly the prime-divisor
term in the principal character's contribution to the Mertens constant. -/
theorem tendsto_sum_logPsiAP_not_isUnit (q : ℕ) [NeZero q] :
    Tendsto (fun x ↦ ∑ a : ZMod q with ¬IsUnit a, logPsiAP q a x) atTop
      (𝓝 (∑ p ∈ q.primeFactors, Real.log p / (p - 1))) := by
  simp_rw [sum_logPsiAP_not_isUnit]
  refine tendsto_finsetSum _ fun p hp ↦ ?_
  have h : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
  have hlog : Tendsto (fun x : ℝ ↦ p.log ⌊x⌋₊) atTop atTop := by
    refine tendsto_atTop.2 fun k ↦ ?_
    filter_upwards [eventually_ge_atTop ((p ^ k : ℕ) : ℝ)] with x hx
    exact Nat.le_log_of_pow_le h (Nat.le_floor hx)
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ (p : ℝ)⁻¹)
    (inv_lt_one_of_one_lt₀ (mod_cast h))).comp hlog
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).const_mul (Real.log p / (p - 1))

/-- A non-unit class is bounded at every cutoff by the prime-divisor correction. -/
theorem logPsiAP_le_sum_primeFactors_of_not_isUnit [NeZero q] (ha : ¬IsUnit a) (x : ℝ) :
    logPsiAP q a x ≤ ∑ p ∈ q.primeFactors, Real.log p / (p - 1) := by
  classical
  calc logPsiAP q a x ≤ ∑ b : ZMod q with ¬IsUnit b, logPsiAP q b x :=
        single_le_sum (fun b _ ↦ logPsiAP_nonneg q b x) (by simpa using ha)
    _ ≤ _ := (Monotone.finsetSum fun b _ ↦ logPsiAP_mono q b).ge_of_tendsto
      (tendsto_sum_logPsiAP_not_isUnit q) x

/-- Subtracting the reduced-class main term in a non-unit class gives divergence to `-∞`. -/
theorem tendsto_logPsiAP_sub_log_div_atBot_of_not_isUnit [NeZero q] (ha : ¬IsUnit a) :
    Tendsto (fun x ↦ logPsiAP q a x - Real.log x / q.totient) atTop atBot := by
  refine tendsto_atBot.2 fun b ↦ ?_
  have hφ : 0 < (q.totient : ℝ) := mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  filter_upwards [(Real.tendsto_log_atTop.atTop_div_const hφ).eventually_ge_atTop
    ((∑ p ∈ q.primeFactors, Real.log p / (p - 1)) - b)] with x hx
  linarith [logPsiAP_le_sum_primeFactors_of_not_isUnit ha x]

end Chebyshev
