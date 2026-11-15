/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import TauCeti.Analysis.Polynomial.SupNorm.Basic
public import TauCeti.Data.Nat.Choose.Central

/-!
# The Gelfond bound for polynomial factors

For complex polynomials with product of degree `d`, the product of the coefficient
sup norms is at most `2 ^ d` times the sup norm of the product. The same bound passes
along any norm-preserving ring homomorphism into `ℂ`, such as `ℤ →+* ℂ` or `ℝ →+* ℂ`.
Over `ℤ`, every nonzero factor has coefficient sup norm at least `1`, so any divisor of a
nonzero integer polynomial `q` has sup norm at most `2 ^ q.natDegree * q.supNorm`
(`Polynomial.supNorm_le_two_pow_mul_supNorm_of_dvd`). Together with the reverse bound in
`SupNorm.Basic`, this controls coefficient heights under factorization. Zero factors and
empty products are included.

The Gelfond bound combines Mathlib's coefficient-to-Mahler and Landau estimates
with supermultiplicativity and the square-root bound for middle binomial coefficients.

## References

* Xiaorun Wu, *Diophantine geometry, week 08: arithmetic heights* (2023), Lemmas 3.5–3.6.
* Lukas Pottmeyer, *Diophantine Approximation* (2022), Lemma 3.2.10.
* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Lemma A.3.
-/

public section

namespace Polynomial

/-- The Gelfond factor bound: the product of the coefficient sup norms of complex
polynomials is at most `2^d` times the sup norm of their degree-`d` product. -/
theorem prod_supNorm_le_two_pow_mul_supNorm_prod
    {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    ∏ i ∈ s, (f i).supNorm ≤
      2 ^ (∏ i ∈ s, f i).natDegree * (∏ i ∈ s, f i).supNorm := by
  classical
  by_cases hz : ∃ i ∈ s, f i = 0
  · obtain ⟨i, hi, hzero⟩ := hz
    have hp : ∏ i ∈ s, f i = 0 := Finset.prod_eq_zero hi hzero
    have hn : ∏ i ∈ s, (f i).supNorm = 0 :=
      Finset.prod_eq_zero hi (by simp [hzero])
    simp [hp, hn]
  · have hne : ∀ i ∈ s, f i ≠ 0 := by simpa using hz
    have hdegree := Polynomial.natDegree_prod s f hne
    have hmahler : (∏ i ∈ s, f i).mahlerMeasure = ∏ i ∈ s, (f i).mahlerMeasure := by
      simpa only [Finset.prod, Multiset.map_map, Function.comp_def] using
        Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod (s.val.map f)
    calc
      ∏ i ∈ s, (f i).supNorm ≤
          ∏ i ∈ s, ((f i).natDegree.choose ((f i).natDegree / 2) : ℝ) *
            (f i).mahlerMeasure := by
        exact Finset.prod_le_prod₀ (fun i _ ↦ (f i).supNorm_nonneg)
          (fun i _ ↦ (f i).supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure)
      _ = (∏ i ∈ s, ((f i).natDegree.choose ((f i).natDegree / 2) : ℝ)) *
          (∏ i ∈ s, f i).mahlerMeasure := by rw [Finset.prod_mul_distrib, hmahler]
      _ ≤ ((∏ i ∈ s, f i).natDegree.choose ((∏ i ∈ s, f i).natDegree / 2) : ℝ) *
          (∏ i ∈ s, f i).mahlerMeasure := by
        refine mul_le_mul_of_nonneg_right ?_ (Polynomial.mahlerMeasure_nonneg _)
        rw [hdegree]
        exact_mod_cast Nat.prod_choose_middle_le_choose_sum_middle s (fun i ↦ (f i).natDegree)
      _ ≤ ((∏ i ∈ s, f i).natDegree.choose ((∏ i ∈ s, f i).natDegree / 2) : ℝ) *
          (Real.sqrt ((∏ i ∈ s, f i).natDegree + 1) * (∏ i ∈ s, f i).supNorm) := by
        exact mul_le_mul_of_nonneg_left
          (Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _) (Nat.cast_nonneg _)
      _ ≤ 2 ^ (∏ i ∈ s, f i).natDegree * (∏ i ∈ s, f i).supNorm := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (Nat.choose_middle_mul_sqrt_le_two_pow _)
          (Polynomial.supNorm_nonneg _)

/-- The Gelfond factor bound over any seminormed commutative ring admitting a norm-preserving
ring homomorphism into `ℂ` (such as `ℤ` or `ℝ`). -/
theorem prod_supNorm_le_two_pow_mul_supNorm_prod_of_ringHomIsometric
    {R ι : Type*} [SeminormedCommRing R] (φ : R →+* ℂ) [RingHomIsometric φ]
    (s : Finset ι) (f : ι → R[X]) :
    ∏ i ∈ s, (f i).supNorm ≤
      2 ^ (∏ i ∈ s, f i).natDegree * (∏ i ∈ s, f i).supNorm := by
  calc ∏ i ∈ s, (f i).supNorm
      = ∏ i ∈ s, ((f i).map φ).supNorm := by simp
    _ ≤ 2 ^ (∏ i ∈ s, (f i).map φ).natDegree * (∏ i ∈ s, (f i).map φ).supNorm :=
        prod_supNorm_le_two_pow_mul_supNorm_prod s (fun i ↦ (f i).map φ)
    _ = 2 ^ ((∏ i ∈ s, f i).map φ).natDegree * (∏ i ∈ s, f i).supNorm := by
        rw [← Polynomial.map_prod, supNorm_map]
    _ ≤ 2 ^ (∏ i ∈ s, f i).natDegree * (∏ i ∈ s, f i).supNorm :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two natDegree_map_le)
          (supNorm_nonneg _)

/-- Binary Gelfond bound for complex polynomials: `‖p‖∞ ‖q‖∞ ≤ 2 ^ deg(p q) ‖p q‖∞`. -/
theorem mul_supNorm_le_two_pow_mul_supNorm_mul (p q : ℂ[X]) :
    p.supNorm * q.supNorm ≤ 2 ^ (p * q).natDegree * (p * q).supNorm := by
  simpa [Fin.prod_univ_two] using prod_supNorm_le_two_pow_mul_supNorm_prod Finset.univ ![p, q]

/-- Binary Gelfond bound over any seminormed commutative ring admitting a norm-preserving ring
homomorphism into `ℂ` (such as `ℤ` or `ℝ` via `Int.castRingHom ℂ` or `Complex.ofRealHom`). -/
theorem mul_supNorm_le_two_pow_mul_supNorm_mul_of_ringHomIsometric
    {R : Type*} [SeminormedCommRing R] (φ : R →+* ℂ) [RingHomIsometric φ] (p q : R[X]) :
    p.supNorm * q.supNorm ≤ 2 ^ (p * q).natDegree * (p * q).supNorm := by
  simpa [Fin.prod_univ_two] using
    prod_supNorm_le_two_pow_mul_supNorm_prod_of_ringHomIsometric φ Finset.univ ![p, q]

/-- Every divisor `p` of a nonzero integer polynomial `q` has coefficient sup norm at most
`2 ^ q.natDegree * q.supNorm`. -/
theorem supNorm_le_two_pow_mul_supNorm_of_dvd {p q : ℤ[X]} (hdvd : p ∣ q) (hq : q ≠ 0) :
    p.supNorm ≤ 2 ^ q.natDegree * q.supNorm := by
  obtain ⟨r, rfl⟩ := hdvd
  have hr : r ≠ 0 := right_ne_zero_of_mul hq
  calc p.supNorm = p.supNorm * 1 := (mul_one _).symm
    _ ≤ p.supNorm * r.supNorm :=
        mul_le_mul_of_nonneg_left (one_le_supNorm_of_ne_zero hr) p.supNorm_nonneg
    _ ≤ 2 ^ (p * r).natDegree * (p * r).supNorm :=
        mul_supNorm_le_two_pow_mul_supNorm_mul_of_ringHomIsometric (Int.castRingHom ℂ) p r

/- The exponential factor `2 ^ d` in Gelfond's bound cannot be replaced by `1`: the product
`(2 X + 1) (X - 2) = 2 X ^ 2 - 3 X - 2` has sup norm `3`, while its factors both have sup norm `2`
and `2 * 2 > 3`. -/
example : ((2 * X + 1) * (X - 2) : ℤ[X]).supNorm = 3 ∧ (2 * X + 1 : ℤ[X]).supNorm = 2 ∧
    (X - 2 : ℤ[X]).supNorm = 2 := by
  have hsup {p : ℤ[X]} {B : ℝ} (hle : ∀ i, ‖p.coeff i‖ ≤ B)
      (heq : ∃ i, ‖p.coeff i‖ = B) : p.supNorm = B := by
    obtain ⟨j, hj⟩ := p.exists_eq_supNorm
    obtain ⟨i, hi⟩ := heq
    exact le_antisymm (hj ▸ hle j) (hi ▸ p.le_supNorm i)
  have hprod : ((2 * X + 1) * (X - 2) : ℤ[X]) = 2 * X ^ 2 - 3 * X - 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hprod]
    refine hsup (fun i ↦ ?_) ⟨1, ?_⟩
    · simp only [← map_ofNat C, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
        Int.norm_eq_abs]
      split_ifs <;> norm_num; omega
    · simp only [← map_ofNat C, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
        Int.norm_eq_abs]
      norm_num
  · refine hsup (fun i ↦ ?_) ⟨1, ?_⟩
    · simp only [← C_1, ← map_ofNat C, coeff_add, coeff_C_mul, coeff_X, coeff_C, Int.norm_eq_abs]
      split_ifs <;> norm_num; omega
    · simp only [← C_1, ← map_ofNat C, coeff_add, coeff_C_mul, coeff_X, coeff_C, Int.norm_eq_abs]
      norm_num
  · refine hsup (fun i ↦ ?_) ⟨0, ?_⟩
    · simp only [← map_ofNat C, coeff_sub, coeff_X, coeff_C, Int.norm_eq_abs]
      split_ifs <;> norm_num
    · simp only [← map_ofNat C, coeff_sub, coeff_X, coeff_C, Int.norm_eq_abs]
      norm_num

end Polynomial
