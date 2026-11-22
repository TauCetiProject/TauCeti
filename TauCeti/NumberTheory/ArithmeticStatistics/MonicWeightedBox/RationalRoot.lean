/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticStatistics.MonicWeightedBox.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds

/-!
# Monic polynomials with a rational root

Among the monic integer polynomials `x^n + a₁ x^(n-1) + ⋯ + aₙ` with `|aᵢ| < X^i`, those with
a rational root number at most `3^n (n + 2) X^(D-n+1) log X` for every `X ≥ 2`, where
`D = n(n+1)/2` is the total weight of the box
(`TauCeti.ncard_monicWeightedBox_rat_root_le`). The box itself has about `2^n X^D`
elements, so a rational root saves a factor `X^(n-1)`, up to the logarithm. Polynomials with a
rational root are reducible, and this bound controls part of the reducible locus that is
discarded when monic polynomials are sieved by their discriminants.

By the rational root theorem a rational root is an integer `r` dividing the constant term
`aₙ`. If `aₙ = 0`, the polynomial is `x` times a polynomial of the degree `n - 1` box. Otherwise
`r ≠ 0`, and `aₙ₋₁` is determined by `a₁, …, aₙ₋₂`, by `aₙ` and by `r`. The pairs `(aₙ, r)`
number `O(X^n log X)` by the average order of the divisor function, which supplies the logarithm.

## References

* M. Bhargava, A. Shankar and X. Wang, *Squarefree values of polynomial discriminants I*,
  arXiv:1611.09806v3, Lemma 4.2.
-/

public section

open Polynomial

namespace TauCeti

/-- A monic integer polynomial with a rational root has zero constant term or a nonzero
integer root. -/
private theorem rat_root_subset (n : ℕ) (X : ℝ) :
    {f ∈ monicWeightedBox n X | ∃ r : ℚ, aeval r f = 0} ⊆
      {f ∈ monicWeightedBox n X | f.coeff 0 = 0} ∪
        {f ∈ monicWeightedBox n X | f.coeff 0 ≠ 0 ∧ ∃ z : ℤ, f.eval z = 0} := by
  rintro f ⟨hf, r, hr⟩
  by_cases h0 : f.coeff 0 = 0
  · exact Or.inl ⟨hf, h0⟩
  · obtain ⟨z, rfl, -⟩ :=
      exists_integer_of_is_root_of_monic (mem_monicWeightedBox.mp hf).1 hr
    refine Or.inr ⟨hf, h0, z, ?_⟩
    rw [aeval_algebraMap_apply_eq_algebraMap_eval] at hr
    exact (algebraMap ℤ ℚ).injective_int hr

/-- Dropping a zero constant term embeds these polynomials into the box of one degree less. -/
private theorem ncard_coeff_zero_eq_zero_le (n : ℕ) (X : ℝ) :
    {f ∈ monicWeightedBox (n + 1) X | f.coeff 0 = 0}.ncard ≤ (monicWeightedBox n X).ncard := by
  refine Set.ncard_le_ncard_of_injOn divX (fun f hf ↦ divX_mem_monicWeightedBox hf.1) ?_
    (finite_monicWeightedBox _ _)
  intro f hf g hg h
  rw [← divX_mul_X_add f, ← divX_mul_X_add g, hf.2, hg.2, h]

/-- A nonzero integer root `z`, the constant term `c` and the second quotient by `X` determine
a polynomial of the degree `n + 2` box, and `z ∣ c` with `0 < |c| < X^(n+2)`. -/
private theorem ncard_coeff_zero_ne_zero_root_le (n : ℕ) (X : ℝ) :
    {f ∈ monicWeightedBox (n + 2) X | f.coeff 0 ≠ 0 ∧ ∃ z : ℤ, f.eval z = 0}.ncard ≤
      (monicWeightedBox n X).ncard *
        {p : ℤ × ℤ | p.1 ≠ 0 ∧ |(p.1 : ℝ)| < X ^ (n + 2) ∧ p.2 ∣ p.1}.ncard := by
  classical
  set B := {f ∈ monicWeightedBox (n + 2) X | f.coeff 0 ≠ 0 ∧ ∃ z : ℤ, f.eval z = 0}
  set root : ℤ[X] → ℤ := fun f ↦ if h : ∃ z : ℤ, f.eval z = 0 then h.choose else 0
  have hroot {f : ℤ[X]} (hf : f ∈ B) : f.eval (root f) = 0 := by
    simp only [root]
    split_ifs with h
    exacts [h.choose_spec, absurd hf.2.2 h]
  have heval (f : ℤ[X]) (z : ℤ) :
      f.eval z = (f.divX.divX.eval z * z + f.coeff 1) * z + f.coeff 0 := by
    conv_lhs => rw [← divX_mul_X_add f, ← divX_mul_X_add f.divX]
    simp [coeff_divX]
  have hroot0 {f : ℤ[X]} (hf : f ∈ B) : root f ≠ 0 := by
    intro h
    have := hroot hf
    rw [h, ← coeff_zero_eq_eval_zero] at this
    exact hf.2.1 this
  rw [← Set.ncard_prod]
  refine Set.ncard_le_ncard_of_injOn (fun f ↦ (f.divX.divX, (f.coeff 0, root f)))
    (fun f hf ↦ ⟨divX_mem_monicWeightedBox (divX_mem_monicWeightedBox hf.1), hf.2.1,
      ?_, ?_⟩) ?_ ((finite_monicWeightedBox n X).prod (finite_setOf_dvd_of_abs_lt _))
  · simpa using (mem_monicWeightedBox.mp hf.1).2.2 0 (by omega)
  · have h := sub_dvd_eval_sub (root f) 0 f
    rwa [sub_zero, hroot hf, ← coeff_zero_eq_eval_zero, zero_sub, dvd_neg] at h
  · intro f hf g hg h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h2, h0, hz⟩ := h
    have hf' := hroot hf
    have hg' := hroot hg
    rw [heval] at hf' hg'
    rw [← h2, ← h0, ← hz] at hg'
    have h1 : f.coeff 1 = g.coeff 1 :=
      mul_right_cancel₀ (hroot0 hf) (by linear_combination hf' - hg')
    ext k
    rcases k with _ | _ | k
    · exact h0
    · exact h1
    · simpa [coeff_divX] using congrArg (fun p : ℤ[X] ↦ p.coeff k) h2

/-- In degree `n + 2`, splitting by the constant term bounds the polynomials with a rational root
by `3^(n+1) X^(T+n+1) + 4 · 3^n X^(T+n+2) (1 + (n + 2) log X)`, where `T = n(n+1)/2`. -/
private theorem ncard_rat_root_le_add (n : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ({f ∈ monicWeightedBox (n + 2) X | ∃ r : ℚ, aeval r f = 0}.ncard : ℝ) ≤
      3 ^ (n + 1) * X ^ (n * (n + 1) / 2 + (n + 1)) +
        4 * (3 ^ n * X ^ (n * (n + 1) / 2 + (n + 2))) * (1 + (n + 2) * Real.log X) := by
  have hcard := (Set.ncard_le_ncard (rat_root_subset (n + 2) X)
    ((finite_monicWeightedBox _ _).subset
      (Set.union_subset (Set.sep_subset _ _) (Set.sep_subset _ _)))).trans
    (Set.ncard_union_le _ _)
  have hA : ({f ∈ monicWeightedBox (n + 2) X | f.coeff 0 = 0}.ncard : ℝ) ≤
      3 ^ (n + 1) * X ^ (n * (n + 1) / 2 + (n + 1)) := by
    have hT : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
      rw [show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring,
        Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    rw [← hT]
    exact (Nat.cast_le.mpr (ncard_coeff_zero_eq_zero_le (n + 1) X)).trans
      (ncard_monicWeightedBox_le (n + 1) hX)
  have hB : ({f ∈ monicWeightedBox (n + 2) X | f.coeff 0 ≠ 0 ∧ ∃ z : ℤ, f.eval z = 0}.ncard :
      ℝ) ≤ 4 * (3 ^ n * X ^ (n * (n + 1) / 2 + (n + 2))) * (1 + (n + 2) * Real.log X) := by
    refine (Nat.cast_le.mpr (ncard_coeff_zero_ne_zero_root_le n X)).trans ?_
    push_cast
    refine (mul_le_mul (ncard_monicWeightedBox_le n hX)
      (ncard_setOf_dvd_of_abs_lt_le (one_le_pow₀ hX)) (by positivity) (by positivity)).trans_eq ?_
    rw [Real.log_pow, pow_add]
    push_cast
    ring
  have := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at this
  linarith

/-- **Monic rational root bound.** Among the monic integer polynomials
`x^n + a₁ x^(n-1) + ⋯ + aₙ` with `|aᵢ| < X^i`, at most `3^n (n + 2) X^(D-n+1) log X` have a
rational root, where `D = n(n+1)/2` and `X ≥ 2`. -/
theorem ncard_monicWeightedBox_rat_root_le (n : ℕ) {X : ℝ} (hX : 2 ≤ X) :
    ({f ∈ monicWeightedBox n X | ∃ r : ℚ, aeval r f = 0}.ncard : ℝ) ≤
      3 ^ n * (n + 2) * X ^ (n * (n + 1) / 2 - n + 1) * Real.log X := by
  have hX1 : 1 ≤ X := by linarith
  have hlog : 1 ≤ 2 * Real.log X := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have := Real.log_le_log (by norm_num) hX
    norm_num at *
    linarith
  have hL : 0 ≤ Real.log X := by linarith
  have hn2 : (2 : ℝ) ≤ n + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rcases lt_or_ge n 2 with hn | hn
  · -- In degree at most one, the whole box is small enough.
    have hexp : n * (n + 1) / 2 ≤ n * (n + 1) / 2 - n + 1 := by interval_cases n <;> simp
    calc ({f ∈ monicWeightedBox n X | ∃ r : ℚ, aeval r f = 0}.ncard : ℝ)
        ≤ (monicWeightedBox n X).ncard := by
          exact_mod_cast Set.ncard_le_ncard (Set.sep_subset _ _) (finite_monicWeightedBox n X)
      _ ≤ 3 ^ n * X ^ (n * (n + 1) / 2) := ncard_monicWeightedBox_le n hX1
      _ ≤ 3 ^ n * X ^ (n * (n + 1) / 2 - n + 1) := by gcongr
      _ ≤ 3 ^ n * X ^ (n * (n + 1) / 2 - n + 1) * ((n + 2) * Real.log X) :=
          le_mul_of_one_le_right (by positivity) (by nlinarith)
      _ = _ := by ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- With `T = m(m+1)/2`, the target weight `D - n + 1` is `T + m + 2`.
  have hT : (m + 2) * (m + 2 + 1) / 2 - (m + 2) + 1 = m * (m + 1) / 2 + (m + 2) := by
    rw [show (m + 2) * (m + 2 + 1) = m * (m + 1) + 2 * (2 * m + 3) by ring,
      Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    omega
  have h := ncard_rat_root_le_add m hX1
  rw [hT]
  set T := m * (m + 1) / 2
  have hk : 0 ≤ 3 ^ m * X ^ (T + (m + 2)) := by positivity
  have hA : 3 ^ (m + 1) * X ^ (T + (m + 1)) ≤ 3 * (3 ^ m * X ^ (T + (m + 2))) * (2 * Real.log X) :=
    calc 3 ^ (m + 1) * X ^ (T + (m + 1)) ≤ 3 * (3 ^ m * X ^ (T + (m + 2))) := by
          rw [pow_succ', mul_assoc]
          gcongr
          norm_num
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hlog
  push_cast at h ⊢
  rw [show (3 : ℝ) ^ (m + 2) = 9 * 3 ^ m by ring]
  nlinarith [mul_nonneg hk hL, mul_nonneg (mul_nonneg hk hL) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

end TauCeti
