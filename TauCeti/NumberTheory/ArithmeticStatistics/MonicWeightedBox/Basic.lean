/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.Polynomial.Card.BoundedCoeff
import TauCeti.Data.Int.Interval

/-!
# Monic integer polynomials in a weighted coefficient box

For a degree `n` and a real cutoff `X`, `TauCeti.monicWeightedBox n X` is the set of monic
integer polynomials `x^n + a₁ x^(n-1) + ⋯ + aₙ` of degree `n` with `|aᵢ| < X^i` for every `i`.
Giving the coefficient `aᵢ` weight `i` makes the discriminant of a monic polynomial weighted
homogeneous of weight `n(n-1)`, so this box is the natural height ball over which monic
polynomials with local or Galois conditions are counted. Indexed by the power of `x`, the
coefficient of `x^i` is bounded by `X^(n-i)`; `TauCeti.mem_monicWeightedBox_iff_descending`
lists the coefficients from `x^(n-1)` down instead.

Removing the constant term, `Polynomial.divX` maps the degree `n + 1` box into the degree `n`
box. The box lies in the coefficient box of `TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_pi`,
so it is finite, with at most `3^n X^(n(n+1)/2)` elements once `X ≥ 1`.
-/

public section

open Polynomial

namespace TauCeti

/-- The monic integer polynomials of degree `n` whose coefficient of `x^i` has absolute value
less than `X^(n-i)`, for every `i < n`. -/
def monicWeightedBox (n : ℕ) (X : ℝ) : Set ℤ[X] :=
  {f | f.Monic ∧ f.natDegree = n ∧ ∀ i < n, |(f.coeff i : ℝ)| < X ^ (n - i)}

@[simp]
theorem mem_monicWeightedBox {n : ℕ} {X : ℝ} {f : ℤ[X]} :
    f ∈ monicWeightedBox n X ↔
      f.Monic ∧ f.natDegree = n ∧ ∀ i < n, |(f.coeff i : ℝ)| < X ^ (n - i) :=
  Iff.rfl

/-- Membership in the weighted box with the coefficients listed from `x^(n-1)` down, as
`x^n + a₁ x^(n-1) + ⋯ + aₙ` with `|aᵢ| < X^i`: the coefficient of `x^(n-1-i)` has absolute value
less than `X^(i+1)` for every `i < n`. -/
theorem mem_monicWeightedBox_iff_descending {n : ℕ} {X : ℝ} {f : ℤ[X]} :
    f ∈ monicWeightedBox n X ↔
      f.Monic ∧ f.natDegree = n ∧ ∀ i : Fin n, |(f.coeff (n - 1 - i) : ℝ)| < X ^ ((i : ℕ) + 1) := by
  refine mem_monicWeightedBox.trans (and_congr_right' (and_congr_right' ⟨fun h i ↦ ?_,
    fun h i hi ↦ ?_⟩))
  · have := h (n - 1 - i) (by omega)
    rwa [show n - (n - 1 - i) = i + 1 by omega] at this
  · have := h ⟨n - 1 - i, by omega⟩
    rwa [show n - 1 - (n - 1 - i) = i by omega, show n - 1 - i + 1 = n - i by omega] at this

/-- The only monic polynomial of degree zero is `1`. -/
@[simp]
theorem monicWeightedBox_zero (X : ℝ) : monicWeightedBox 0 X = {1} := by
  ext f
  simp only [mem_monicWeightedBox, Nat.not_lt_zero, false_imp_iff, imp_true_iff, and_true,
    Set.mem_singleton_iff]
  exact ⟨fun ⟨hf, hd⟩ ↦ hf.natDegree_eq_zero.mp hd,
    fun h ↦ h ▸ ⟨monic_one, natDegree_one⟩⟩

/-- Dropping the constant term maps the degree `n + 1` box into the degree `n` box. -/
theorem divX_mem_monicWeightedBox {n : ℕ} {X : ℝ} {f : ℤ[X]}
    (hf : f ∈ monicWeightedBox (n + 1) X) : f.divX ∈ monicWeightedBox n X := by
  obtain ⟨hm, hd, hc⟩ := mem_monicWeightedBox.mp hf
  have hdeg : f.divX.natDegree = n := by
    rw [natDegree_divX_eq_natDegree_tsub_one, hd, Nat.add_sub_cancel]
  refine ⟨?_, hdeg, fun i hi ↦ ?_⟩
  · rw [Monic.def, ← coeff_natDegree, hdeg, coeff_divX, ← hd]
    exact hm.coeff_natDegree
  · rw [coeff_divX]
    simpa using hc (i + 1) (by omega)

/-- The allowed values of the coefficient of `x^i` in the degree `n` box: the integers in
`(-⌈X^(n-i)⌉, ⌈X^(n-i)⌉)` for `i < n`, and `1` for the leading coefficient. -/
private noncomputable def coeffBox (n : ℕ) (X : ℝ) (i : Fin (n + 1)) : Finset ℤ :=
  if (i : ℕ) < n then Finset.Ioo (-⌈X ^ (n - i)⌉) ⌈X ^ (n - i)⌉ else {1}

/-- The weighted box lies among the polynomials of degree at most `n` whose coefficient of `x^i`
lies in `coeffBox n X i`, the family counted by
`TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_pi`. -/
private theorem monicWeightedBox_subset (n : ℕ) (X : ℝ) :
    monicWeightedBox n X ⊆
      {f : ℤ[X] | f.natDegree ≤ n ∧ ∀ i : Fin (n + 1), f.coeff i ∈ coeffBox n X i} := by
  rintro f ⟨hm, hd, hc⟩
  refine ⟨hd.le, fun i ↦ ?_⟩
  rw [coeffBox]
  split_ifs with hi
  · rw [← Finset.mem_coe, ← setOf_abs_intCast_lt_eq_Ioo]
    exact hc i hi
  · rw [Finset.mem_singleton, show (i : ℕ) = n by omega, ← hd]
    exact hm.coeff_natDegree

/-- The weighted box is finite. -/
theorem finite_monicWeightedBox (n : ℕ) (X : ℝ) : (monicWeightedBox n X).Finite :=
  (TauCeti.Polynomial.finite_setOf_natDegree_le_coeff_mem_pi n
    fun i ↦ (coeffBox n X i).finite_toSet).subset (monicWeightedBox_subset n X)

/-- For `X ≥ 1`, the degree `n` weighted box has at most `3^n X^(n(n+1)/2)` elements. -/
theorem ncard_monicWeightedBox_le (n : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((monicWeightedBox n X).ncard : ℝ) ≤ 3 ^ n * X ^ (n * (n + 1) / 2) := by
  have hcard (i : Fin n) : ((coeffBox n X i.castSucc).card : ℝ) ≤ 3 * X ^ (n - i) := by
    simp only [coeffBox, Fin.val_castSucc, i.isLt, ↓reduceIte]
    rw [← Set.ncard_coe_finset, ← setOf_abs_intCast_lt_eq_Ioo]
    exact ncard_setOf_abs_intCast_lt_le (one_le_pow₀ hX)
  calc ((monicWeightedBox n X).ncard : ℝ)
      ≤ (∏ i, (coeffBox n X i).card : ℕ) := by
        exact_mod_cast (Set.ncard_le_ncard (monicWeightedBox_subset n X)
          (TauCeti.Polynomial.finite_setOf_natDegree_le_coeff_mem_pi n
            fun i ↦ (coeffBox n X i).finite_toSet)).trans_eq
          (TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_pi n _)
    _ = ∏ i : Fin n, ((coeffBox n X i.castSucc).card : ℝ) := by
        rw [Nat.cast_prod, Fin.prod_univ_castSucc]
        simp [coeffBox]
    _ ≤ ∏ i : Fin n, (3 * X ^ (n - (i : ℕ))) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ hcard i
    _ = 3 ^ n * X ^ (n * (n + 1) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (n - ·), Finset.sum_range_sub_id]

end TauCeti
