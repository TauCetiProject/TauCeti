/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticStatistics.FormDensity.LocalDensity
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import TauCeti.Data.Nat.Choose.Bounds
import TauCeti.Data.ZMod.LocalRing
import TauCeti.RingTheory.LocalRing.Card

/-!
# The first moment of local densities

Let `R` be a finite local ring whose residue field has `q` elements, such as `ℤ/pʳ` with `q = p`.
For a form `f_a` of degree `d` in `n + 1` variables with primitive coefficient vector `a`, the local
density `σ(a; R)` counts the primitive zeros of `f_a`, normalized by `(#R)ⁿ`. This file computes
its average over all primitive coefficient vectors exactly: with `N = binom(n + d, d)` monomials,

`(1 / #R_N) ∑_{a ∈ R_N} σ(a; R) = (1 - q^{-(n+1)}) (1 - q^{-(N-1)}) / (1 - q^{-N})`.

The proof swaps the two sums. By the coefficient evaluation identity `f_a(b) = a ⬝ᵥ ν(b)`, the
coefficient vectors vanishing at a primitive point `b` are those orthogonal to its Veronese vector
`ν(b)`, which is again primitive (`FormDensity.isUnimodular_veronese`). Over a local ring the
number of primitive vectors orthogonal to a fixed primitive vector does not depend on it
(`FormDensity.card_primitiveVectors_filter_dotProduct_eq_zero`), so every point `b` contributes
the same count.

## Main results

* `FormDensity.sum_card_primitiveZeros`: the total number of primitive zeros of all primitive
  forms.
* `FormDensity.sum_localDensity_div_card_primitiveVectors`: the exact first moment over a finite
  local ring, and `FormDensity.sum_localDensity_div_card_primitiveVectors_zmod_prime_pow` modulo
  `pʳ`.
* `FormDensity.sum_localDensity_div_card_primitiveVectors_le_one`: the first moment is at most one;
* `FormDensity.one_sub_two_mul_le_sum_localDensity_div_card_primitiveVectors`: for `d ≥ 2` and
  `n ≥ 1` it is at least `1 - 2 q^{-(n+1)}`.

## References

* T. Browning, P. Le Boudec, W. Sawin, *The Hasse principle for random Fano hypersurfaces*,
  arXiv:2006.02356v1, §5.2, Lemma 5.4 and its proof.
-/

public section

open Finset MvPolynomial IsLocalRing

open scoped Matrix

namespace TauCeti.FormDensity

section FirstMoment

variable {R : Type*} [CommRing R] [IsLocalRing R] [Fintype R] {d n : ℕ}

/-- **Counting the primitive zeros of all primitive forms.** Over a finite local ring, the primitive
forms of degree `d` in `n + 1` variables have together `#R_{n+1} · (#R^{N-1} - #𝔪^{N-1})` primitive
zeros, where `R_{n+1}` is the set of primitive points and `N = binom(n + d, d)`: each primitive
point is a zero of the same number of primitive forms. -/
theorem sum_card_primitiveZeros :
    ∑ a ∈ primitiveVectors (Monomials (Fin (n + 1)) d) R, #(primitiveZeros a) =
      #(primitiveVectors (Fin (n + 1)) R) *
        (Nat.card R ^ ((n + d).choose d - 1) -
          Nat.card (maximalIdeal R) ^ ((n + d).choose d - 1)) := by
  classical
  have hzeros (a : Monomials (Fin (n + 1)) d → R) :
      primitiveZeros a = (primitiveVectors (Fin (n + 1)) R).bipartiteAbove
        (fun a b ↦ a ⬝ᵥ veronese b = 0) a := by
    ext b
    simp [bipartiteAbove, eval_form]
  simp_rw [hzeros]
  rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  refine sum_const_nat fun b hb ↦ ?_
  rw [bipartiteBelow, card_primitiveVectors_filter_dotProduct_eq_zero
    (isUnimodular_veronese (mem_primitiveVectors.mp hb)), Fintype.card_coe, card_monomials_fin]

/-- Over a finite local ring with residue field of size `q`, there are `#Rᵐ (1 - q⁻ᵐ)` primitive
vectors of length `m`. -/
private theorem card_primitiveVectors_eq_real (ι : Type*) [Fintype ι] :
    (#(primitiveVectors ι R) : ℝ) =
      (Nat.card R : ℝ) ^ Fintype.card ι *
        (1 - ((Nat.card (ResidueField R) : ℝ) ^ Fintype.card ι)⁻¹) := by
  have hk : (0 : ℝ) < Nat.card (ResidueField R) :=
    Nat.cast_pos.mpr (zero_lt_one.trans (TauCeti.IsLocalRing.one_lt_card_residueField R))
  have h := congrArg (Nat.cast : ℕ → ℝ)
    (TauCeti.IsLocalRing.card_residueField_pow_mul_card_isUnimodular R ι)
  rw [← card_primitiveVectors] at h
  push_cast [Nat.one_le_pow _ _ (Nat.cast_pos.mp hk)] at h
  field_simp
  linarith

omit [Fintype R] in
/-- The size of the residue field of a finite local ring, as a real number, exceeds one. -/
private theorem one_lt_card_residueField_real [Finite R] :
    (1 : ℝ) < Nat.card (ResidueField R) :=
  Nat.one_lt_cast.mpr (TauCeti.IsLocalRing.one_lt_card_residueField R)

/-- The first moment of local densities in terms of `M = N - 1`, where `N = binom(n + d, d)` is the
number of monomials: it is `(1 - q^{-(n+1)}) (1 - q^{-M}) / (1 - q^{-(M+1)})`. -/
private theorem sum_localDensity_div_card_primitiveVectors_eq_sub_one :
    (∑ a ∈ primitiveVectors (Monomials (Fin (n + 1)) d) R, localDensity a) /
        #(primitiveVectors (Monomials (Fin (n + 1)) d) R) =
      (1 - ((Nat.card (ResidueField R) : ℝ) ^ (n + 1))⁻¹) *
        (1 - ((Nat.card (ResidueField R) : ℝ) ^ ((n + d).choose d - 1))⁻¹) /
          (1 - ((Nat.card (ResidueField R) : ℝ) ^ ((n + d).choose d - 1 + 1))⁻¹) := by
  obtain ⟨M, hM⟩ : ∃ M, (n + d).choose d = M + 1 :=
    Nat.exists_eq_add_one.mpr (Nat.choose_pos (Nat.le_add_left d n))
  have hcard (m : ℕ) : (Nat.card R ^ m - Nat.card (maximalIdeal R) ^ m : ℕ) =
      (#(primitiveVectors (Fin m) R) : ℝ) := by
    rw [card_primitiveVectors, TauCeti.IsLocalRing.card_isUnimodular, Fintype.card_fin]
  have hsum : ∑ a ∈ primitiveVectors (Monomials (Fin (n + 1)) d) R, localDensity a =
      #(primitiveVectors (Fin (n + 1)) R) * #(primitiveVectors (Fin M) R) /
        (Nat.card R : ℝ) ^ n := by
    simp only [localDensity_def, ← Finset.sum_div, ← Nat.cast_sum, sum_card_primitiveZeros, hM,
      Nat.add_sub_cancel, Nat.cast_mul, hcard, ← Nat.card_eq_fintype_card]
  have hN : (#(primitiveVectors (Monomials (Fin (n + 1)) d) R) : ℝ) =
      #(primitiveVectors (Fin (M + 1)) R) := by
    rw [card_primitiveVectors_eq_real, card_primitiveVectors_eq_real, Fintype.card_coe,
      card_monomials_fin, hM, Fintype.card_fin]
  rw [hsum, hN, hM, Nat.add_sub_cancel]
  simp only [card_primitiveVectors_eq_real, Fintype.card_fin]
  have hq : (Nat.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hk := one_lt_card_residueField_real (R := R)
  field_simp
  ring

/-- **The first moment of local densities.** Over a finite local ring whose residue field has `q`
elements, the average of the local density `σ(a; R)` over the primitive coefficient vectors `a`
of the forms of degree `d` in `n + 1` variables is
`(1 - q^{-(n+1)}) (1 - q^{-(N-1)}) / (1 - q^{-N})`, where `N = binom(n + d, d)` is the number of
monomials. -/
theorem sum_localDensity_div_card_primitiveVectors :
    (∑ a ∈ primitiveVectors (Monomials (Fin (n + 1)) d) R, localDensity a) /
        #(primitiveVectors (Monomials (Fin (n + 1)) d) R) =
      (1 - ((Nat.card (ResidueField R) : ℝ) ^ (n + 1))⁻¹) *
        (1 - ((Nat.card (ResidueField R) : ℝ) ^ ((n + d).choose d - 1))⁻¹) /
          (1 - ((Nat.card (ResidueField R) : ℝ) ^ (n + d).choose d)⁻¹) := by
  rw [sum_localDensity_div_card_primitiveVectors_eq_sub_one,
    Nat.sub_add_cancel (Nat.choose_pos (Nat.le_add_left d n))]

/-- **The first moment of local densities modulo `pʳ`.** For a prime `p` and `r ≠ 0`, the average
of the local density `σ(a; pʳ)` over the primitive coefficient vectors `a` modulo `pʳ` of the forms
of degree `d` in `n + 1` variables is `(1 - p^{-(n+1)}) (1 - p^{-(N-1)}) / (1 - p^{-N})`, where
`N = binom(n + d, d)`. It does not depend on `r`. -/
theorem sum_localDensity_div_card_primitiveVectors_zmod_prime_pow (p r : ℕ) [Fact p.Prime]
    (hr : r ≠ 0) :
    (∑ a ∈ primitiveVectors (Monomials (Fin (n + 1)) d) (ZMod (p ^ r)), localDensity a) /
        #(primitiveVectors (Monomials (Fin (n + 1)) d) (ZMod (p ^ r))) =
      (1 - ((p : ℝ) ^ (n + 1))⁻¹) * (1 - ((p : ℝ) ^ ((n + d).choose d - 1))⁻¹) /
        (1 - ((p : ℝ) ^ (n + d).choose d)⁻¹) := by
  have : NeZero r := ⟨hr⟩
  rw [sum_localDensity_div_card_primitiveVectors, ZMod.card_residueField_prime_pow]

/-- The first moment of local densities is at most one. -/
theorem sum_localDensity_div_card_primitiveVectors_le_one :
    (∑ a ∈ primitiveVectors (Monomials (Fin (n + 1)) d) R, localDensity a) /
        #(primitiveVectors (Monomials (Fin (n + 1)) d) R) ≤ 1 := by
  rw [sum_localDensity_div_card_primitiveVectors_eq_sub_one]
  have hq := one_lt_card_residueField_real (R := R)
  set q : ℝ := (Nat.card (ResidueField R) : ℝ)
  set M := (n + d).choose d - 1
  -- With `x = q^{-(n+1)}`, `y = q^{-M}` and `z = q^{-(M+1)} ≤ y`: `(1 - x)(1 - y) ≤ 1 - y ≤ 1 - z`.
  have hx : 0 ≤ (q ^ (n + 1))⁻¹ := by positivity
  have hy₁ : (q ^ M)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq.le)
  have hzy : (q ^ (M + 1))⁻¹ ≤ (q ^ M)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le M.le_succ)
  have hz : (q ^ (M + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq M.succ_ne_zero)
  rw [div_le_one (sub_pos.mpr hz)]
  nlinarith

/-- For `d ≥ 2` and `n ≥ 1`, the first moment of local densities over a finite local ring whose
residue field has `q` elements is at least `1 - 2 q^{-(n+1)}`. -/
theorem one_sub_two_mul_le_sum_localDensity_div_card_primitiveVectors (hd : 2 ≤ d) (hn : 1 ≤ n) :
    1 - 2 * ((Nat.card (ResidueField R) : ℝ) ^ (n + 1))⁻¹ ≤
      (∑ a ∈ primitiveVectors (Monomials (Fin (n + 1)) d) R, localDensity a) /
        #(primitiveVectors (Monomials (Fin (n + 1)) d) R) := by
  rw [sum_localDensity_div_card_primitiveVectors_eq_sub_one]
  have hq := one_lt_card_residueField_real (R := R)
  have hnM : n + 1 ≤ (n + d).choose d - 1 := by have := Nat.add_two_le_add_choose hd hn; omega
  set q : ℝ := (Nat.card (ResidueField R) : ℝ)
  set M := (n + d).choose d - 1
  -- With `x = q^{-(n+1)}`, `y = q^{-M} ≤ x` and `z = q^{-(M+1)}`, so that `0 < 1 - z ≤ 1`:
  -- `1 - 2x ≤ (1 - x)(1 - y) ≤ (1 - x)(1 - y) / (1 - z)`.
  have hx₀ : 0 ≤ (q ^ (n + 1))⁻¹ := by positivity
  have hx₁ : (q ^ (n + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq.le)
  have hy₀ : 0 ≤ (q ^ M)⁻¹ := by positivity
  have hy₁ : (q ^ M)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq.le)
  have hyx : (q ^ M)⁻¹ ≤ (q ^ (n + 1))⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le hnM)
  have hz₀ : 0 ≤ (q ^ (M + 1))⁻¹ := by positivity
  have hz : (q ^ (M + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq M.succ_ne_zero)
  calc 1 - 2 * (q ^ (n + 1))⁻¹ ≤ (1 - (q ^ (n + 1))⁻¹) * (1 - (q ^ M)⁻¹) := by nlinarith
    _ ≤ (1 - (q ^ (n + 1))⁻¹) * (1 - (q ^ M)⁻¹) / (1 - (q ^ (M + 1))⁻¹) :=
      le_div_self (mul_nonneg (by linarith) (by linarith)) (by linarith) (by linarith)

end FirstMoment

end TauCeti.FormDensity
