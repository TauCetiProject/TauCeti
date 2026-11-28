/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.BinaryForm
public import TauCeti.RingTheory.MvPolynomial.Abv.HomogeneousEvaluation

import Mathlib.RingTheory.Valuation.Integers
import TauCeti.RingTheory.Valuation.AbsoluteValue

/-!
# Nonarchimedean bounds for binary forms

The binary resultant gives a lower bound for the maximum absolute value of the two
evaluations, provided the forms have integral coefficients. A resultant of absolute value
one gives equality with the degree power of the input maximum, and iterates raise this
maximum to the corresponding power of the degree.

The lower bound uses `MvPolynomial.IsHomogeneous.exists_mul_add_mul_eq_C_binaryResultant_mul_X_pow`
over the subring of integral elements. The upper bound uses
`IsNonarchimedean.eval_mvPolynomial_le_pow_of_coeff_le_one`.
These are the nonarchimedean estimates of Baker and Rumely, *Equidistribution of small
points, rational dynamics, and potential theory*, Remark 3.3 and Lemma 3.9.
-/

public section

open MvPolynomial

namespace IsNonarchimedean

variable {K : Type*} [CommRing K] {v : AbsoluteValue K ℝ}

variable {F G : MvPolynomial (Fin 2) K} {d : ℕ}

/-- For two integral binary forms of the same positive degree, the absolute value of their
resultant times the degree power of the input maximum bounds the output maximum from below.
The estimate also holds when the resultant vanishes. -/
theorem binaryResultant_mul_iSup_pow_le (hv : IsNonarchimedean v)
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d) (hd : d ≠ 0)
    (hcF : ∀ s, v (F.coeff s) ≤ 1) (hcG : ∀ s, v (G.coeff s) ≤ 1) (x : Fin 2 → K) :
    v (F.binaryResultant G d d) * (⨆ i, v (x i)) ^ d ≤
      ⨆ i, v (![F.eval x, G.eval x] i) := by
  rcases subsingleton_or_nontrivial K with _ | _
  · simp [Subsingleton.eq_zero (α := K), zero_pow hd]
  let O := (v.toValuation hv).integer
  let incl : O →+* K := O.subtype
  have hInt (a : K) : a ∈ O ↔ v a ≤ 1 := by
    rw [Valuation.mem_integer_iff, ← NNReal.coe_le_coe, AbsoluteValue.coe_toValuation_apply,
      NNReal.coe_one]
  have lift {P : MvPolynomial (Fin 2) K} (hc : ∀ s, v (P.coeff s) ≤ 1) :
      ∃ Q, map incl Q = P := by
    rw [← Set.mem_range, mem_range_map_iff_coeffs_subset]
    rintro _ hc'
    obtain ⟨s, -, rfl⟩ := mem_coeffs_iff.mp hc'
    exact Set.mem_range.mpr ⟨⟨_, (hInt _).mpr (hc s)⟩, rfl⟩
  obtain ⟨F₀, hF₀⟩ := lift hcF
  obtain ⟨G₀, hG₀⟩ := lift hcG
  let r := ⨆ i, v (x i)
  let b := ⨆ i, v (![F.eval x, G.eval x] i)
  obtain ⟨k, hk⟩ : ∃ k, v (x k) = r := exists_eq_ciSup_of_finite
  rcases (hk ▸ v.nonneg _ : 0 ≤ r).eq_or_lt with hz | hpos
  · have hz' : (⨆ i, v (x i)) = 0 := hz.symm
    rw [hz', zero_pow hd, mul_zero]
    exact Real.iSup_nonneg_of_nonnegHomClass v _
  obtain ⟨A, B, hA, hB, h⟩ := IsHomogeneous.exists_mul_add_mul_eq_C_binaryResultant_mul_X_pow
    (.of_map Subtype.val_injective (hF₀ ▸ hF)) (.of_map Subtype.val_injective (hG₀ ▸ hG))
    (.inl hd) k
  have he := congrArg (fun P ↦ eval x (map incl P)) h
  simp only [map_add, map_mul, map_pow, map_C, map_X, eval_C, eval_X] at he
  rw [← binaryResultant_map, hF₀, hG₀] at he
  have hbound {P : MvPolynomial (Fin 2) O} (hP : P.IsHomogeneous (d - 1)) :
      v (eval x (map incl P)) ≤ r ^ (d - 1) := by
    refine hv.eval_mvPolynomial_le_pow_of_coeff_le_one (hP.map incl) (fun s ↦ ?_) x
    rw [coeff_map]
    exact (hInt _).mp (P.coeff s).property
  have hle (i : Fin 2) : v (![F.eval x, G.eval x] i) ≤ b :=
    le_ciSup (Set.finite_range (fun j ↦ v (![F.eval x, G.eval x] j))).bddAbove i
  have hcert : v (F.binaryResultant G d d) * r ^ (d + d - 1) ≤ r ^ (d - 1) * b := by
    conv_lhs => rw [← hk, ← v.map_pow, ← v.map_mul, ← he]
    refine (hv _ _).trans ?_
    simp only [v.map_mul, max_le_iff]
    exact ⟨mul_le_mul (hbound hA) (hle 0) (v.nonneg _) (pow_nonneg hpos.le _),
      mul_le_mul (hbound hB) (hle 1) (v.nonneg _) (pow_nonneg hpos.le _)⟩
  rw [Nat.add_sub_assoc (Nat.pos_of_ne_zero hd), pow_add, ← mul_assoc, mul_comm _ b] at hcert
  exact le_of_mul_le_mul_right hcert (pow_pos hpos _)

/-- An integral binary lift of positive degree with resultant of absolute value one
raises the maximum coordinate absolute value to the degree power. -/
theorem iSup_eval_eq_pow_of_binaryResultant (hv : IsNonarchimedean v)
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d) (hd : d ≠ 0)
    (hcF : ∀ s, v (F.coeff s) ≤ 1) (hcG : ∀ s, v (G.coeff s) ≤ 1)
    (hres : v (F.binaryResultant G d d) = 1) (x : Fin 2 → K) :
    (⨆ i, v (![F.eval x, G.eval x] i)) = (⨆ i, v (x i)) ^ d := by
  refine le_antisymm (ciSup_le (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)) ?_
  · simpa only [Matrix.cons_val_zero] using hv.eval_mvPolynomial_le_pow_of_coeff_le_one hF hcF x
  · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using
      hv.eval_mvPolynomial_le_pow_of_coeff_le_one hG hcG x
  · simpa only [hres, one_mul] using hv.binaryResultant_mul_iSup_pow_le hF hG hd hcF hcG x

/-- Iterating a pair of integral binary forms with resultant of absolute value one
raises the maximum coordinate absolute value to the corresponding power of their
common positive degree. -/
theorem iSup_iterate_eval_eq_pow_of_binaryResultant (hv : IsNonarchimedean v)
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d) (hd : d ≠ 0)
    (hcF : ∀ s, v (F.coeff s) ≤ 1) (hcG : ∀ s, v (G.coeff s) ≤ 1)
    (hres : v (F.binaryResultant G d d) = 1) (x : Fin 2 → K) (n : ℕ) :
    (⨆ i, v (((fun y ↦ ![F.eval y, G.eval y])^[n]) x i)) = (⨆ i, v (x i)) ^ (d ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', hv.iSup_eval_eq_pow_of_binaryResultant hF hG hd hcF hcG hres,
      ih, ← pow_mul, pow_succ]

end IsNonarchimedean
