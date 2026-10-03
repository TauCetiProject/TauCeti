/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Basic

import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.RingTheory.MvPolynomial.Finrank
import TauCeti.RingTheory.Polynomial.Dickson

/-!
# The dimension of the space of period polynomials

Let `K` be a field of characteristic zero and `w` a positive even integer. The period-polynomial
space `W_w = A ∩ B` is cut out of the `(w + 1)`-dimensional space `V_w` of binary forms of
degree `w` by `A = ker (1 + S)` and `B = ker (1 + U + U²)`, where `S` and `U = T S` act with
`S² = 1` and `U³ = 1`. Its dimension is computed here by finite linear algebra, with no modular
forms involved:

* the dimension of the kernel of `1 + S`, respectively `1 + U + U²`, is read off the traces of `S`,
  respectively of `U` and `U²`, on `V_w`
  (`TauCeti.LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one` and
  `TauCeti.LinearMap.three_mul_finrank_ker_one_add_add_sq_of_pow_three_eq_one`);
* these traces are the Eichler–Selberg weights `P_{w+2}(t, 1)` at the traces `t = 0, 1, -1` of
  `S`, `U` and `U²`, periodic in `w` (`TauCeti.trace_binaryFormRep_eq_dickson_eval`), which gives
  `dim A = 2 ⌈w / 4⌉` and `dim B = 2 ⌈w / 3⌉`;
* `A + B = V_w` (`TauCeti.codisjoint_ker_one_add_S_ker_one_add_U_add_U_sq`), so
  `dim W_w = dim A + dim B - (w + 1)`.

Comparing with Mathlib's level-one dimension formula `ModularForm.dimension_level_one` shows that
`dim W_w = dim M_{w+2}(SL(2, ℤ)) + dim S_{w+2}(SL(2, ℤ))` for every `w`. This is the dimension
count by which the Eichler–Shimura period maps `S_k → W_w⁻` and `M_k → W_w⁺`, once known to be
injective, are isomorphisms: the even and odd parts `W_w^±` together span `W_w`
(`TauCeti.evenPeriodPolynomials_sup_oddPeriodPolynomials`).

## Main results

* `TauCeti.finrank_ker_one_add_S`: for even `w`, `dim ker (1 + S) = 2 ⌈w / 4⌉` on `V_w`.
* `TauCeti.finrank_ker_one_add_U_add_U_sq`: for even `w`, `dim ker (1 + U + U²) = 2 ⌈w / 3⌉` on
  `V_w`.
* `TauCeti.finrank_periodPolynomials_add_eq`: for positive even `w`,
  `dim W_w + (w + 1) = 2 ⌈w / 4⌉ + 2 ⌈w / 3⌉`.
* `TauCeti.periodPolynomials_zero`: `W_0 = 0`.
* `TauCeti.finrank_periodPolynomials_eq_finrank_modularForm_add_finrank_cuspForm`: for every `w`,
  `dim W_w = dim M_{w+2}(SL(2, ℤ)) + dim S_{w+2}(SL(2, ℤ))` over `ℂ`.

## References

* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular Forms*
  (R. A. Rankin, ed.), Ellis Horwood, 1984, 197–249, §1.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2.
-/

public section

open Matrix MulOpposite MvPolynomial ModularGroup Module Polynomial
open scoped MatrixGroups

namespace TauCeti

variable {K : Type*} [Field K] {w : ℕ}

/-! ### The traces of `S`, `U` and `U²` on binary forms -/

/-- `S` acts on `V_w` with trace `P_{w+2}(0, 1)`. -/
private lemma trace_binaryFormRep_S :
    LinearMap.trace K _ (binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ))) =
      (dickson 2 (1 : K) w).eval 0 := by
  rw [trace_binaryFormRep_eq_dickson_eval, Matrix.SpecialLinearGroup.det_coe, coe_S]
  simp [Matrix.trace_fin_two]

/-- `U = T S = !![1, -1; 1, 0]`. -/
private lemma coe_T_mul_S :
    ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `U` acts on `V_w` with trace `P_{w+2}(1, 1)`. -/
private lemma trace_binaryFormRep_U :
    LinearMap.trace K _ (binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))) =
      (dickson 2 (1 : K) w).eval 1 := by
  rw [trace_binaryFormRep_eq_dickson_eval, Matrix.SpecialLinearGroup.det_coe, coe_T_mul_S]
  simp [Matrix.trace_fin_two]

/-- `U²` acts on `V_w` with trace `P_{w+2}(-1, 1)`. -/
private lemma trace_binaryFormRep_U_sq :
    LinearMap.trace K _
        (binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2) =
      (dickson 2 (1 : K) w).eval (-1) := by
  rw [← map_pow, ← op_pow, trace_binaryFormRep_eq_dickson_eval,
    ← Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.det_coe,
    Matrix.SpecialLinearGroup.coe_pow, coe_T_mul_S]
  simp [sq, Matrix.trace_fin_two]

/-! ### The dimensions of `ker (1 + S)` and `ker (1 + U + U²)` -/

/-- **The binary forms of even degree `w` negated by `S` form a space of dimension
`2 ⌈w / 4⌉`.** -/
theorem finrank_ker_one_add_S [CharZero K] (hw : Even w) :
    finrank K (LinearMap.ker (1 + binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ)))) =
      2 * ((w + 3) / 4) := by
  have h := LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one
    (binaryFormRep_S_sq_of_even (R := K) hw)
  rw [finrank_homogeneousSubmodule_fin_two, trace_binaryFormRep_S] at h
  obtain ⟨m, rfl⟩ := hw
  have hs : (dickson 2 (1 : K) (m + m)).eval 0 = (-1) ^ m := by
    rw [← two_mul]
    exact dickson_two_one_eval_zero_two_mul m
  rw [hs] at h
  apply Nat.cast_injective (R := K)
  -- `2 dim = w + 1 - (-1) ^ (w / 2)`, according to the parity of `w / 2`
  rcases Nat.even_or_odd m with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [show (i + i + (i + i) + 3) / 4 = i by omega]
    rw [Even.neg_one_pow ⟨i, rfl⟩] at h
    push_cast at h ⊢
    linear_combination h / 2
  · rw [show (2 * i + 1 + (2 * i + 1) + 3) / 4 = i + 1 by omega]
    rw [Odd.neg_one_pow ⟨i, rfl⟩] at h
    push_cast at h ⊢
    linear_combination h / 2

/-- **The binary forms of even degree `w` killed by `1 + U + U²` form a space of dimension
`2 ⌈w / 3⌉`.** -/
theorem finrank_ker_one_add_U_add_U_sq [CharZero K] (hw : Even w) :
    finrank K (LinearMap.ker
      (1 + binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
        binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2)) =
      2 * ((w + 2) / 3) := by
  have h := LinearMap.three_mul_finrank_ker_one_add_add_sq_of_pow_three_eq_one
    (binaryFormRep_U_pow_three_of_even (R := K) hw)
  rw [finrank_homogeneousSubmodule_fin_two, trace_binaryFormRep_U, trace_binaryFormRep_U_sq] at h
  apply Nat.cast_injective (R := K)
  -- `3 dim = 2 (w + 1) - P_{w+2}(1, 1) - P_{w+2}(-1, 1)`, according to `w mod 6`
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, (r = 0 ∨ r = 2 ∨ r = 4) ∧ w = 6 * j + r :=
    ⟨w / 6, w % 6, by obtain ⟨m, rfl⟩ := hw; omega, (Nat.div_add_mod w 6).symm⟩
  have hU₂ := dickson_two_one_eval_neg_one_three_mul_add (R := K) (2 * j) r
  rw [← mul_assoc, show 3 * 2 = 6 by rfl] at hU₂
  rw [dickson_two_one_eval_one_six_mul_add, hU₂] at h
  rcases hr with rfl | rfl | rfl
  · rw [show (6 * j + 0 + 2) / 3 = 2 * j by omega]
    norm_num at h
    push_cast at h ⊢
    linear_combination h / 3
  · rw [show (6 * j + 2 + 2) / 3 = 2 * j + 1 by omega]
    norm_num [dickson_two] at h
    push_cast at h ⊢
    linear_combination h / 3
  · rw [show (6 * j + 4 + 2) / 3 = 2 * j + 2 by omega]
    rw [show (4 : ℕ) = 1 + 3 by rfl, dickson_two_one_eval_one_add_three,
      dickson_two_one_eval_neg_one_add_three] at h
    norm_num at h
    push_cast at h ⊢
    linear_combination h / 3

/-! ### The dimension of `W_w` -/

/-- **The dimension of the period-polynomial space**, computed by linear algebra: for positive even
`w`, `dim W_w = 2 ⌈w / 4⌉ + 2 ⌈w / 3⌉ - (w + 1)`, stated without truncated subtraction. -/
theorem finrank_periodPolynomials_add_eq [CharZero K] (hw : Even w) (hw₀ : w ≠ 0) :
    finrank K (periodPolynomials K w) + (w + 1) = 2 * ((w + 3) / 4) + 2 * ((w + 2) / 3) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (1 + binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ))))
    (LinearMap.ker (1 + binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
      binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2))
  rw [codisjoint_iff.1 (codisjoint_ker_one_add_S_ker_one_add_U_add_U_sq hw hw₀), finrank_top,
    finrank_homogeneousSubmodule_fin_two, ← periodPolynomials_def, finrank_ker_one_add_S hw,
    finrank_ker_one_add_U_add_U_sq hw] at h
  omega

/-- **In degree `0` there are no nonzero period polynomials**: `S` fixes the constants, so `1 + S`
is injective on `V_0`. -/
theorem periodPolynomials_zero [CharZero K] : periodPolynomials K 0 = ⊥ := by
  have h := finrank_ker_one_add_S (K := K) (w := 0) ⟨0, rfl⟩
  rw [Submodule.finrank_eq_zero] at h
  rw [eq_bot_iff, ← h, periodPolynomials_def]
  exact inf_le_left

/-- **The period-polynomial space has the dimension of `M_{w+2} ⊕ S_{w+2}`**: over `ℂ`,
`dim W_w = dim M_{w+2}(SL(2, ℤ)) + dim S_{w+2}(SL(2, ℤ))` for every `w`.

The left side is computed by linear algebra on binary forms (`finrank_periodPolynomials_add_eq`),
the right side by Mathlib's level-one dimension formula. For `w = 0` and for odd `w` both sides
vanish. This is the dimension count which, together with the injectivity of the Eichler–Shimura
period maps `S_{w+2} → W_w⁻` and `M_{w+2} → W_w⁺`, makes them isomorphisms. -/
theorem finrank_periodPolynomials_eq_finrank_modularForm_add_finrank_cuspForm (w : ℕ) :
    finrank ℂ (periodPolynomials ℂ w) =
      finrank ℂ (ModularForm 𝒮ℒ (w + 2 : ℕ)) + finrank ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) := by
  -- cusp forms are modular forms, so `dim S_k ≤ dim M_k`
  have hSM := LinearMap.finrank_le_finrank_of_injective
    (CuspForm.toModularFormₗ_injective (Γ := 𝒮ℒ) (k := (w + 2 : ℕ)))
  rcases Nat.even_or_odd w with hw | hw
  · rcases eq_or_ne w 0 with rfl | hw₀
    · -- weight `2`: `M_2 = 0`, and `W_0 = 0`
      have hM : finrank ℂ (ModularForm 𝒮ℒ (0 + 2 : ℕ)) = 0 :=
        finrank_eq_of_rank_eq (by simpa using ModularForm.levelOne_weight_two_rank_zero)
      rw [periodPolynomials_zero, finrank_bot]
      omega
    · -- `dim M_k = 1 + dim S_k`, with `dim M_k` given by the level-one dimension formula
      have hk : Even (w + 2) := hw.add even_two
      have : FiniteDimensional ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) :=
        .of_injective _ CuspForm.toModularFormₗ_injective
      have hMS := ModularForm.rank_eq_one_add_rank_cuspForm (k := w + 2) (by omega) hk
      rw [← finrank_eq_rank, ← finrank_eq_rank] at hMS
      norm_cast at hMS
      have hM := finrank_eq_of_rank_eq (ModularForm.dimension_level_one (w + 2) hk)
      have hW := finrank_periodPolynomials_add_eq (K := ℂ) hw hw₀
      obtain ⟨m, rfl⟩ := hw
      split_ifs at hM with h12 <;>
      · rw [Nat.ModEq] at h12
        omega
  · -- odd weight: `M_k = 0`, and `W_w = 0`
    have hM : finrank ℂ (ModularForm 𝒮ℒ (w + 2 : ℕ)) = 0 :=
      finrank_eq_of_rank_eq <| by
        simpa using ModularForm.levelOne_odd_weight_rank_zero (k := (w + 2 : ℕ))
          (by exact_mod_cast hw.add_even even_two)
    rw [periodPolynomials_eq_bot_of_odd (mul_right_injective₀ two_ne_zero) hw, finrank_bot]
    omega

end TauCeti
