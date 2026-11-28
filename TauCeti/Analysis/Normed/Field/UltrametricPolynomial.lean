/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Analysis.Normed.Field.Ultra

/-!
# Ultrametric coefficient bounds and integral multiples for polynomials

Over a non-archimedean normed field `K` (`[NormedField K] [IsUltrametricDist K]`), this file
proves Gauss-lemma bounds for cancelling a monic polynomial factor, constructs an integral
polynomial multiple `e` with `e.eval 1 = 1` from a congruence against a monic factor, and shows
that a nonzero polynomial has some power shift `y ^ i` separating all its roots from `1` modulo
the maximal ideal.

## Main results

* `TauCeti.norm_coeff_le_of_mul_monic`: monic factor cancellation for `≤ η`.
* `TauCeti.norm_coeff_lt_one_of_mul_monic`: monic factor cancellation for `< 1`.
* `TauCeti.exists_integral_multiple_eval_one`: integral multiple `e` with `e.eval 1 = 1` from a
  congruence `A * B ≡ C ≡ A' * B` modulo norm `< 1`.
* `TauCeti.exists_one_le_norm_one_sub_pow_mul_root`: power shift separating all roots of `p` from
  `1` modulo the maximal ideal.

## Provenance

Adapted from `src/Lib/GaloisRep/Main/AttachedRepresentations.lean` (`norm_coeff_le_of_mul_monic`)
and `src/New/Congruences/FirstOrder/HeckeStrings.lean` (`New.Selmer.norm_coeff_lt_one_of_mul_monic`,
`New.Selmer.exists_integral_multiple_eval_one`,
`New.Selmer.exists_one_le_nnnorm_one_sub_pow_mul_root`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Polynomial IsUltrametricDist

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Over a non-archimedean normed field, if `R` is monic and all coefficients of `D * R` have norm
at most `η`, then all coefficients of `D` have norm at most `η`. -/
theorem norm_coeff_le_of_mul_monic {D R : K[X]} {η : ℝ} (hR : R.Monic)
    (h_le : ∀ i : ℕ, ‖(D * R).coeff i‖ ≤ η) (i : ℕ) : ‖D.coeff i‖ ≤ η := by
  by_cases hDR : D * R = 0
  · have hD : D = 0 := (mul_eq_zero.mp hDR).resolve_right hR.ne_zero
    simpa [hD] using (norm_nonneg ((D * R).coeff 0)).trans (h_le 0)
  let v : AbsoluteValue K ℝ :=
    { toFun := norm, map_mul' := norm_mul, nonneg' := norm_nonneg,
      eq_zero' := fun _ ↦ norm_eq_zero, add_le' := norm_add_le }
  have h_le_gn (P : K[X]) (k : ℕ) : ‖P.coeff k‖ ≤ P.gaussNorm v 1 := by
    by_cases hk : P.coeff k = 0
    · simpa [hk] using Polynomial.gaussNorm_nonneg v P one_pos.le
    · have hne : P.support.Nonempty := ⟨k, Polynomial.mem_support_iff.mpr hk⟩
      simp only [Polynomial.gaussNorm, hne, ↓reduceDIte, one_pow, mul_one]
      exact Finset.le_sup' (f := fun j ↦ v (P.coeff j)) (Polynomial.mem_support_iff.mpr hk)
  have hR_ge : 1 ≤ R.gaussNorm v 1 := by
    simpa [hR.coeff_natDegree] using h_le_gn R R.natDegree
  have h_mul : (D * R).gaussNorm v 1 = D.gaussNorm v 1 * R.gaussNorm v 1 :=
    D.gaussNorm_mul isNonarchimedean_norm one_pos R
  have h_top : (D * R).gaussNorm v 1 ≤ η := by
    have hne : (D * R).support.Nonempty := Polynomial.support_nonempty.mpr hDR
    simp only [Polynomial.gaussNorm, hne, ↓reduceDIte, one_pow, mul_one]
    exact Finset.sup'_le hne _ fun j _ ↦ h_le j
  calc ‖D.coeff i‖ ≤ D.gaussNorm v 1 := h_le_gn D i
    _ ≤ D.gaussNorm v 1 * R.gaussNorm v 1 :=
      le_mul_of_one_le_right (Polynomial.gaussNorm_nonneg v D one_pos.le) hR_ge
    _ = (D * R).gaussNorm v 1 := h_mul.symm
    _ ≤ η := h_top

/-- Over a non-archimedean normed field, if `R` is monic and all coefficients of `Q * R` have norm
less than `1`, then all coefficients of `Q` have norm less than `1`. -/
theorem norm_coeff_lt_one_of_mul_monic {Q R : K[X]} (hR : R.Monic)
    (h_lt : ∀ i : ℕ, ‖(Q * R).coeff i‖ < 1) (i : ℕ) : ‖Q.coeff i‖ < 1 := by
  classical
  let s := (Finset.range ((Q * R).natDegree + 1)).image fun j ↦ ‖(Q * R).coeff j‖
  have hs : s.Nonempty := ⟨‖(Q * R).coeff 0‖, Finset.mem_image_of_mem _ (by simp)⟩
  have h_le (j : ℕ) : ‖(Q * R).coeff j‖ ≤ s.max' hs := by
    by_cases hj : j ≤ (Q * R).natDegree
    · exact Finset.le_max' s _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
      exact (norm_nonneg _).trans
        (Finset.le_max' s ‖(Q * R).coeff 0‖ (Finset.mem_image_of_mem _ (by simp)))
  have h_lt_max : s.max' hs < 1 := by
    rw [Finset.max'_lt_iff]
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact h_lt j
  exact (norm_coeff_le_of_mul_monic hR h_le i).trans_lt h_lt_max

/-- Over a non-archimedean normed field, let `B` be monic, `C` have all coefficients of norm `≤ 1`,
`A * B ≡ C ≡ A' * B` coefficientwise modulo norm `< 1`, and `1 ≤ ‖A'.eval 1‖`. Then `A` divides a
polynomial `e` with all coefficients of norm `≤ 1` and `e.eval 1 = 1`. -/
theorem exists_integral_multiple_eval_one {A A' B C : K[X]} (hB : B.Monic)
    (hC : ∀ i : ℕ, ‖C.coeff i‖ ≤ 1) (hAB : ∀ i : ℕ, ‖(A * B - C).coeff i‖ < 1)
    (hA'B : ∀ i : ℕ, ‖C.coeff i - (A' * B).coeff i‖ < 1) (hA'_one : 1 ≤ ‖A'.eval 1‖) :
    ∃ e : K[X], A ∣ e ∧ (∀ i : ℕ, ‖e.coeff i‖ ≤ 1) ∧ e.eval 1 = 1 := by
  have hAB_int (i : ℕ) : ‖(A * B).coeff i‖ ≤ 1 :=
    calc ‖(A * B).coeff i‖ = ‖(A * B - C).coeff i + C.coeff i‖ := by rw [coeff_sub, sub_add_cancel]
      _ ≤ max ‖(A * B - C).coeff i‖ ‖C.coeff i‖ := norm_add_le_max _ _
      _ ≤ 1 := max_le (hAB i).le (hC i)
  have hA_int (i : ℕ) : ‖A.coeff i‖ ≤ 1 := norm_coeff_le_of_mul_monic hB hAB_int i
  have h_prod (i : ℕ) : ‖((A - A') * B).coeff i‖ < 1 :=
    calc ‖((A - A') * B).coeff i‖
        = ‖(A * B - C).coeff i + (C.coeff i - (A' * B).coeff i)‖ := by
          rw [sub_mul, coeff_sub, coeff_sub, sub_add_sub_cancel]
      _ ≤ max ‖(A * B - C).coeff i‖ ‖C.coeff i - (A' * B).coeff i‖ := norm_add_le_max _ _
      _ < 1 := max_lt (hAB i) (hA'B i)
  have h_diff_coeff : ∀ i : ℕ, ‖(A' - A).coeff i‖ < 1 := fun i ↦ by
    simpa [coeff_sub, norm_sub_rev] using norm_coeff_lt_one_of_mul_monic hB h_prod i
  have h_diff_one : ‖(A' - A).eval 1‖ < 1 := by
    classical
    rw [eval_eq_sum_range]
    simp only [one_pow, mul_one]
    let s := (Finset.range ((A' - A).natDegree + 1)).image fun i ↦ ‖(A' - A).coeff i‖
    have hs : s.Nonempty := ⟨‖(A' - A).coeff 0‖, Finset.mem_image_of_mem _ (by simp)⟩
    refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty (C := s.max' hs) (by simp)
      fun i hi ↦ Finset.le_max' s _ (Finset.mem_image_of_mem _ hi)).trans_lt ?_
    rw [Finset.max'_lt_iff]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact h_diff_coeff i
  have hA_one : 1 ≤ ‖A.eval 1‖ := by
    contrapose! hA'_one
    calc ‖A'.eval 1‖ = ‖(A' - A).eval 1 + A.eval 1‖ := by rw [eval_sub, sub_add_cancel]
      _ ≤ max ‖(A' - A).eval 1‖ ‖A.eval 1‖ := norm_add_le_max _ _
      _ < 1 := max_lt h_diff_one hA'_one
  have hA_ne : A.eval 1 ≠ 0 := norm_pos_iff.mp (one_pos.trans_le hA_one)
  refine ⟨A * Polynomial.C (A.eval 1)⁻¹, dvd_mul_right A _, fun i ↦ ?_, ?_⟩
  · rw [coeff_mul_C, norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.mpr hA_ne), one_mul]
    exact (hA_int i).trans hA_one
  · rw [eval_mul, eval_C, mul_inv_cancel₀ hA_ne]

/-- Over a non-archimedean normed field, if `p` is nonzero and `‖y ^ j - 1‖ = 1` for all
`1 ≤ j ≤ p.natDegree`, then for some `i : ℕ`, every root `μ` of `p` satisfies
`1 ≤ ‖1 - y ^ i * μ‖`. -/
theorem exists_one_le_norm_one_sub_pow_mul_root {p : K[X]} (hp : p ≠ 0) {y : K}
    (hy : ∀ j ∈ Set.Icc 1 p.natDegree, ‖y ^ j - 1‖ = 1) :
    ∃ i : ℕ, ∀ μ ∈ p.roots, 1 ≤ ‖1 - y ^ i * μ‖ := by
  classical
  by_contra! h_all
  choose μ h_root h_lt using h_all
  have h_ne (i j : Fin (p.natDegree + 1)) (hij : i < j) : μ i ≠ μ j := by
    intro h_eq
    have h_unit : ‖y ^ (i : ℕ) * μ i‖ = 1 := by
      refine le_antisymm ?_ ?_
      · calc ‖y ^ (i : ℕ) * μ i‖ = ‖(1 : K) + -(1 - y ^ (i : ℕ) * μ i)‖ := by ring_nf
          _ ≤ max ‖(1 : K)‖ ‖-(1 - y ^ (i : ℕ) * μ i)‖ := norm_add_le_max _ _
          _ ≤ 1 := by simpa [norm_neg, norm_sub_rev] using (h_lt i).le
      · by_contra! h_lt1
        have h1 : ‖(1 : K)‖ < 1 :=
          calc ‖(1 : K)‖ = ‖(1 - y ^ (i : ℕ) * μ i) + y ^ (i : ℕ) * μ i‖ := by ring_nf
            _ ≤ max ‖1 - y ^ (i : ℕ) * μ i‖ ‖y ^ (i : ℕ) * μ i‖ := norm_add_le_max _ _
            _ < 1 := max_lt (h_lt i) h_lt1
        simp at h1
    have h_step : ‖y ^ (j - i : ℕ) - 1‖ = 1 := hy _ ⟨by omega, by omega⟩
    have h_factor : 1 - y ^ (i : ℕ) * μ i - (1 - y ^ (j : ℕ) * μ j) =
        y ^ (i : ℕ) * μ i * (y ^ (j - i : ℕ) - 1) := by
      rw [← h_eq, ← pow_sub_mul_pow y (show (i : ℕ) ≤ j from hij.le)]
      ring
    have h_lt_sub : ‖1 - y ^ (i : ℕ) * μ i - (1 - y ^ (j : ℕ) * μ j)‖ < 1 := by
      rw [sub_eq_add_neg]
      exact (norm_add_le_max _ _).trans_lt
        (by simpa [norm_neg, norm_sub_rev] using max_lt (h_lt i) (h_lt j))
    exact h_lt_sub.ne (by rw [h_factor, norm_mul, h_unit, h_step, mul_one])
  exact hp <| eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (Function.Injective.of_lt_imp_ne h_ne) (fun i ↦ isRoot_of_mem_roots (h_root i))
    (by rw [Fintype.card_fin]; exact Nat.lt_succ_self _)

end TauCeti
