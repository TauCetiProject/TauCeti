/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.PowerSeries.DFinite.Basic

import TauCeti.Algebra.Polynomial.Eval.Subsemiring
import TauCeti.NumberTheory.NumberField.AdjoinPair

/-!
# Number-field containment for algebraic D-finite series

Any sequence `a : ℕ → F` of `ℚ`-algebraic elements in a characteristic-zero field whose generating
series `PowerSeries.mk a` is D-finite over `algebraicClosure ℚ F` is generated past the natural
roots of its leading recurrence polynomial by finitely many algebraic numbers, so all coefficients
lie in a single intermediate number field of `F / ℚ`.

## Main results

* `TauCeti.exists_numberField_of_isDFinite_mk`: coefficients of an algebraic D-finite series lie
  in a single intermediate number field.
-/

public section

open Polynomial PowerSeries

namespace TauCeti

/-- If a sequence `a : ℕ → F` of `ℚ`-algebraic elements in a characteristic-zero field has a
generating series `PowerSeries.mk a` that is D-finite over `algebraicClosure ℚ F`, then all
coefficients `a n` belong to a single intermediate number field `K` of `F / ℚ`. -/
theorem exists_numberField_of_isDFinite_mk {F : Type*} [Field F] [CharZero F] {a : ℕ → F}
    (halg : ∀ n, IsAlgebraic ℚ (a n))
    (hdf : PowerSeries.IsDFinite (algebraicClosure ℚ F) (PowerSeries.mk a)) :
    ∃ (K : IntermediateField ℚ F) (_ : NumberField K), ∀ n, a n ∈ K := by
  obtain ⟨r, q, hq, hrec⟩ := PowerSeries.isDFinite_iff_pRecursive.mp hdf
  have : CharZero (algebraicClosure ℚ F) := (algebraMap (algebraicClosure ℚ F) F).charZero
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (q (Fin.last r)).eval (n : algebraicClosure ℚ F) ≠ 0 :=
    Filter.eventually_atTop.mp (Nat.cofinite_eq_atTop ▸
      Nat.cast_injective.tendsto_cofinite.eventually
        (Polynomial.eventually_eval_ne_zero_cofinite hq))
  let ι := Fin (N + r) ⊕ Σ i : Fin (r + 1), Fin ((q i).natDegree + 1)
  let gen : ι → F := Sum.elim (fun m ↦ a m) (fun ij ↦ ((q ij.1).coeff ij.2 : F))
  have hgen_alg : ∀ x : ι, IsAlgebraic ℚ (gen x) := by
    rintro (m | ⟨i, j⟩); exacts [halg m, mem_algebraicClosure_iff.mp ((q i).coeff j).2]
  obtain ⟨K, hK, y, hy⟩ := exists_numberField_comp hgen_alg
  have hmem_gen : ∀ x : ι, gen x ∈ K := fun x ↦ by rw [← congrFun hy x]; exact (y x).2
  set evalF : Fin (r + 1) → ℕ → F :=
    fun i n ↦ algebraMap (algebraicClosure ℚ F) F ((q i).eval (n : algebraicClosure ℚ F))
  have heval_mem : ∀ i n, evalF i n ∈ K := fun i n ↦ by
    dsimp only [evalF]
    rw [← Polynomial.eval_map_apply, ← Polynomial.eval₂_eq_eval_map]
    refine Polynomial.eval₂_mem (fun j hj ↦ ?_) (by simpa only [map_natCast] using K.natCast_mem n)
    exact hmem_gen (Sum.inr ⟨i, ⟨j, Nat.lt_succ_of_le (le_natDegree_of_mem_supp j hj)⟩⟩)
  refine ⟨K, hK, fun m ↦ ?_⟩
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hm : m < N + r
    · exact hmem_gen (Sum.inl ⟨m, hm⟩)
    · set n := m - r
      have hmr : n + r = m := by omega
      have hstep : ∑ i : Fin (r + 1), evalF i n * a (n + i) = 0 := by
        simpa only [Algebra.smul_def, coeff_mk] using hrec n
      rw [Fin.sum_univ_castSucc, Fin.val_last, hmr] at hstep
      simp only [Fin.val_castSucc] at hstep
      have hne : evalF (Fin.last r) n ≠ 0 := (_root_.map_ne_zero _).mpr (hN n (by omega))
      have hcm : evalF (Fin.last r) n * a m = -∑ i : Fin r, evalF i.castSucc n * a (n + i) := by
        linear_combination hstep
      have hsol : a m =
          -(evalF (Fin.last r) n)⁻¹ * ∑ i : Fin r, evalF i.castSucc n * a (n + i) := by
        rw [← inv_mul_cancel_left₀ hne (a m), hcm, mul_neg, neg_mul]
      rw [hsol]
      refine K.mul_mem (K.neg_mem (K.inv_mem (heval_mem _ n))) (K.sum_mem fun i _ ↦ ?_)
      exact K.mul_mem (heval_mem _ n) (ih _ (by have := i.isLt; omega))

end TauCeti
