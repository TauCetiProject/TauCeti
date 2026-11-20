/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.RingTheory.MvPolynomial.Symmetric.Maclaurin

/-!
# Norm bounds for elementary symmetric functions

Taking norms of the entries bounds the norm of every elementary symmetric function. Maclaurin's
bound and the multiset Cauchy–Schwarz inequality then bound these values in terms of the
root-mean-square norm, rather than the largest norm of an entry.
-/

public section

namespace Multiset

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R]

/-- The norm of an elementary symmetric function is bounded by the same function of the norms. -/
theorem norm_esymm_le_esymm_map_norm (s : Multiset R) (k : ℕ) :
    ‖s.esymm k‖ ≤ (s.map norm).esymm k := by
  rw [esymm, esymm, powersetCard_map]
  refine (norm_multiset_sum_le _).trans ?_
  simp only [map_map, Function.comp_def]
  exact sum_map_le_sum_map _ _ fun t _ ↦ by
    simpa using (List.norm_prod_le (l := t.toList))

/-- The norm of the `k`th elementary symmetric function is bounded by the binomial coefficient
 times the `k`th power of the root-mean-square norm of the entries. -/
theorem norm_esymm_le_choose_mul_sqrt_mean_sq_pow (s : Multiset R) (k : ℕ) :
    ‖s.esymm k‖ ≤ (s.card.choose k : ℝ) * √((s.map fun a ↦ ‖a‖ ^ 2).sum / s.card) ^ k := by
  have hm : (s.map norm).sum / s.card ≤ √((s.map fun a ↦ ‖a‖ ^ 2).sum / s.card) := by
    apply Real.le_sqrt_of_sq_le
    rcases eq_or_ne s.card 0 with h | h
    · simp [h]
    have hcs := (s.map norm).sq_sum_le_card_mul_sum_sq
    simp only [card_map, map_map, Function.comp_def] at hcs
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < s.card)]
    exact (mul_le_mul_of_nonneg_right hcs (Nat.cast_nonneg s.card)).trans_eq (by ring)
  refine (s.norm_esymm_le_esymm_map_norm k).trans ?_
  have hnorm : ∀ a ∈ s.map norm, 0 ≤ a := by
    simp only [mem_map, forall_exists_index, and_imp]
    rintro a b _ rfl
    exact norm_nonneg b
  have hmean := (s.map norm).esymm_le_choose_mul_mean_pow hnorm k
  rw [card_map] at hmean
  refine hmean.trans ?_
  gcongr
  exact div_nonneg (sum_nonneg hnorm) (Nat.cast_nonneg _)

end Multiset
