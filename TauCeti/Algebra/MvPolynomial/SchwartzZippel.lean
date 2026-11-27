/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Cast

/-!
# Natural-cardinality Schwartz–Zippel bound

Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` bounds the fraction of zeros of a nonzero
multivariate polynomial on a grid `Sⁿ` in `ℚ≥0`. This file clears the denominator and transports
along `Fintype.equivFin` to give the natural-number cardinality bound
`MvPolynomial.card_filter_piFinset_eval_eq_zero_le` for any finite variable type `σ`, including
the empty-grid and empty-variable cases.

## Main results

* `MvPolynomial.card_filter_piFinset_eval_eq_zero_le`: a nonzero polynomial `p` in `σ` variables
  over an integral domain has at most `S.card ^ (Fintype.card σ - 1) * p.totalDegree` zeros in
  `σ → S`.
-/

public section

namespace MvPolynomial

private theorem card_filter_piFinset_eval_eq_zero_le_fin {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] {n : ℕ} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Finset R) :
    ((Fintype.piFinset fun _ : Fin n ↦ S).filter fun v ↦ eval v p = 0).card ≤
      S.card ^ (n - 1) * p.totalDegree := by
  cases n with
  | zero =>
    rw [p.eq_C_of_isEmpty] at *
    simp [C_ne_zero.mp hp]
  | succ m =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    · have hsz := schwartz_zippel_totalDegree hp S
      have hS_pos : (0 : ℚ≥0) < S.card := Nat.cast_pos.mpr hS.card_pos
      have h := (div_le_iff₀ (pow_pos hS_pos (m + 1))).mp hsz
      have hrhs : (p.totalDegree : ℚ≥0) / S.card * (S.card : ℚ≥0) ^ (m + 1) =
          (S.card : ℚ≥0) ^ m * p.totalDegree := by
        rw [pow_succ', ← mul_assoc, div_mul_cancel₀ _ hS_pos.ne', mul_comm]
      rw [hrhs] at h
      exact_mod_cast h

/-- **Schwartz–Zippel bound (natural-cardinality form).** Over an integral domain, a nonzero
polynomial `p : MvPolynomial σ R` in finitely many variables has at most
`S.card ^ (Fintype.card σ - 1) * p.totalDegree` zeros on the square grid `σ → S` (including when
`S` or `σ` is empty). -/
theorem card_filter_piFinset_eval_eq_zero_le {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] [IsDomain R] [DecidableEq R] {p : MvPolynomial σ R} (hp : p ≠ 0)
    (S : Finset R) :
    ((Fintype.piFinset fun _ : σ ↦ S).filter fun v ↦ eval v p = 0).card ≤
      S.card ^ (Fintype.card σ - 1) * p.totalDegree := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let p' : MvPolynomial (Fin (Fintype.card σ)) R := rename e p
  have hp' : p' ≠ 0 := (renameEquiv R e).injective.ne hp
  have hcard :
      ((Fintype.piFinset fun _ : σ ↦ S).filter fun v ↦ eval v p = 0).card =
        ((Fintype.piFinset fun _ : Fin (Fintype.card σ) ↦ S).filter
          fun w ↦ eval w p' = 0).card := by
    refine Finset.card_equiv (Equiv.arrowCongr e (Equiv.refl R)) fun v ↦ ?_
    simp [p', eval_rename, e.forall_congr_left, Function.comp_def]
  rw [hcard, ← totalDegree_renameEquiv e p]
  exact card_filter_piFinset_eval_eq_zero_le_fin hp' S

end MvPolynomial
