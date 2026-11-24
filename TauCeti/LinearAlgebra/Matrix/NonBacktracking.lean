/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

/-!
# Non-backtracking walk matrices

For a square matrix `H` over a semiring, read as edge weights of a directed graph on the index
type, `Matrix.nonbacktrackingPow H k` sums the weights `∏ₜ H (w t) (w (t + 1))` of the walks
`w` of length `k` that never step straight back, `w (t + 2) ≠ w t`. Without this condition the sum
would be `H ^ k`. For the Hermitian dilation of a rectangular matrix `Y`, the row block of the
non-backtracking walk matrix of length `2 * l` is the matrix `T(l)` of Bai and Yin, whose norm
bounds control the spectrum of `Y * Yᴴ` around `1 + c` when the columns have squared norms
near `c`.

Walk matrices of this kind satisfy a three-term recursion. A walk of length `k + 2` is a walk of
length `k + 1` with one more step in front, except that the new step must not be undone by the
next one. The correction subtracts the walks that step forward and straight back. A second
correction returns the walks that step forward, back and forward again along the same edge, which
the first correction removed twice. To keep the recursion closed, `Matrix.nonbacktrackingMul G H k`
weighs the first step by a second matrix `G` and continues with a non-backtracking walk of `H`
of length `k` that does not undo it.

## Main definitions

* `Matrix.nonbacktrackingPow H k`: the non-backtracking walk matrix of length `k`.
* `Matrix.nonbacktrackingMul G H k`: a step weighted by `G` followed by a non-backtracking walk of
  `H` of length `k` that does not step back.

## Main results

* `Matrix.nonbacktrackingPow_apply`: the entries of `nonbacktrackingPow H k` are sums over the
  non-backtracking walks.
* `Matrix.nonbacktrackingMul_add_two`: writing `B k` for `nonbacktrackingPow H k` and `G ⋆ B k`
  for `nonbacktrackingMul G H k`, the recursion
  `G ⋆ B (k + 2) = G * B (k + 2) - D_G * B (k + 1) + G' ⋆ B k`, where `D_G` is the diagonal matrix
  of the weights `∑ w, G i w * H w i` of the steps going back and forth, and `G'` reweighs the
  first step by `H w i * H i w`.
* `Matrix.nonbacktrackingPow_add_three`: its case `G = H`, the non-backtracking recursion
  `B (k + 3) = H * B (k + 2) - D * B (k + 1) + H' ⋆ B k`.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294.
* N. Alon, I. Benjamini, E. Lubetzky and S. Sodin, *Non-backtracking random walks mix faster*,
  Commun. Contemp. Math. 9 (2007), 585–603.
-/

public section

open Finset

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

section Semiring

variable [Semiring R]

/-- The weights of the non-backtracking walks of length `k` whose first step does not go to `f`.
The recursion prepends a step from `i` to `w ≠ f`, and forbids the next step to return to `i`. -/
private def nonbacktrackingAux (H : Matrix ι ι R) : ℕ → Option ι → Matrix ι ι R
  | 0, _ => 1
  | k + 1, f => of fun i j ↦ ∑ w with some w ≠ f, H i w * nonbacktrackingAux H k (some i) w j

/-- **The non-backtracking walk matrix of length `k`.** Its entry `(i, j)` is the sum of the
weights `∏ₜ H (w t) (w (t + 1))` of the walks `w` of length `k` from `i` to `j` that never step
straight back, `w (t + 2) ≠ w t` (`Matrix.nonbacktrackingPow_apply`). -/
def nonbacktrackingPow (H : Matrix ι ι R) (k : ℕ) : Matrix ι ι R :=
  nonbacktrackingAux H k none

/-- A step weighted by `G` followed by a non-backtracking walk of `H` of length `k` that does not
step back. Its entry `(i, j)` sums `G i w` times the weight of each non-backtracking walk of `H` of
length `k` from `w` to `j` whose first step does not return to `i`. For `G = H` this is the
non-backtracking walk matrix of length `k + 1` (`Matrix.nonbacktrackingPow_succ`). -/
def nonbacktrackingMul (G H : Matrix ι ι R) (k : ℕ) : Matrix ι ι R :=
  of fun i j ↦ ∑ w, G i w * nonbacktrackingAux H k (some i) w j

/-- The only walk of length zero from `i` ends at `i`. -/
@[simp]
theorem nonbacktrackingPow_zero (H : Matrix ι ι R) : nonbacktrackingPow H 0 = 1 := (rfl)

/-- A non-backtracking walk of length `k + 1` is a first step followed by a non-backtracking walk of
length `k` that does not step back. -/
theorem nonbacktrackingPow_succ (H : Matrix ι ι R) (k : ℕ) :
    nonbacktrackingPow H (k + 1) = nonbacktrackingMul H H k := by
  ext i j
  simp [nonbacktrackingPow, nonbacktrackingMul, nonbacktrackingAux]

/-- A weighted step followed by a walk of length zero is the weight of the step. -/
@[simp]
theorem nonbacktrackingMul_zero (G H : Matrix ι ι R) : nonbacktrackingMul G H 0 = G := by
  ext i j
  simp [nonbacktrackingMul, nonbacktrackingAux, Matrix.one_apply]

/-- The non-backtracking walks of length one are the steps. -/
@[simp]
theorem nonbacktrackingPow_one (H : Matrix ι ι R) : nonbacktrackingPow H 1 = H := by
  rw [nonbacktrackingPow_succ, nonbacktrackingMul_zero]

end Semiring

section Ring

variable [Ring R]

/-- Forbidding the first step to go to `f` removes the walks that start with the step to `f`. -/
private theorem nonbacktrackingAux_succ_some (H : Matrix ι ι R) (k : ℕ) (f w j : ι) :
    nonbacktrackingAux H (k + 1) (some f) w j =
      nonbacktrackingPow H (k + 1) w j - H w f * nonbacktrackingAux H k (some w) f j := by
  simp only [nonbacktrackingPow, nonbacktrackingAux, of_apply, ne_eq, Option.some.injEq,
    reduceCtorEq, not_false_eq_true, filter_true]
  rw [filter_ne', sum_erase_eq_sub (mem_univ f)]

/-- **The recursion for a weighted first step.** The non-backtracking walks of length `k + 2`
after a step weighted by `G` are all the walks after that step, minus those stepping straight
back, which carry the weight `D_G i = ∑ w, G i w * H w i`, plus those stepping back and then
forward along the same edge again, which were subtracted twice. -/
theorem nonbacktrackingMul_add_two (G H : Matrix ι ι R) (k : ℕ) :
    nonbacktrackingMul G H (k + 2) =
      G * nonbacktrackingPow H (k + 2) -
        diagonal (fun i ↦ ∑ w, G i w * H w i) * nonbacktrackingPow H (k + 1) +
        nonbacktrackingMul (of fun i w ↦ G i w * (H w i * H i w)) H k := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [nonbacktrackingMul, of_apply, nonbacktrackingAux_succ_some, mul_sub, sum_sub_distrib,
    sum_mul, mul_assoc, (rfl : k + 1 + 1 = k + 2)]
  abel

/-- The step weighted by `G` followed by a walk of length one that does not step back. -/
theorem nonbacktrackingMul_one (G H : Matrix ι ι R) :
    nonbacktrackingMul G H 1 = G * H - diagonal (fun i ↦ ∑ w, G i w * H w i) := by
  ext i j
  have h (w : ι) : nonbacktrackingAux H 1 (some i) w j = H w j - H w i * (1 : Matrix ι ι R) i j :=
    by simpa [nonbacktrackingAux] using nonbacktrackingAux_succ_some H 0 i w j
  simp only [nonbacktrackingMul, of_apply, h, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, mul_sub, sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one,
    mul_zero]
  split_ifs <;> simp

/-- The non-backtracking walk matrix of length two is `H * H` minus the steps forward and straight
back. -/
theorem nonbacktrackingPow_two (H : Matrix ι ι R) :
    nonbacktrackingPow H 2 = H * H - diagonal (fun i ↦ ∑ w, H i w * H w i) := by
  rw [nonbacktrackingPow_succ, nonbacktrackingMul_one]

/-- **The non-backtracking recursion.** The walks of length `k + 3` are the walks of length `k + 2`
with a step in front, minus those whose second step undoes the first, plus those that then traverse
the same edge a third time. -/
theorem nonbacktrackingPow_add_three (H : Matrix ι ι R) (k : ℕ) :
    nonbacktrackingPow H (k + 3) =
      H * nonbacktrackingPow H (k + 2) -
        diagonal (fun i ↦ ∑ w, H i w * H w i) * nonbacktrackingPow H (k + 1) +
        nonbacktrackingMul (of fun i w ↦ H i w * (H w i * H i w)) H k := by
  rw [nonbacktrackingPow_succ, nonbacktrackingMul_add_two]

end Ring

section Walks

omit [Fintype ι] [DecidableEq ι] in
/-- A walk starting with a step to `v 0` from `i` never steps straight back exactly when `v` never
does and its second vertex `v 1` differs from `i`. -/
private theorem forall_cons_ne_iff {k : ℕ} (i : ι) (v : Fin (k + 1) → ι) :
    (∀ s t : Fin (k + 2), (s : ℕ) + 2 = t →
        (Fin.cons i v : Fin (k + 2) → ι) s ≠ (Fin.cons i v : Fin (k + 2) → ι) t) ↔
      (∀ s t : Fin (k + 1), (s : ℕ) + 2 = t → v s ≠ v t) ∧
        ∀ t : Fin (k + 1), (t : ℕ) = 1 → some (v t) ≠ some i := by
  constructor
  · intro h
    refine ⟨fun s t hst ↦ ?_, fun t ht ↦ ?_⟩
    · simpa using h s.succ t.succ (by simp [hst])
    · simpa [eq_comm] using h 0 t.succ (by simp [ht])
  · rintro ⟨hv, hi⟩ s t hst
    induction s using Fin.cases with
    | zero =>
      induction t using Fin.cases with
      | zero => simp at hst
      | succ t =>
        have ht : (t : ℕ) = 1 := by simp only [Fin.val_zero, Fin.val_succ] at hst; omega
        simpa [eq_comm] using hi t ht
    | succ s =>
      induction t using Fin.cases with
      | zero => simp at hst
      | succ t => simpa using hv s t (by simpa using hst)

variable [CommSemiring R]

/-- The walk sum behind `nonbacktrackingAux`, with the first step avoiding `f`. -/
private theorem nonbacktrackingAux_apply (H : Matrix ι ι R) (k : ℕ) (f : Option ι) (i j : ι) :
    nonbacktrackingAux H k f i j =
      ∑ w : Fin (k + 1) → ι with w 0 = i ∧ w (Fin.last k) = j ∧
          (∀ s t : Fin (k + 1), (s : ℕ) + 2 = t → w s ≠ w t) ∧
          (∀ t : Fin (k + 1), (t : ℕ) = 1 → some (w t) ≠ f),
        ∏ t : Fin k, H (w t.castSucc) (w t.succ) := by
  induction k generalizing f i with
  | zero =>
    -- A walk of length zero is its starting point.
    rw [sum_filter, ← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    rcases eq_or_ne i j with rfl | h
    · simp [nonbacktrackingAux, Fin.last]
    · rw [sum_eq_zero fun a _ ↦ ite_eq_right fun ha ↦ h (ha.1.symm.trans ha.2.1)]
      simp [nonbacktrackingAux, h]
  | succ k ih =>
    -- Both sides sum over the walks `v` of length `k` after the first step `i → v 0`.
    have hL : nonbacktrackingAux H (k + 1) f i j = ∑ v : Fin (k + 1) → ι,
        if some (v 0) ≠ f ∧ v (Fin.last k) = j ∧
            (∀ s t : Fin (k + 1), (s : ℕ) + 2 = t → v s ≠ v t) ∧
            (∀ t : Fin (k + 1), (t : ℕ) = 1 → some (v t) ≠ some i) then
          H i (v 0) * ∏ t : Fin k, H (v t.castSucc) (v t.succ) else 0 := by
      simp only [nonbacktrackingAux, of_apply, ih, mul_sum, sum_filter, ite_sum_zero]
      rw [sum_comm]
      refine sum_congr rfl fun v _ ↦ ?_
      rw [Fintype.sum_eq_single (v 0) fun a ha ↦ by simp [Ne.symm ha]]
      by_cases h : some (v 0) ≠ f <;> simp [h]
    rw [hL, sum_filter, ← (Fin.consEquiv (n := k + 1) fun _ ↦ ι).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_eq_single i fun a ha ↦ by simp [ha]]
    refine sum_congr rfl fun v _ ↦ ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_last, forall_cons_ne_iff,
      Fin.prod_univ_succ, Fin.cons_succ, Fin.castSucc_zero, true_and]
    refine if_congr ⟨fun h ↦ ⟨h.2.1, h.2.2, fun t ht ↦ ?_⟩, fun h ↦ ⟨?_, h.1, h.2.1⟩⟩ rfl rfl
    · induction t using Fin.cases with
      | zero => simp at ht
      | succ t => simpa [(Fin.ext (by simpa using ht) : t = 0)] using h.1
    · simpa using h.2.2 1 (by simp)

/-- **Non-backtracking walk sums.** Entry `(i, j)` of `nonbacktrackingPow H k` is the sum over the
walks `w : Fin (k + 1) → ι` from `i` to `j` with `w s ≠ w t` whenever `t = s + 2` of the products
`∏ₜ H (w t) (w (t + 1))`. -/
theorem nonbacktrackingPow_apply (H : Matrix ι ι R) (k : ℕ) (i j : ι) :
    nonbacktrackingPow H k i j =
      ∑ w : Fin (k + 1) → ι with w 0 = i ∧ w (Fin.last k) = j ∧
          ∀ s t : Fin (k + 1), (s : ℕ) + 2 = t → w s ≠ w t,
        ∏ t : Fin k, H (w t.castSucc) (w t.succ) := by
  simp [nonbacktrackingPow, nonbacktrackingAux_apply]

end Walks

end Matrix
