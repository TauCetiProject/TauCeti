/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.DeterminantBound
import TauCeti.Analysis.Normed.Ring.ProdSubProd

/-!
# The determinant is Lipschitz on entrywise bounded matrices

Over a seminormed commutative ring, if every entry of two square matrices `A` and `B` of size
`n` has norm at most `c`, and every entry of `A - B` has norm at most `ε`, then

`‖det A - det B‖ ≤ n! * n * c ^ (n - 1) * ε`

(`Matrix.norm_det_sub_det_le`). Each of the `n!` terms of the Leibniz formula is a product of `n`
entries, and two such products differ by at most `c ^ (n - 1)` times the sum of the differences
of their factors (`TauCeti.norm_prod_sub_prod_le_pow_mul_sum_norm_sub`).

For a nonempty index type the determinants also have norm at most `n! * c ^ n`
(`Matrix.norm_det_le_factorial_mul_pow_of_nonempty`), so the squares of their norms differ by at
most `2 * n! ^ 2 * n * c ^ (2 * n - 1) * ε` (`Matrix.abs_norm_det_sq_sub_le`); for an empty index
type both determinants are `1`.

## Main results

* `Matrix.norm_det_sub_det_le`: the Lipschitz bound for the determinant.
* `Matrix.abs_norm_det_sq_sub_le`: the Lipschitz bound for the square of its norm.
-/

public section

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The determinant is Lipschitz on entrywise bounded matrices.** If the entries of `A` and `B`
have norm at most `c` and those of `A - B` norm at most `ε`, then
`‖det A - det B‖ ≤ n! * n * c ^ (n - 1) * ε`, where `n` is the size of the matrices. -/
theorem norm_det_sub_det_le {R : Type*} [SeminormedCommRing R] {A B : Matrix n n R} {c ε : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ c) (hB : ∀ i j, ‖B i j‖ ≤ c) (hAB : ∀ i j, ‖A i j - B i j‖ ≤ ε) :
    ‖A.det - B.det‖ ≤
      (Fintype.card n).factorial * Fintype.card n * c ^ (Fintype.card n - 1) * ε := by
  -- Each Leibniz term moves by at most `c ^ (n - 1) * (n * ε)`.
  have hterm (σ : Equiv.Perm n) :
      ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i - Equiv.Perm.sign σ • ∏ i, B (σ i) i‖ ≤
        c ^ (Fintype.card n - 1) * (Fintype.card n * ε) := by
    rw [← smul_sub, norm_units_zsmul]
    refine (TauCeti.norm_prod_sub_prod_le_pow_mul_sum_norm_sub _ (fun i _ ↦ hA _ _)
      (fun i _ ↦ hB _ _)).trans ?_
    rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩
    · simp
    have hc : 0 ≤ c := (norm_nonneg _).trans (hA i i)
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc _)
    simpa using sum_le_sum fun j (_ : j ∈ univ) ↦ hAB (σ j) j
  rw [det_apply, det_apply, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun σ _ ↦ hterm σ).trans_eq ?_)
  rw [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul]
  ring

/-- **The square of the norm of the determinant is Lipschitz on entrywise bounded matrices.** Over
a seminormed commutative ring, if the entries of `A` and `B` have norm at most `c` and those of
`A - B` norm at most `ε`, then
`|‖det A‖ ^ 2 - ‖det B‖ ^ 2| ≤ 2 * n! ^ 2 * n * c ^ (2 * n - 1) * ε`, where `n` is the size of the
matrices. -/
theorem abs_norm_det_sq_sub_le {R : Type*} [SeminormedCommRing R]
    {A B : Matrix n n R} {c ε : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ c) (hB : ∀ i j, ‖B i j‖ ≤ c)
    (hAB : ∀ i j, ‖A i j - B i j‖ ≤ ε) :
    |‖A.det‖ ^ 2 - ‖B.det‖ ^ 2| ≤
      2 * (Fintype.card n).factorial ^ 2 * Fintype.card n * c ^ (2 * Fintype.card n - 1) * ε := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  have hsub := (abs_norm_sub_norm_le A.det B.det).trans (norm_det_sub_det_le hA hB hAB)
  have hR := (abs_nonneg _).trans hsub
  have hmax : max |‖A.det‖| |‖B.det‖| ≤ (Fintype.card n).factorial * c ^ Fintype.card n := by
    simpa only [abs_norm] using max_le (norm_det_le_factorial_mul_pow_of_nonempty hA)
      (norm_det_le_factorial_mul_pow_of_nonempty hB)
  have hk : 2 * Fintype.card n - 1 = Fintype.card n - 1 + Fintype.card n := by omega
  calc _ ≤ |‖A.det‖ - ‖B.det‖| * (2 : ℕ) * max |‖A.det‖| |‖B.det‖| ^ (2 - 1) :=
        abs_pow_sub_pow_le _ _ 2
    _ ≤ (Fintype.card n).factorial * Fintype.card n * c ^ (Fintype.card n - 1) * ε * 2 *
          ((Fintype.card n).factorial * c ^ Fintype.card n) := by
        rw [Nat.cast_ofNat, pow_one]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hsub zero_le_two) hmax (by positivity)
          (mul_nonneg hR zero_le_two)
    _ = _ := by rw [hk, pow_add]; ring

end Matrix
