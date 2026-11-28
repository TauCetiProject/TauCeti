/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import TauCeti.Analysis.Calculus.IteratedFDeriv.Mul

/-!
# Smoothness of determinants and adjugates

The determinant of a square matrix is a polynomial in its entries, so a matrix-valued map whose
entries are `C^n` has a `C^n` determinant. This is the `C^n` counterpart of Mathlib's
`Continuous.matrix_det`, and holds at every regularity, including analytic regularity, globally
(`ContDiff.matrix_det`), on a set (`ContDiffOn.matrix_det`) and at a point
(`ContDiffAt.matrix_det`).

Each entry of the adjugate is the determinant of a matrix whose entries are entries of the
original matrix or constants, so the adjugate of such a map again has `C^n` entries
(`ContDiff.matrix_adjugate`, `ContDiffOn.matrix_adjugate` and `ContDiffAt.matrix_adjugate`), the
`C^n` counterpart of Mathlib's `Continuous.matrix_adjugate`.

The Leibniz expansion of the determinant also bounds its iterated derivatives by those of the
entries (`TauCeti.norm_iteratedFDeriv_det_le`), and likewise for the entries of the adjugate
(`TauCeti.norm_iteratedFDeriv_adjugate_apply_le`). Dividing by a determinant through the adjugate
is how a cutoff is divided by an invertible matrix symbol, as in microlocal elliptic regularity
for systems.
-/

public section

variable {𝕜 E 𝔸 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}
  {s : Set E}

/-- A matrix-valued map whose entries are `C^n` on a set has a determinant that is `C^n` there. -/
theorem ContDiffOn.matrix_det {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiffOn 𝕜 n (fun x ↦ M x i j) s) :
    ContDiffOn 𝕜 n (fun x ↦ (M x).det) s := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ ↦ contDiffOn_const.mul (contDiffOn_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map whose entries are `C^n` at a point has a determinant which is `C^n` there.
-/
theorem ContDiffAt.matrix_det {M : E → Matrix ι ι 𝔸} {x : E}
    (hM : ∀ i j, ContDiffAt 𝕜 n (fun y ↦ M y i j) x) : ContDiffAt 𝕜 n (fun y ↦ (M y).det) x := by
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ ↦ contDiffAt_const.mul (contDiffAt_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map with `C^n` entries has a `C^n` determinant. -/
theorem ContDiff.matrix_det {M : E → Matrix ι ι 𝔸} (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) :
    ContDiff 𝕜 n fun x ↦ (M x).det :=
  contDiffOn_univ.1 (ContDiffOn.matrix_det fun i j ↦ (hM i j).contDiffOn)

/-- A matrix-valued map whose entries are `C^n` on a set has an adjugate whose entries are `C^n`
there. -/
theorem ContDiffOn.matrix_adjugate {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiffOn 𝕜 n (fun x ↦ M x i j) s) (i j : ι) :
    ContDiffOn 𝕜 n (fun x ↦ (M x).adjugate i j) s := by
  simp only [Matrix.adjugate_apply]
  refine ContDiffOn.matrix_det fun k l ↦ ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hM k l

/-- A matrix-valued map whose entries are `C^n` at a point has an adjugate whose entries are `C^n`
there. -/
theorem ContDiffAt.matrix_adjugate {M : E → Matrix ι ι 𝔸} {x : E}
    (hM : ∀ i j, ContDiffAt 𝕜 n (fun y ↦ M y i j) x) (i j : ι) :
    ContDiffAt 𝕜 n (fun y ↦ (M y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  refine ContDiffAt.matrix_det fun k l ↦ ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffAt_const
  · exact hM k l

/-- A matrix-valued map with `C^n` entries has an adjugate with `C^n` entries. -/
theorem ContDiff.matrix_adjugate {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) (i j : ι) :
    ContDiff 𝕜 n fun x ↦ (M x).adjugate i j :=
  contDiffOn_univ.1 (ContDiffOn.matrix_adjugate (fun i j ↦ (hM i j).contDiffOn) i j)

namespace TauCeti

variable [NormOneClass 𝔸]

/-- **Derivative bounds for a determinant.** If the derivatives of order at most `k ≤ n` at `y` of
the `C^n` entries `M x i j` of a matrix-valued map are bounded by `C i j`, then those of its
determinant are bounded by `∑ σ, 2 ^ (k * card ι) ∏ i, C (σ i) i`, following the Leibniz expansion
of the determinant. -/
theorem norm_iteratedFDeriv_det_le {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) {k : ℕ} (hk : k ≤ n) {C : ι → ι → ℝ} {y : E}
    (hC : ∀ i j, ∀ l ≤ k, ‖iteratedFDeriv 𝕜 l (fun x ↦ M x i j) y‖ ≤ C i j) :
    ∀ l ≤ k, ‖iteratedFDeriv 𝕜 l (fun x ↦ (M x).det) y‖ ≤
      ∑ σ : Equiv.Perm ι, 2 ^ (k * Fintype.card ι) * ∏ i, C (σ i) i := by
  intro l hl
  have hdet : (fun x ↦ (M x).det) = ∑ σ : Equiv.Perm ι,
      fun x ↦ (Equiv.Perm.sign σ : ℤ) • ∏ i, M x (σ i) i := by
    ext x
    simp [Matrix.det_apply, Units.smul_def]
  have hl' : (l : WithTop ℕ∞) ≤ n := (Nat.cast_le.2 hl).trans hk
  rw [hdet, iteratedFDeriv_sum_apply fun σ _ ↦
    ((contDiff_prod fun i _ ↦ hM _ _).const_smul _).contDiffAt.of_le hl']
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ ↦ ?_)
  rw [iteratedFDeriv_const_smul_apply' ((contDiff_prod fun i _ ↦ hM _ _).contDiffAt.of_le hl')]
  have h := norm_iteratedFDeriv_prod_le_of_forall_le Finset.univ (fun i _ ↦ hM _ _) hk
    (fun i _ ↦ hC (σ i) i) l hl
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simpa [hσ] using h

/-- **Derivative bounds for an adjugate.** If the derivatives of order at most `k ≤ n` at `y` of
the `C^n` entries of a matrix-valued map are bounded by `X`, then those of every entry of its
adjugate are bounded by `(card ι)! 2 ^ (k * card ι) X ^ (card ι - 1)`: each term of the Leibniz
expansion of an entry of the adjugate has one constant factor. -/
theorem norm_iteratedFDeriv_adjugate_apply_le {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) {k : ℕ} (hk : k ≤ n) {X : ℝ} {y : E}
    (hX : ∀ i j, ∀ l ≤ k, ‖iteratedFDeriv 𝕜 l (fun x ↦ M x i j) y‖ ≤ X) (i j : ι) :
    ∀ l ≤ k, ‖iteratedFDeriv 𝕜 l (fun x ↦ (M x).adjugate i j) y‖ ≤
      (Fintype.card ι).factorial * 2 ^ (k * Fintype.card ι) * X ^ (Fintype.card ι - 1) := by
  intro l hl
  -- The adjugate is the determinant of `M` with its `j`-th row replaced by a constant row, whose
  -- derivatives are bounded by `1`.
  have hrow (a b : ι) : ∀ l ≤ k, ‖iteratedFDeriv 𝕜 l
      (fun x ↦ (M x).updateRow j (Pi.single i 1) a b) y‖ ≤ if a = j then 1 else X := by
    intro l hl
    by_cases h : a = j
    · simp only [h, Matrix.updateRow_self, ↓reduceIte]
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · by_cases hb : b = i <;> simp [hb]
      · simp [iteratedFDeriv_const_of_ne hl0.ne']
    · simpa [h] using hX a b l hl
  simp_rw [Matrix.adjugate_apply]
  refine (norm_iteratedFDeriv_det_le (fun a b ↦ ?_) hk hrow l hl).trans_eq ?_
  · by_cases h : a = j
    · simp [h, contDiff_const]
    · simpa [h] using hM a b
  -- Exactly one factor of each Leibniz term comes from the constant row.
  have hprod (σ : Equiv.Perm ι) :
      ∏ a, (if σ a = j then (1 : ℝ) else X) = X ^ (Fintype.card ι - 1) := by
    rw [Equiv.prod_comp σ (fun a ↦ if a = j then (1 : ℝ) else X)]
    simp [Finset.prod_ite, Finset.filter_ne', Finset.card_erase_of_mem]
  simp only [hprod, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  ring

end TauCeti
