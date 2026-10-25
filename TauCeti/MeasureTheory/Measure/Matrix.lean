/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Almost-sure rank of matrices with a density

A rectangular real matrix sampled from a law absolutely continuous with respect to product
Lebesgue measure has maximal rank almost surely. More precisely, each fixed square submatrix
selected by embeddings has nonzero determinant almost surely. The determinant polynomial is
Mathlib's `Matrix.mvPolynomialX`, renamed along the selected coordinates; its zero locus is null
by `MvPolynomial.volume_setOfPred_eval_eq_zero`.

These results apply to matrices with dependent entries as well as independent ones, provided
the joint law has a density. Empty row, column, and minor index types are allowed.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]

/-- Every fixed square minor of a real matrix with an absolutely continuous law is nonzero
almost surely. The row and column embeddings need not preserve any ordering. -/
theorem ae_det_submatrix_ne_zero [DecidableEq l] (μ : Measure (m → n → ℝ))
    (hμ : μ ≪ volume)
    (r : l ↪ m) (c : l ↪ n) :
    ∀ᵐ A ∂μ, ((Matrix.of A).submatrix r c).det ≠ 0 := by
  classical
  let e : (l × l) ↪ (Σ _ : m, n) :=
    (r.prodMap c).trans (Equiv.sigmaEquivProd m n).symm.toEmbedding
  let P := MvPolynomial.rename e (Matrix.mvPolynomialX l l ℝ).det
  have hP : P ≠ 0 := by
    intro h
    apply Matrix.det_mvPolynomialX_ne_zero l ℝ
    apply MvPolynomial.rename_injective e e.injective
    simpa only [map_zero] using h
  have hflat : ∀ᵐ x : (Σ _ : m, n) → ℝ ∂volume,
      ((Matrix.of (Sigma.curry x)).submatrix r c).det ≠ 0 := by
    have hnull := compl_mem_ae_iff.mpr (P.volume_setOfPred_eval_eq_zero hP)
    filter_upwards [hnull] with x hx
    have heval : MvPolynomial.eval x P =
        ((Matrix.of (Sigma.curry x)).submatrix r c).det := by
      rw [MvPolynomial.eval_rename, Matrix.eval_det_mvPolynomialX]
      -- Both matrices definitionally have (i, j)-entry x ⟨r i, c j⟩.
      congr 1
    exact fun hzero => hx (heval.trans hzero)
  have h := (TauCeti.measurePreserving_piCurry (fun _ : m => fun _ : n =>
    (volume : Measure ℝ))).symm.quasiMeasurePreserving.ae hflat
  filter_upwards [hμ.ae_le h] with A hA
  simpa only [MeasurableEquiv.coe_piCurry_symm, Sigma.curry_uncurry] using hA

/-- A rectangular real matrix whose law is absolutely continuous with respect to product
Lebesgue measure has maximal rank almost surely, including when one index type is empty. -/
theorem ae_rank_eq_min (μ : Measure (m → n → ℝ)) (hμ : μ ≪ volume) :
    ∀ᵐ A ∂μ, (Matrix.of A).rank = min (Fintype.card m) (Fintype.card n) := by
  classical
  let k := min (Fintype.card m) (Fintype.card n)
  obtain ⟨r⟩ : Nonempty (Fin k ↪ m) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using min_le_left (Fintype.card m) (Fintype.card n))
  obtain ⟨c⟩ : Nonempty (Fin k ↪ n) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using min_le_right (Fintype.card m) (Fintype.card n))
  filter_upwards [μ.ae_det_submatrix_ne_zero hμ r c] with A hA
  apply le_antisymm (le_min (Matrix.of A).rank_le_card_height (Matrix.of A).rank_le_card_width)
  simpa only [Matrix.rank_of_det_ne_zero hA, Fintype.card_fin] using
    (Matrix.of A).rank_submatrix_le r c

end MeasureTheory.Measure
