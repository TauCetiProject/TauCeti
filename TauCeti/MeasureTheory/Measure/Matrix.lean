/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank.Closed
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix
public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Almost-sure rank of matrices with a density

A rectangular matrix over a measurable field, sampled from a law absolutely continuous with
respect to an atomless sigma-finite product reference measure, has maximal rank almost surely.
More precisely, each fixed square submatrix
selected by embeddings has nonzero determinant almost surely. The determinant polynomial is
Mathlib's `Matrix.mvPolynomialX`, renamed along the selected coordinates; its zero locus is null
by `MvPolynomial.volume_setOfPred_eval_eq_zero`.

In particular this applies to Lebesgue measure over both `ℝ` and `ℂ`. The results apply to
dependent entries as well as independent ones, provided the joint law has a density.
Empty row, column, and minor index types are allowed.

The exact-rank strata are measurable, and the maximal-rank conclusion is available both for
function-valued arrays and for the bundled `Matrix` type.
-/

public section

open MeasureTheory

namespace Matrix

/-- Matrices over a topological field of rank exactly `k` form a measurable set. -/
theorem measurableSet_setOfPred_rank_eq {m n K : Type*} [Finite m] [Fintype n]
    [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (k : ℕ) :
    MeasurableSet {A : Matrix m n K | A.rank = k} := by
  classical
  let _ := Fintype.ofFinite m
  cases k with
  | zero =>
      simpa only [Nat.le_zero] using
        (isClosed_setOfPred_rank_le (m := m) (n := n) (K := K) 0).measurableSet
  | succ k =>
      have hle :=
        (isClosed_setOfPred_rank_le (m := m) (n := n) (K := K) (k + 1)).measurableSet
      have hlt :=
        (isClosed_setOfPred_rank_le (m := m) (n := n) (K := K) k).measurableSet
      convert hle.inter hlt.compl using 1
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      omega

end Matrix

namespace MeasureTheory.Measure

variable {m n l K : Type*} [Fintype m] [Fintype n] [Fintype l]
  [Field K] [MeasureSpace K] [MeasurableSingletonClass K] [MeasurableAdd₂ K] [MeasurableMul₂ K]
  [SigmaFinite (volume : Measure K)]
  [NullSingletonClass (volume : Measure K)]

/-- Every fixed square minor of a matrix with an absolutely continuous law is nonzero
almost surely. The row and column embeddings need not preserve any ordering. -/
theorem ae_det_submatrix_ne_zero [DecidableEq l] (μ : Measure (m → n → K))
    (hμ : μ ≪ volume)
    (r : l ↪ m) (c : l ↪ n) :
    ∀ᵐ A ∂μ, ((Matrix.of A).submatrix r c).det ≠ 0 := by
  classical
  let e : (l × l) ↪ (Σ _ : m, n) :=
    (r.prodMap c).trans (Equiv.sigmaEquivProd m n).symm.toEmbedding
  let P := MvPolynomial.rename e (Matrix.mvPolynomialX l l K).det
  have hP : P ≠ 0 := by
    intro h
    apply Matrix.det_mvPolynomialX_ne_zero l K
    apply MvPolynomial.rename_injective e e.injective
    simpa only [map_zero] using h
  have hflat : ∀ᵐ x : (Σ _ : m, n) → K ∂volume,
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
    (volume : Measure K))).symm.quasiMeasurePreserving.ae hflat
  filter_upwards [hμ.ae_le h] with A hA
  simpa only [MeasurableEquiv.coe_piCurry_symm, Sigma.curry_uncurry] using hA

/-- A rectangular matrix whose law is absolutely continuous with respect to atomless product
volume has maximal rank almost surely, including when one index type is empty. -/
theorem ae_rank_eq_min (μ : Measure (m → n → K)) (hμ : μ ≪ volume) :
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

/-- A matrix whose law is absolutely continuous with respect to atomless product volume
has maximal rank almost surely, including when one index type is empty. -/
theorem ae_rank_eq_min_matrix (μ : Measure (Matrix m n K)) (hμ : μ ≪ volume) :
    ∀ᵐ X ∂μ, X.rank = min (Fintype.card m) (Fintype.card n) := by
  classical
  have hflat := ae_rank_eq_min
    (volume : Measure (m → n → K)) Measure.AbsolutelyContinuous.rfl
  have hmatrix := ((Matrix.volume_preserving_ofMeasurableEquiv m n K).symm
    (Matrix.ofMeasurableEquiv m n K)).quasiMeasurePreserving.ae hflat
  refine hμ.ae_le (hmatrix.mono fun X hX ↦ ?_)
  simpa only [Matrix.ofMeasurableEquiv_symm_apply, Equiv.apply_symm_apply] using hX

end MeasureTheory.Measure
