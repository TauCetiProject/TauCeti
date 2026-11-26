/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.LapMatrix.Eigenvalues
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Combinatorics.SimpleGraph.LapMatrix.Basic

/-!
# Laplacian eigenvalues of the complement

On a graph with `n > 0` vertices, the decreasing Laplacian spectrum of the complement is
`n - νₙ₋₁, …, n - ν₁, 0`, where the `νᵢ` are the decreasing Laplacian eigenvalues of the
original graph. The largest Laplacian eigenvalue of the original graph is bounded by `n`,
with equality exactly when its complement is disconnected.

The proof adds the all-ones matrix to the complement Laplacian, then uses rank-one interlacing
and equality of the sums of the corresponding eigenvalues after removing one entry from each
list.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer Universitext (2012),
  §1.3.2 and §3.9.
-/

public section

open Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Laplacian spectrum of the complement without its final zero, indexed by
`castSucc` into the complement's spectrum and by reversed `succ` into the original spectrum. -/
private theorem lapEigenvalues_compl_castSucc {m : ℕ} (hm : Fintype.card V = m + 1)
    (k : Fin m) :
    Gᶜ.lapEigenvalues (k.castSucc.cast hm.symm) =
      Fintype.card V - G.lapEigenvalues (k.succ.cast hm.symm).rev := by
  let n : ℝ := Fintype.card V
  let A : Matrix V V ℝ := -(G.lapMatrix ℝ) + n • 1
  have hG := G.isHermitian_lapMatrix ℝ
  have hA : A.IsHermitian := hG.neg.add (isHermitian_one.smul (R := ℝ) (k := n) rfl)
  have hC := Gᶜ.isHermitian_lapMatrix ℝ
  have hdiff : A - Gᶜ.lapMatrix ℝ = Matrix.of 1 := by
    have hsum := sub_eq_iff_eq_add.mp (G.lapMatrix_add_lapMatrix_compl ℝ).symm
    dsimp [A, n]
    rw [Nat.cast_smul_eq_nsmul, nsmul_one, hsum]
    abel
  have hrank : (A - Gᶜ.lapMatrix ℝ).rank ≤ 1 := by
    rw [hdiff]
    have hone : (Matrix.of 1 : Matrix V V ℝ) = vecMulVec (1 : V → ℝ) (1 : V → ℝ) := by
      ext v w
      simp [Matrix.of_apply, Matrix.vecMulVec]
    rw [hone]
    exact Matrix.rank_vecMulVec_le _ _
  have hreflect (i : Fin (Fintype.card V)) : hA.eigenvalues₀ i = n - G.lapEigenvalues i.rev := by
    rw [hG.neg.eigenvalues₀_add_smul_one n hA, Pi.add_apply, hG.eigenvalues₀_neg,
      lapEigenvalues_def]
    abel
  let e : Fin (m + 1) ≃ Fin (Fintype.card V) := Fin.castOrderIso hm.symm
  have hfirst : hA.eigenvalues₀ (e 0) = n := by
    rw [hreflect, G.lapEigenvalues_eq_zero_of_add_one_eq, sub_zero]
    simp [e, Fin.val_rev, hm]
  have hlast : hC.eigenvalues₀ (e (Fin.last m)) = 0 := by
    rw [← lapEigenvalues_def]
    exact Gᶜ.lapEigenvalues_eq_zero_of_add_one_eq (by simpa [e] using hm.symm)
  -- Rank-one interlacing gives a pointwise inequality between the two tails. Their sums agree
  -- because the trace difference is exactly the first eigenvalue removed from `A`.
  have hle (j : Fin m) : hA.eigenvalues₀ (e j.succ) ≤ hC.eigenvalues₀ (e j.castSucc) :=
    hA.eigenvalues₀_le_of_rank_sub_le hC hrank (by simp [e])
  have htrace : (∑ j, hA.eigenvalues₀ j) - (∑ j, hC.eigenvalues₀ j) = n := by
    rw [hA.sum_eigenvalues₀_eq_re_trace, hC.sum_eigenvalues₀_eq_re_trace,
      RCLike.re_to_real, RCLike.re_to_real, ← Matrix.trace_sub, hdiff]
    simp [Matrix.trace, n]
  rw [← e.sum_comp hA.eigenvalues₀, ← e.sum_comp hC.eigenvalues₀,
    Fin.sum_univ_succ, Fin.sum_univ_castSucc, hfirst, hlast, add_zero] at htrace
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ hle j)).mp (by linarith)
  rw [lapEigenvalues_def]
  exact (heq k (Finset.mem_univ _)).symm.trans (hreflect _)

/-- The sorted Laplacian eigenvalues of the complement, before the final zero, are
those of the original graph before its final zero, reversed and subtracted from the
number of vertices (Brouwer–Haemers, §1.3.2). -/
theorem lapEigenvalues_compl {i j : Fin (Fintype.card V)}
    (h : (i : ℕ) + j + 2 = Fintype.card V) :
    Gᶜ.lapEigenvalues i = Fintype.card V - G.lapEigenvalues j := by
  have hn : Fintype.card V ≠ 0 := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let k : Fin m := ⟨i, by omega⟩
  have hi : k.castSucc.cast hm.symm = i := Fin.ext rfl
  have hj : (k.succ.cast hm.symm).rev = j := by
    apply Fin.ext
    simp [Fin.val_rev, k]
    omega
  simpa only [hi, hj] using G.lapEigenvalues_compl_castSucc hm k

/-- On at least two vertices, the largest Laplacian eigenvalue of a graph and the algebraic
connectivity of its complement sum to the vertex count. -/
theorem largestLapEigenvalue_add_algebraicConnectivity_compl [Nonempty V]
    (h : 2 ≤ Fintype.card V) :
    G.largestLapEigenvalue + Gᶜ.algebraicConnectivity = Fintype.card V := by
  rw [G.largestLapEigenvalue_def, Gᶜ.algebraicConnectivity_of_two_le h,
    G.lapEigenvalues_compl (j := ⟨0, Fintype.card_pos⟩) (by simp; omega)]
  abel

/-- On a single vertex, the largest Laplacian eigenvalue is strictly below the vertex count. -/
private theorem largestLapEigenvalue_lt_card_of_lt_two [Nonempty V] (h : Fintype.card V < 2) :
    G.largestLapEigenvalue < Fintype.card V := by
  have hn := Fintype.card_pos (α := V)
  rw [G.largestLapEigenvalue_def, G.lapEigenvalues_eq_zero_of_add_one_eq]
  · exact_mod_cast hn
  · simp
    omega

/-- The largest Laplacian eigenvalue of a finite simple graph is at most its vertex count. -/
theorem largestLapEigenvalue_le_card [Nonempty V] :
    G.largestLapEigenvalue ≤ Fintype.card V := by
  by_cases h : 2 ≤ Fintype.card V
  · linarith [G.largestLapEigenvalue_add_algebraicConnectivity_compl h,
      Gᶜ.algebraicConnectivity_nonneg]
  · exact (G.largestLapEigenvalue_lt_card_of_lt_two (by omega)).le

/-- The largest Laplacian eigenvalue equals the vertex count exactly when the complement is
disconnected (Brouwer–Haemers, §3.9). -/
theorem largestLapEigenvalue_eq_card_iff_not_connected_compl [Nonempty V] :
    G.largestLapEigenvalue = Fintype.card V ↔ ¬ Gᶜ.Connected := by
  by_cases h : 2 ≤ Fintype.card V
  · rw [← Gᶜ.algebraicConnectivity_pos_iff_connected h]
    have := G.largestLapEigenvalue_add_algebraicConnectivity_compl h
    have := Gᶜ.algebraicConnectivity_nonneg
    constructor <;> intro h' <;> linarith
  · have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    simp [(G.largestLapEigenvalue_lt_card_of_lt_two (by omega)).ne,
      Connected.of_subsingleton (G := Gᶜ)]

end SimpleGraph
