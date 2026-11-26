/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.NonBacktracking
public import TauCeti.LinearAlgebra.Matrix.Trace.NonBacktracking
public import TauCeti.Probability.RandomMatrix.SampleCovariance.Trace.Word
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Expected traces of bipartite non-backtracking walk matrices

For a rectangular matrix of independent centered entries, the expected traces of powers of
the row block of its Hermitian dilation's non-backtracking walk matrix are sums over closed
bipartite words. Only words that read each matrix position at least twice contribute. For
bounded entries, the magnitude of each remaining word's contribution is controlled by its
number of distinct positions and by the second moments of the entries.

These formulas reduce bounds on the trace moments to weighted counts of the bipartite words
`TauCeti.bipartiteNonbacktrackingWords`, whose reversals can occur only at joins of the
constituent walks. Those weighted counts are bounded by
`TauCeti.sum_pow_card_bipartiteEdge_mul_pow_le_of_nonbacktracking`.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294.
-/

public section

open Finset Matrix MeasureTheory TauCeti
open scoped ENNReal

namespace ProbabilityTheory.iIndepFun

open TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω}
  [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n] {X : Ω → Matrix p n 𝕜}

/-- The expected trace of a positive power of the row block is a sum over the closed bipartite
words `bipartiteNonbacktrackingWords`, which are non-backtracking within each walk and read
every position at least twice. For trace order r and walks of length 2(k + 1), the entries need
moments of order 2r(k + 1). -/
theorem integral_trace_pow_toBlocks₁₁_nonbacktrackingPow
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hcenter : ∀ i j, ∫ ω, X ω i j ∂P = 0) {r : ℕ} (hr : r ≠ 0) (k : ℕ)
    (hmom : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * (r * (k + 1) : ℕ)) P) :
    let m := r * (k + 1)
    ∫ ω, (((nonbacktrackingPow (fromBlocks 0 (X ω) (X ω)ᴴ 0) (2 * (k + 1))).toBlocks₁₁) ^ r).trace
      ∂P =
      ∑ uv ∈ bipartiteNonbacktrackingWords (α := p) (β := n) r k,
        ∫ ω, ∏ t : Fin m,
          X ω (uv.1 t) (uv.2 t) * star (X ω (uv.1 (finRotate m t)) (uv.2 t)) ∂P := by
  classical
  dsimp only
  simp_rw [trace_pow_toBlocks₁₁_nonbacktrackingPow _ _ hr, conjTranspose_apply]
  have hm : r * (k + 1) ≠ 0 := Nat.mul_ne_zero hr (Nat.succ_ne_zero k)
  rw [integral_finsetSum _ fun uv _ ↦ integrable_prod_apply_mul_star_apply hm hmom uv.1 uv.2]
  refine (Finset.sum_subset (fun uv huv ↦ ?_) fun uv huv hW ↦ ?_).symm
  · exact mem_filter.mpr ⟨mem_univ _, (mem_bipartiteNonbacktrackingWords.mp huv).1⟩
  -- A nonbacktracking word with an edge read only once has vanishing expectation.
  have hrep : ¬∀ a, ∃ b ≠ a, bipartiteEdge uv.1 uv.2 b = bipartiteEdge uv.1 uv.2 a :=
    fun h ↦ hW (mem_bipartiteNonbacktrackingWords.mpr ⟨(mem_filter.mp huv).2, h⟩)
  push Not at hrep
  obtain ⟨a, ha⟩ := hrep
  exact integral_prod_apply_mul_star_apply_eq_zero
    (fun i j ↦ (hmom i j).aemeasurable) hindep hcenter uv.1 uv.2
    fun b hb ↦ by_contra fun hba ↦ ha b hba hb

/-- With entries bounded by b and second absolute moments bounded by c, the expected trace
has norm at most the weighted number of the closed words `bipartiteNonbacktrackingWords`.
A word of half-length m with e distinct matrix positions receives weight
min(c, b²)^e * b^(2m - 2e). -/
theorem norm_integral_trace_pow_toBlocks₁₁_nonbacktrackingPow_le
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hmeas : ∀ i j, AEStronglyMeasurable (fun ω ↦ X ω i j) P)
    (hcenter : ∀ i j, ∫ ω, X ω i j ∂P = 0) {b c : ℝ}
    (hb : ∀ i j, ∀ᵐ ω ∂P, ‖X ω i j‖ ≤ b)
    (hc : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P ≤ c) {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    let m := r * (k + 1)
    ‖∫ ω, (((nonbacktrackingPow (fromBlocks 0 (X ω) (X ω)ᴴ 0) (2 * (k + 1))).toBlocks₁₁) ^ r).trace
      ∂P‖ ≤
      ∑ uv ∈ bipartiteNonbacktrackingWords (α := p) (β := n) r k,
        min c (b ^ 2) ^ #(univ.image (bipartiteEdge uv.1 uv.2)) *
          b ^ (2 * m - 2 * #(univ.image (bipartiteEdge uv.1 uv.2))) := by
  classical
  dsimp only
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rw [hindep.integral_trace_pow_toBlocks₁₁_nonbacktrackingPow hcenter hr k
    (fun i j ↦ .of_bound (hmeas i j) b (hb i j))]
  refine (norm_sum_le _ _).trans (sum_le_sum fun uv huv ↦ ?_)
  have hrepeat := (mem_bipartiteNonbacktrackingWords.mp huv).2
  refine norm_integral_prod_mul_star_le_of_no_singleton_edge
    hindep (fun _ ↦ (hmeas _ _).aemeasurable) hrepeat fun a ↦ ?_
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le'
    (two_le_card_filter_eq_of_no_singleton_fiber hrepeat _ (mem_image_of_mem _ (mem_univ a)))
  rw [hd, Nat.add_sub_cancel]
  exact integral_norm_pow_add_two_le (hb _ _) (hc _ _) d

end ProbabilityTheory.iIndepFun
