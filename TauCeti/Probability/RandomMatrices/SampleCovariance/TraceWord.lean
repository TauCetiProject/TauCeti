/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Combinatorics.TraceWord.Bipartite
public import TauCeti.LinearAlgebra.Matrix.Trace.Pow
public import TauCeti.Probability.Independence.Integration

/-!
# Trace words of sample covariance matrices

The moment method for the Marchenko–Pastur law expands the expected moment
`E trace (X Xᴴ) ^ k` of a random `p × n` matrix `X` into a sum over the closed bipartite words
`u 0, v 0, u 1, v 1, …, v (k - 1), u 0` alternating between row indices `u : Fin k → p` and
column indices `v : Fin k → n` (`Matrix.trace_mul_conjTranspose_pow_eq_sum_prod`). The word reads
the entry `X (u t) (v t)` and the conjugate entry `star (X (u (t + 1)) (v t))` for each `t`; the
positions it reads are `TauCeti.bipartiteEdge u v`.

When the entries are independent and centred, a word reading some position exactly once has
expectation zero: that entry, or its conjugate, is independent of all the other factors and has
mean zero. Consequently only the words reading each of their positions at least twice contribute
to the expected moment. Such a word visits at most `k + 1` row and column indices
(`TauCeti.card_image_add_card_image_le_add_one_of_no_singleton_edge`), which is what makes the
words with fewer indices negligible after normalization. Neither identical distribution nor any
moment condition beyond integrability of the products is needed for this reduction.

## Main results

* `TauCeti.Probability.integral_prod_apply_mul_star_apply_eq_zero`: for independent centred
  entries, a bipartite word reading some position exactly once has expectation zero.
* `TauCeti.Probability.integrable_prod_apply_mul_star_apply`: for entries in `L²ᵏ`, the product
  along a bipartite word of half-length `k` is integrable.
* `TauCeti.Probability.integral_trace_mul_conjTranspose_pow`: for independent centred entries in
  `L²ᵏ`, the expected trace of `(X Xᴴ) ^ k` is the sum, over the bipartite words reading each of
  their positions at least twice, of their expectations.
* `TauCeti.Probability.integral_trace_sampleCovariance_pow`: the same expansion for the sample
  covariance matrix `X Xᴴ / n`.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.2.1.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, the analogous reduction for Wigner matrices.
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω}
  {X : Ω → Matrix p n 𝕜}

/-- The function applied to the entry read at a step of a bipartite word: the entry itself on
the steps `inl t` and its conjugate on the steps `inr t`. -/
private def readFactor {k : ℕ} : Fin k ⊕ Fin k → 𝕜 → 𝕜 :=
  Sum.elim (fun _ ↦ id) fun _ ↦ star

private theorem measurable_readFactor {k : ℕ} (s : Fin k ⊕ Fin k) :
    Measurable (readFactor (𝕜 := 𝕜) s) := by
  cases s
  · exact measurable_id
  · exact continuous_star.measurable

/-- The product along a bipartite word, as a product over its steps of the factors applied to
the entries at the positions they read. -/
private theorem prod_mul_star_eq_prod_readFactor {k : ℕ} (A : Matrix p n 𝕜) (u : Fin k → p)
    (v : Fin k → n) :
    ∏ t, A (u t) (v t) * star (A (u (finRotate k t)) (v t)) =
      ∏ s, readFactor s (A (bipartiteEdge u v s).1 (bipartiteEdge u v s).2) := by
  simp [Fintype.prod_sum_type, readFactor, Finset.prod_mul_distrib]

/-- **Singleton positions vanish.** Let the entries of a random rectangular matrix `X` be
independent and centred. If a bipartite word `u, v` reads some position at exactly one of its
steps, then the product of the entries `X (u t) (v t)` and conjugate entries
`star (X (u (t + 1)) (v t))` along the word has expectation zero. -/
theorem integral_prod_apply_mul_star_apply_eq_zero [Finite p] [Finite n]
    (hXm : ∀ i j, AEMeasurable (fun ω ↦ X ω i j) P)
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hX : ∀ i j, ∫ ω, X ω i j ∂P = 0) {k : ℕ} (u : Fin k → p) (v : Fin k → n)
    {a : Fin k ⊕ Fin k} (ha : ∀ b, bipartiteEdge u v b = bipartiteEdge u v a → b = a) :
    ∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P = 0 := by
  classical
  have := Fintype.ofFinite p
  have := Fintype.ofFinite n
  simp_rw [prod_mul_star_eq_prod_readFactor]
  rw [hindep.integral_fun_prod_comp_fiberwise (fun ij ↦ hXm ij.1 ij.2) (bipartiteEdge u v)
    measurable_readFactor]
  refine Finset.prod_eq_zero (Finset.mem_univ (bipartiteEdge u v a)) ?_
  have hfiber : ({b | bipartiteEdge u v b = bipartiteEdge u v a} : Finset _) = {a} := by
    ext b
    simpa using ⟨ha b, fun h ↦ h ▸ rfl⟩
  simp only [hfiber, Finset.prod_singleton]
  cases a with
  | inl t => exact hX _ _
  | inr t =>
    simp only [readFactor, Sum.elim_inr, RCLike.star_def]
    rw [integral_conj, hX, map_zero]

/-- If the entries of a random rectangular matrix `X` lie in `L²ᵏ`, `k ≠ 0`, then the product of
the entries `X (u t) (v t)` and conjugate entries `star (X (u (t + 1)) (v t))` along a bipartite
word of half-length `k` is integrable. -/
theorem integrable_prod_apply_mul_star_apply {k : ℕ} (hk : k ≠ 0)
    (hXk : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P) (u : Fin k → p) (v : Fin k → n) :
    Integrable (fun ω ↦ ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t))) P := by
  simp_rw [prod_mul_star_eq_prod_readFactor]
  have hfactor (s : Fin k ⊕ Fin k) : MemLp (fun ω ↦ readFactor s
      (X ω (bipartiteEdge u v s).1 (bipartiteEdge u v s).2)) (2 * k) P := by
    cases s
    · exact hXk _ _
    · exact (hXk _ _).star
  have hexponent : (∑ _ : Fin k ⊕ Fin k, (2 * k : ℝ≥0∞)⁻¹) = 1 := by
    have h2k : (2 * k : ℝ≥0∞) ≠ 0 := by simpa using hk
    simpa [nsmul_eq_mul, ← two_mul] using
      ENNReal.mul_inv_cancel h2k (ENNReal.mul_ne_top (by simp) (by simp))
  simpa [hexponent, memLp_one_iff_integrable] using
    (MemLp.fun_prod (s := Finset.univ) fun s _ ↦ hfactor s)

/-- **Trace-word expansion of sample covariance moments.** Let the entries of a random
rectangular matrix `X` be independent, centred and in `L²ᵏ`, `k ≠ 0`. Then the expected trace of
`(X Xᴴ) ^ k` is the sum, over the bipartite words `u, v` that read each of their positions at
least twice, of the expected products of the entries `X (u t) (v t)` and conjugate entries
`star (X (u (t + 1)) (v t))` along the word: the words reading some position exactly once
contribute zero. -/
theorem integral_trace_mul_conjTranspose_pow [Fintype p] [DecidableEq p] [Fintype n]
    [DecidableEq n]
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hX : ∀ i j, ∫ ω, X ω i j ∂P = 0) {k : ℕ} (hk : k ≠ 0)
    (hXk : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P) :
    ∫ ω, ((X ω * (X ω)ᴴ) ^ k).trace ∂P =
      ∑ u : Fin k → p, ∑ v : Fin k → n with
        ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a,
        ∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P := by
  have hint := integrable_prod_apply_mul_star_apply hk hXk
  simp_rw [trace_mul_conjTranspose_pow_eq_sum_prod _ hk]
  rw [integral_finsetSum _ fun u _ ↦ integrable_finsetSum _ fun v _ ↦ hint u v]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [integral_finsetSum _ fun v _ ↦ hint u v]
  refine (Finset.sum_filter_of_ne fun v _ hv a ↦ ?_).symm
  by_contra! h
  exact hv (integral_prod_apply_mul_star_apply_eq_zero
    (fun i j ↦ (hXk i j).aestronglyMeasurable.aemeasurable) hindep hX u v
    fun b hb ↦ by_contra fun hba ↦ h b hba hb)

/-- **Trace-word expansion of sample covariance moments**, normalized: under the hypotheses of
`TauCeti.Probability.integral_trace_mul_conjTranspose_pow`, the expected trace of the `k`-th
power of the sample covariance matrix `X Xᴴ / n` is `n⁻ᵏ` times the sum, over the bipartite
words reading each of their positions at least twice, of their expectations. -/
theorem integral_trace_sampleCovariance_pow [Fintype p] [DecidableEq p] [Fintype n]
    [DecidableEq n]
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hX : ∀ i j, ∫ ω, X ω i j ∂P = 0) {k : ℕ} (hk : k ≠ 0)
    (hXk : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P) :
    ∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P =
      (Fintype.card n : 𝕜)⁻¹ ^ k * ∑ u : Fin k → p, ∑ v : Fin k → n with
        ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a,
        ∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P := by
  simp_rw [sampleCovariance_def, smul_pow, trace_smul, RCLike.real_smul_eq_coe_mul]
  rw [integral_const_mul, integral_trace_mul_conjTranspose_pow hindep hX hk hXk]
  simp

end TauCeti.Probability
