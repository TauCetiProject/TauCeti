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
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Data.Fintype.SmallRange
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# Trace words of sample covariance matrices

The moment method for the Marchenko–Pastur law expands the expected moment
`E trace (X Xᴴ) ^ k` of a random `p × n` matrix `X` into a sum over the closed bipartite words
`u 0, v 0, u 1, v 1, …, v (k - 1), u 0` alternating between row indices `u : Fin k → p` and
column indices `v : Fin k → n` (`Matrix.trace_mul_conjTranspose_pow_eq_sum_prod`). The word reads
the entry `X (u t) (v t)` and the conjugate entry `star (X (u (t + 1)) (v t))` for each `t`; the
positions it reads are `TauCeti.bipartiteEdge u v`.

When the entries are independent and have zero integrals, the totalized Bochner integral of a
word reading some position exactly once vanishes. For integrable word products this gives
expectation zero, so only the words reading each position at least twice contribute to the
expected moment. Such a word visits at most `k + 1` row and column indices
(`TauCeti.card_image_add_card_image_le_add_one_of_no_singleton_edge`).
To show that words with fewer indices are asymptotically negligible after normalization,
one also needs control of the word moments across dimensions.

Under a bound `B` on the `2k`th absolute moments of the entries, every word contributes at most
`B`, and there are at most `|p|ᵃ aᵏ |n|ᵇ bᵏ` words using at most `a` rows and `b` columns. These
estimates suppress the words with fewer than `k + 1` row and column indices as the dimensions grow
with `p / n` bounded.

## Main results

* `TauCeti.Probability.integral_prod_apply_mul_star_apply_eq_zero`: for independent entries with
  zero integrals, a bipartite word reading some position exactly once has integral zero.
* `TauCeti.Probability.integrable_prod_apply_mul_star_apply`: for entries in `L²ᵏ`, the product
  along a bipartite word of half-length `k` is integrable.
* `TauCeti.Probability.integral_trace_mul_conjTranspose_pow`: for independent centred entries in
  `L²ᵏ`, the expected trace of `(X Xᴴ) ^ k` is the sum, over the bipartite words reading each of
  their positions at least twice, of their expectations.
* `TauCeti.Probability.integral_trace_sampleCovariance_pow`: the same expansion for the sample
  covariance matrix `X Xᴴ / n`.
* `TauCeti.Probability.memLp_trace_pow_sampleCovariance` and
  `TauCeti.Probability.integrable_trace_pow_sampleCovariance`: on a finite measure space with
  entries in `L^(q * 2k)`, the trace of the `k`th power of the sample covariance matrix lies in
  `L^q`; with entries in `L^(2k)` it is integrable.
* `TauCeti.Probability.norm_integral_prod_mul_star_le` and
  `TauCeti.Probability.norm_sum_integral_prod_mul_star_le`: moment bounds for one bipartite word
  and for a family of bipartite words with a bounded number of rows and columns.
* `TauCeti.Probability.norm_inv_mul_integral_trace_pow_sampleCovariance_sub_sum_le`: for
  independent centred entries whose `2k`th absolute moments are bounded by `B`, the normalized
  moment `(card p)⁻¹ E tr Sᵏ` minus the contribution of the words with `k + 1` row and column
  indices has norm at most `k^(2k) B ∑_{a<k} (p/n)ᵃ / n`.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.2.1.
* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, second
  edition, Springer (2010), §3.1.2: the moment method for the Marchenko–Pastur law.
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
independent with zero Bochner integrals. If a bipartite word `u, v` reads some position exactly
once, then the product of the entries `X (u t) (v t)` and conjugate entries
`star (X (u (t + 1)) (v t))` along the word has totalized Bochner integral zero.
In particular, an integrable word product has expectation zero. -/
theorem integral_prod_apply_mul_star_apply_eq_zero
    (hXm : ∀ i j, AEMeasurable (fun ω ↦ X ω i j) P)
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hX : ∀ i j, ∫ ω, X ω i j ∂P = 0) {k : ℕ} (u : Fin k → p) (v : Fin k → n)
    {a : Fin k ⊕ Fin k} (ha : ∀ b, bipartiteEdge u v b = bipartiteEdge u v a → b = a) :
    ∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P = 0 := by
  classical
  simp_rw [prod_mul_star_eq_prod_readFactor]
  refine hindep.integral_fun_prod_comp_eq_zero (fun ij ↦ hXm ij.1 ij.2) measurable_readFactor
    ha ?_
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

section MomentBounds

open Finset

variable {k : ℕ}

private theorem norm_readFactor (s : Fin k ⊕ Fin k) (z : 𝕜) : ‖readFactor s z‖ = ‖z‖ := by
  cases s <;> simp [readFactor]

/-- A bipartite word of half-length `k` has `2 * k` steps. -/
private theorem card_univ_sum_fin : #(univ : Finset (Fin k ⊕ Fin k)) = 2 * k := by
  simp [two_mul]

/-- The Hölder exponent of a product of `m ≠ 0` factors in `L^(q * m)` is `q`. -/
private theorem inv_natCast_mul_inv_mul_natCast {m : ℕ} (hm : m ≠ 0) (q : ℝ≥0∞) :
    ((m : ℝ≥0∞) * (q * m)⁻¹)⁻¹ = q := by
  have hm' : (m : ℝ≥0∞) ≠ 0 := by simpa
  rw [ENNReal.mul_inv (.inr (by simp)) (.inr hm'), mul_left_comm,
    ENNReal.mul_inv_cancel hm' (by simp), mul_one, inv_inv]

/-- A bound on the `2k`th absolute moments of the entries of a matrix with a nonempty set of
positions is nonnegative. -/
private theorem nonneg_of_integral_norm_pow_le [Nonempty p] [Nonempty n] {B : ℝ}
    (hB : ∀ a b, ∫ ω, ‖X ω a b‖ ^ (2 * k) ∂P ≤ B) : 0 ≤ B :=
  (integral_nonneg fun ω ↦ by positivity).trans (hB (Classical.arbitrary p) (Classical.arbitrary n))

/-- On a finite measure space, the product along a bipartite word with entries in `L^(q * 2k)`
lies in `L^q`. -/
private theorem memLp_prod_mul_star [IsFiniteMeasure P] {q : ℝ≥0∞}
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (q * (2 * k : ℕ)) P) (u : Fin k → p) (v : Fin k → n) :
    MemLp (fun ω ↦ ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t))) q P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [memLp_const]
  simp_rw [prod_mul_star_eq_prod_readFactor]
  have h := MemLp.fun_prod (s := (univ : Finset (Fin k ⊕ Fin k))) (p := fun _ ↦ q * (2 * k : ℕ))
    (f := fun s ω ↦ readFactor s (X ω (bipartiteEdge u v s).1 (bipartiteEdge u v s).2))
    fun s _ ↦ by
      cases s
      · exact hX _ _
      · exact (hX _ _).star
  rwa [sum_const, card_univ_sum_fin, nsmul_eq_mul,
    inv_natCast_mul_inv_mul_natCast (by omega)] at h

/-- On a finite measure space, the trace of the `k`th power of the sample covariance matrix of
`X` lies in `L^q` whenever all entries of `X` lie in `L^(q * 2k)`. Neither independence nor
centering is required, and `k = 0` is included. -/
theorem memLp_trace_pow_sampleCovariance [Fintype p] [Fintype n] [DecidableEq p]
    [IsFiniteMeasure P] {q : ℝ≥0∞}
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (q * (2 * k : ℕ)) P) :
    MemLp (fun ω ↦ ((X ω).sampleCovariance ^ k).trace) q P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [memLp_const]
  simp_rw [Matrix.trace_pow_sampleCovariance_eq_sum_prod _ hk]
  exact (memLp_finsetSum _ fun u _ ↦ memLp_finsetSum _ fun v _ ↦
    memLp_prod_mul_star hX u v).const_mul _

/-- On a finite measure space, the trace of the `k`th power of the sample covariance matrix of
`X` is integrable whenever all entries of `X` lie in `L^(2k)`. Neither independence nor centering
is required, and `k = 0` is included. -/
theorem integrable_trace_pow_sampleCovariance [Fintype p] [Fintype n] [DecidableEq p]
    [IsFiniteMeasure P]
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P) :
    Integrable (fun ω ↦ ((X ω).sampleCovariance ^ k).trace) P :=
  memLp_one_iff_integrable.mp (memLp_trace_pow_sampleCovariance (by simpa using hX))

/-- A bound `B` on the `2k`th absolute moments of the entries of `X` bounds the expected product
along every bipartite word of half-length `k ≠ 0`. The positions read may repeat, and no
independence or centering is required. -/
theorem norm_integral_prod_mul_star_le (hk : k ≠ 0) {B : ℝ}
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P)
    (hB : ∀ a b, ∫ ω, ‖X ω a b‖ ^ (2 * k) ∂P ≤ B) (u : Fin k → p) (v : Fin k → n) :
    ‖∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P‖ ≤ B := by
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  simp_rw [prod_mul_star_eq_prod_readFactor]
  calc
    _ ≤ ((2 * k : ℕ) : ℝ)⁻¹ * ∑ s : Fin k ⊕ Fin k,
        ∫ ω, ‖readFactor s (X ω (bipartiteEdge u v s).1 (bipartiteEdge u v s).2)‖ ^ (2 * k) ∂P := by
      simpa only [card_univ_sum_fin] using norm_integral_prod_le_inv_card_mul_sum_integral_norm_pow
        (fun s ω ↦ readFactor s (X ω (bipartiteEdge u v s).1 (bipartiteEdge u v s).2))
        univ_nonempty (fun s _ ↦ by
          rw [card_univ_sum_fin]
          simpa [norm_readFactor] using (hX _ _).integrable_norm_pow (by omega))
    _ ≤ ((2 * k : ℕ) : ℝ)⁻¹ * ∑ _s : Fin k ⊕ Fin k, B := by
      gcongr with s
      simpa [norm_readFactor] using hB _ _
    _ = B := by
      rw [sum_const, card_univ_sum_fin, nsmul_eq_mul]
      field_simp

/-- Under a bound `B` on the `2k`th absolute moments of the entries of `X`, a family `S` of
bipartite words of half-length `k ≠ 0`, each using at most `a` rows and at most `b` columns, has
total expected product of norm at most `|p|ᵃ aᵏ |n|ᵇ bᵏ B`. No independence or centering is
required. -/
theorem norm_sum_integral_prod_mul_star_le [Fintype p] [Fintype n] [DecidableEq p]
    [DecidableEq n] (hk : k ≠ 0) {B : ℝ}
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P)
    (hB : ∀ a b, ∫ ω, ‖X ω a b‖ ^ (2 * k) ∂P ≤ B) {a b : ℕ}
    (S : Finset ((Fin k → p) × (Fin k → n)))
    (hS : ∀ w ∈ S, #(univ.image w.1) ≤ a ∧ #(univ.image w.2) ≤ b) :
    ‖∑ w ∈ S, ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P‖ ≤
      (Fintype.card p : ℝ) ^ a * (a : ℝ) ^ k * ((Fintype.card n : ℝ) ^ b * (b : ℝ) ^ k) * B := by
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  -- If an index type is empty, there are no words and the bound has a vanishing factor.
  rcases isEmpty_or_nonempty p with hp | hp
  · rw [S.eq_empty_of_isEmpty, sum_empty, norm_zero]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [hk]
    · simp [ha.ne']
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [S.eq_empty_of_isEmpty, sum_empty, norm_zero]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [hk]
    · simp [hb.ne']
  have hB0 := nonneg_of_integral_norm_pow_le hB
  have hcard : (#S : ℝ) ≤ (Fintype.card p : ℝ) ^ a * (a : ℝ) ^ k *
      ((Fintype.card n : ℝ) ^ b * (b : ℝ) ^ k) := by
    have hsub : S ⊆ ({f : Fin k → p | #(univ.image f) ≤ a} : Finset _) ×ˢ
        ({f : Fin k → n | #(univ.image f) ≤ b} : Finset _) := fun w hw ↦ by
      simpa using hS w hw
    have h₁ := card_filter_card_image_le (α := Fin k) (β := p) a
    have h₂ := card_filter_card_image_le (α := Fin k) (β := n) b
    simp only [Fintype.card_fin] at h₁ h₂
    have := ((card_le_card hsub).trans_eq (card_product _ _)).trans (Nat.mul_le_mul h₁ h₂)
    exact_mod_cast this
  calc
    _ ≤ ∑ w ∈ S, ‖∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _w ∈ S, B := sum_le_sum fun w _ ↦ norm_integral_prod_mul_star_le hk hX hB w.1 w.2
    _ = #S * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr

/-- Bipartite words using at most `k` rows and columns in total, grouped by their number `a + 1`
of rows, have total expected product bounded by the sum over `a < k` of the bounds of
`norm_sum_integral_prod_mul_star_le` for `a + 1` rows and `k - (a + 1)` columns. -/
private theorem norm_sum_integral_prod_mul_star_le_of_card_image_add_card_image_le [Fintype p]
    [Fintype n] [DecidableEq p] [DecidableEq n] (hk : k ≠ 0) {B : ℝ}
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P)
    (hB : ∀ a b, ∫ ω, ‖X ω a b‖ ^ (2 * k) ∂P ≤ B) (R : Finset ((Fin k → p) × (Fin k → n)))
    (hR : ∀ w ∈ R, #(univ.image w.1) + #(univ.image w.2) ≤ k) :
    ‖∑ w ∈ R, ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P‖ ≤
      ∑ a ∈ range k, (Fintype.card p : ℝ) ^ (a + 1) * ((a + 1 : ℕ) : ℝ) ^ k *
        ((Fintype.card n : ℝ) ^ (k - (a + 1)) * ((k - (a + 1) : ℕ) : ℝ) ^ k) * B := by
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hmaps : ∀ w ∈ R, #(univ.image w.1) ∈ range (k + 1) := fun w hw ↦
    mem_range.2 (by have := hR w hw; omega)
  -- Group the words by their number of rows, which is positive.
  rw [← sum_fiberwise_of_maps_to hmaps, sum_range_succ', sum_eq_zero (s := R.filter _), add_zero]
  · refine (norm_sum_le _ _).trans (sum_le_sum fun a _ ↦ ?_)
    refine norm_sum_integral_prod_mul_star_le hk hX hB _ fun w hw ↦ ?_
    obtain ⟨hwR, hwa⟩ := mem_filter.1 hw
    have := hR w hwR
    omega
  · intro w hw
    exact absurd (mem_filter.1 hw).2 (univ_nonempty.image _).card_pos.ne'

/-- **Nonleading bipartite words are negligible.** Let the entries of `X` be independent and
centred with `2k`th absolute moments bounded by `B`, `k ≠ 0`. Subtracting from the expected
normalized trace `(card p)⁻¹ E tr Sᵏ` of the sample covariance matrix `S = X Xᴴ / n` the
contribution of the bipartite words that read each of their positions at least twice and visit
the maximal number `k + 1` of rows and columns leaves a remainder of norm at most
`k^(2k) B ∑_{a < k} (p / n)ᵃ / n`. This is `O(n⁻¹)` when the ratio `p / n` stays bounded. -/
theorem norm_inv_mul_integral_trace_pow_sampleCovariance_sub_sum_le [Fintype p] [Fintype n]
    [DecidableEq p] [DecidableEq n] [Nonempty p] (hk : k ≠ 0) {B : ℝ}
    (hindep : iIndepFun (fun e : p × n ↦ fun ω ↦ X ω e.1 e.2) P)
    (hzero : ∀ a b, ∫ ω, X ω a b ∂P = 0)
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P)
    (hB : ∀ a b, ∫ ω, ‖X ω a b‖ ^ (2 * k) ∂P ≤ B) :
    ‖(Fintype.card p : 𝕜)⁻¹ * (∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P -
        (Fintype.card n : 𝕜)⁻¹ ^ k * ∑ w : (Fin k → p) × (Fin k → n) with
          (∀ a, ∃ b ≠ a, bipartiteEdge w.1 w.2 b = bipartiteEdge w.1 w.2 a) ∧
            #(univ.image w.1) + #(univ.image w.2) = k + 1,
          ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P)‖ ≤
      (k : ℝ) ^ (2 * k) * B *
        ∑ a ∈ range k, ((Fintype.card p : ℝ) / Fintype.card n) ^ a / Fintype.card n := by
  set T : Finset ((Fin k → p) × (Fin k → n)) :=
    {w | ∀ a, ∃ b ≠ a, bipartiteEdge w.1 w.2 b = bipartiteEdge w.1 w.2 a}
  set F : (Fin k → p) × (Fin k → n) → 𝕜 := fun w ↦
    ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P
  have hprod : ∑ u : Fin k → p, ∑ v : Fin k → n with
      ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a, F (u, v) = ∑ w ∈ T, F w := by
    simp only [T, sum_filter]
    exact (Fintype.sum_prod_type' _).symm
  have hsplit : ∑ w ∈ T, F w - ∑ w ∈ T with #(univ.image w.1) + #(univ.image w.2) = k + 1, F w =
      ∑ w ∈ T with ¬(#(univ.image w.1) + #(univ.image w.2) = k + 1), F w :=
    sub_eq_of_eq_add' (sum_filter_add_sum_filter_not _ _ _).symm
  rw [integral_trace_sampleCovariance_pow hindep hzero hk (by exact_mod_cast hX), hprod,
    ← filter_filter, ← mul_sub, hsplit, norm_mul, norm_mul, norm_pow, norm_inv, norm_inv,
    RCLike.norm_natCast, RCLike.norm_natCast]
  have hR := norm_sum_integral_prod_mul_star_le_of_card_image_add_card_image_le hk hX hB
    (T.filter fun w ↦ ¬(#(univ.image w.1) + #(univ.image w.2) = k + 1)) fun w hw ↦ by
      have := card_image_add_card_image_le_add_one_of_no_singleton_edge
        (mem_filter.1 (mem_filter.1 hw).1).2
      have := (mem_filter.1 hw).2
      omega
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR (by positivity))
    (by positivity)).trans ?_
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [hk]
  have hB0 := nonneg_of_integral_norm_pow_le hB
  have hp : (Fintype.card p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hn : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_le_sum fun a ha ↦ ?_
  obtain ⟨m, hm⟩ : ∃ m, k = a + 1 + m := ⟨k - (a + 1), by have := mem_range.1 ha; omega⟩
  have hkm : k - (a + 1) = m := by omega
  have hrows : ((a + 1 : ℕ) : ℝ) ^ k ≤ (k : ℝ) ^ k := by
    gcongr
    exact_mod_cast (by omega : a + 1 ≤ k)
  have hcols : ((m : ℕ) : ℝ) ^ k ≤ (k : ℝ) ^ k := by
    gcongr
    exact_mod_cast (by omega : m ≤ k)
  rw [hkm]
  calc
    _ = ((a + 1 : ℕ) : ℝ) ^ k * (m : ℝ) ^ k * B *
        (((Fintype.card p : ℝ) / Fintype.card n) ^ a / Fintype.card n) := by
      rw [hm, inv_pow, div_pow]
      field_simp
      ring
    _ ≤ (k : ℝ) ^ k * (k : ℝ) ^ k * B *
        (((Fintype.card p : ℝ) / Fintype.card n) ^ a / Fintype.card n) := by
      gcongr
    _ = _ := by ring

end MomentBounds

end TauCeti.Probability
