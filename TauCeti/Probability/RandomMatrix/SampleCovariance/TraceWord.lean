/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Combinatorics.TraceWord.Bipartite
public import TauCeti.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Data.Fintype.SmallRange
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# Trace words of sample covariance matrices

The moment method for the Marchenko–Pastur law expands the moments `E tr Sᵏ` of the sample
covariance matrix `S = X Xᴴ / n` of a random `p × n` matrix `X` over trace words
(`Matrix.trace_pow_sampleCovariance_eq_sum_prod`). A trace word is a pair of sequences
`i : Fin k → p` and `j : Fin k → n`, read as the closed bipartite walk `TauCeti.bipartiteWord i j`
of length `2 * k`. It contributes `(card n)⁻ᵏ` times the expectation of the product

`∏ₜ X (i t) (j t) * conj (X (i (t + 1)) (j t))`

of the `2 * k` entries read along its steps.

When the entries of `X` are independent and centred, a word with an edge traversed exactly once
reads the corresponding entry exactly once, so its contribution vanishes. Only the words traversing
each of their edges at least twice remain in the expansion of `E tr Sᵏ`, and these use at most
`k + 1` rows and columns in total (`TauCeti.card_image_add_card_image_le_of_no_singleton_edge`).
Under a bound `B` on the `2k`th absolute moments of the entries, every word contributes at most `B`
before normalization, and there are at most `|p|ᵃ aᵏ |n|ᵇ bᵏ` words using at most `a` rows and `b`
columns. These estimates suppress the words with fewer than `k + 1` vertices as the dimensions
grow with `p / n` bounded.

The entries may be real or complex and need not be identically distributed; the dimensions are
arbitrary finite types.

## Main results

* `TauCeti.Probability.memLp_trace_pow_sampleCovariance` and
  `TauCeti.Probability.integrable_trace_pow_sampleCovariance`: on a finite measure space with
  entries in `L^(q * 2k)`, the trace of `Sᵏ` lies in `L^q`; with entries in `L^(2k)` it is
  integrable.
* `TauCeti.Probability.integral_prod_mul_star_eq_zero_of_singleton_edge`: for independent centred
  entries, a trace word with an edge traversed exactly once has expectation zero.
* `TauCeti.Probability.integral_trace_pow_sampleCovariance`: for independent centred entries in
  `L^(2k)`, `E tr Sᵏ` is `(card n)⁻ᵏ` times the sum of the expected products over the trace words
  traversing each of their edges at least twice.
* `TauCeti.Probability.norm_integral_prod_mul_star_le` and
  `TauCeti.Probability.norm_sum_integral_prod_mul_star_le`: moment bounds for one trace word and
  for a family of trace words with a bounded number of rows and columns.
* `TauCeti.Probability.norm_inv_mul_integral_trace_pow_sampleCovariance_sub_sum_le`: for
  independent centred entries whose `2k`th absolute moments are bounded by `B`, the normalized
  moment `(card p)⁻¹ E tr Sᵏ` minus the contribution of the words with `k + 1` vertices has norm at
  most `k^(2k) B ∑_{a<k} (p/n)ᵃ / n`.

## References

* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, second
  edition, Springer (2010), §3.1.2: the moment method for the Marchenko–Pastur law.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3: trace words and the vanishing of singleton edges.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]
  {X : Ω → Matrix p n 𝕜} {k : ℕ}

/-- The matrix position read by the factor `r` of the trace word `(i, j)`: the unconjugated
factor `inl t` reads `(i t, j t)` and the conjugated factor `inr t` reads `(i (t + 1), j t)`. -/
private def readPos (i : Fin k → p) (j : Fin k → n) : Fin k ⊕ Fin k → p × n :=
  Sum.elim (fun t ↦ (i t, j t)) (fun t ↦ (i (finRotate k t), j t))

/-- The factor `r` of a trace word applies the identity to the entry it reads when `r = inl t`,
and conjugation when `r = inr t`. -/
private def readFun : Fin k ⊕ Fin k → 𝕜 → 𝕜 :=
  Sum.elim (fun _ ↦ id) (fun _ ↦ star)

private theorem measurable_readFun (r : Fin k ⊕ Fin k) : Measurable (readFun (𝕜 := 𝕜) r) := by
  cases r
  · exact measurable_id
  · exact continuous_star.measurable

private theorem norm_readFun (r : Fin k ⊕ Fin k) (z : 𝕜) : ‖readFun r z‖ = ‖z‖ := by
  cases r <;> simp [readFun]

/-- A trace word of length `k` has `2 * k` factors. -/
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

/-- The product along a trace word as a product of its `2 * k` factors. -/
private theorem prod_mul_star_eq_prod_readFun (x : Matrix p n 𝕜) (i : Fin k → p)
    (j : Fin k → n) :
    ∏ t, x (i t) (j t) * star (x (i (finRotate k t)) (j t)) =
      ∏ r, readFun r (x (readPos i j r).1 (readPos i j r).2) := by
  simp [Fintype.prod_sum_type, prod_mul_distrib, readPos, readFun]

/-- The unordered edge of the bipartite word at the step of the factor `r` determines the position
that factor reads. -/
private theorem sym2_bipartiteWord_eq (i : Fin k → p) (j : Fin k → n) (r : Fin k ⊕ Fin k) :
    s(bipartiteWord i j (finSumFinInterleaveEquiv k r),
        bipartiteWord i j (finRotate (2 * k) (finSumFinInterleaveEquiv k r))) =
      s(.inl (readPos i j r).1, .inr (readPos i j r).2) := by
  cases r
  · simp only [finRotate_finSumFinInterleaveEquiv_inl, bipartiteWord_inl, bipartiteWord_inr,
      readPos, Sum.elim_inl]
  · simp only [finRotate_finSumFinInterleaveEquiv_inr, bipartiteWord_inl, bipartiteWord_inr,
      readPos, Sum.elim_inr, Sym2.eq_swap]

/-- On a finite measure space, a trace word with entries in `L^(q * 2k)` lies in `L^q`. -/
private theorem memLp_prod_mul_star [IsFiniteMeasure P] {q : ℝ≥0∞}
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (q * (2 * k : ℕ)) P) (i : Fin k → p) (j : Fin k → n) :
    MemLp (fun ω ↦ ∏ t, X ω (i t) (j t) * star (X ω (i (finRotate k t)) (j t))) q P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [memLp_const]
  simp_rw [prod_mul_star_eq_prod_readFun]
  have h := MemLp.fun_prod (s := (univ : Finset (Fin k ⊕ Fin k))) (p := fun _ ↦ q * (2 * k : ℕ))
    (f := fun r ω ↦ readFun r (X ω (readPos i j r).1 (readPos i j r).2)) fun r _ ↦ by
      cases r
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
  exact (memLp_finsetSum _ fun i _ ↦ memLp_finsetSum _ fun j _ ↦
    memLp_prod_mul_star hX i j).const_mul _

/-- On a finite measure space, the trace of the `k`th power of the sample covariance matrix of
`X` is integrable whenever all entries of `X` lie in `L^(2k)`. Neither independence nor centering
is required, and `k = 0` is included. -/
theorem integrable_trace_pow_sampleCovariance [Fintype p] [Fintype n] [DecidableEq p]
    [IsFiniteMeasure P]
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P) :
    Integrable (fun ω ↦ ((X ω).sampleCovariance ^ k).trace) P :=
  memLp_one_iff_integrable.mp (memLp_trace_pow_sampleCovariance (by simpa using hX))

/-- **Singleton edges vanish.** Let the entries of `X` be independent and centred. If some
unordered edge of the bipartite word of `(i, j)` is traversed exactly once, the product of the
entries read along the word has expectation zero. No integrability is required. -/
theorem integral_prod_mul_star_eq_zero_of_singleton_edge
    (hindep : iIndepFun (fun e : p × n ↦ fun ω ↦ X ω e.1 e.2) P)
    (hXm : ∀ a b, AEMeasurable (fun ω ↦ X ω a b) P) (hzero : ∀ a b, ∫ ω, X ω a b ∂P = 0)
    (i : Fin k → p) (j : Fin k → n) {s : Fin (2 * k)}
    (hs : ∀ s', s(bipartiteWord i j s', bipartiteWord i j (finRotate (2 * k) s')) =
      s(bipartiteWord i j s, bipartiteWord i j (finRotate (2 * k) s)) → s' = s) :
    ∫ ω, ∏ t, X ω (i t) (j t) * star (X ω (i (finRotate k t)) (j t)) ∂P = 0 := by
  obtain ⟨r, rfl⟩ := (finSumFinInterleaveEquiv k).surjective s
  simp_rw [prod_mul_star_eq_prod_readFun]
  refine hindep.integral_fun_prod_comp_eq_zero (fun e ↦ hXm e.1 e.2) measurable_readFun
    (t := r) (fun r' hr' ↦ (finSumFinInterleaveEquiv k).injective (hs _ ?_)) ?_
  · rw [sym2_bipartiteWord_eq, sym2_bipartiteWord_eq, hr']
  · cases r
    · simpa [readFun] using hzero _ _
    · simpa [readFun, RCLike.star_def, integral_conj] using
        congrArg (starRingEnd 𝕜) (hzero _ _)

/-- **Trace-word expansion of sample covariance moments.** Let the entries of `X` be independent,
centred and in `L^(2k)`, `k ≠ 0`. Then the expected trace of `Sᵏ`, for the sample covariance matrix
`S = X Xᴴ / n`, is `(card n)⁻ᵏ` times the sum, over the trace words `(i, j)` whose bipartite word
traverses each of its unordered edges at least twice, of the expected product of the entries read
along the word: the words with an edge traversed exactly once contribute zero. -/
theorem integral_trace_pow_sampleCovariance [Fintype p] [Fintype n] [DecidableEq p]
    [DecidableEq n] (hk : k ≠ 0)
    (hindep : iIndepFun (fun e : p × n ↦ fun ω ↦ X ω e.1 e.2) P)
    (hzero : ∀ a b, ∫ ω, X ω a b ∂P = 0)
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P) :
    ∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P = (Fintype.card n : 𝕜)⁻¹ ^ k *
      ∑ w : (Fin k → p) × (Fin k → n) with
        ∀ s, ∃ s' ≠ s,
          s(bipartiteWord w.1 w.2 s', bipartiteWord w.1 w.2 (finRotate (2 * k) s')) =
            s(bipartiteWord w.1 w.2 s, bipartiteWord w.1 w.2 (finRotate (2 * k) s)),
        ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  simp_rw [Matrix.trace_pow_sampleCovariance_eq_sum_prod _ hk, ← Fintype.sum_prod_type']
  rw [integral_const_mul, integral_finsetSum _ fun w _ ↦
    memLp_one_iff_integrable.mp (memLp_prod_mul_star (by simpa using hX) _ _)]
  congr 1
  refine (Finset.sum_filter_of_ne fun w _ hw s ↦ ?_).symm
  by_contra! h
  exact hw (integral_prod_mul_star_eq_zero_of_singleton_edge hindep
    (fun a b ↦ (hX a b).aestronglyMeasurable.aemeasurable) hzero w.1 w.2
    fun s' hs' ↦ by_contra fun hss ↦ h s' hss hs')

/-- A bound `B` on the `2k`th absolute moments of the entries of `X` bounds the expected product
along every trace word of length `k ≠ 0`. The positions read may repeat, and no independence or
centering is required. -/
theorem norm_integral_prod_mul_star_le (hk : k ≠ 0) {B : ℝ}
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P)
    (hB : ∀ a b, ∫ ω, ‖X ω a b‖ ^ (2 * k) ∂P ≤ B) (i : Fin k → p) (j : Fin k → n) :
    ‖∫ ω, ∏ t, X ω (i t) (j t) * star (X ω (i (finRotate k t)) (j t)) ∂P‖ ≤ B := by
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  simp_rw [prod_mul_star_eq_prod_readFun]
  calc
    _ ≤ ((2 * k : ℕ) : ℝ)⁻¹ * ∑ r : Fin k ⊕ Fin k,
        ∫ ω, ‖readFun r (X ω (readPos i j r).1 (readPos i j r).2)‖ ^ (2 * k) ∂P := by
      simpa only [card_univ_sum_fin] using norm_integral_prod_le_inv_card_mul_sum_integral_norm_pow
        (fun r ω ↦ readFun r (X ω (readPos i j r).1 (readPos i j r).2)) univ_nonempty
        (fun r _ ↦ by
          rw [card_univ_sum_fin]
          simpa [norm_readFun] using (hX _ _).integrable_norm_pow (by omega))
    _ ≤ ((2 * k : ℕ) : ℝ)⁻¹ * ∑ _r : Fin k ⊕ Fin k, B := by
      gcongr with r
      simpa [norm_readFun] using hB _ _
    _ = B := by
      rw [sum_const, card_univ_sum_fin, nsmul_eq_mul]
      field_simp

/-- Under a bound `B` on the `2k`th absolute moments of the entries of `X`, a family `S` of trace
words of length `k ≠ 0`, each using at most `a` rows and at most `b` columns, has total expected
product of norm at most `|p|ᵃ aᵏ |n|ᵇ bᵏ B`. No independence or centering is required. -/
theorem norm_sum_integral_prod_mul_star_le [Fintype p] [Fintype n] [DecidableEq p]
    [DecidableEq n] (hk : k ≠ 0) {B : ℝ}
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P)
    (hB : ∀ a b, ∫ ω, ‖X ω a b‖ ^ (2 * k) ∂P ≤ B) {a b : ℕ}
    (S : Finset ((Fin k → p) × (Fin k → n)))
    (hS : ∀ w ∈ S, #(univ.image w.1) ≤ a ∧ #(univ.image w.2) ≤ b) :
    ‖∑ w ∈ S, ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P‖ ≤
      (Fintype.card p : ℝ) ^ a * (a : ℝ) ^ k * ((Fintype.card n : ℝ) ^ b * (b : ℝ) ^ k) * B := by
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  -- If an index type is empty, there are no trace words and the bound has a vanishing factor.
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

/-- Trace words using at most `k` rows and columns in total, grouped by their number `a + 1` of
rows, have total expected product bounded by the sum over `a < k` of the bounds of
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

/-- **Nonleading trace words are negligible.** Let the entries of `X` be independent and centred
with `2k`th absolute moments bounded by `B`, `k ≠ 0`. Subtracting from the expected normalized
trace `(card p)⁻¹ E tr Sᵏ` the contribution of the trace words that traverse each edge at least
twice and use the maximal number `k + 1` of rows and columns leaves a remainder of norm at most
`k^(2k) B ∑_{a < k} (p / n)ᵃ / n`. This is `O(n⁻¹)` when the ratio `p / n` stays bounded. -/
theorem norm_inv_mul_integral_trace_pow_sampleCovariance_sub_sum_le [Fintype p] [Fintype n]
    [DecidableEq p] [DecidableEq n] [Nonempty p] (hk : k ≠ 0) {B : ℝ}
    (hindep : iIndepFun (fun e : p × n ↦ fun ω ↦ X ω e.1 e.2) P)
    (hzero : ∀ a b, ∫ ω, X ω a b ∂P = 0)
    (hX : ∀ a b, MemLp (fun ω ↦ X ω a b) (2 * k : ℕ) P)
    (hB : ∀ a b, ∫ ω, ‖X ω a b‖ ^ (2 * k) ∂P ≤ B) :
    ‖(Fintype.card p : 𝕜)⁻¹ * (∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P -
        (Fintype.card n : 𝕜)⁻¹ ^ k * ∑ w : (Fin k → p) × (Fin k → n) with
          (∀ s, ∃ s' ≠ s,
            s(bipartiteWord w.1 w.2 s', bipartiteWord w.1 w.2 (finRotate (2 * k) s')) =
              s(bipartiteWord w.1 w.2 s, bipartiteWord w.1 w.2 (finRotate (2 * k) s))) ∧
            #(univ.image w.1) + #(univ.image w.2) = k + 1,
          ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P)‖ ≤
      (k : ℝ) ^ (2 * k) * B *
        ∑ a ∈ range k, ((Fintype.card p : ℝ) / Fintype.card n) ^ a / Fintype.card n := by
  set T : Finset ((Fin k → p) × (Fin k → n)) := {w | ∀ s, ∃ s' ≠ s,
    s(bipartiteWord w.1 w.2 s', bipartiteWord w.1 w.2 (finRotate (2 * k) s')) =
      s(bipartiteWord w.1 w.2 s, bipartiteWord w.1 w.2 (finRotate (2 * k) s))}
  set F : (Fin k → p) × (Fin k → n) → 𝕜 := fun w ↦
    ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P
  have hsplit : ∑ w ∈ T, F w - ∑ w ∈ T with #(univ.image w.1) + #(univ.image w.2) = k + 1, F w =
      ∑ w ∈ T with ¬(#(univ.image w.1) + #(univ.image w.2) = k + 1), F w :=
    sub_eq_of_eq_add' (sum_filter_add_sum_filter_not _ _ _).symm
  rw [integral_trace_pow_sampleCovariance hk hindep hzero hX, ← filter_filter, ← mul_sub, hsplit,
    norm_mul, norm_mul, norm_pow, norm_inv, norm_inv, RCLike.norm_natCast, RCLike.norm_natCast]
  have hR := norm_sum_integral_prod_mul_star_le_of_card_image_add_card_image_le hk hX hB
    (T.filter fun w ↦ ¬(#(univ.image w.1) + #(univ.image w.2) = k + 1)) fun w hw ↦ by
      have := card_image_add_card_image_le_of_no_singleton_edge (mem_filter.1 (mem_filter.1 hw).1).2
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

end TauCeti.Probability
