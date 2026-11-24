/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import TauCeti.Data.Fintype.SmallRange
public import TauCeti.MeasureTheory.Integral.MeanInequalities
public import TauCeti.Probability.RandomMatrix.Wigner.Trace.Word

/-!
# Bounds for nonleading Wigner trace words

A uniform bound on the `k`th absolute moments of the unnormalized entries bounds every
length-`k` expected trace word by `B / (√n)^k`, without independence. There are at most
`n^r r^k` words visiting at most `r` vertices. Together these estimates suppress the words
with fewer than the leading number of vertices in the normalized trace expansion.

For independent centered entries, the singleton-edge reduction then gives a bound of order
`n⁻¹` for the even-moment remainder after removing the words visiting `m + 1` vertices, and
of order `n^(-1/2)` for the entire expected odd moment. The bounds are uniform over position
and do not require identical distributions or any second-moment normalization.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, proof of Lemma 2.1.6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology NNReal

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

/-- Uniform `k`th absolute moments on the `n × n` corner bound every expected product of `k`
entries of the `n × n` Wigner matrix, indexed by a finite nonempty type `ι` of cardinality `k`.
The positions may repeat, and no independence or centering is required. -/
theorem norm_integral_prod_wignerMatrix_apply_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} {B : ℝ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (Fintype.card ι) P)
    (hηp : ∀ i < n, MemLp (η i) (Fintype.card ι) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ Fintype.card ι ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ Fintype.card ι ∂P ≤ B) (u v : ι → Fin n) :
    ‖∫ ω, ∏ t, wignerMatrix ξ η n ω (u t) (v t) ∂P‖ ≤
      (Real.sqrt n)⁻¹ ^ Fintype.card ι * B := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ t, ∫ ω, ‖wignerMatrix ξ η n ω (u t) (v t)‖ ^ Fintype.card ι ∂P := by
      simpa using norm_integral_prod_le_inv_card_mul_sum_integral_norm_pow _ univ_nonempty
        (fun t _ ↦ (memLp_wignerMatrix_apply hξp hηp (u t) (v t)).integrable_norm_pow (by simp))
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ _t : ι, (Real.sqrt n)⁻¹ ^ Fintype.card ι * B := by
      gcongr with t
      exact integral_norm_wignerMatrix_apply_pow_le hξ hη (u t) (v t)
    _ = _ := by simp [hk]

/-- Under a uniform `k`th absolute moment bound `B` on the `n × n` corner, the sum over any
collection of length-`k` cyclic Wigner words visiting at most `r` vertices has norm at most
`r^k n^r (√n)⁻ᵏ B`, for `k ≠ 0`. No independence or centering is required. -/
theorem norm_sum_integral_prod_wignerMatrix_le {k n r : ℕ} (hk : k ≠ 0) {B : ℝ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) k P)
    (hηp : ∀ i < n, MemLp (η i) k P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    (S : Finset (Fin k → Fin n)) (hS : ∀ w ∈ S, #(univ.image w) ≤ r) :
    ‖∑ w ∈ S, ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate k t)) ∂P‖ ≤
      (r : ℝ) ^ k * (n : ℝ) ^ r * (Real.sqrt n)⁻¹ ^ k * B := by
  classical
  have : NeZero k := ⟨hk⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Finset.eq_empty_of_isEmpty S, hk]
  have : NeZero n := ⟨hn⟩
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) k).trans
      (hη 0 (Nat.pos_of_ne_zero hn))
  have hcard : #S ≤ n ^ r * r ^ k :=
    (card_le_card (fun w hw ↦ mem_filter.mpr ⟨mem_univ _, hS w hw⟩)).trans
      (by simpa using card_filter_card_image_le (α := Fin k) (β := Fin n) r)
  calc
    _ ≤ ∑ w ∈ S, ‖∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate k t)) ∂P‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _w ∈ S, (Real.sqrt n)⁻¹ ^ k * B := by
      apply sum_le_sum
      intro w _
      simpa using norm_integral_prod_wignerMatrix_apply_le
        (fun ij hij ↦ by simpa using hξp ij hij) (fun i hi ↦ by simpa using hηp i hi)
        (fun ij hij ↦ by simpa using hξ ij hij) (fun i hi ↦ by simpa using hη i hi)
        w (w ∘ finRotate k)
    _ = (#S : ℝ) * ((Real.sqrt n)⁻¹ ^ k * B) := by simp
    _ ≤ (n ^ r * r ^ k : ℕ) * ((Real.sqrt n)⁻¹ ^ k * B) := by
      gcongr
    _ = _ := by push_cast; ring

/-- For independent centered entries in the `n × n` corner with `2m`th absolute moments bounded
by `B`, subtracting the sum over singleton-free words visiting `m + 1` vertices from the expected
even trace and normalizing by `n⁻¹` leaves a remainder of norm at most `m^(2m) B / n`. The
assumption `m ≠ 0` excludes the zeroth moment, whose empty word has no visited vertices. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le {m n : ℕ} (hm : m ≠ 0)
    {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i < n, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      ∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P)‖ ≤
      (m : ℝ) ^ (2 * m) * B / n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  classical
  let S : Finset (Fin (2 * m) → Fin n) := {w | ∀ t, ∃ s ≠ t,
    s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))}
  let F (w : Fin (2 * m) → Fin n) :=
    ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P
  -- Partition the singleton-free expansion into its maximal-vertex and remaining words.
  have hsplit : (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      ∑ w ∈ S with #(univ.image w) = m + 1, F w =
        ∑ w ∈ S with #(univ.image w) ≠ m + 1, F w := by
    rw [integral_trace_pow_wignerMatrix (by omega) hindep hξzero hηzero hξp hηp]
    refine sub_eq_iff_eq_add.mpr ?_
    rw [add_comm]
    exact (sum_filter_add_sum_filter_not S (fun w ↦ #(univ.image w) = m + 1) F).symm
  have hbound := norm_sum_integral_prod_wignerMatrix_le (ξ := ξ) (η := η) (n := n) (r := m)
    (by omega) hξp hηp hξ hη
    (S.filter fun w ↦ #(univ.image w) ≠ m + 1) (by
      intro w hw
      obtain ⟨hwS, hwne⟩ := mem_filter.mp hw
      have hv := card_image_le_div_two_add_one_of_no_singleton_edge w (mem_filter.mp hwS).2
      omega)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : (Real.sqrt n) ^ (2 * m) = (n : ℝ) ^ m := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [filter_filter, S, F] at hsplit
  rw [hsplit, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((m : ℝ) ^ (2 * m) * (n : ℝ) ^ m * (Real.sqrt n)⁻¹ ^ (2 * m) * B) :=
      by simpa only [S, filter_filter] using mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; field_simp

/-- For independent centered entries in the `n × n` corner with `(2m + 1)`st absolute moments
bounded by `B`, the expected normalized odd Wigner moment has norm at most
`(m + 1)^(2m + 1) B / √n`. No higher moments or identical distributions are required. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le {m n : ℕ}
    {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i < n, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m + 1)).trace ∂P‖ ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  classical
  let S : Finset (Fin (2 * m + 1) → Fin n) := {w | ∀ t, ∃ s ≠ t,
    s(w s, w (finRotate (2 * m + 1) s)) = s(w t, w (finRotate (2 * m + 1) t))}
  have hbound := norm_sum_integral_prod_wignerMatrix_le (ξ := ξ) (η := η) (n := n) (r := m + 1)
    (by omega) hξp hηp hξ hη S (by
      intro w hw
      have hv := card_image_le_div_two_add_one_of_no_singleton_edge w (mem_filter.mp hw).2
      omega)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : (Real.sqrt n) ^ (2 * m + 1) = (n : ℝ) ^ m * Real.sqrt n := by
    rw [pow_succ, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [integral_trace_pow_wignerMatrix (by omega) hindep hξzero hηzero hξp hηp,
    norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * (((m + 1 : ℕ) : ℝ) ^ (2 * m + 1) * (n : ℝ) ^ (m + 1) *
        (Real.sqrt n)⁻¹ ^ (2 * m + 1) * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; push_cast; field_simp; ring

section Centered

variable
  (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
  (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)

include hindep hξzero hηzero

/-- For independent centered entries with uniformly bounded `2m`th absolute moments, subtracting
the sum over singleton-free words visiting `m + 1` vertices from the expected even trace and
normalizing by `n⁻¹` gives a remainder tending to zero, for `m ≠ 0`. -/
theorem tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum {m : ℕ} (hm : m ≠ 0)
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      ∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ (m : ℝ) ^ (2 * m) * B / n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact squeeze_zero_norm (fun n ↦
    norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le hm
      (iIndepFun_sumElim_ofReal_subtype_lt hindep)
      (fun ij _ ↦ hξzero ij) (fun i _ ↦ hηzero i)
      (fun ij _ ↦ hξp ij) (fun i _ ↦ hηp i)
      (fun ij _ ↦ hξ ij) (fun i _ ↦ hη i)) hlim

/-- Every expected normalized odd Wigner moment converges to zero when the corresponding
absolute moments of the independent centered entries are uniformly bounded. -/
theorem tendsto_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix {m : ℕ}
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m + 1)).trace ∂P)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  exact squeeze_zero_norm (fun n ↦
    norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le
      (iIndepFun_sumElim_ofReal_subtype_lt hindep)
      (fun ij _ ↦ hξzero ij) (fun i _ ↦ hηzero i)
      (fun ij _ ↦ hξp ij) (fun i _ ↦ hηp i)
      (fun ij _ ↦ hξ ij) (fun i _ ↦ hη i)) hlim

end Centered

end TauCeti
