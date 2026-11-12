/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import TauCeti.Data.Fintype.SmallRange
public import TauCeti.MeasureTheory.Integral.MeanInequalities
public import TauCeti.Probability.RandomMatrix.TraceWord

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
open scoped Topology

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

/-- A bound on the `k`th absolute moments of the entry array passes to Wigner entries with
normalization factor `(√n)⁻ᵏ`. -/
theorem integral_norm_wignerMatrix_apply_pow_le {k : ℕ} {B : ℝ}
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    {n : ℕ} (i j : Fin n) :
    ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ k ∂P ≤ (Real.sqrt n)⁻¹ ^ k * B := by
  have hc : ‖(Real.sqrt n : ℂ)⁻¹‖ = (Real.sqrt n)⁻¹ := by
    simp [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h, norm_mul, mul_pow, hc, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hξ _) (by positivity)
  · obtain rfl := Fin.ext h
    simp only [wignerMatrix_apply_self, norm_mul, mul_pow, hc, Complex.norm_real,
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hη _) (by positivity)
  · simp only [wignerMatrix_apply_of_gt _ _ _ h, norm_mul, norm_star, mul_pow, hc,
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hξ _) (by positivity)

/-- Uniform `k`th absolute moments bound every expected product of `k` Wigner entries.
The positions may repeat, and no independence or centering is required. -/
theorem norm_integral_prod_wignerMatrix_apply_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (Fintype.card ι) P)
    (hηp : ∀ i, MemLp (η i) (Fintype.card ι) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ Fintype.card ι ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ Fintype.card ι ∂P ≤ B) {n : ℕ} (u v : ι → Fin n) :
    ‖∫ ω, ∏ t, wignerMatrix ξ η n ω (u t) (v t) ∂P‖ ≤
      (Real.sqrt n)⁻¹ ^ Fintype.card ι * B := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ t, ∫ ω, ‖wignerMatrix ξ η n ω (u t) (v t)‖ ^ Fintype.card ι ∂P :=
      norm_integral_prod_le_average_integral_norm_pow _ fun t ↦
        (memLp_wignerMatrix_apply hξp hηp (u t) (v t)).integrable_norm_pow Fintype.card_ne_zero
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ _t : ι, (Real.sqrt n)⁻¹ ^ Fintype.card ι * B := by
      gcongr with t
      exact integral_norm_wignerMatrix_apply_pow_le hξ hη (u t) (v t)
    _ = _ := by simp [hk]

/-- A sum over any collection of length-`k` words visiting at most `r` vertices has a bound
obtained by counting the words and bounding each expected product. -/
theorem norm_sum_integral_prod_wignerMatrix_le {k n r : ℕ} (hk : k ≠ 0) [NeZero n]
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    (S : Finset (Fin k → Fin n)) (hS : ∀ w ∈ S, #(univ.image w) ≤ r) :
    ‖∑ w ∈ S, ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate k t)) ∂P‖ ≤
      (r : ℝ) ^ k * (n : ℝ) ^ r * (Real.sqrt n)⁻¹ ^ k * B := by
  classical
  have : NeZero k := ⟨hk⟩
  have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) k).trans (hη 0)
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
        (by simpa using hξp) (by simpa using hηp) (by simpa using hξ) (by simpa using hη)
        w (w ∘ finRotate k)
    _ = (#S : ℝ) * ((Real.sqrt n)⁻¹ ^ k * B) := by simp
    _ ≤ (n ^ r * r ^ k : ℕ) * ((Real.sqrt n)⁻¹ ^ k * B) := by
      gcongr
    _ = _ := by push_cast; ring

section Centered

variable [IsFiniteMeasure P]
  (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
  (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)

include hindep hξzero hηzero

/-- After retaining the leading words with `m + 1` vertices, the expected normalized even
Wigner moment has remainder at most `m^(2m) B / n`. The assumption `m ≠ 0` excludes the zeroth
moment, whose empty word has no visited vertices. -/
theorem norm_integral_trace_pow_wignerMatrix_sub_leading_le {m n : ℕ} (hm : m ≠ 0) [NeZero n]
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      ∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P)‖ ≤
      (m : ℝ) ^ (2 * m) * B / n := by
  classical
  let S : Finset (Fin (2 * m) → Fin n) := {w | ∀ t, ∃ s ≠ t,
    s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))}
  let F (w : Fin (2 * m) → Fin n) :=
    ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P
  have hsplit : (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      ∑ w ∈ S with #(univ.image w) = m + 1, F w =
        ∑ w ∈ S with #(univ.image w) ≠ m + 1, F w := by
    rw [integral_trace_pow_wignerMatrix hindep hξzero hηzero (by omega) hξp hηp]
    apply sub_eq_iff_eq_add.mpr
    simpa only [S, F, add_comm] using
      (sum_filter_add_sum_filter_not S (fun w ↦ #(univ.image w) = m + 1) F).symm
  have hbound := norm_sum_integral_prod_wignerMatrix_le (n := n) (r := m)
    (by omega) hξp hηp hξ hη (S.filter fun w ↦ #(univ.image w) ≠ m + 1) (by
      intro w hw
      obtain ⟨hwS, hwne⟩ := mem_filter.mp hw
      have hv := card_image_le_div_two_add_one_of_no_singleton_edge w (mem_filter.mp hwS).2
      omega)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hs : (Real.sqrt n) ^ (2 * m) = (n : ℝ) ^ m := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  -- Partition the singleton-free expansion into its maximal-vertex and remaining words.
  simp only [filter_filter, S, F] at hsplit
  rw [hsplit, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((m : ℝ) ^ (2 * m) * (n : ℝ) ^ m * (Real.sqrt n)⁻¹ ^ (2 * m) * B) :=
      by simpa only [S, filter_filter] using mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; field_simp

/-- Every expected normalized odd Wigner moment is bounded by
`(m + 1)^(2m + 1) B / √n`. Only the absolute moment of the order being estimated is needed. -/
theorem norm_integral_trace_pow_wignerMatrix_odd_le {m n : ℕ} [NeZero n]
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m + 1)).trace ∂P‖ ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt n := by
  classical
  let S : Finset (Fin (2 * m + 1) → Fin n) := {w | ∀ t, ∃ s ≠ t,
    s(w s, w (finRotate (2 * m + 1) s)) = s(w t, w (finRotate (2 * m + 1) t))}
  have hbound := norm_sum_integral_prod_wignerMatrix_le (n := n) (r := m + 1)
    (by omega) hξp hηp hξ hη S (by
      intro w hw
      have hv := card_image_le_div_two_add_one_of_no_singleton_edge w (mem_filter.mp hw).2
      omega)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hs : (Real.sqrt n) ^ (2 * m + 1) = (n : ℝ) ^ m * Real.sqrt n := by
    rw [pow_succ, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [integral_trace_pow_wignerMatrix hindep hξzero hηzero (by omega) hξp hηp,
    norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * (((m + 1 : ℕ) : ℝ) ^ (2 * m + 1) * (n : ℝ) ^ (m + 1) *
        (Real.sqrt n)⁻¹ ^ (2 * m + 1) * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; push_cast; field_simp; ring

/-- Under a uniform absolute moment bound, the nonleading part of each positive even expected
normalized Wigner moment tends to zero. -/
theorem tendsto_integral_trace_pow_wignerMatrix_sub_leading {m : ℕ} (hm : m ≠ 0)
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
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : NeZero n := ⟨hn⟩
  exact norm_integral_trace_pow_wignerMatrix_sub_leading_le
    hindep hξzero hηzero hm hξp hηp hξ hη

/-- Every expected normalized odd Wigner moment converges to zero when the corresponding
absolute moments of the independent centered entries are uniformly bounded. -/
theorem tendsto_integral_trace_pow_wignerMatrix_odd {m : ℕ}
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
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : NeZero n := ⟨hn⟩
  exact norm_integral_trace_pow_wignerMatrix_odd_le hindep hξzero hηzero hξp hηp hξ hη

end Centered

end TauCeti
