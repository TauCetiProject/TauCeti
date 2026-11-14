/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import TauCeti.Combinatorics.TreeWalk.Count
public import TauCeti.Data.Fintype.SmallRange
public import TauCeti.MeasureTheory.Integral.MeanInequalities
public import TauCeti.Probability.RandomMatrix.TraceWord
import TauCeti.Data.Nat.Factorial.Bounds
import TauCeti.Probability.Independence.Basic

/-!
# Bounds for nonleading Wigner trace words and expected trace moments

A uniform bound on the `k`th absolute moments of the unnormalized entries bounds every
length-`k` expected trace word by `B / (√n)^k`, without independence. There are at most
`n^r r^k` words visiting at most `r` vertices. Together these estimates suppress the words
with fewer than the leading number of vertices in the normalized trace expansion.

For independent centered entries, the singleton-edge reduction then gives a bound of order
`n⁻¹` for the even-moment remainder after removing the words visiting `m + 1` vertices, and
of order `n^(-1/2)` for the entire expected odd moment. Combining the leading-word expectation
`sum_integral_prod_wignerMatrix_leading_eq` with the falling-factorial collision estimate yields the
quantitative `O(n⁻¹)` bound `norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le`
between the expected normalized even trace and the Catalan number `catalan m`.

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

/-- A bound on the `k`th absolute moments of the `n × n` corner passes to Wigner entries with
normalization factor `(√n)⁻ᵏ`. -/
theorem integral_norm_wignerMatrix_apply_pow_le_of_lt {k n : ℕ} {B : ℝ}
    (hξ : ∀ ij, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B)
    (hη : ∀ i, i < n → ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B) (i j : Fin n) :
    ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ k ∂P ≤ (Real.sqrt n)⁻¹ ^ k * B := by
  have hc : ‖(Real.sqrt n : ℂ)⁻¹‖ = (Real.sqrt n)⁻¹ := by
    simp [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h, norm_mul, mul_pow, hc, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hξ ⟨_, h⟩ j.2) (by positivity)
  · obtain rfl := Fin.ext h
    simp only [wignerMatrix_apply_self, norm_mul, mul_pow, hc, Complex.norm_real,
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hη i.val i.2) (by positivity)
  · simp only [wignerMatrix_apply_of_gt _ _ _ h, norm_mul, norm_star, mul_pow, hc,
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hξ ⟨_, h⟩ i.2) (by positivity)

/-- A bound on the `k`th absolute moments of the entry array passes to Wigner entries with
normalization factor `(√n)⁻ᵏ`. -/
theorem integral_norm_wignerMatrix_apply_pow_le {k : ℕ} {B : ℝ}
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    {n : ℕ} (i j : Fin n) :
    ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ k ∂P ≤ (Real.sqrt n)⁻¹ ^ k * B :=
  integral_norm_wignerMatrix_apply_pow_le_of_lt (fun ij _ ↦ hξ ij) (fun i _ ↦ hη i) i j

/-- Uniform `k`th absolute moments on the `n × n` corner bound every nonempty expected product of
`k` Wigner entries. The positions may repeat, and no independence or centering is required. -/
theorem norm_integral_prod_wignerMatrix_apply_le_of_lt {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} {B : ℝ}
    (hξp : ∀ ij, ij.1.2 < n → MemLp (ξ ij) (Fintype.card ι) P)
    (hηp : ∀ i, i < n → MemLp (η i) (Fintype.card ι) P)
    (hξ : ∀ ij, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ Fintype.card ι ∂P ≤ B)
    (hη : ∀ i, i < n → ∫ ω, ‖η i ω‖ ^ Fintype.card ι ∂P ≤ B) (u v : ι → Fin n) :
    ‖∫ ω, ∏ t, wignerMatrix ξ η n ω (u t) (v t) ∂P‖ ≤
      (Real.sqrt n)⁻¹ ^ Fintype.card ι * B := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ t, ∫ ω, ‖wignerMatrix ξ η n ω (u t) (v t)‖ ^ Fintype.card ι ∂P := by
      simpa using norm_integral_prod_le_inv_card_mul_sum_integral_norm_pow _ univ_nonempty
        (fun t _ ↦ (memLp_wignerMatrix_apply_of_lt hξp hηp (u t) (v t)).integrable_norm_pow
          (by simp))
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ _t : ι, (Real.sqrt n)⁻¹ ^ Fintype.card ι * B := by
      gcongr with t
      exact integral_norm_wignerMatrix_apply_pow_le_of_lt hξ hη (u t) (v t)
    _ = _ := by simp [hk]

/-- Uniform `k`th absolute moments bound every expected product of `k` Wigner entries.
The positions may repeat, and no independence or centering is required. -/
theorem norm_integral_prod_wignerMatrix_apply_le {ι : Type*} [Fintype ι]
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (Fintype.card ι) P)
    (hηp : ∀ i, MemLp (η i) (Fintype.card ι) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ Fintype.card ι ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ Fintype.card ι ∂P ≤ B) {n : ℕ} (u v : ι → Fin n) :
    ‖∫ ω, ∏ t, wignerMatrix ξ η n ω (u t) (v t) ∂P‖ ≤
      (Real.sqrt n)⁻¹ ^ Fintype.card ι * B := by
  cases isEmpty_or_nonempty ι
  · simpa [abs_of_nonneg measureReal_nonneg] using hη 0
  · exact norm_integral_prod_wignerMatrix_apply_le_of_lt
      (fun ij _ ↦ hξp ij) (fun i _ ↦ hηp i) (fun ij _ ↦ hξ ij) (fun i _ ↦ hη i) u v

/-- Under a uniform `k`th absolute moment bound `B`, the sum over any collection of length-`k`
cyclic Wigner words visiting at most `r` vertices has norm at most `r^k n^r (√n)⁻ᵏ B`, for
`k ≠ 0`. No independence or centering is required. -/
theorem norm_sum_integral_prod_wignerMatrix_le {k n r : ℕ} (hk : k ≠ 0)
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    (S : Finset (Fin k → Fin n)) (hS : ∀ w ∈ S, #(univ.image w) ≤ r) :
    ‖∑ w ∈ S, ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate k t)) ∂P‖ ≤
      (r : ℝ) ^ k * (n : ℝ) ^ r * (Real.sqrt n)⁻¹ ^ k * B := by
  classical
  have : NeZero k := ⟨hk⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Finset.eq_empty_of_isEmpty S, hk]
  have : NeZero n := ⟨hn⟩
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

/-- For independent centered entries on a finite measure space with `2m`th absolute moments
bounded by `B`, subtracting the sum over singleton-free words visiting `m + 1` vertices from
the expected even trace and normalizing by `n⁻¹` leaves a remainder of norm at most
`m^(2m) B / n`. The assumption `m ≠ 0` excludes the zeroth moment, whose empty word has no
visited vertices. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le {m n : ℕ} (hm : m ≠ 0)
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
  rcases eq_or_ne n 0 with rfl | hn
  · simp
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
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : (Real.sqrt n) ^ (2 * m) = (n : ℝ) ^ m := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  -- Partition the singleton-free expansion into its maximal-vertex and remaining words.
  simp only [filter_filter, S, F] at hsplit
  rw [hsplit, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((m : ℝ) ^ (2 * m) * (n : ℝ) ^ m * (Real.sqrt n)⁻¹ ^ (2 * m) * B) :=
      by simpa only [S, filter_filter] using mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; field_simp

/-- For independent centered entries on a finite measure space with `(2m + 1)`st absolute
moments bounded by `B`, the expected normalized odd Wigner moment has norm at most
`(m + 1)^(2m + 1) B / √n`. No higher moments or identical distributions are required. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le {m n : ℕ}
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m + 1)).trace ∂P‖ ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt n := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  let S : Finset (Fin (2 * m + 1) → Fin n) := {w | ∀ t, ∃ s ≠ t,
    s(w s, w (finRotate (2 * m + 1) s)) = s(w t, w (finRotate (2 * m + 1) t))}
  have hbound := norm_sum_integral_prod_wignerMatrix_le (n := n) (r := m + 1)
    (by omega) hξp hηp hξ hη S (by
      intro w hw
      have hv := card_image_le_div_two_add_one_of_no_singleton_edge w (mem_filter.mp hw).2
      omega)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : (Real.sqrt n) ^ (2 * m + 1) = (n : ℝ) ^ m * Real.sqrt n := by
    rw [pow_succ, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [integral_trace_pow_wignerMatrix hindep hξzero hηzero (by omega) hξp hηp,
    norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * (((m + 1 : ℕ) : ℝ) ^ (2 * m + 1) * (n : ℝ) ^ (m + 1) *
        (Real.sqrt n)⁻¹ ^ (2 * m + 1) * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; push_cast; field_simp; ring

/-- For independent centered entries on a finite measure space with uniformly bounded `2m`th
absolute moments, subtracting the sum over singleton-free words visiting `m + 1` vertices from
the expected even trace and normalizing by `n⁻¹` gives a remainder tending to zero, for `m ≠ 0`. -/
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
    norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le
      hindep hξzero hηzero hm hξp hηp hξ hη) hlim

/-- Every expected normalized odd Wigner moment converges to zero when the corresponding
absolute moments of the independent centered entries on a finite measure space are uniformly
bounded. -/
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
      hindep hξzero hηzero hξp hηp hξ hη) hlim

end Centered

section LeadingAndCatalan

private def padZeroOffDiag (ξ : StrictUpper → Ω → ℂ) (n : ℕ) (ij : StrictUpper) : Ω → ℂ :=
  if ij.1.2 < n then ξ ij else 0

private def padZeroDiag (η : ℕ → Ω → ℝ) (n : ℕ) (i : ℕ) : Ω → ℝ :=
  if i < n then η i else 0

omit [MeasurableSpace Ω] in
private theorem wignerMatrix_padZero_eq (n : ℕ) (ω : Ω) :
    wignerMatrix (padZeroOffDiag ξ n) (padZeroDiag η n) n ω = wignerMatrix ξ η n ω :=
  wignerMatrix_congr ω (fun ij hij ↦ by simp [padZeroOffDiag, hij])
    (fun i hi ↦ by simp [padZeroDiag, hi])

private theorem iIndepFun_padZero {n : ℕ}
    (hindep : iIndepFun
      (fun k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n k)) P) :
    iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦
        Sum.elim (padZeroOffDiag ξ n) (fun i ω ↦ (padZeroDiag η n i ω : ℂ)) r) P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  refine TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_range
    (e := wignerCoordinateIndex n) (hindep.congr fun k ↦ .of_forall fun ω ↦ ?_) ?_
  · cases k with
    | inl i => simp [padZeroDiag, i.2]
    | inr p => simp [padZeroOffDiag, p.1.2.2]
  · rintro (ij | i) hnot
    · have hij : ¬ ij.1.2 < n := fun h ↦
        hnot ⟨.inr ⟨(⟨ij.1.1, ij.2.trans h⟩, ⟨ij.1.2, h⟩), ij.2⟩, by simp⟩
      exact ⟨0, .of_forall fun ω ↦ by simp [padZeroOffDiag, hij]⟩
    · have hi : ¬ i < n := fun h ↦ hnot ⟨.inl ⟨i, h⟩, by simp⟩
      exact ⟨0, .of_forall fun ω ↦ by simp [padZeroDiag, hi]⟩

/-- Summing the expected entry products over all leading cyclic Wigner words of length `2 * m`
(`m ≠ 0`) yields `(catalan m * n.descFactorial (m + 1)) * n⁻ᵐ` whenever the strict-upper entries of
the `n × n` corner are independent with unit second absolute moments. -/
theorem sum_integral_prod_wignerMatrix_leading_eq {m n : ℕ} (hm : m ≠ 0)
    (hindep : iIndepFun (fun p : FinStrictUpper n ↦ ξ ⟨(p.val.1.val, p.val.2.val), p.property⟩) P)
    (hsecond : ∀ ij, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1) :
    ∑ w : Fin (2 * m) → Fin n with TreeWalk.IsLeadingCyclicWord m w,
      (∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) =
      (catalan m * n.descFactorial (m + 1) : ℂ) * (n : ℂ)⁻¹ ^ m := by
  have : NeZero m := ⟨hm⟩
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let ξ' : StrictUpper → Ω → ℂ := fun ij ω ↦ if ij.1.2 < n then ξ ij ω else 1
  let e : FinStrictUpper n → StrictUpper := fun p ↦ ⟨(p.val.1.val, p.val.2.val), p.property⟩
  have hindep' : iIndepFun ξ' P :=
    TauCeti.Probability.iIndepFun_of_ae_eq_const_outside_range (e := e)
      (hindep.congr fun p ↦ .of_forall fun ω ↦ by simp [ξ', e, p.1.2.2])
      fun ij hnot ↦ ⟨1, .of_forall fun ω ↦ by
        have hij : ¬ ij.1.2 < n := fun h ↦
          hnot ⟨⟨(⟨ij.1.1, ij.2.trans h⟩, ⟨ij.1.2, h⟩), ij.2⟩, rfl⟩
        simp [ξ', hij]⟩
  have hsecond' (ij : StrictUpper) : ∫ ω, ‖ξ' ij ω‖ ^ 2 ∂P = 1 := by
    dsimp only [ξ']
    split_ifs with hij
    · exact hsecond ij hij
    · simp
  have hcongr (ω : Ω) : wignerMatrix ξ η n ω = wignerMatrix ξ' η n ω :=
    wignerMatrix_congr ω (fun ij hij ↦ by simp [ξ', hij]) (fun _ _ ↦ rfl)
  have hterm : ∀ w ∈ ({w : Fin (2 * m) → Fin n | TreeWalk.IsLeadingCyclicWord m w} : Finset _),
      (∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) = (n : ℂ)⁻¹ ^ m := by
    intro w hw
    obtain ⟨hns, hv⟩ := (mem_filter.mp hw).2
    simp_rw [hcongr]
    exact integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one
      hindep' hsecond' w hns hv
  rw [sum_congr rfl hterm, sum_const, TreeWalk.card_filter_leadingCyclicWord]
  simp [Fintype.card_fin]

/-- Quantitative `O(n⁻¹)` error bound between the expected even normalized Wigner trace of degree
`2 * m` and the Catalan number `catalan m`, for `n ≠ 0`, requiring hypotheses only on the `n × n`
corner. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le {m n : ℕ}
    (hn : n ≠ 0) {B : ℝ}
    (hindep : iIndepFun
      (fun k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n k)) P)
    (hξzero : ∀ ij, ij.1.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, i < n → ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, ij.1.2 < n → MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, i < n → MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, i < n → ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (catalan m : ℂ)‖ ≤
      ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / n := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans
      (hη 0 (Nat.pos_of_ne_zero hn))
  rcases eq_or_ne m 0 with rfl | hm
  · have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp [hnc, div_nonneg hB (Nat.cast_nonneg n)]
  · let S := ∑ w : Fin (2 * m) → Fin n with TreeWalk.IsLeadingCyclicWord m w,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P
    have hrem := norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le
      (ξ := padZeroOffDiag ξ n) (η := padZeroDiag η n) (n := n)
      (iIndepFun_padZero hindep)
      (fun ij ↦ by
        dsimp [padZeroOffDiag]
        split_ifs with h
        · exact hξzero ij h
        · simp)
      (fun i ↦ by
        dsimp [padZeroDiag]
        split_ifs with h
        · exact hηzero i h
        · simp)
      hm
      (fun ij ↦ by
        dsimp [padZeroOffDiag]
        split_ifs with h
        · exact hξp ij h
        · exact MemLp.zero)
      (fun i ↦ by
        dsimp [padZeroDiag]
        split_ifs with h
        · exact hηp i h
        · exact MemLp.zero)
      (fun ij ↦ by
        dsimp [padZeroOffDiag]
        split_ifs with h
        · exact hξ ij h
        · simpa [zero_pow (by omega : 2 * m ≠ 0)] using hB)
      (fun i ↦ by
        dsimp [padZeroDiag]
        split_ifs with h
        · exact hη i h
        · simpa [zero_pow (by omega : 2 * m ≠ 0)] using hB)
    simp_rw [wignerMatrix_padZero_eq] at hrem
    have hindepξ : iIndepFun (fun p : FinStrictUpper n ↦
        ξ ⟨(p.val.1.val, p.val.2.val), p.property⟩) P := by
      simpa only [Function.comp_def, wignerCoordinateIndex_inr, Sum.elim_inl] using
        hindep.precomp (g := Sum.inr) Sum.inr_injective
    have hlead : (n : ℂ)⁻¹ * S - (catalan m : ℂ) =
        (catalan m : ℂ) * (((n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1)) - 1) := by
      dsimp only [S]
      rw [sum_integral_prod_wignerMatrix_leading_eq (η := η) hm hindepξ hsecond]
      rw [inv_pow, pow_succ', div_eq_mul_inv, mul_inv]
      ring
    have hdesc : ‖((n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1)) - 1‖ ≤
        ((m + 1).choose 2 : ℝ) / n := by
      have hcast : ((n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1)) - 1 =
          ((((n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1)) - 1 : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      exact Nat.abs_descFactorial_div_pow_sub_one_le hn (m + 1)
    have hsplit : (n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (catalan m : ℂ) =
        (n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - S) +
          ((n : ℂ)⁻¹ * S - (catalan m : ℂ)) := by ring
    rw [hsplit]
    calc
      ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - S) +
          ((n : ℂ)⁻¹ * S - (catalan m : ℂ))‖
        ≤ ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - S)‖ +
            ‖(n : ℂ)⁻¹ * S - (catalan m : ℂ)‖ := norm_add_le _ _
      _ ≤ (m : ℝ) ^ (2 * m) * B / n +
            (catalan m : ℝ) * (((m + 1).choose 2 : ℝ) / n) := by
        gcongr
        rw [hlead, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hdesc (by positivity)
      _ = ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / n := by ring

/-- For independent centered entries on the `n × n` corner with `(2m + 1)`st absolute moments
bounded by `B`, the expected normalized odd Wigner moment has norm at most
`(m + 1)^(2m + 1) B / √n`. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le_of_lt {m n : ℕ}
    {B : ℝ}
    (hindep : iIndepFun
      (fun k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n k)) P)
    (hξzero : ∀ ij, ij.1.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, i < n → ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, ij.1.2 < n → MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, i < n → MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, i < n → ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m + 1)).trace ∂P‖ ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
    have hB : 0 ≤ B :=
      (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans
        (hη 0 (Nat.pos_of_ne_zero hn))
    have h := norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le
      (ξ := padZeroOffDiag ξ n) (η := padZeroDiag η n) (n := n)
      (iIndepFun_padZero hindep)
      (fun ij ↦ by
        dsimp [padZeroOffDiag]
        split_ifs with h
        · exact hξzero ij h
        · simp)
      (fun i ↦ by
        dsimp [padZeroDiag]
        split_ifs with h
        · exact hηzero i h
        · simp)
      (fun ij ↦ by
        dsimp [padZeroOffDiag]
        split_ifs with h
        · exact hξp ij h
        · exact MemLp.zero)
      (fun i ↦ by
        dsimp [padZeroDiag]
        split_ifs with h
        · exact hηp i h
        · exact MemLp.zero)
      (fun ij ↦ by
        dsimp [padZeroOffDiag]
        split_ifs with h
        · exact hξ ij h
        · simpa [zero_pow (by omega : 2 * m + 1 ≠ 0)] using hB)
      (fun i ↦ by
        dsimp [padZeroDiag]
        split_ifs with h
        · exact hη i h
        · simpa [zero_pow (by omega : 2 * m + 1 ≠ 0)] using hB)
    simp_rw [wignerMatrix_padZero_eq] at h
    exact h

end LeadingAndCatalan

end TauCeti
