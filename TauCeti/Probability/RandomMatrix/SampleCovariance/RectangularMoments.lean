/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.Leading
public import TauCeti.Probability.RandomMatrix.SampleCovariance.ExpectedSpectralMeasure
public import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.RandomMatrix.SampleCovariance.Moment
import TauCeti.Probability.RandomMatrix.SampleCovariance.TraceWord
import TauCeti.Combinatorics.TraceWord.Bipartite.Counting

/-!
# The rectangular trace-word method for sample covariance moments

For positive degree `k` and independent centred entries in `L^(2k)`,
`integral_trace_sampleCovariance_pow` supplies the expected trace expansion with no
singleton-edge terms.
A leading word matches each entry with its conjugate, and its expectation is the product of
the corresponding second absolute moments. The leading words are counted by noncrossing
column partitions with injective row and column labellings. The remaining words contribute
an error controlled by the absolute entry moment of order `2k`.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), §2.1.2, (2.15).
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Function
open scoped ENNReal NNReal

namespace TauCeti.Probability

open Classical in
/-- The leading covariance moment for `p` rows and `n` columns. At positive degree `k`,
each noncrossing column partition contributes the count of its injective row and column
labellings, weighted by `p⁻¹ * (n⁻¹)^k`. Since zero has inverse zero, the positive-degree
moment vanishes when either dimension is zero. At degree zero the moment is one for positive
`p` and zero for `p = 0`. -/
noncomputable def leadingCovarianceMoment (k p n : ℕ) : ℝ :=
  (p : ℝ)⁻¹ * (n : ℝ)⁻¹ ^ k * ∑ π : NoncrossingPartition (univ : Finset (Fin k)),
    (p.descFactorial (k + 1 - #π.val.parts) : ℝ) * n.descFactorial #π.val.parts

open Classical in
/-- The leading covariance moment as a falling-factorial sum over noncrossing partitions. -/
theorem leadingCovarianceMoment_def (k p n : ℕ) :
    leadingCovarianceMoment k p n =
      (p : ℝ)⁻¹ * (n : ℝ)⁻¹ ^ k * ∑ π : NoncrossingPartition (univ : Finset (Fin k)),
        (p.descFactorial (k + 1 - #π.val.parts) : ℝ) * n.descFactorial #π.val.parts :=
  (rfl)

/-- For positive degree, the falling-factorial sum is the number of leading bipartite words
multiplied by `p⁻¹ * (n⁻¹)^k` for row and column dimensions `p` and `n`. This is zero
when either index type is empty. -/
theorem leadingCovarianceMoment_eq_normalized_card_leadingBipartiteWord {p n : Type*}
    [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n] {k : ℕ} (hk : k ≠ 0) :
    leadingCovarianceMoment k (Fintype.card p) (Fintype.card n) =
      (Fintype.card p : ℝ)⁻¹ * (Fintype.card n : ℝ)⁻¹ ^ k *
        (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : ℝ) := by
  rw [leadingCovarianceMoment_def, card_leadingBipartiteWord hk]
  simp only [Nat.card_eq_fintype_card, Nat.cast_sum, Nat.cast_mul]

/-- The zeroth leading covariance moment is one when there is at least one row. -/
@[simp] theorem leadingCovarianceMoment_zero (p n : ℕ) :
    leadingCovarianceMoment 0 p n = if p = 0 then 0 else 1 := by
  classical
  have hparts (π : NoncrossingPartition (univ : Finset (Fin 0))) : #π.val.parts = 0 := by simp
  rw [leadingCovarianceMoment_def]
  simp only [hparts, pow_zero, mul_one, Nat.sub_zero, Nat.zero_add, Nat.descFactorial_one,
    Nat.descFactorial_zero, Nat.cast_one, Fintype.sum_unique]
  by_cases hp : p = 0
  · simp [hp]
  · simp [hp]

/-- The first leading covariance moment is one when both dimensions are positive and zero
when either is empty. -/
@[simp] theorem leadingCovarianceMoment_one (p n : ℕ) :
    leadingCovarianceMoment 1 p n = if p = 0 ∨ n = 0 then 0 else 1 := by
  have h := leadingCovarianceMoment_eq_normalized_card_leadingBipartiteWord
    (p := Fin p) (n := Fin n) one_ne_zero
  simp only [card_leadingBipartiteWord_one, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.cast_mul, pow_one] at h
  rw [h]
  by_cases hp : p = 0
  · simp [hp]
  by_cases hn : n = 0
  · simp [hn]
  simp only [hp, hn, or_self, ite_false]
  field_simp [Nat.cast_ne_zero.mpr hp, Nat.cast_ne_zero.mpr hn]

section Trace

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  {P : Measure Ω} {X : Ω → Matrix p n 𝕜} {k : ℕ}

/-- A leading word contributes the product of the second absolute moments of its row-to-column
entries when their squared norms are independent and almost everywhere strongly measurable.
The phases of the entries cancel, so they need not be independent. -/
theorem integral_prod_apply_mul_star_apply_of_isLeadingBipartiteWord
    [DecidableEq p] [DecidableEq n]
    {u : Fin k → p} {v : Fin k → n} (hw : IsLeadingBipartiteWord u v)
    (hXm : ∀ t, AEStronglyMeasurable (fun ω ↦ ‖X ω (u t) (v t)‖ ^ 2) P)
    (hindep : iIndepFun (fun t ω ↦ ‖X ω (u t) (v t)‖ ^ 2) P) :
    (∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P) =
      ∏ t, ((∫ ω, ‖X ω (u t) (v t)‖ ^ 2 ∂P : ℝ) : 𝕜) := by
  obtain ⟨π, hπ, _⟩ := hw.existsUnique_perm_matching_bipartiteEdges
  simp only [bipartiteEdge_inl, bipartiteEdge_inr, Prod.mk.injEq] at hπ
  have hreindex (ω : Ω) :
      (∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t))) =
        ((∏ t, ‖X ω (u t) (v t)‖ ^ 2 : ℝ) : 𝕜) := by
    have hstar : (∏ t, star (X ω (u (finRotate k t)) (v t))) = ∏ t, star (X ω (u t) (v t)) :=
      Fintype.prod_equiv π _ _ fun t ↦ by rw [(hπ t).1, (hπ t).2]
    rw [prod_mul_distrib, hstar, ← prod_mul_distrib, RCLike.ofReal_prod]
    simp only [RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]
  simp_rw [hreindex]
  rw [integral_ofReal, hindep.integral_fun_prod_eq_prod_integral hXm, RCLike.ofReal_prod]

variable [Fintype p] [DecidableEq p] [Fintype n] [DecidableEq n]

omit [Fintype p] [Fintype n] in
private theorem integral_prod_apply_mul_star_apply_eq_one
    {u : Fin k → p} {v : Fin k → n} (hw : IsLeadingBipartiteWord u v)
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hXk : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P)
    (hsecond : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P = 1) :
    ∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P = 1 := by
  have hInj : Injective (fun t : Fin k ↦ (u t, v t)) := by
    simpa only [Function.comp_def, bipartiteEdge_inl] using
      hw.injective_bipartiteEdge_orientations.1
  rw [integral_prod_apply_mul_star_apply_of_isLeadingBipartiteWord hw
    (fun t ↦ (hXk (u t) (v t)).aestronglyMeasurable.norm.pow 2)
    ((hindep.precomp hInj).comp (fun _ z ↦ ‖z‖ ^ 2) fun _ ↦ by fun_prop)]
  simp only [hsecond, RCLike.ofReal_one, prod_const_one]

/-- The expected trace at positive degree `k` differs from the leading-word count times
`n⁻ᵏ` by at most `n⁻ᵏ p max(p,n)^(k-1) k^(2k+1) B`. Entries have unit second absolute
moment. For `k > 1` they are also independent, centred, and in `L^(2k)`, with their absolute
moments of order `2k` bounded by `B`. -/
theorem norm_integral_trace_sampleCovariance_pow_sub_leading_le (hk : k ≠ 0)
    (hindep : 1 < k → iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hX : 1 < k → ∀ i j, ∫ ω, X ω i j ∂P = 0)
    (hXk : 1 < k → ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P)
    (hX₂ : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P = 1) {B : ℝ≥0}
    (hB : 1 < k → ∀ i j, ∫ ω, ‖X ω i j‖ ^ (2 * k) ∂P ≤ B) :
    ‖(∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P) - (Fintype.card n : 𝕜)⁻¹ ^ k *
      (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : 𝕜)‖ ≤
      (Fintype.card n : ℝ)⁻¹ ^ k * (Fintype.card p *
        max (Fintype.card p) (Fintype.card n) ^ (k - 1) * k ^ (2 * k + 1) : ℕ) * B := by
  classical
  rcases eq_or_ne k 1 with rfl | hk₁
  · rw [card_leadingBipartiteWord_one]
    simp only [pow_one, integral_trace_sampleCovariance_eq X hX₂,
      Nat.card_eq_fintype_card, sub_self, norm_zero]
    positivity
  have hk' : 1 < k := by omega
  specialize hindep hk'
  specialize hX hk'
  specialize hXk hk'
  specialize hB hk'
  let f (w : (Fin k → p) × (Fin k → n)) : 𝕜 :=
    ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P
  let S : Finset ((Fin k → p) × (Fin k → n)) :=
    {w | ∀ a, ∃ b ≠ a, bipartiteEdge w.1 w.2 b = bipartiteEdge w.1 w.2 a}
  let L : Finset ((Fin k → p) × (Fin k → n)) := {w | IsLeadingBipartiteWord w.1 w.2}
  have hLS : L ⊆ S := fun w hw ↦ mem_filter.mpr ⟨mem_univ _,
    (isLeadingBipartiteWord_iff.mp (mem_filter.mp hw).2).1⟩
  have htrace : (∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P) =
      (Fintype.card n : 𝕜)⁻¹ ^ k * ∑ w ∈ S, f w := by
    rw [integral_trace_sampleCovariance_pow hindep hX hk hXk]
    simp only [S, sum_filter, Fintype.sum_prod_type, f]
  have hleading : ∑ w ∈ L, f w =
      (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : 𝕜) := by
    rw [sum_congr rfl (g := fun _ ↦ 1) fun w hw ↦ by
      exact integral_prod_apply_mul_star_apply_eq_one (mem_filter.mp hw).2 hindep hXk hX₂]
    rw [sum_const, nsmul_one, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcount := card_bipartiteWord_le_of_card_image_add_card_image_le hk (S \ L) fun w hw ↦ by
    obtain ⟨hS, hL⟩ := mem_sdiff.mp hw
    have hS' := (mem_filter.mp hS).2
    have hv := card_image_add_card_image_le_add_one_of_no_singleton_edge hS'
    have hne : #(univ.image w.1) + #(univ.image w.2) ≠ k + 1 := fun he ↦
      hL (mem_filter.mpr ⟨mem_univ _, isLeadingBipartiteWord_iff.mpr ⟨hS', he⟩⟩)
    omega
  rw [htrace, ← hleading, ← mul_sub, ← sum_sdiff hLS, add_sub_cancel_right,
    norm_mul, norm_pow, norm_inv, RCLike.norm_natCast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc
    _ ≤ ∑ w ∈ S \ L, ‖f w‖ := norm_sum_le _ _
    _ ≤ ∑ _w ∈ S \ L, (B : ℝ) := by
      apply sum_le_sum
      intro w _
      exact norm_integral_prod_apply_mul_star_apply_le hk w.1 w.2
        (fun _ ↦ MemLp.integrable_norm_pow
          (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hXk _ _) (by omega))
        (fun _ ↦ hB _ _)
    _ = (#(S \ L) : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) B.coe_nonneg

end Trace

private theorem covarianceMoment_error_bound (p n k : ℕ) (hp : p ≠ 0)
    (hk : k ≠ 0) (B : ℝ) :
    (p : ℝ)⁻¹ * ((n : ℝ)⁻¹ ^ k * (p * max p n ^ (k - 1) * k ^ (2 * k + 1) : ℕ) * B) =
      ((k : ℝ) ^ (2 * k + 1) * B * max ((p : ℝ) / n) 1 ^ (k - 1)) / n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zero_pow hk]
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmax : ((max p n : ℕ) : ℝ) = max ((p : ℝ) / n) 1 * n := by
    rw [Nat.cast_max, max_mul_of_nonneg _ _ (Nat.cast_nonneg _), div_mul_cancel₀ _ hnR, one_mul]
  have hpow : (n : ℝ) ^ k = (n : ℝ) ^ (k - 1) * n := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)]
  simp only [Nat.cast_mul, Nat.cast_pow, hmax, mul_pow, inv_pow, hpow]
  field_simp

section Bound

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  [Fintype p] [DecidableEq p] [Nonempty p] [Fintype n]
  {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ} {X : Ω → Matrix p n 𝕜}

/-- The expected spectral moment at positive degree `k` differs from the normalized leading-word
count by at most `k^(2k+1) * B * max(p/n,1)^(k-1) / n`. The matrix is almost everywhere
measurable and its entries have unit second absolute moment. For `k > 1` the entries are also
independent, centred and in `L^(2k)`, with absolute moments of order `2k` bounded by `B`.
With empty columns the positive-degree moment and leading count both vanish, so the bound is
exact with zero error. -/
theorem norm_integral_pow_expectedCovarianceSpectralMeasure_sub_leadingCovarianceMoment_le
    (hk : k ≠ 0)
    (hXm : AEMeasurable X P)
    (hindep : 1 < k → iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hmean : 1 < k → ∀ i j, ∫ ω, X ω i j ∂P = 0)
    (hLp : 1 < k → ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P)
    (hsecond : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P = 1) {B : ℝ≥0}
    (hB : 1 < k → ∀ i j, ∫ ω, ‖X ω i j‖ ^ (2 * k) ∂P ≤ B) :
    ‖(∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure hXm : Measure ℝ)) -
        leadingCovarianceMoment k (Fintype.card p) (Fintype.card n)‖ ≤
      ((k : ℝ) ^ (2 * k + 1) * B *
        max ((Fintype.card p : ℝ) / Fintype.card n) 1 ^ (k - 1)) / Fintype.card n := by
  let : DecidableEq n := Classical.decEq n
  have hLp' : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P := by
    rcases eq_or_ne k 1 with rfl | hk₁
    · intro i j
      have hm : AEMeasurable (fun ω ↦ X ω i j) P :=
        (measurable_pi_apply j).comp_aemeasurable ((measurable_pi_apply i).comp_aemeasurable hXm)
      simpa only [Nat.cast_one, mul_one] using
        (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
          (Integrable.of_integral_ne_zero (by rw [hsecond i j]; exact one_ne_zero))
    · exact hLp (by omega)
  have hlead : (leadingCovarianceMoment k (Fintype.card p) (Fintype.card n) : 𝕜) =
      (Fintype.card p : 𝕜)⁻¹ * (Fintype.card n : 𝕜)⁻¹ ^ k *
        (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : 𝕜) := by
    simpa only [RCLike.ofReal_mul, RCLike.ofReal_inv, RCLike.ofReal_pow,
      RCLike.ofReal_natCast] using congrArg (RCLike.ofReal : ℝ → 𝕜)
        (leadingCovarianceMoment_eq_normalized_card_leadingBipartiteWord (p := p) (n := n) hk)
  rw [Real.norm_eq_abs, ← RCLike.norm_ofReal (K := 𝕜), RCLike.ofReal_sub,
    ofReal_integral_pow_expectedCovarianceSpectralMeasure hXm
      (integrable_trace_sampleCovariance_pow_of_ne_zero hk hLp'),
    hlead, mul_assoc, ← mul_sub, norm_mul, norm_inv, RCLike.norm_natCast,
    ← covarianceMoment_error_bound _ _ k Fintype.card_ne_zero hk B]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_trace_sampleCovariance_pow_sub_leading_le (X := X)
      hk hindep hmean hLp hsecond hB)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

end Bound

end TauCeti.Probability
