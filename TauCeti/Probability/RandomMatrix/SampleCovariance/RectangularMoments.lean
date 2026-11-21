/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.Leading
public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Probability.RandomMatrix.SampleCovariance.ExpectedSpectralMeasure
public import Mathlib.Probability.Independence.Integration
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
labellings, weighted by `1 / (p * n^k)`. At degree zero the moment is one for positive `p`
and zero for `p = 0`. -/
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
divided by the row dimension and the `k`th power of the column dimension. -/
theorem leadingCovarianceMoment_eq_normalized_card_leadingBipartiteWord {p n : Type*}
    [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n] {k : ℕ} (hk : k ≠ 0) :
    leadingCovarianceMoment k (Fintype.card p) (Fintype.card n) =
      (Fintype.card p : ℝ)⁻¹ * (Fintype.card n : ℝ)⁻¹ ^ k *
        (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : ℝ) := by
  rw [leadingCovarianceMoment_def, card_leadingBipartiteWord hk]
  simp only [Nat.card_eq_fintype_card, Nat.cast_sum, Nat.cast_mul]

section Trace

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  {P : Measure Ω} {X : Ω → Matrix p n 𝕜} {k : ℕ}

/-- For independent, almost everywhere measurable entries, a leading word contributes the product
of the second absolute moments of its row-to-column entries. -/
theorem integral_prod_apply_mul_star_apply_of_isLeadingBipartiteWord
    [DecidableEq p] [DecidableEq n]
    {u : Fin k → p} {v : Fin k → n} (hw : IsLeadingBipartiteWord u v)
    (hXm : ∀ t, AEMeasurable (fun ω ↦ X ω (u t) (v t)) P)
    (hindep : iIndepFun (fun t ω ↦ X ω (u t) (v t)) P) :
    (∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P) =
      ∏ t, ((∫ ω, ‖X ω (u t) (v t)‖ ^ 2 ∂P : ℝ) : 𝕜) := by
  obtain ⟨π, hπ, _⟩ := hw.existsUnique_perm_matching_bipartiteEdges
  simp only [bipartiteEdge_inl, bipartiteEdge_inr, Prod.mk.injEq] at hπ
  have hreindex (ω : Ω) :
      (∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t))) =
        ∏ t, X ω (u t) (v t) * star (X ω (u t) (v t)) := by
    simp only [prod_mul_distrib]
    congr 1
    exact (Fintype.prod_equiv π _ _ fun t ↦ by rw [(hπ t).1, (hπ t).2])
  simp_rw [hreindex]
  rw [hindep.integral_fun_prod_comp hXm
    (f := fun _ z ↦ z * star z)
      (fun _ ↦ (continuous_id.mul continuous_star).aestronglyMeasurable)]
  simp only [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, integral_ofReal]

variable [Fintype p] [DecidableEq p] [Fintype n] [DecidableEq n]

open Classical in
private theorem card_leadingBipartiteWord_one :
    Nat.card {w : (Fin 1 → p) × (Fin 1 → n) // IsLeadingBipartiteWord w.1 w.2} =
      Fintype.card p * Fintype.card n := by
  have h : (univ : Finset (Fin 1)) = {0} := univ_unique
  let : Unique (NoncrossingPartition (univ : Finset (Fin 1))) := by
    rw [h]
    infer_instance
  rw [card_leadingBipartiteWord one_ne_zero]
  have hparts (π : NoncrossingPartition (univ : Finset (Fin 1))) : #π.val.parts = 1 := by
    have hpos := (π.val.parts_nonempty (by simp)).card_pos
    have hle := π.val.card_parts_le_card
    simp only [card_univ, Fintype.card_fin] at hle
    omega
  simp only [hparts, Nat.add_sub_cancel, Nat.descFactorial_one, Nat.card_eq_fintype_card,
    Fintype.sum_unique]

omit [DecidableEq p] [DecidableEq n] in
private theorem integral_trace_sampleCovariance_eq
    (hsecond : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P = 1) :
    ∫ ω, (X ω).sampleCovariance.trace ∂P =
      (Fintype.card n : 𝕜)⁻¹ * (Fintype.card p * Fintype.card n : ℕ) := by
  have hint (i : p) (j : n) : Integrable (fun ω ↦ ‖X ω i j‖ ^ 2) P :=
    Integrable.of_integral_ne_zero (by rw [hsecond i j]; exact one_ne_zero)
  have htrace (ω : Ω) :
      (X ω).sampleCovariance.trace =
        ((RCLike.re (X ω).sampleCovariance.trace : ℝ) : 𝕜) := by
    symm
    apply RCLike.conj_eq_iff_re.mp
    rw [← RCLike.star_def, ← Matrix.trace_conjTranspose, (isHermitian_sampleCovariance (X ω)).eq]
  rw [integral_congr_ae (.of_forall htrace), integral_ofReal]
  simp_rw [re_trace_sampleCovariance, one_div, integral_const_mul]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hint _ j)]
  simp [hsecond]

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
    (fun t ↦ (hXk (u t) (v t)).aestronglyMeasurable.aemeasurable) (hindep.precomp hInj)]
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
  · simp only [pow_one, integral_trace_sampleCovariance_eq hX₂,
      card_leadingBipartiteWord_one, sub_self, norm_zero]
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
  have hcount := card_bipartiteWord_le hk (S \ L) fun w hw ↦ by
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
      exact norm_integral_prod_apply_mul_star_apply_le hk w.1 w.2 (fun _ ↦ hXk _ _) (fun _ ↦ hB _ _)
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
independent, centred and in `L^(2k)`, with absolute moments of order `2k` bounded by `B`. -/
theorem norm_integral_pow_expectedCovarianceSpectralMeasure_sub_le (hk : k ≠ 0)
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
  classical
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
    rw [@leadingCovarianceMoment_eq_normalized_card_leadingBipartiteWord p n _ _
      inferInstance inferInstance k hk]
    push_cast
    rfl
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
