/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.Leading
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
public import TauCeti.Probability.RandomMatrix.SampleCovariance.ExpectedSpectralMeasure
import TauCeti.Data.Nat.Factorial.Asymptotics
import TauCeti.Probability.Distributions.MarchenkoPastur.Moments
import TauCeti.Probability.Moments.WeakConvergence
import TauCeti.Probability.RandomMatrix.SampleCovariance.RectangularMoments
import TauCeti.Probability.RandomMatrix.SampleCovariance.TraceWord

/-!
# The Marchenko–Pastur moment limit for sample covariance matrices

For almost everywhere measurable random matrices with independent centred entries of unit second
absolute moment, the expected spectral moments converge to the Marchenko–Pastur moments when the
column dimension tends to infinity and the aspect ratio converges. At each positive degree `k`,
the entries must eventually lie in `L^(2k)` with a uniform bound on their absolute moments of
order `2k`. The formula `integral_pow_marchenkoPastur` identifies the limits of the leading counts,
and `ProbabilityMeasure.tendsto_of_tendsto_integral_pow` turns moment convergence into weak
convergence of the expected spectral measures.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.1.2, (2.15).
-/

public section

open Filter Finset Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

open Classical in
/-- The normalized leading-word contribution at degree `k), with `p` rows and `n` columns.
Each noncrossing column partition contributes the count of its injective row and column labellings,
weighted by `1 / (p * n^k)`. -/
noncomputable def leadingCovarianceMoment (k p n : ℕ) : ℝ :=
  (p : ℝ)⁻¹ * (n : ℝ)⁻¹ ^ k * ∑ π : NoncrossingPartition (univ : Finset (Fin k)),
    (p.descFactorial (k + 1 - #π.val.parts) : ℝ) * n.descFactorial #π.val.parts

/-- For positive degree, the falling-factorial sum is the number of leading bipartite words
divided by the row dimension and the `k`th power of the column dimension. -/
theorem leadingCovarianceMoment_eq_card_leadingBipartiteWord {p n : Type*}
    [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n] {k : ℕ} (hk : k ≠ 0) :
    leadingCovarianceMoment k (Fintype.card p) (Fintype.card n) =
      (Fintype.card p : ℝ)⁻¹ * (Fintype.card n : ℝ)⁻¹ ^ k *
        (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : ℝ) := by
  rw [leadingCovarianceMoment, card_leadingBipartiteWord hk]
  simp only [Nat.card_eq_fintype_card, Nat.cast_sum, Nat.cast_mul]

private theorem leadingCovarianceMoment_summand_eq (p n k c : ℕ)
    (hp : p ≠ 0) (hc : c ≤ k) :
    (p : ℝ)⁻¹ * (n : ℝ)⁻¹ ^ k *
        ((p.descFactorial (k + 1 - c) : ℝ) * n.descFactorial c) =
      ((p - 1).descFactorial (k - c) : ℝ) / (n : ℝ) ^ (k - c) *
        ((n.descFactorial c : ℝ) / (n : ℝ) ^ c) := by
  have hr : k + 1 - c = (k - c) + 1 := by omega
  have hpn : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hfactor : p.descFactorial ((k - c) + 1) = p * (p - 1).descFactorial (k - c) := by
    cases p with
    | zero => contradiction
    | succ p => simpa only [Nat.add_sub_cancel] using Nat.succ_descFactorial_succ p (k - c)
  rw [hr, hfactor, Nat.cast_mul, inv_pow, div_mul_div_comm, ← pow_add, Nat.sub_add_cancel hc]
  field_simp

private theorem tendsto_leadingCovarianceMoment {ι : Type*} {l : Filter ι} {p n : ι → ℕ}
    {y : ℝ≥0} (hn : Tendsto n l atTop) (hp : ∀ᶠ i in l, p i ≠ 0)
    (hy : Tendsto (fun i ↦ (p i : ℝ) / n i) l (𝓝 (y : ℝ))) (k : ℕ) :
    Tendsto (fun i ↦ leadingCovarianceMoment k (p i) (n i)) l
      (𝓝 (∫ x, x ^ k ∂marchenkoPastur y)) := by
  classical
  rw [integral_pow_marchenkoPastur]
  simp only [leadingCovarianceMoment, mul_sum]
  apply tendsto_finsetSum
  intro π _
  have hc : #π.val.parts ≤ k := by simpa using π.val.card_parts_le_card
  have hnpos : ∀ᶠ i in l, n i ≠ 0 := (hn.eventually_ge_atTop 1).mono fun _ hi ↦ by omega
  have hself : Tendsto (fun i ↦ (n i : ℝ) / n i) l (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    exact hnpos.mono fun _ hi ↦ (div_self (Nat.cast_ne_zero.mpr hi)).symm
  have hnR : Tendsto (fun i ↦ (n i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hn
  have hr := hnR.natCast_descFactorial_sub_div_pow hy 1 (k - #π.val.parts)
  have hs := hnR.natCast_descFactorial_sub_div_pow hself 0 #π.val.parts
  simp only [Nat.sub_zero] at hs
  have ht := hr.mul hs
  rw [one_pow, mul_one] at ht
  refine ht.congr' ?_
  filter_upwards [hp] with i hpi
  exact (leadingCovarianceMoment_summand_eq (p i) (n i) k #π.val.parts hpi hc).symm

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

/-- For independent centred entries in `L^(2k)` with unit second absolute moment, the
`k`th expected spectral moment differs from the normalized leading-word count by at most
`k^(2k+1) * B * max(p/n,1)^(k-1) / n`. Here `k > 0`, the matrix is almost everywhere
measurable, and `B` bounds the absolute entry moments of order `2k`. -/
theorem norm_integral_pow_expectedCovarianceSpectralMeasure_sub_le (hk : k ≠ 0)
    (hXm : AEMeasurable X P)
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂P = 0)
    (hLp : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P)
    (hsecond : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P = 1) {B : ℝ≥0}
    (hB : ∀ i j, ∫ ω, ‖X ω i j‖ ^ (2 * k) ∂P ≤ B) :
    ‖(∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure hXm : Measure ℝ)) -
        leadingCovarianceMoment k (Fintype.card p) (Fintype.card n)‖ ≤
      ((k : ℝ) ^ (2 * k + 1) * B *
        max ((Fintype.card p : ℝ) / Fintype.card n) 1 ^ (k - 1)) / Fintype.card n := by
  classical
  have hlead : (leadingCovarianceMoment k (Fintype.card p) (Fintype.card n) : 𝕜) =
      (Fintype.card p : 𝕜)⁻¹ * (Fintype.card n : 𝕜)⁻¹ ^ k *
        (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : 𝕜) := by
    rw [@leadingCovarianceMoment_eq_card_leadingBipartiteWord p n _ _
      inferInstance inferInstance k hk]
    push_cast
    rfl
  rw [Real.norm_eq_abs, ← RCLike.norm_ofReal (K := 𝕜), RCLike.ofReal_sub,
    ofReal_integral_pow_expectedCovarianceSpectralMeasure hXm
      (integrable_trace_sampleCovariance_pow_of_ne_zero hk hLp),
    hlead, mul_assoc, ← mul_sub, norm_mul, norm_inv, RCLike.norm_natCast,
    ← covarianceMoment_error_bound _ _ k Fintype.card_ne_zero hk B]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_trace_sampleCovariance_pow_sub_leading_le (X := X)
      hk hindep hmean hLp hsecond hB)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

end Bound

section Limit

variable {ι : Type*} {l : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {𝕜 : Type*} [RCLike 𝕜]
  {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
  {p n : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (p i)] [∀ i, Nonempty (p i)]
  {X : (i : ι) → Ω i → Matrix (p i) (n i) 𝕜} {y : ℝ≥0}

/-- If the column dimension tends to infinity and the aspect ratio tends to `y`, the
`k`th expected spectral moment tends to the `k`th Marchenko–Pastur moment. The matrices are
almost everywhere measurable at every index. For positive `k`, the entries are eventually
independent, centred and in `L^(2k)`, with unit second absolute moment and a uniform bound
on the absolute moments of order `2k`. -/
theorem tendsto_integral_pow_expectedCovarianceSpectralMeasure_marchenkoPastur (k : ℕ)
    (hn : Tendsto (fun i ↦ Fintype.card (n i)) l atTop)
    (hy : Tendsto (fun i ↦ (Fintype.card (p i) : ℝ) / Fintype.card (n i)) l (𝓝 (y : ℝ)))
    (hXm : ∀ i, AEMeasurable (X i) (P i))
    (hindep : k ≠ 0 → ∀ᶠ i in l,
      iIndepFun (fun ab : p i × n i ↦ fun ω ↦ X i ω ab.1 ab.2) (P i))
    (hmean : k ≠ 0 → ∀ᶠ i in l, ∀ a b, ∫ ω, X i ω a b ∂P i = 0)
    (hLp : k ≠ 0 → ∀ᶠ i in l, ∀ a b, MemLp (fun ω ↦ X i ω a b) (2 * k) (P i))
    (hsecond : k ≠ 0 → ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ 2 ∂P i = 1)
    (hB : k ≠ 0 → ∃ B : ℝ≥0, ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ (2 * k) ∂P i ≤ B) :
    Tendsto (fun i ↦ ∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure (hXm i) : Measure ℝ)) l
      (𝓝 (∫ x, x ^ k ∂marchenkoPastur y)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa only [pow_zero, integral_const, probReal_univ, one_smul] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℝ)) l (𝓝 1))
  obtain ⟨B, hBound⟩ := hB hk
  have hnR : Tendsto (fun i ↦ (Fintype.card (n i) : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hmajorant : Tendsto (fun i ↦ ((k : ℝ) ^ (2 * k + 1) * B *
      max ((Fintype.card (p i) : ℝ) / Fintype.card (n i)) 1 ^ (k - 1)) / Fintype.card (n i))
      l (𝓝 0) :=
    (tendsto_const_nhds.mul ((hy.max tendsto_const_nhds).pow (k - 1))).div_atTop hnR
  have herror : Tendsto (fun i ↦
      (∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure (hXm i) : Measure ℝ)) -
        leadingCovarianceMoment k (Fintype.card (p i)) (Fintype.card (n i))) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmajorant
    filter_upwards [hindep hk, hmean hk, hLp hk, hsecond hk, hBound] with i hI hM hL hS hBi
    exact norm_integral_pow_expectedCovarianceSpectralMeasure_sub_le hk (hXm i) hI hM hL hS hBi
  have hlead := tendsto_leadingCovarianceMoment hn (.of_forall fun _ ↦ Fintype.card_ne_zero) hy k
  simpa only [sub_add_cancel, zero_add] using herror.add hlead

/-- **Marchenko–Pastur convergence of the expected spectral measures by moments.** The matrices
are almost everywhere measurable at every index, and their entries are eventually independent
and centred with unit second absolute moment. For every positive degree `k`, the entries
eventually lie in `L^(2k)` and have uniformly bounded absolute moments of order `2k`. The expected
spectral measures converge weakly when the column dimension tends to infinity and the aspect
ratio converges. Sample spaces and entry laws may vary. At aspect ratio zero the limit is the
point mass at one. -/
theorem tendsto_expectedCovarianceSpectralMeasure_marchenkoPastur_of_uniform_entry_moment_bounds
    (hn : Tendsto (fun i ↦ Fintype.card (n i)) l atTop)
    (hy : Tendsto (fun i ↦ (Fintype.card (p i) : ℝ) / Fintype.card (n i)) l (𝓝 (y : ℝ)))
    (hXm : ∀ i, AEMeasurable (X i) (P i))
    (hindep : ∀ᶠ i in l, iIndepFun (fun ab : p i × n i ↦ fun ω ↦ X i ω ab.1 ab.2) (P i))
    (hmean : ∀ᶠ i in l, ∀ a b, ∫ ω, X i ω a b ∂P i = 0)
    (hsecond : ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ 2 ∂P i = 1)
    (hLp : ∀ k : ℕ, k ≠ 0 → ∀ᶠ i in l, ∀ a b, MemLp (fun ω ↦ X i ω a b) (2 * k) (P i))
    (hB : ∀ k : ℕ, k ≠ 0 → ∃ B : ℝ≥0, ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ (2 * k) ∂P i ≤ B) :
    Tendsto (fun i ↦ expectedCovarianceSpectralMeasure (hXm i)) l
      (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_integral_pow isCompact_Icc
    (ae_iff.mp (ae_mem_Icc_zero_marchenkoPastur y)) ?_ ?_
  · intro k
    rcases eq_or_ne k 0 with rfl | hk
    · exact .of_forall fun _ ↦ by simp
    filter_upwards [hLp k hk] with i hi
    exact integrable_pow_expectedCovarianceSpectralMeasure (hXm i)
      (integrable_trace_sampleCovariance_pow_of_ne_zero hk hi)
  · intro k
    exact tendsto_integral_pow_expectedCovarianceSpectralMeasure_marchenkoPastur
      k hn hy hXm (fun _ ↦ hindep) (fun _ ↦ hmean) (hLp k) (fun _ ↦ hsecond) (hB k)

end Limit

end TauCeti.Probability
