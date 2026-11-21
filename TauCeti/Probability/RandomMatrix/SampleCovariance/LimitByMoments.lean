/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
public import TauCeti.Probability.RandomMatrix.SampleCovariance.ExpectedSpectralMeasure
import TauCeti.Data.Nat.Factorial.Asymptotics
import TauCeti.Probability.Distributions.MarchenkoPastur.Moments
import TauCeti.Probability.Moments.WeakConvergence
import TauCeti.Probability.RandomMatrix.SampleCovariance.RectangularMoments

/-!
# The Marchenko–Pastur moment limit for sample covariance matrices

The expected spectral moments of independent centred entries with unit second absolute moment
and uniformly bounded higher moments converge to the Marchenko–Pastur moments. For each fixed
degree only a bound of twice that degree is needed. The row and column dimensions can vary
independently as long as their ratio converges and the column dimension tends to infinity.
The method of moments then gives weak convergence of the expected spectral measures.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.1.2, (2.15).
-/

public section

open Filter Finset Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

section Integrability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  [Fintype p] [DecidableEq p] [Nonempty p] [Fintype n]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → Matrix p n 𝕜} {k : ℕ}

/-- For sample covariance matrices, integrability of the trace power implies finiteness of
the corresponding moment of the expected spectral measure. -/
theorem integrable_pow_expectedCovarianceSpectralMeasure (hXm : AEMeasurable X P)
    (htrace : Integrable (fun ω ↦ ((X ω).sampleCovariance ^ k).trace) P) :
    Integrable (fun x : ℝ ↦ x ^ k) (expectedCovarianceSpectralMeasure hXm : Measure ℝ) := by
  let L (ω : Ω) : Measure ℝ := ((X ω).sampleCovariance.spectralMeasure
    (isHermitian_sampleCovariance (X ω)) : Measure ℝ)
  have hL : AEMeasurable L P :=
    measurable_subtypeVal.comp_aemeasurable (measurable_spectralMeasure_sampleCovariance
      |>.comp_aemeasurable hXm)
  rw [toMeasure_expectedCovarianceSpectralMeasure]
  refine ⟨(continuous_pow k).aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
  rw [Measure.lintegral_bind hL (by fun_prop)]
  have hinner (ω : Ω) :
      ∫⁻ x, ENNReal.ofReal ‖x ^ k‖ ∂L ω =
        ENNReal.ofReal ‖(Fintype.card p : ℝ)⁻¹ *
          RCLike.re ((X ω).sampleCovariance ^ k).trace‖ := by
    have hpos : ∀ᵐ x ∂L ω, 0 ≤ x ^ k :=
      ((Matrix.posSemidef_sampleCovariance (X ω)).ae_mem_Ici_spectralMeasure).mono
        fun _ hx ↦ pow_nonneg hx k
    have hint : Integrable (fun x : ℝ ↦ x ^ k) (L ω) :=
      ⟨(continuous_pow k).aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr
        ((lintegral_ofReal_norm_pow_spectralMeasure_le _ _ k).trans_lt ENNReal.ofReal_lt_top)⟩
    have he := integral_pow_spectralMeasure (X ω).sampleCovariance
      (isHermitian_sampleCovariance (X ω)) k
    have hnonneg := integral_nonneg_of_ae hpos
    simp only [Real.norm_of_nonneg (he ▸ hnonneg)]
    rw [← he, ofReal_integral_eq_lintegral_ofReal hint hpos]
    apply lintegral_congr_ae
    exact hpos.mono fun x hx ↦ congrArg ENNReal.ofReal (Real.norm_of_nonneg hx)
  simp_rw [hinner]
  exact (hasFiniteIntegral_iff_norm _).mp
    ((RCLike.reCLM.integrable_comp htrace).const_mul _).hasFiniteIntegral

/-- The expected spectral moment, cast into the matrix scalar field, is the expected
normalized trace power. -/
theorem ofReal_integral_pow_expectedCovarianceSpectralMeasure (hXm : AEMeasurable X P)
    (htrace : Integrable (fun ω ↦ ((X ω).sampleCovariance ^ k).trace) P) :
    ((∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure hXm : Measure ℝ) : ℝ) : 𝕜) =
      (Fintype.card p : 𝕜)⁻¹ * ∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P := by
  rw [integral_expectedCovarianceSpectralMeasure hXm
    (integrable_pow_expectedCovarianceSpectralMeasure hXm htrace), ← integral_ofReal]
  simp_rw [ofReal_integral_pow_spectralMeasure]
  exact integral_const_mul _ _

end Integrability

open Classical in
private noncomputable def leadingCovarianceMoment (k p n : ℕ) : ℝ :=
  (p : ℝ)⁻¹ * (n : ℝ)⁻¹ ^ k * ∑ π : NoncrossingPartition (univ : Finset (Fin k)),
    (p.descFactorial (k + 1 - #π.val.parts) : ℝ) * n.descFactorial #π.val.parts

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
  have hr := hn.natCast_descFactorial_sub_div_pow hy 1 (k - #π.val.parts)
  have hs := hn.natCast_descFactorial_sub_div_pow hself 0 #π.val.parts
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

variable {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  {P : Measure Ω} [IsProbabilityMeasure P] {p n k : ℕ} [NeZero p]
  {X : Ω → Matrix (Fin p) (Fin n) 𝕜}

private theorem norm_integral_pow_expectedCovarianceSpectralMeasure_sub_le (hk : k ≠ 0)
    (hXm : AEMeasurable X P)
    (hindep : iIndepFun (fun ij : Fin p × Fin n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂P = 0)
    (hLp : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P)
    (hsecond : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P = 1) {B : ℝ≥0}
    (hB : ∀ i j, ∫ ω, ‖X ω i j‖ ^ (2 * k) ∂P ≤ B) :
    ‖(∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure hXm : Measure ℝ)) -
        leadingCovarianceMoment k p n‖ ≤
      ((k : ℝ) ^ (2 * k + 1) * B * max ((p : ℝ) / n) 1 ^ (k - 1)) / n := by
  have hlead : (leadingCovarianceMoment k p n : 𝕜) = (p : 𝕜)⁻¹ * (n : 𝕜)⁻¹ ^ k *
      (Nat.card {w : (Fin k → Fin p) × (Fin k → Fin n) // IsLeadingBipartiteWord w.1 w.2} : 𝕜) := by
    rw [leadingCovarianceMoment, card_leadingBipartiteWord hk]
    push_cast
    simp only [Nat.card_fin]
  rw [Real.norm_eq_abs, ← RCLike.norm_ofReal (K := 𝕜), RCLike.ofReal_sub,
    ofReal_integral_pow_expectedCovarianceSpectralMeasure hXm
      (integrable_trace_sampleCovariance_pow hLp),
    Fintype.card_fin, hlead, mul_assoc, ← mul_sub,
    norm_mul, norm_inv, RCLike.norm_natCast,
    ← covarianceMoment_error_bound p n k (NeZero.ne p) hk B]
  have hfinite := norm_integral_trace_sampleCovariance_pow_sub_leading_le (X := X)
    hk hindep hmean hLp hsecond hB
  have hp : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  simpa only [Fintype.card_fin] using mul_le_mul_of_nonneg_left hfinite hp

end Bound

section Limit

variable {ι : Type*} {l : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {𝕜 : Type*} [RCLike 𝕜]
  {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
  {p n : ι → ℕ} [∀ i, NeZero (p i)] {X : (i : ι) → Ω i → Matrix (Fin (p i)) (Fin (n i)) 𝕜}
  {y : ℝ≥0}

/-- If the column dimension tends to infinity and the aspect ratio tends to `y`, the
`k`th expected spectral moment tends to the `k`th Marchenko–Pastur moment. For positive
`k`, this uses only independence, centring, unit second absolute moments and a uniform bound
on the entry moments of order `2k`, eventually along the filter. -/
theorem tendsto_integral_pow_expectedCovarianceSpectralMeasure_marchenkoPastur (k : ℕ)
    (hn : Tendsto n l atTop) (hy : Tendsto (fun i ↦ (p i : ℝ) / n i) l (𝓝 (y : ℝ)))
    (hXm : ∀ i, AEMeasurable (X i) (P i))
    (hindep : ∀ᶠ i in l,
      iIndepFun (fun ab : Fin (p i) × Fin (n i) ↦ fun ω ↦ X i ω ab.1 ab.2) (P i))
    (hmean : ∀ᶠ i in l, ∀ a b, ∫ ω, X i ω a b ∂P i = 0)
    (hLp : ∀ᶠ i in l, ∀ a b, MemLp (fun ω ↦ X i ω a b) (2 * k) (P i))
    (hsecond : ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ 2 ∂P i = 1)
    {B : ℝ≥0} (hB : ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ (2 * k) ∂P i ≤ B) :
    Tendsto (fun i ↦ ∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure (hXm i) : Measure ℝ)) l
      (𝓝 (∫ x, x ^ k ∂marchenkoPastur y)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa only [pow_zero, integral_const, probReal_univ, one_smul] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℝ)) l (𝓝 1))
  have hnR : Tendsto (fun i ↦ (n i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hn
  have hmajorant : Tendsto (fun i ↦
      ((k : ℝ) ^ (2 * k + 1) * B * max ((p i : ℝ) / n i) 1 ^ (k - 1)) / n i) l (𝓝 0) :=
    (tendsto_const_nhds.mul ((hy.max tendsto_const_nhds).pow (k - 1))).div_atTop hnR
  have herror : Tendsto (fun i ↦
      (∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure (hXm i) : Measure ℝ)) -
        leadingCovarianceMoment k (p i) (n i)) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmajorant
    filter_upwards [hindep, hmean, hLp, hsecond, hB] with i hI hM hL hS hBound
    exact norm_integral_pow_expectedCovarianceSpectralMeasure_sub_le
      hk (hXm i) hI hM hL hS hBound
  have hlead := tendsto_leadingCovarianceMoment hn (.of_forall fun i ↦ NeZero.ne (p i)) hy k
  simpa only [sub_add_cancel, zero_add] using herror.add hlead

/-- **Marchenko–Pastur convergence of the expected spectral measures by moments.** Independent
centred entries with unit second absolute moment and uniformly bounded moments of every order
give weak convergence of the expected empirical spectral measures when the column dimension
tends to infinity and the aspect ratio converges. Sample spaces and entry laws may vary with
the matrix size. The limit at aspect ratio zero is the point mass at one. -/
theorem tendsto_expectedCovarianceSpectralMeasure_marchenkoPastur_of_moments
    (hn : Tendsto n l atTop) (hy : Tendsto (fun i ↦ (p i : ℝ) / n i) l (𝓝 (y : ℝ)))
    (hXm : ∀ i, AEMeasurable (X i) (P i))
    (hindep : ∀ᶠ i in l,
      iIndepFun (fun ab : Fin (p i) × Fin (n i) ↦ fun ω ↦ X i ω ab.1 ab.2) (P i))
    (hmean : ∀ᶠ i in l, ∀ a b, ∫ ω, X i ω a b ∂P i = 0)
    (hsecond : ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ 2 ∂P i = 1)
    (hLp : ∀ k : ℕ, ∀ᶠ i in l, ∀ a b, MemLp (fun ω ↦ X i ω a b) (2 * k) (P i))
    (hB : ∀ k : ℕ, ∃ B : ℝ≥0, ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ (2 * k) ∂P i ≤ B) :
    Tendsto (fun i ↦ expectedCovarianceSpectralMeasure (hXm i)) l
      (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_integral_pow isCompact_Icc
    (ae_iff.mp (ae_mem_Icc_zero_marchenkoPastur y)) ?_ ?_
  · intro k
    filter_upwards [hLp k] with i hi
    exact integrable_pow_expectedCovarianceSpectralMeasure (hXm i)
      (integrable_trace_sampleCovariance_pow hi)
  · intro k
    obtain ⟨B, hBk⟩ := hB k
    exact tendsto_integral_pow_expectedCovarianceSpectralMeasure_marchenkoPastur
      k hn hy hXm hindep hmean (hLp k) hsecond hBk

end Limit

end TauCeti.Probability
