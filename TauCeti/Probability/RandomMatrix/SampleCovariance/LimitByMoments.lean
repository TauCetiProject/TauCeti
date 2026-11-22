/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
public import TauCeti.Probability.RandomMatrix.SampleCovariance.RectangularMoments
import TauCeti.Data.Nat.Factorial.Asymptotics
import TauCeti.Probability.Distributions.MarchenkoPastur.Moments
import TauCeti.Probability.Moments.WeakConvergence
import TauCeti.Probability.RandomMatrix.SampleCovariance.TraceWord
import TauCeti.Probability.RandomMatrix.SampleCovariance.TraceIntegrability

/-!
# The Marchenko–Pastur moment limit for sample covariance matrices

For almost everywhere measurable random matrices with independent centred entries of unit second
absolute moment, the expected spectral moments converge to the Marchenko–Pastur moments when the
column dimension tends to infinity and the ratio of rows to columns converges. The row type is
nonempty at every index, including when this ratio tends to zero. At each degree `k > 1`,
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

/-- The leading covariance moment tends to the Marchenko–Pastur moment of the same degree
when the column count tends to infinity, the row count is eventually positive and the ratio
of rows to columns tends to `y`. -/
theorem tendsto_leadingCovarianceMoment {ι : Type*} {l : Filter ι} {p n : ι → ℕ}
    {y : ℝ≥0} (hn : Tendsto n l atTop) (hp : ∀ᶠ i in l, p i ≠ 0)
    (hy : Tendsto (fun i ↦ (p i : ℝ) / n i) l (𝓝 (y : ℝ))) (k : ℕ) :
    Tendsto (fun i ↦ leadingCovarianceMoment k (p i) (n i)) l
      (𝓝 (∫ x, x ^ k ∂marchenkoPastur y)) := by
  classical
  rw [integral_pow_marchenkoPastur]
  simp only [leadingCovarianceMoment_def, mul_sum]
  apply tendsto_finsetSum
  intro π _
  have hc : #π.val.parts ≤ k := by simpa using π.val.card_parts_le_card
  -- The row falling factorial in `leadingCovarianceMoment` has length `k + 1 - c`, while the
  -- limit lemma for it is stated for lengths of the form `m + 1`. Truncated subtraction makes
  -- this a propositional, not definitional, identity, so it is proved by `omega`.
  have hlen : k + 1 - #π.val.parts = k - #π.val.parts + 1 := by omega
  have hnpos : ∀ᶠ i in l, n i ≠ 0 := (hn.eventually_ge_atTop 1).mono fun _ hi ↦ by omega
  have hself : Tendsto (fun i ↦ (n i : ℝ) / n i) l (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    exact hnpos.mono fun _ hi ↦ (div_self (Nat.cast_ne_zero.mpr hi)).symm
  have hnR : Tendsto (fun i ↦ (n i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hn
  have hr := hnR.natCast_descFactorial_add_one_div_mul_pow hp hy (k - #π.val.parts)
  have hs := hnR.natCast_descFactorial_sub_div_pow hself 0 #π.val.parts
  simp only [Nat.sub_zero] at hs
  have ht := hr.mul hs
  rw [one_pow, mul_one] at ht
  refine ht.congr fun i ↦ ?_
  rw [hlen, ← pow_sub_mul_pow (n i : ℝ)⁻¹ hc]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

section Limit

variable {ι : Type*} {l : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {𝕜 : Type*} [RCLike 𝕜]
  {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
  {p n : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (p i)] [∀ i, Nonempty (p i)]
  {X : (i : ι) → Ω i → Matrix (p i) (n i) 𝕜} {y : ℝ≥0}

/-- If the column dimension tends to infinity and the ratio of rows to columns tends to `y`, the
`k`th expected spectral moment tends to the `k`th Marchenko–Pastur moment. The row types are
nonempty and the matrices are almost everywhere measurable at every index. For positive `k`, the
entries eventually have unit second absolute moment. For `k > 1`, they are also eventually
independent, centred and in `L^(2k)`, with a uniform bound on their absolute moments of order
`2k`. -/
theorem tendsto_integral_pow_expectedCovarianceSpectralMeasure_marchenkoPastur (k : ℕ)
    (hn : Tendsto (fun i ↦ Fintype.card (n i)) l atTop)
    (hy : Tendsto (fun i ↦ (Fintype.card (p i) : ℝ) / Fintype.card (n i)) l (𝓝 (y : ℝ)))
    (hXm : ∀ i, AEMeasurable (X i) (P i))
    (hindep : 1 < k → ∀ᶠ i in l,
      iIndepFun (fun ab : p i × n i ↦ fun ω ↦ X i ω ab.1 ab.2) (P i))
    (hmean : 1 < k → ∀ᶠ i in l, ∀ a b, ∫ ω, X i ω a b ∂P i = 0)
    (hLp : 1 < k → ∀ᶠ i in l, ∀ a b, MemLp (fun ω ↦ X i ω a b) (2 * k) (P i))
    (hsecond : k ≠ 0 → ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ 2 ∂P i = 1)
    (hB : 1 < k → ∃ B : ℝ≥0, ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ (2 * k) ∂P i ≤ B) :
    Tendsto (fun i ↦ ∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure (hXm i) : Measure ℝ)) l
      (𝓝 (∫ x, x ^ k ∂marchenkoPastur y)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa only [pow_zero, integral_const, probReal_univ, one_smul] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℝ)) l (𝓝 1))
  obtain ⟨B, hBound⟩ : ∃ B : ℝ≥0, ∀ᶠ i in l,
      1 < k → ∀ a b, ∫ ω, ‖X i ω a b‖ ^ (2 * k) ∂P i ≤ B := by
    by_cases hlarge : 1 < k
    · obtain ⟨B, hB⟩ := hB hlarge
      exact ⟨B, eventually_imp_distrib_left.mpr fun _ ↦ hB⟩
    · exact ⟨0, eventually_imp_distrib_left.mpr fun h' ↦ (hlarge h').elim⟩
  have hnR : Tendsto (fun i ↦ (Fintype.card (n i) : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hmajorant : Tendsto (fun i ↦ (k : ℝ) ^ (2 * k) * B * ∑ a ∈ range k,
      ((Fintype.card (p i) : ℝ) / Fintype.card (n i)) ^ a / Fintype.card (n i)) l (𝓝 0) := by
    simpa using (tendsto_finsetSum (range k) fun a _ ↦ (hy.pow a).div_atTop hnR).const_mul
      ((k : ℝ) ^ (2 * k) * B)
  have herror : Tendsto (fun i ↦
      (∫ x, x ^ k ∂(expectedCovarianceSpectralMeasure (hXm i) : Measure ℝ)) -
        leadingCovarianceMoment k (Fintype.card (p i)) (Fintype.card (n i))) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmajorant
    filter_upwards [eventually_imp_distrib_left.mpr hindep, eventually_imp_distrib_left.mpr hmean,
      eventually_imp_distrib_left.mpr hLp, hsecond hk, hBound] with i hI hM hL hS hBi
    exact norm_integral_pow_expectedCovarianceSpectralMeasure_sub_leadingCovarianceMoment_le hk
      (hXm i) hI hM hL hS hBi
  have hlead := tendsto_leadingCovarianceMoment hn (.of_forall fun _ ↦ Fintype.card_ne_zero) hy k
  simpa only [sub_add_cancel, zero_add] using herror.add hlead

/-- **Marchenko–Pastur convergence of the expected spectral measures by moments.** The row types
are nonempty and the matrices are almost everywhere measurable at every index. The entries are
eventually independent and centred with unit second absolute moment. For each degree `k > 1`, the
entries eventually lie in `L^(2k)` and have uniformly bounded absolute moments of order `2k`. The
expected spectral measures converge weakly when the column dimension tends to infinity and the
ratio of rows to columns converges. Sample spaces and entry laws may vary. At aspect ratio zero the
limit is the point mass at one. -/
theorem tendsto_expectedCovarianceSpectralMeasure_marchenkoPastur_of_uniform_entry_moment_bounds
    (hn : Tendsto (fun i ↦ Fintype.card (n i)) l atTop)
    (hy : Tendsto (fun i ↦ (Fintype.card (p i) : ℝ) / Fintype.card (n i)) l (𝓝 (y : ℝ)))
    (hXm : ∀ i, AEMeasurable (X i) (P i))
    (hindep : ∀ᶠ i in l, iIndepFun (fun ab : p i × n i ↦ fun ω ↦ X i ω ab.1 ab.2) (P i))
    (hmean : ∀ᶠ i in l, ∀ a b, ∫ ω, X i ω a b ∂P i = 0)
    (hsecond : ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ 2 ∂P i = 1)
    (hLp : ∀ k : ℕ, 1 < k → ∀ᶠ i in l, ∀ a b, MemLp (fun ω ↦ X i ω a b) (2 * k) (P i))
    (hB : ∀ k : ℕ, 1 < k → ∃ B : ℝ≥0, ∀ᶠ i in l, ∀ a b, ∫ ω, ‖X i ω a b‖ ^ (2 * k) ∂P i ≤ B) :
    Tendsto (fun i ↦ expectedCovarianceSpectralMeasure (hXm i)) l
      (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_integral_pow isCompact_Icc
    (ae_iff.mp (ae_mem_Icc_zero_marchenkoPastur y)) ?_ ?_
  · intro k
    filter_upwards [hLp (max k 2) (by omega)] with i hi
    exact integrable_pow_expectedCovarianceSpectralMeasure (hXm i)
      (integrable_trace_pow_sampleCovariance (fun _ ↦ inferInstance) fun a b ↦
        (hi a b).mono_exponent (by
          push_cast
          gcongr
          exact_mod_cast le_max_left k 2))
  · intro k
    exact tendsto_integral_pow_expectedCovarianceSpectralMeasure_marchenkoPastur
      k hn hy hXm (fun _ ↦ hindep) (fun _ ↦ hmean) (hLp k) (fun _ ↦ hsecond) (hB k)

end Limit

end TauCeti.Probability
