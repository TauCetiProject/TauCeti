/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Convex.FiniteMean
public import TauCeti.Analysis.Matrix.SampleSecondMoment

/-!
# Second moments of sample means

Let `X₁, …, X_r` be pairwise independent, square-integrable random vectors in a real Hilbert space
with a common mean `m`. Their sample mean `S = r⁻¹ ∑ₖ Xₖ` has mean-square error

`∫ ‖S - m‖² dP = r⁻² ∑ₖ ∫ ‖Xₖ - m‖² dP`,

so that averaging `r` samples with a common per-sample error `γ` divides it by `r`. Together with
Chebyshev's inequality for the second moment, `TauCeti.meas_ge_le_integral_norm_sq_div_sq` in
`TauCeti.Probability.Moments.Chebyshev`, this is the scale `1 / r` behind the elementary
concentration of empirical moments.

The identity rests on Bienaymé's identity for random vectors: the squared norm of a sum of
pairwise independent, centered, square-integrable random vectors has expectation equal to the
sum of the expected squared norms. Only pairwise independence is used, through the factorization
`∫ ⟪Xᵢ, Xⱼ⟫ = ⟪∫ Xᵢ, ∫ Xⱼ⟫` of `ProbabilityTheory.IndepFun.integral_bilin`, which makes every
cross term vanish. The sample mean is `TauCeti.finiteMean`, and the scalar statement is the
case `E = ℝ`.

The empirical second-moment matrix `TauCeti.sampleSecondMoment` of real random vectors is the
sample mean of their outer products, so each of its entries is a sample mean of products of
coordinates and the scalar identity bounds its mean-square error.

## Main statements

* `TauCeti.integral_norm_sum_sq_of_pairwise_indepFun`: Bienaymé's identity for random vectors.
* `TauCeti.integral_norm_finiteMean_sub_sq`: the mean-square error of a sample mean.
* `TauCeti.integral_finiteMean_sub_sq`: the same identity for real random variables.
* `TauCeti.integral_norm_finiteMean_sub_sq_of_forall_eq` and
  `TauCeti.integral_norm_finiteMean_sub_sq_le_of_forall_le`: the mean-square error is `γ / r`
  when every per-sample error equals `γ`, and at most `γ / r` when every one is at most `γ`.
* `TauCeti.integral_sampleSecondMoment_apply_sub_sq_le`: each entry of the empirical second-moment
  matrix has mean-square error at most `v / r` when the per-sample errors are at most `v`.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §1.3: the variance of sums of independent
  random variables.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

namespace TauCeti

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E]

/-- **Bienaymé's identity for random vectors.** If the random vectors `X i`, `i ∈ s`, in a real
Hilbert space are square-integrable, centered and pairwise independent, then the expected squared
norm of their sum is the sum of their expected squared norms. -/
theorem integral_norm_sum_sq_of_pairwise_indepFun [IsFiniteMeasure μ] {X : ι → Ω → E}
    {s : Finset ι} (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hindep : Set.Pairwise ↑s fun i j ↦ X i ⟂ᵢ[μ] X j) :
    ∫ ω, ‖∑ i ∈ s, X i ω‖ ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  -- Over `ℝ`, `innerSL ℝ` is linear only up to `starRingEnd ℝ = RingHom.id ℝ`, so its applications
  -- below are not syntactically `⟪·, ·⟫` and `simp` cannot rewrite them with
  -- `innerSL_apply_apply`; they agree with `⟪·, ·⟫` by that lemma, which is `rfl`.
  have hint : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω ↦ ⟪X i ω, X j ω⟫) μ := by
    intro i hi j hj
    obtain rfl | hij := eq_or_ne i j
    · simpa only [real_inner_self_eq_norm_sq] using
        (memLp_two_iff_integrable_sq_norm (hX i hi).aestronglyMeasurable).1 (hX i hi)
    · exact (hindep hi hj hij).integrable_bilin ((hX i hi).integrable one_le_two)
        ((hX j hj).integrable one_le_two) (innerSL ℝ)
  -- Pairwise independence makes every cross term `∫ ⟪X i, X j⟫` vanish.
  have hcross : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → ∫ ω, ⟪X i ω, X j ω⟫ ∂μ = 0 := by
    intro i hi j hj hji
    have h := (hindep hi hj hji.symm).integral_bilin ((hX i hi).integrable one_le_two)
      ((hX j hj).integrable one_le_two) (innerSL ℝ)
    rw [hmean i hi, map_zero, zero_apply] at h
    exact h
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  rw [integral_finsetSum _ fun i hi ↦ integrable_finsetSum _ fun j hj ↦ hint i hi j hj]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [integral_finsetSum _ fun j hj ↦ hint i hi j hj,
    sum_eq_single_of_mem i hi fun j hj hji ↦ hcross i hi j hj hji]

section SampleMean

variable [Fintype ι] [Nonempty ι]

/-- **The mean-square error of a sample mean.** If the random vectors `X i` in a real Hilbert space
are square-integrable, pairwise independent and have a common mean `m`, then their sample mean
`S` satisfies `∫ ‖S - m‖² = r⁻² ∑ᵢ ∫ ‖X i - m‖²`, where `r` is the number of samples. -/
theorem integral_norm_finiteMean_sub_sq [IsProbabilityMeasure μ] {X : ι → Ω → E} {m : E}
    (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = m)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) :
    ∫ ω, ‖finiteMean ℝ (X · ω) - m‖ ^ 2 ∂μ =
      ((Fintype.card ι : ℝ) ^ 2)⁻¹ * ∑ i, ∫ ω, ‖X i ω - m‖ ^ 2 ∂μ := by
  -- The deviation of the sample mean is the sample mean of the deviations.
  simp_rw [← finiteMean_sub_const, finiteMean_eq_inv_smul_sum, norm_smul, mul_pow, norm_inv,
    Real.norm_natCast, inv_pow]
  rw [integral_const_mul, integral_norm_sum_sq_of_pairwise_indepFun (X := fun i ω ↦ X i ω - m)
    (fun i _ ↦ (hX i).sub (memLp_const m)) (fun i _ ↦ ?_)
    (fun i _ j _ hij ↦ (hindep hij).comp (measurable_sub_const m) (measurable_sub_const m))]
  simp [integral_sub ((hX i).integrable one_le_two) (integrable_const m), hmean i]

/-- **The mean-square error of a sample mean of real random variables.** If the real random
variables `Z i` are square-integrable, pairwise independent and have a common mean `c`, then their
sample mean `S` satisfies `∫ (S - c)² = r⁻² ∑ᵢ ∫ (Z i - c)²`, where `r` is the number of
samples. -/
theorem integral_finiteMean_sub_sq [IsProbabilityMeasure μ] {Z : ι → Ω → ℝ} {c : ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, μ[Z i] = c)
    (hindep : Pairwise fun i j ↦ Z i ⟂ᵢ[μ] Z j) :
    ∫ ω, (finiteMean ℝ (Z · ω) - c) ^ 2 ∂μ =
      ((Fintype.card ι : ℝ) ^ 2)⁻¹ * ∑ i, ∫ ω, (Z i ω - c) ^ 2 ∂μ := by
  simpa only [Real.norm_eq_abs, sq_abs] using integral_norm_finiteMean_sub_sq hZ hmean hindep

/-- If, in addition to the hypotheses of `TauCeti.integral_norm_finiteMean_sub_sq`, every sample
has the same mean-square error `γ`, then the sample mean has mean-square error `γ / r`, where `r`
is the number of samples. -/
theorem integral_norm_finiteMean_sub_sq_of_forall_eq [IsProbabilityMeasure μ] {X : ι → Ω → E}
    {m : E} (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = m)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) {γ : ℝ}
    (hγ : ∀ i, ∫ ω, ‖X i ω - m‖ ^ 2 ∂μ = γ) :
    ∫ ω, ‖finiteMean ℝ (X · ω) - m‖ ^ 2 ∂μ = γ / Fintype.card ι := by
  have hr : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [integral_norm_finiteMean_sub_sq hX hmean hindep, sum_congr rfl fun i _ ↦ hγ i, sum_const,
    card_univ, nsmul_eq_mul]
  field_simp

/-- If, in addition to the hypotheses of `TauCeti.integral_norm_finiteMean_sub_sq`, every sample
has mean-square error at most `γ`, then the sample mean has mean-square error at most `γ / r`,
where `r` is the number of samples. -/
theorem integral_norm_finiteMean_sub_sq_le_of_forall_le [IsProbabilityMeasure μ]
    {X : ι → Ω → E} {m : E} (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = m)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) {γ : ℝ}
    (hγ : ∀ i, ∫ ω, ‖X i ω - m‖ ^ 2 ∂μ ≤ γ) :
    ∫ ω, ‖finiteMean ℝ (X · ω) - m‖ ^ 2 ∂μ ≤ γ / Fintype.card ι := by
  have hr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  rw [integral_norm_finiteMean_sub_sq hX hmean hindep]
  calc ((Fintype.card ι : ℝ) ^ 2)⁻¹ * ∑ i, ∫ ω, ‖X i ω - m‖ ^ 2 ∂μ
      ≤ ((Fintype.card ι : ℝ) ^ 2)⁻¹ * ∑ _i : ι, γ := by gcongr with i; exact hγ i
    _ = γ / Fintype.card ι := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        field_simp

end SampleMean

section SecondMomentMatrix

variable {κ : Type*} [Fintype ι]

/-- An entry of a random empirical second-moment matrix is square-integrable when the
corresponding products of coordinates of the samples are. -/
theorem memLp_sampleSecondMoment_apply {V : ι → Ω → κ → ℝ} {k l : κ}
    (hV : ∀ i, MemLp (fun ω ↦ V i ω k * V i ω l) 2 μ) :
    MemLp (fun ω ↦ sampleSecondMoment (V · ω) k l) 2 μ := by
  simp_rw [sampleSecondMoment_apply, finiteMean_eq_inv_smul_sum, smul_eq_mul]
  exact (memLp_finsetSum _ fun i _ ↦ hV i).const_mul _

/-- **Per-entry second-moment bound for the empirical second moment.** Fix coordinates `k, l` and
let `Yᵢ = Vᵢₖ Vᵢₗ`. If the `Yᵢ` are square-integrable, pairwise independent, have common mean
`M k l` and centered second moments at most `v`, then the corresponding entry of the empirical
second-moment matrix of the `r` samples has mean-square error at most `v / r`. -/
theorem integral_sampleSecondMoment_apply_sub_sq_le [IsProbabilityMeasure μ] [Nonempty ι]
    {V : ι → Ω → κ → ℝ} {M : Matrix κ κ ℝ} {k l : κ}
    (hV : ∀ i, MemLp (fun ω ↦ V i ω k * V i ω l) 2 μ)
    (hmean : ∀ i, ∫ ω, V i ω k * V i ω l ∂μ = M k l)
    (hindep : Pairwise fun i j ↦ (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[μ] fun ω ↦ V j ω k * V j ω l)
    {v : ℝ} (hv : ∀ i, ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂μ ≤ v) :
    ∫ ω, (sampleSecondMoment (V · ω) k l - M k l) ^ 2 ∂μ ≤ v / Fintype.card ι := by
  simpa only [sampleSecondMoment_apply, Real.norm_eq_abs, sq_abs] using
    integral_norm_finiteMean_sub_sq_le_of_forall_le hV hmean hindep
      (by simpa only [Real.norm_eq_abs, sq_abs] using hv)

end SecondMomentMatrix

end TauCeti
