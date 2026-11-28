/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import TauCeti.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Convex.FiniteMean
public import Mathlib.Probability.Moments.Variance
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Second moments of sample means

Let `X₁, …, X_r` be pairwise independent, square-integrable random vectors in a real Hilbert space
with a common mean `m`. Their sample mean `S = r⁻¹ ∑ₖ Xₖ` has mean-square error

`∫ ‖S - m‖² dP = r⁻² ∑ₖ ∫ ‖Xₖ - m‖² dP`,

so that averaging `r` samples with a common per-sample error `γ` divides it by `r`. Together with
Chebyshev's inequality for the second moment, `TauCeti.meas_ge_le_integral_sq_div_sq` in
`TauCeti.Probability.Moments.Chebyshev`, this is the scale `1 / r` behind the elementary
concentration of empirical moments.

The identity rests on Bienaymé's identity for random vectors: the squared norm of a sum of
pairwise independent, centered, square-integrable random vectors has expectation equal to the
sum of the expected squared norms. Only pairwise independence is used, through the factorization
`∫ ⟪Xᵢ, Xⱼ⟫ = ⟪∫ Xᵢ, ∫ Xⱼ⟫` of `ProbabilityTheory.IndepFun.integral_bilin`, which makes every
cross term vanish. The sample mean is `TauCeti.finiteMean`, and the scalar statement is the
case `E = ℝ`.

For real variables, the sum of squared deviations from the sample mean then has expectation
`(1 - r⁻¹) ∑ₖ ∫ (Xₖ - m)² dP`, by the König–Huygens identity `TauCeti.sum_sub_finiteMean_sq`.
For a sample `z` of size `r` drawn independently from one law `ν`, that is under
`Measure.pi fun _ ↦ ν`, the sample mean of `f (z i)` has expectation `∫ f dν` and variance
`r⁻¹ Var_ν(f)`. For `r ≥ 1` the sum of the squared deviations from the sample mean has
expectation `(r - 1) Var_ν(f)`, so for `r ≥ 2` the sample variance with divisor `r - 1` is
unbiased for `Var_ν(f)`.

## Main statements

* `TauCeti.integral_norm_sum_sq_of_pairwise_indepFun`: Bienaymé's identity for random vectors.
* `TauCeti.integral_norm_finiteMean_sub_sq`: the mean-square error of a sample mean.
* `TauCeti.integral_finiteMean_sub_sq`: the same identity for real random variables.
* `TauCeti.integral_norm_finiteMean_sub_sq_of_forall_eq` and
  `TauCeti.integral_norm_finiteMean_sub_sq_le_of_forall_le`: the mean-square error is `γ / r`
  when every per-sample error equals `γ`, and at most `γ / r` when every one is at most `γ`.
* `TauCeti.integral_sum_sub_finiteMean_sq`: the expected sum of squared deviations from the
  sample mean.
* `MeasureTheory.MemLp.finiteMean_pi`, `TauCeti.integral_finiteMean_pi` and
  `TauCeti.variance_finiteMean_pi`: integrability, mean and variance of the sample mean of an
  independent sample from one law.
* `TauCeti.integral_sum_sub_finiteMean_sq_pi`: the expected sum of squared deviations of a
  nonempty sample, `(r - 1) Var_ν(f)`; for `r ≥ 2` the sample variance is unbiased.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §1.3: the variance of sums of independent
  random variables.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

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
  -- Pairwise independence makes every cross term `∫ ⟪X i, X j⟫` vanish.
  have hcross : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → ∫ ω, ⟪X i ω, X j ω⟫ ∂μ = 0 := by
    intro i hi j hj hji
    have h := (hindep hi hj hji.symm).integral_bilin ((hX i hi).integrable one_le_two)
      ((hX j hj).integrable one_le_two) (innerSL ℝ)
    rw [hmean i hi, map_zero, zero_apply] at h
    exact h
  exact integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero
    (fun i hi j hj ↦ (hX i hi).integrable_inner (hX j hj))
    (fun i hi j hj hij ↦ hcross i hi j hj hij.symm)

/-- For centered, pairwise independent square-integrable variables on a probability space,
a common second-moment bound controls the mean norm of their sum. -/
theorem integral_norm_sum_le_of_pairwise_indepFun [IsProbabilityMeasure μ]
    {X : ι → Ω → E} {s : Finset ι} (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (hindep : Set.Pairwise ↑s fun i j ↦ X i ⟂ᵢ[μ] X j)
    {v : ℝ} (hv : ∀ i ∈ s, ∫ ω, ‖X i ω‖ ^ 2 ∂μ ≤ v) :
    (∫ ω, ‖∑ i ∈ s, X i ω‖ ∂μ) ≤ Real.sqrt (s.card * v) := by
  refine (le_of_abs_le ((memLp_finsetSum s hX).norm.integrable_sq.abs_integral_le_sqrt_integral_sq
    prob_le_one)).trans ?_
  rw [integral_norm_sum_sq_of_pairwise_indepFun hX hmean hindep]
  exact Real.sqrt_le_sqrt ((sum_le_sum hv).trans_eq (by simp [nsmul_eq_mul]))

/-- The second moment of a linear form in pairwise independent centered coordinates is the
sum of the coordinate second moments weighted by the squared coefficients. -/
theorem integral_sq_sum_mul_of_pairwise_indepFun [Fintype ι] [IsFiniteMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hind : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) (a : ι → ℝ) :
    ∫ ω, (∑ i, a i * X i ω) ^ 2 ∂μ = ∑ i, a i ^ 2 * ∫ ω, X i ω ^ 2 ∂μ := by
  have h := integral_norm_sum_sq_of_pairwise_indepFun
    (s := (univ : Finset ι)) (X := fun i ω ↦ a i * X i ω)
    (fun i _ ↦ (hX i).const_mul _) (fun i _ ↦ by simp [integral_const_mul, hmean i])
    (fun i _ j _ hij ↦ (hind hij).comp (measurable_const_mul _) (measurable_const_mul _))
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, integral_const_mul] using h

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

omit [Nonempty ι] in
/-- **The expected sum of squared deviations from the sample mean.** If the real random variables
`Z i` are square-integrable, pairwise independent and have a common mean `c`, then the sum of the
squared deviations of the `Z i` from their sample mean has expectation
`(1 - r⁻¹) ∑ᵢ ∫ (Z i - c)²`, where `r` is the number of samples. For no samples both sides
are `0`. -/
theorem integral_sum_sub_finiteMean_sq [IsProbabilityMeasure μ] {Z : ι → Ω → ℝ} {c : ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, μ[Z i] = c)
    (hindep : Pairwise fun i j ↦ Z i ⟂ᵢ[μ] Z j) :
    ∫ ω, ∑ i, (Z i ω - finiteMean ℝ (Z · ω)) ^ 2 ∂μ =
      (1 - (Fintype.card ι : ℝ)⁻¹) * ∑ i, ∫ ω, (Z i ω - c) ^ 2 ∂μ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hr : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hint (i : ι) : Integrable (fun ω ↦ (Z i ω - c) ^ 2) μ :=
    ((hZ i).sub (memLp_const c)).integrable_sq
  have hbar : MemLp (fun ω ↦ finiteMean ℝ (Z · ω)) 2 μ := by
    simp only [finiteMean_eq_inv_smul_sum]
    exact (memLp_finsetSum univ fun i _ ↦ hZ i).const_smul (Fintype.card ι : ℝ)⁻¹
  have hbar' : Integrable (fun ω ↦ (finiteMean ℝ (Z · ω) - c) ^ 2) μ :=
    (hbar.sub (memLp_const c)).integrable_sq
  simp only [sum_sub_finiteMean_sq _ c]
  rw [integral_sub (integrable_finsetSum _ fun i _ ↦ hint i) (hbar'.const_mul _),
    integral_finsetSum _ fun i _ ↦ hint i, integral_const_mul,
    integral_finiteMean_sub_sq hZ hmean hindep]
  field_simp

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

section Pi

/-! ### Samples drawn independently from one law -/

variable {M : Type*} [MeasurableSpace M] {ν : Measure M} [IsProbabilityMeasure ν]

omit [Nonempty ι] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The sample mean of a function in `Lᵖ(ν)` over a sample drawn independently from `ν` is in
`Lᵖ` of the product law. -/
theorem _root_.MeasureTheory.MemLp.finiteMean_pi [NormedSpace ℝ E] {p : ℝ≥0∞} {f : M → E}
    (hf : MemLp f p ν) :
    MemLp (fun z : ι → M ↦ finiteMean ℝ (fun i ↦ f (z i))) p (Measure.pi fun _ : ι ↦ ν) := by
  simp only [finiteMean_eq_inv_smul_sum]
  exact (memLp_finsetSum univ fun i _ ↦
    hf.comp_measurePreserving (measurePreserving_eval _ i)).const_smul (Fintype.card ι : ℝ)⁻¹

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The sample mean of an integrable `f` over a sample drawn independently from `ν` has
expectation `∫ f dν`. -/
theorem integral_finiteMean_pi [NormedSpace ℝ E] {f : M → E} (hf : Integrable f ν) :
    ∫ z, finiteMean ℝ (fun i ↦ f (z i)) ∂(Measure.pi fun _ : ι ↦ ν) = ∫ x, f x ∂ν := by
  have hr : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have heval (i : ι) : ∫ z, f (z i) ∂(Measure.pi fun _ : ι ↦ ν) = ∫ x, f x ∂ν :=
    integral_comp_eval hf.aestronglyMeasurable
  simp only [finiteMean_eq_inv_smul_sum]
  rw [integral_smul, integral_finsetSum _ fun i _ ↦ integrable_comp_eval hf]
  simp only [heval, sum_const, card_univ, smul_smul, ← Nat.cast_smul_eq_nsmul ℝ,
    inv_mul_cancel₀ hr, one_smul]

omit [Nonempty ι] in
/-- The sample mean of a square-integrable real `f` over a sample of size `r` drawn independently
from `ν` has variance `r⁻¹ Var_ν(f)`. For `r = 0` both sides are `0`. -/
theorem variance_finiteMean_pi {f : M → ℝ} (hf : MemLp f 2 ν) :
    variance (fun z ↦ finiteMean ℝ (fun i ↦ f (z i))) (Measure.pi fun _ : ι ↦ ν) =
      (Fintype.card ι : ℝ)⁻¹ * variance f ν := by
  -- The sample mean is `r⁻¹` times a sum of `r` independent copies of `f`: Mathlib's
  -- `variance_sum_pi` gives the variance `r Var_ν(f)` of the sum.
  have hsum : Var[fun z : ι → M ↦ ∑ i, f (z i); Measure.pi fun _ ↦ ν] = ∑ _ : ι, Var[f; ν] := by
    simpa only [Finset.sum_fn] using variance_sum_pi (μ := fun _ : ι ↦ ν) fun _ ↦ hf
  simp only [finiteMean_eq_inv_smul_sum, smul_eq_mul, variance_const_mul, hsum, sum_const,
    card_univ, nsmul_eq_mul]
  rcases eq_or_ne (Fintype.card ι : ℝ) 0 with hr | hr
  · simp [hr]
  · field_simp

/-- **Unbiasedness of the sample variance.** For a square-integrable real `f` and a sample of
size `r ≥ 1` drawn independently from `ν`, the sum of the squared deviations of the `f (z i)` from
their sample mean has expectation `(r - 1) Var_ν(f)`. Hence for `r ≥ 2` the sample variance with
divisor `r - 1` is unbiased for `Var_ν(f)`; for `r = 1` both sides are `0`. -/
theorem integral_sum_sub_finiteMean_sq_pi {f : M → ℝ} (hf : MemLp f 2 ν) :
    ∫ z, ∑ i, (f (z i) - finiteMean ℝ (fun i ↦ f (z i))) ^ 2 ∂(Measure.pi fun _ : ι ↦ ν) =
      ((Fintype.card ι : ℝ) - 1) * variance f ν := by
  have hr : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hfm := hf.aestronglyMeasurable
  have hZ (i : ι) : MemLp (fun z : ι → M ↦ f (z i)) 2 (Measure.pi fun _ : ι ↦ ν) :=
    hf.comp_measurePreserving (measurePreserving_eval _ i)
  have hindep : Pairwise fun i j ↦ (fun z : ι → M ↦ f (z i)) ⟂ᵢ[Measure.pi fun _ : ι ↦ ν]
      fun z ↦ f (z j) := fun _ _ hij ↦ (iIndepFun_pi fun _ ↦ hfm.aemeasurable).indepFun hij
  have hsq (i : ι) :
      ∫ z, (f (z i) - ∫ x, f x ∂ν) ^ 2 ∂(Measure.pi fun _ : ι ↦ ν) = variance f ν := by
    rw [variance_eq_integral hfm.aemeasurable]
    exact integral_comp_eval (μ := fun _ : ι ↦ ν) (f := fun x ↦ (f x - ∫ x, f x ∂ν) ^ 2)
      (by fun_prop)
  refine (integral_sum_sub_finiteMean_sq hZ (fun _ ↦ integral_comp_eval hfm) hindep).trans ?_
  simp only [hsq, sum_const, card_univ, nsmul_eq_mul]
  field_simp

end Pi

end TauCeti
