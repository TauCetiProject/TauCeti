/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Analysis.Convex.FiniteMean
import TauCeti.Probability.Moments.Mixture
import TauCeti.Probability.Moments.SampleMean

/-!
# Rubin's combining rules for multiple imputation

The observed data are fixed. The complete-data posterior of a real parameter `θ` given the
missing data `z ∈ M` is a kernel `κ : Kernel M ℝ`, and the posterior predictive law of the
missing data is `ν : Measure M`, so that the observed-data posterior is the mixture `κ ∘ₘ ν`.
From `D` imputations `z₁, …, z_D` of the missing data, Rubin's combining rules form

* the multiple-imputation estimate `θ_MI = D⁻¹ ∑_d mean(κ z_d)` (`TauCeti.miMean`),
* the within-imputation variance `V_W = D⁻¹ ∑_d Var(κ z_d)` (`TauCeti.miWithin`),
* the between-imputation variance `B = (D - 1)⁻¹ ∑_d (mean(κ z_d) - θ_MI)²`
  (`TauCeti.miBetween`), and
* the total variance `T = V_W + (1 + D⁻¹) B` (`TauCeti.rubinTotalVariance`).

The means and variances are Bochner integrals and Mathlib's `variance`, so they are the
completed-data posterior moments when `κ z_d` is a probability measure with finite second moment.
For `D = 0` the estimate and the within-imputation variance are `0`, and for `D ≤ 1` the
between-imputation variance is `0`, through Lean's `0⁻¹ = 0` and the empty sum.

When the imputations are drawn independently from `ν`, the following identities hold exactly; they
are moment identities given the observed data, not the Student-`t` approximation of the source.
Write `B_∞ = Var_ν(z ↦ mean(κ z))` for the variance of the completed-data posterior means.

* `E θ_MI = E(θ | Y_obs)`, the mean of `κ ∘ₘ ν`, for `D ≥ 1`.
* `E V_W = ∫ Var(κ z) dν`, for `D ≥ 1` when the completed-data variances are integrable, and
  `E B = B_∞`, for `D ≥ 2`, the divisor `D - 1` making `B` unbiased.
* `Var θ_MI = D⁻¹ B_∞`.
* `E T = Var(θ | Y_obs) + D⁻¹ B_∞`, for `D ≥ 2`, by the law of total variance
  `Var(κ ∘ₘ ν) = ∫ Var(κ z) dν + B_∞`.
* For `θ` drawn from `κ ∘ₘ ν` independently of the imputations,
  `E(θ - θ_MI)² = Var(θ | Y_obs) + D⁻¹ B_∞`, for `D ≥ 1`. For `D ≥ 2`, the total variance is
  an unbiased estimate of the mean-square error of `θ_MI`.

## Main definitions

* `TauCeti.miMean`, `TauCeti.miWithin`, `TauCeti.miBetween`, `TauCeti.rubinTotalVariance`:
  `θ_MI`, `V_W`, `B` and `T`.

## Main results

* `TauCeti.integral_miMean`, `TauCeti.integral_miWithin`, `TauCeti.integral_miBetween`: the
  expectations of `θ_MI`, `V_W` and `B` over independent imputations.
* `TauCeti.variance_miMean`: the variance of `θ_MI`.
* `TauCeti.integral_sub_miMean_sq`: the mean-square error of `θ_MI` for an independent draw `θ`
  from the observed-data posterior.
* `TauCeti.integral_rubinTotalVariance`: Rubin's combining rules, exact form, collecting the
  expectations of `θ_MI`, `T` and `(θ - θ_MI)²` (Little–Rubin, (10.12)–(10.14)).

The mixture step is Tau Ceti's law of total variance `ProbabilityTheory.Kernel.variance_comp`, and
the unbiasedness of `B` is `TauCeti.integral_sum_sub_finiteMean_sq_pi`. There is no counterpart
in lean-CKSD.

## References

* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley
  (2019), Section 10.2, (10.8)–(10.14), pp. 233–234.
* D. B. Rubin, *Multiple Imputation for Nonresponse in Surveys*, Wiley (1987).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace TauCeti

variable {M : Type*} [MeasurableSpace M]

section Definitions

/-- The multiple-imputation estimate `θ_MI`, the average of the completed-data posterior means
`∫ x ∂κ (z d)` over the `D` imputations `z d`. It is `0` for `D = 0`. -/
def miMean {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) : ℝ :=
  (D : ℝ)⁻¹ * ∑ d, ∫ x, x ∂κ (z d)

/-- The within-imputation variance `V_W`, the average of the completed-data posterior variances
over the `D` imputations. It is `0` for `D = 0`. -/
def miWithin {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) : ℝ :=
  (D : ℝ)⁻¹ * ∑ d, variance id (κ (z d))

/-- The between-imputation variance `B`, the sample variance with divisor `D - 1` of the
completed-data posterior means. It is `0` for `D ≤ 1`. -/
def miBetween {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) : ℝ :=
  ((D : ℝ) - 1)⁻¹ * ∑ d, (∫ x, x ∂κ (z d) - miMean κ z) ^ 2

/-- Rubin's total variance `T = V_W + (1 + D⁻¹) B`. -/
def rubinTotalVariance {D : ℕ} (κ : Kernel M ℝ) (z : Fin D → M) : ℝ :=
  miWithin κ z + (1 + (D : ℝ)⁻¹) * miBetween κ z

end Definitions

section Basic

variable {D : ℕ} (κ : Kernel M ℝ)

/-- The defining formula of `TauCeti.miMean`. -/
theorem miMean_def (z : Fin D → M) : miMean κ z = (D : ℝ)⁻¹ * ∑ d, ∫ x, x ∂κ (z d) :=
  (rfl)

/-- The defining formula of `TauCeti.miWithin`. -/
theorem miWithin_def (z : Fin D → M) :
    miWithin κ z = (D : ℝ)⁻¹ * ∑ d, variance id (κ (z d)) :=
  (rfl)

/-- The defining formula of `TauCeti.miBetween`. -/
theorem miBetween_def (z : Fin D → M) :
    miBetween κ z = ((D : ℝ) - 1)⁻¹ * ∑ d, (∫ x, x ∂κ (z d) - miMean κ z) ^ 2 :=
  (rfl)

/-- The defining formula of `TauCeti.rubinTotalVariance`. -/
theorem rubinTotalVariance_def (z : Fin D → M) :
    rubinTotalVariance κ z = miWithin κ z + (1 + (D : ℝ)⁻¹) * miBetween κ z :=
  (rfl)

/-- The multiple-imputation estimate is the sample mean of the completed-data posterior means. -/
theorem miMean_eq_finiteMean (z : Fin D → M) :
    miMean κ z = finiteMean ℝ (fun d ↦ ∫ x, x ∂κ (z d)) := by
  rw [miMean_def, finiteMean_eq_inv_smul_sum, Fintype.card_fin, smul_eq_mul]

/-- The within-imputation variance is the sample mean of the completed-data posterior
variances. -/
theorem miWithin_eq_finiteMean (z : Fin D → M) :
    miWithin κ z = finiteMean ℝ (fun d ↦ variance id (κ (z d))) := by
  rw [miWithin_def, finiteMean_eq_inv_smul_sum, Fintype.card_fin, smul_eq_mul]

/-- With no imputations the estimate is `0`. -/
@[simp]
theorem miMean_fin_zero (z : Fin 0 → M) : miMean κ z = 0 := by
  simp [miMean_def]

/-- With no imputations the within-imputation variance is `0`. -/
@[simp]
theorem miWithin_fin_zero (z : Fin 0 → M) : miWithin κ z = 0 := by
  simp [miWithin_def]

/-- With no imputations the between-imputation variance is `0`. -/
@[simp]
theorem miBetween_fin_zero (z : Fin 0 → M) : miBetween κ z = 0 := by
  simp [miBetween_def]

/-- With no imputations the total variance is `0`. -/
@[simp]
theorem rubinTotalVariance_fin_zero (z : Fin 0 → M) : rubinTotalVariance κ z = 0 := by
  simp [rubinTotalVariance_def]

/-- With one imputation the estimate is the completed-data posterior mean. -/
@[simp]
theorem miMean_fin_one (z : Fin 1 → M) : miMean κ z = ∫ x, x ∂κ (z 0) := by
  simp [miMean_def]

/-- With one imputation the within-imputation variance is the completed-data posterior
variance. -/
@[simp]
theorem miWithin_fin_one (z : Fin 1 → M) : miWithin κ z = variance id (κ (z 0)) := by
  simp [miWithin_def]

/-- With one imputation the between-imputation variance is `0`, through `0⁻¹ = 0`. -/
@[simp]
theorem miBetween_fin_one (z : Fin 1 → M) : miBetween κ z = 0 := by
  simp [miBetween_def]

/-- With one imputation the total variance is the completed-data posterior variance. -/
@[simp]
theorem rubinTotalVariance_fin_one (z : Fin 1 → M) :
    rubinTotalVariance κ z = variance id (κ (z 0)) := by
  simp [rubinTotalVariance_def]

/-- The within-imputation variance is nonnegative. -/
theorem miWithin_nonneg (z : Fin D → M) : 0 ≤ miWithin κ z := by
  rw [miWithin_def]
  exact mul_nonneg (by positivity) (sum_nonneg fun d _ ↦ variance_nonneg _ _)

/-- The between-imputation variance is nonnegative. -/
theorem miBetween_nonneg (z : Fin D → M) : 0 ≤ miBetween κ z := by
  rcases D with _ | D
  · simp
  · rw [miBetween_def]
    exact mul_nonneg (inv_nonneg.2 (by push_cast; linarith)) (sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Rubin's total variance is nonnegative. -/
theorem rubinTotalVariance_nonneg (z : Fin D → M) : 0 ≤ rubinTotalVariance κ z := by
  rw [rubinTotalVariance_def]
  exact add_nonneg (miWithin_nonneg κ z) (mul_nonneg (by positivity) (miBetween_nonneg κ z))

/-- The between-imputation variance vanishes exactly when every completed-data posterior mean
equals the multiple-imputation estimate; for `D ≤ 1` both sides hold. -/
theorem miBetween_eq_zero_iff (z : Fin D → M) :
    miBetween κ z = 0 ↔ ∀ d, ∫ x, x ∂κ (z d) = miMean κ z := by
  rcases lt_or_ge D 2 with hD | hD
  · interval_cases D
    · simp
    · simp only [miBetween_fin_one, miMean_fin_one, true_iff]
      intro d
      rw [Subsingleton.elim d 0]
  · have hD' : ((D : ℝ) - 1)⁻¹ ≠ 0 := inv_ne_zero (by
      have : (2 : ℝ) ≤ D := by exact_mod_cast hD
      linarith)
    rw [miBetween_def, mul_eq_zero, or_iff_right hD',
      sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _]
    simp [sub_eq_zero]

end Basic

section Moments

variable (ν : Measure M) [IsProbabilityMeasure ν] (κ : Kernel M ℝ)

/-- If the completed-data posterior means are in `Lᵖ(ν)`, then the multiple-imputation estimate
is in `Lᵖ` of the law of `D` independent imputations from `ν`. -/
theorem memLp_miMean {p : ℝ≥0∞} (hm : MemLp (fun z ↦ ∫ x, x ∂κ z) p ν) {D : ℕ} :
    MemLp (miMean κ) p (Measure.pi fun _ : Fin D ↦ ν) := by
  simpa only [← miMean_eq_finiteMean] using hm.finiteMean_pi (ι := Fin D)

/-- If the completed-data posterior variances are integrable under `ν`, then the
within-imputation variance is integrable under the law of `D` independent imputations from `ν`.
By `ProbabilityTheory.Kernel.integrable_variance` this holds when `x²` is integrable under the
mixture `κ ∘ₘ ν` of a finite kernel. -/
theorem integrable_miWithin (hv : Integrable (fun z ↦ variance id (κ z)) ν) {D : ℕ} :
    Integrable (miWithin κ) (Measure.pi fun _ : Fin D ↦ ν) := by
  simpa only [← miWithin_eq_finiteMean, memLp_one_iff_integrable] using
    (memLp_one_iff_integrable.2 hv).finiteMean_pi (ι := Fin D)

/-- If the completed-data posterior means are square-integrable under `ν`, then the
between-imputation variance is integrable under the law of `D` independent imputations
from `ν`. -/
theorem integrable_miBetween (hm : MemLp (fun z ↦ ∫ x, x ∂κ z) 2 ν) {D : ℕ} :
    Integrable (miBetween κ) (Measure.pi fun _ : Fin D ↦ ν) := by
  have hbar := memLp_miMean ν κ hm (D := D)
  -- `miBetween κ` unfolds to a constant times a finite sum of squares of `L²` functions.
  exact (integrable_finsetSum _ fun d _ ↦
    ((hm.comp_measurePreserving (measurePreserving_eval _ d)).sub hbar).integrable_sq).const_mul _

/-- With `D ≥ 1` imputations drawn independently from `ν`, the multiple-imputation estimate has
expectation the observed-data posterior mean `∫ x ∂(κ ∘ₘ ν)`. -/
theorem integral_miMean (h : Integrable (fun x : ℝ ↦ x) (κ ∘ₘ ν)) {D : ℕ} (hD : D ≠ 0) :
    ∫ z, miMean κ z ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ x, x ∂(κ ∘ₘ ν) := by
  have : NeZero D := ⟨hD⟩
  simp only [miMean_eq_finiteMean]
  rw [integral_finiteMean_pi (Measure.integrable_integral_bind κ.aemeasurable h),
    Measure.integral_bind κ.aemeasurable h]

/-- With `D ≥ 1` imputations drawn independently from `ν`, the within-imputation variance has
expectation `∫ Var(κ z) dν`, the mean completed-data posterior variance, if the latter are
integrable. -/
theorem integral_miWithin (hv : Integrable (fun z ↦ variance id (κ z)) ν) {D : ℕ} (hD : D ≠ 0) :
    ∫ z, miWithin κ z ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ z, variance id (κ z) ∂ν := by
  have : NeZero D := ⟨hD⟩
  simp only [miWithin_eq_finiteMean]
  exact integral_finiteMean_pi hv

/-- With `D ≥ 2` imputations drawn independently from `ν`, the between-imputation variance has
expectation `B_∞ = Var_ν(z ↦ ∫ x ∂κ z)`, the variance of the completed-data posterior means: the
divisor `D - 1` makes it unbiased. -/
theorem integral_miBetween (hm : MemLp (fun z ↦ ∫ x, x ∂κ z) 2 ν) {D : ℕ} (hD : 2 ≤ D) :
    ∫ z, miBetween κ z ∂(Measure.pi fun _ : Fin D ↦ ν) = variance (fun z ↦ ∫ x, x ∂κ z) ν := by
  have : NeZero D := ⟨by omega⟩
  have hD1 : (D : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  simp only [miBetween_def, miMean_eq_finiteMean]
  rw [integral_const_mul, integral_sum_sub_finiteMean_sq_pi hm, Fintype.card_fin,
    inv_mul_cancel_left₀ hD1]

/-- With `D` imputations drawn independently from `ν`, the multiple-imputation estimate has
variance `D⁻¹ B_∞`, with `B_∞ = Var_ν(z ↦ ∫ x ∂κ z)`; for `D = 0` both sides are `0`. -/
theorem variance_miMean (hm : MemLp (fun z ↦ ∫ x, x ∂κ z) 2 ν) {D : ℕ} :
    variance (miMean κ) (Measure.pi fun _ : Fin D ↦ ν) =
      (D : ℝ)⁻¹ * variance (fun z ↦ ∫ x, x ∂κ z) ν := by
  rw [funext (miMean_eq_finiteMean κ), variance_finiteMean_pi hm, Fintype.card_fin]

/-- **The mean-square error of the multiple-imputation estimate.** Let `θ` be drawn from the
observed-data posterior `κ ∘ₘ ν`, with finite second moment, independently of `D ≥ 1`
imputations drawn independently from `ν`. Then
`E(θ - θ_MI)² = Var(κ ∘ₘ ν) + D⁻¹ B_∞`, with `B_∞ = Var_ν(z ↦ ∫ x ∂κ z)`. -/
theorem integral_sub_miMean_sq [IsMarkovKernel κ]
    (h2 : Integrable (fun x : ℝ ↦ x ^ 2) (κ ∘ₘ ν)) {D : ℕ} (hD : D ≠ 0) :
    ∫ p, (p.1 - miMean κ p.2) ^ 2 ∂((κ ∘ₘ ν).prod (Measure.pi fun _ : Fin D ↦ ν)) =
      variance id (κ ∘ₘ ν) + (D : ℝ)⁻¹ * variance (fun z ↦ ∫ x, x ∂κ z) ν := by
  set P := Measure.pi fun _ : Fin D ↦ ν
  have hX : MemLp (fun x : ℝ ↦ x) 2 (κ ∘ₘ ν) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 h2
  have hm : MemLp (fun z ↦ ∫ x, x ∂κ z) 2 ν :=
    Measure.memLp_integral_bind one_le_two (c := 1) κ.aemeasurable (ae_of_all _ fun _ ↦ by simp)
      hX
  have hbar : MemLp (miMean κ) 2 P := memLp_miMean ν κ hm
  -- `θ - θ_MI` has mean `0`, so its second moment is its variance, which splits over the
  -- product law as `Var θ + Var θ_MI`.
  have hmean : ∫ p, (p.1 - miMean κ p.2) ∂((κ ∘ₘ ν).prod P) = 0 := by
    rw [integral_sub ((hX.integrable one_le_two).comp_fst P)
      ((hbar.integrable one_le_two).comp_snd _), integral_fun_fst (fun x : ℝ ↦ x),
      integral_fun_snd (miMean κ), integral_miMean ν κ (hX.integrable one_le_two) hD]
    simp
  have hvar := variance_add_prod hX hbar.neg
  simp only [Pi.neg_apply, ← sub_eq_add_neg, variance_neg] at hvar
  rw [← variance_of_integral_eq_zero (X := fun p : ℝ × (Fin D → M) ↦ p.1 - miMean κ p.2)
    ((hX.comp_fst P).sub (hbar.comp_snd _)).aestronglyMeasurable.aemeasurable hmean, hvar,
    variance_miMean ν κ hm]
  rfl

/-- **Rubin's combining rules, exact form.** Given the observed data, let the `D ≥ 2` imputations
be drawn independently from the posterior predictive law `ν`, and let `θ` be drawn from the
observed-data posterior `κ ∘ₘ ν`, with finite second moment, independently of them. Then the
multiple-imputation estimate `θ_MI` has mean `E(θ | Y_obs)`, and both Rubin's total variance `T`
and the mean-square error `(θ - θ_MI)²` have mean `Var(θ | Y_obs) + D⁻¹ B_∞`, with
`B_∞ = Var_ν(z ↦ ∫ x ∂κ z)` (Little–Rubin, (10.12)–(10.14)). -/
theorem integral_rubinTotalVariance [IsMarkovKernel κ]
    (h2 : Integrable (fun x : ℝ ↦ x ^ 2) (κ ∘ₘ ν)) {D : ℕ} (hD : 2 ≤ D) :
    ∫ z, miMean κ z ∂(Measure.pi fun _ : Fin D ↦ ν) = ∫ x, x ∂(κ ∘ₘ ν) ∧
    ∫ z, rubinTotalVariance κ z ∂(Measure.pi fun _ : Fin D ↦ ν) =
      variance id (κ ∘ₘ ν) + (D : ℝ)⁻¹ * variance (fun z ↦ ∫ x, x ∂κ z) ν ∧
    ∫ p, (p.1 - miMean κ p.2) ^ 2 ∂((κ ∘ₘ ν).prod (Measure.pi fun _ : Fin D ↦ ν)) =
      variance id (κ ∘ₘ ν) + (D : ℝ)⁻¹ * variance (fun z ↦ ∫ x, x ∂κ z) ν := by
  have hD0 : D ≠ 0 := by omega
  have hX : MemLp id 2 (κ ∘ₘ ν) := (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 h2
  have hm : MemLp (fun z ↦ ∫ x, x ∂κ z) 2 ν :=
    Measure.memLp_integral_bind one_le_two (c := 1) κ.aemeasurable (ae_of_all _ fun _ ↦ by simp)
      hX
  refine ⟨integral_miMean ν κ (hX.integrable one_le_two) hD0, ?_,
    integral_sub_miMean_sq ν κ h2 hD0⟩
  simp only [rubinTotalVariance_def]
  have hv := κ.integrable_variance hX
  rw [integral_add (integrable_miWithin ν κ hv) ((integrable_miBetween ν κ hm).const_mul _),
    integral_const_mul, integral_miWithin ν κ hv hD0,
    integral_miBetween ν κ hm hD, Kernel.variance_comp κ hX]
  simp only [id]
  ring

end Moments

end TauCeti
