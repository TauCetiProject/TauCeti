/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Probability.Process.EmpiricalMeasure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The kernel density estimator

For a kernel `K : ℝ → ℝ`, a bandwidth `h` and a finite sample `x`, the kernel density estimator
is `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)` at `t`, where `n` is the size of the sample (Tsybakov, (1.2)).
Its sequence form uses the first `n` observations of a sequence and a bandwidth `hₙ`.

The estimator is the average over the sample of the rescaled translates `h⁻¹ K((t - xᵢ) / h)`.
For `h ≥ 0` the estimator of a nonnegative kernel is nonnegative, and for `h > 0` and a nonempty
sample it integrates to `∫ K` for an integrable kernel. For a Lebesgue-almost everywhere
nonnegative, almost everywhere measurable kernel and any bandwidth `h`, the convolution of the
empirical measure of the sample with `volume.withDensity (ENNReal.ofReal ∘ K_h)`, where
`K_h(t) = h⁻¹ K(t / h)`, is `volume.withDensity (ENNReal.ofReal ∘ fₙ)` for the estimator `fₙ`.
For `h > 0` both `K_h` and `fₙ` are then almost everywhere nonnegative, so the clipping by
`ENNReal.ofReal` changes nothing almost everywhere and `fₙ` is a density of that convolution; if
moreover `K` is a probability density and the sample is nonempty, both measures are probability
laws (the empirical distribution of the sample convolved with the law of density `K_h`). For
`h < 0` both clipped densities vanish almost everywhere.

## Main definitions

* `TauCeti.finiteKernelDensityEstimator K h x t`: the estimator of a finite sample `x`.
* `TauCeti.kernelDensityEstimator K h X n ω t`: the estimator of the first `n` observations of
  the sequence `X`, with bandwidth `h n`.

## Main results

* `TauCeti.finiteKernelDensityEstimator_eq_mul_sum`: the closed form `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)`.
* `TauCeti.finiteKernelDensityEstimator_nonneg`: the estimator of a nonnegative kernel with
  bandwidth `h ≥ 0` is nonnegative.
* `TauCeti.integral_finiteKernelDensityEstimator`: for an integrable kernel, `h > 0` and a
  nonempty sample, the estimator integrates to `∫ K`.
* `TauCeti.measurable_finiteKernelDensityEstimator_comp`,
  `TauCeti.measurable_kernelDensityEstimator`: for a measurable kernel, the estimator is jointly
  measurable in a measurable sample and a measurable evaluation point.
* `TauCeti.conv_withDensity_eq_withDensity_finiteKernelDensityEstimator`: for an almost everywhere
  nonnegative, almost everywhere measurable kernel, the empirical measure convolved with
  `volume.withDensity (ENNReal.ofReal ∘ K_h)` is `volume.withDensity (ENNReal.ofReal ∘ fₙ)`; for
  `h > 0` and a nonnegative kernel, the estimator is the density of that convolution.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, (1.2) (p. 3).

The definitions are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Nonparametric/Basic.lean`; the proofs are new.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace TauCeti

variable {κ : Type*} [Fintype κ]

/-- The kernel density estimator `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)` of a finite sample `x` of size
`n`, with kernel `K` and bandwidth `h`: the average over the sample of `h⁻¹ K((t - xᵢ) / h)`. -/
def finiteKernelDensityEstimator (K : ℝ → ℝ) (h : ℝ) (x : κ → ℝ) (t : ℝ) : ℝ :=
  univ.expect fun i ↦ h⁻¹ * K ((t - x i) / h)

/-- The kernel density estimator is the average of `h⁻¹ K((t - xᵢ) / h)` over the sample. -/
theorem finiteKernelDensityEstimator_def (K : ℝ → ℝ) (h : ℝ) (x : κ → ℝ) (t : ℝ) :
    finiteKernelDensityEstimator K h x t = univ.expect fun i ↦ h⁻¹ * K ((t - x i) / h) :=
  (rfl)

/-- The kernel density estimator is `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)`. -/
theorem finiteKernelDensityEstimator_eq_mul_sum (K : ℝ → ℝ) (h : ℝ) (x : κ → ℝ) (t : ℝ) :
    finiteKernelDensityEstimator K h x t = (Fintype.card κ * h)⁻¹ * ∑ i, K ((t - x i) / h) := by
  rw [finiteKernelDensityEstimator_def, Fintype.expect_eq_sum_div_card, ← mul_sum, mul_inv,
    div_eq_mul_inv]
  ring

/-- The kernel density estimator of the first `n` observations `X 0 ω, …, X (n - 1) ω` of a
sequence, with kernel `K` and bandwidth `h n`. -/
def kernelDensityEstimator {Ω : Type*} (K : ℝ → ℝ) (h : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (t : ℝ) : ℝ :=
  finiteKernelDensityEstimator K (h n) (fun i : Fin n ↦ X i ω) t

/-- The kernel density estimator of a sequence is the estimator of its first `n`
observations. -/
theorem kernelDensityEstimator_def {Ω : Type*} (K : ℝ → ℝ) (h : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) (t : ℝ) : kernelDensityEstimator K h X n ω t =
      finiteKernelDensityEstimator K (h n) (fun i : Fin n ↦ X i ω) t :=
  (rfl)

/-- The kernel density estimator of a sequence is `(n hₙ)⁻¹ ∑_{i < n} K((t - Xᵢ) / hₙ)`. -/
theorem kernelDensityEstimator_eq_sum_range {Ω : Type*} (K : ℝ → ℝ) (h : ℕ → ℝ)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : kernelDensityEstimator K h X n ω t =
      (n * h n)⁻¹ * ∑ i ∈ range n, K ((t - X i ω) / h n) := by
  rw [kernelDensityEstimator_def, finiteKernelDensityEstimator_eq_mul_sum, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range fun i ↦ K ((t - X i ω) / h n)]

/-- The kernel density estimator of a measurable kernel is measurable. -/
@[fun_prop]
theorem measurable_finiteKernelDensityEstimator {K : ℝ → ℝ} (hK : Measurable K) (h : ℝ)
    (x : κ → ℝ) : Measurable (finiteKernelDensityEstimator K h x) := by
  rw [funext (finiteKernelDensityEstimator_eq_mul_sum K h x)]
  fun_prop

/-- The kernel density estimator of a measurable kernel is jointly measurable in a measurable
sample `x ω` and a measurable evaluation point `t ω`. -/
@[fun_prop]
theorem measurable_finiteKernelDensityEstimator_comp {Ω : Type*} [MeasurableSpace Ω]
    {K : ℝ → ℝ} (hK : Measurable K) (h : ℝ) {x : Ω → κ → ℝ} (hx : ∀ i, Measurable fun ω ↦ x ω i)
    {t : Ω → ℝ} (ht : Measurable t) :
    Measurable fun ω ↦ finiteKernelDensityEstimator K h (x ω) (t ω) := by
  simp_rw [finiteKernelDensityEstimator_eq_mul_sum]
  fun_prop

/-- The kernel density estimator of a sequence of measurable observations, with a measurable
kernel, is jointly measurable in the sample point `ω` and a measurable evaluation point `t ω`. -/
@[fun_prop]
theorem measurable_kernelDensityEstimator {Ω : Type*} [MeasurableSpace Ω] {K : ℝ → ℝ}
    (hK : Measurable K) (h : ℕ → ℝ) {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (n : ℕ)
    {t : Ω → ℝ} (ht : Measurable t) :
    Measurable fun ω ↦ kernelDensityEstimator K h X n ω (t ω) := by
  simp_rw [kernelDensityEstimator_def]
  exact measurable_finiteKernelDensityEstimator_comp (x := fun ω (i : Fin n) ↦ X i ω) hK (h n)
    (fun i ↦ hX i) ht

/-- The kernel density estimator of a nonnegative kernel with a nonnegative bandwidth is
nonnegative. -/
theorem finiteKernelDensityEstimator_nonneg {K : ℝ → ℝ} (hK : ∀ u, 0 ≤ K u) {h : ℝ}
    (hh : 0 ≤ h) (x : κ → ℝ) (t : ℝ) : 0 ≤ finiteKernelDensityEstimator K h x t :=
  finiteKernelDensityEstimator_eq_mul_sum K h x t ▸
    mul_nonneg (inv_nonneg.2 (mul_nonneg (Nat.cast_nonneg _) hh)) (sum_nonneg fun _ _ ↦ hK _)

/-- The kernel density estimator of a nonempty sample with an integrable kernel and a positive
bandwidth integrates to `∫ K`. -/
theorem integral_finiteKernelDensityEstimator [Nonempty κ] {K : ℝ → ℝ} (hK : Integrable K)
    {h : ℝ} (hh : 0 < h) (x : κ → ℝ) :
    ∫ t, finiteKernelDensityEstimator K h x t = ∫ u, K u := by
  have hint : ∀ a : ℝ, Integrable fun t ↦ K ((t - a) / h) := fun a ↦
    (hK.comp_div hh.ne').comp_sub_right a
  have hone : ∀ a : ℝ, ∫ t, K ((t - a) / h) = h * ∫ u, K u := fun a ↦ by
    rw [integral_sub_right_eq_self (fun t ↦ K (t / h)) a, Measure.integral_comp_div,
      abs_of_pos hh, smul_eq_mul]
  simp only [finiteKernelDensityEstimator_eq_mul_sum]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint (x i)]
  simp only [hone, sum_const, card_univ, nsmul_eq_mul]
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- The convolution identity of `conv_withDensity_eq_withDensity_finiteKernelDensityEstimator`
for an everywhere nonnegative measurable kernel. -/
private theorem conv_withDensity_eq_withDensity_finiteKernelDensityEstimator_of_measurable
    {K : ℝ → ℝ} (hK : ∀ u, 0 ≤ K u) (hKm : Measurable K) (h : ℝ) (x : κ → ℝ) :
    (Probability.empiricalFiniteMeasure x : Measure ℝ) ∗
        volume.withDensity (fun t ↦ ENNReal.ofReal (h⁻¹ * K (t / h))) =
      volume.withDensity fun t ↦ ENNReal.ofReal (finiteKernelDensityEstimator K h x t) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp [finiteKernelDensityEstimator_eq_mul_sum]
  rcases lt_or_ge h 0 with hneg | hh
  · -- For a negative bandwidth both densities are nonpositive, so both measures vanish.
    have hzero : ∀ t, h⁻¹ * K (t / h) ≤ 0 := fun t ↦
      mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 hneg.le) (hK _)
    have hzero' : ∀ t, finiteKernelDensityEstimator K h x t ≤ 0 := fun t ↦
      (finiteKernelDensityEstimator_eq_mul_sum K h x t).symm ▸ mul_nonpos_of_nonpos_of_nonneg
        (inv_nonpos.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hneg.le))
        (sum_nonneg fun _ _ ↦ hK _)
    simp [ENNReal.ofReal_of_nonpos (hzero _), ENNReal.ofReal_of_nonpos (hzero' _)]
  set g : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (h⁻¹ * K (t / h))
  have hg : Measurable g := by fun_prop
  -- The estimator is the empirical average of the translates of `K_h`.
  have hdens : ∀ t, ENNReal.ofReal (finiteKernelDensityEstimator K h x t) =
      ∑ i, ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ * g (t - x i) := by
    intro t
    have hn : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
    rw [finiteKernelDensityEstimator_eq_mul_sum, mul_inv, mul_assoc, mul_sum,
      ENNReal.ofReal_mul (inv_nonneg.2 hn.le),
      ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg (inv_nonneg.2 hh) (hK _),
      ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast, mul_sum]
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.lintegral_conv hf, Probability.lintegral_empiricalFiniteMeasure
      (f := fun y ↦ ∫⁻ z, f (y + z) ∂volume.withDensity g)
      (hf.comp measurable_add).lintegral_prod_right',
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  simp only [hdens, sum_mul, Pi.mul_apply]
  rw [lintegral_finsetSum _ fun i _ ↦ by fun_prop, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ hg (by fun_prop)]
  simp_rw [mul_assoc]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [← lintegral_add_left_eq_self (fun t ↦ g (t - x i) * f t) (x i)]
  simp

/-- If two kernels agree Lebesgue-almost everywhere, so do their rescalings `h⁻¹ K(t / h)`. -/
private theorem inv_mul_comp_div_ae_eq {K K' : ℝ → ℝ} (hKK' : K =ᵐ[volume] K') (h : ℝ) :
    (fun t ↦ h⁻¹ * K (t / h)) =ᵐ[volume] fun t ↦ h⁻¹ * K' (t / h) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have h' := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hh)).ae_eq_comp hKK'
  filter_upwards [h'] with t ht
  simp only [Function.comp_apply, smul_eq_mul, inv_mul_eq_div] at ht
  rw [ht]

/-- For a Lebesgue-almost everywhere nonnegative, almost everywhere measurable kernel `K` and any
bandwidth `h`, the convolution of the empirical measure of `x` with
`volume.withDensity (ENNReal.ofReal ∘ K_h)`, `K_h(t) = h⁻¹ K(t / h)`, is `volume.withDensity` of
`ENNReal.ofReal` of the kernel density estimator of `x`. For `h > 0` and an everywhere
nonnegative kernel both functions are nonnegative, so the estimator itself is the density of the
convolution; for `h < 0` both clipped densities are almost everywhere zero, and for an empty
sample both measures are zero. -/
theorem conv_withDensity_eq_withDensity_finiteKernelDensityEstimator {K : ℝ → ℝ}
    (hK : ∀ᵐ u ∂volume, 0 ≤ K u) (hKm : AEMeasurable K volume) (h : ℝ) (x : κ → ℝ) :
    (Probability.empiricalFiniteMeasure x : Measure ℝ) ∗
        volume.withDensity (fun t ↦ ENNReal.ofReal (h⁻¹ * K (t / h))) =
      volume.withDensity fun t ↦ ENNReal.ofReal (finiteKernelDensityEstimator K h x t) := by
  set K' : ℝ → ℝ := fun u ↦ max (hKm.mk K u) 0
  have hKK' : K =ᵐ[volume] K' := by
    filter_upwards [hKm.ae_eq_mk, hK] with u hu h0
    simp only [K', ← hu, max_eq_left h0]
  have hKh := inv_mul_comp_div_ae_eq hKK' h
  have hest : finiteKernelDensityEstimator K h x =ᵐ[volume]
      finiteKernelDensityEstimator K' h x := by
    have hi (i : κ) := (measurePreserving_sub_right volume (x i)).quasiMeasurePreserving.ae_eq_comp
      hKh
    filter_upwards [ae_all_iff.2 hi] with t ht
    simp only [Function.comp_apply] at ht
    simp only [finiteKernelDensityEstimator_def, ht]
  have e₁ : volume.withDensity (fun t ↦ ENNReal.ofReal (h⁻¹ * K (t / h))) =
      volume.withDensity fun t ↦ ENNReal.ofReal (h⁻¹ * K' (t / h)) :=
    withDensity_congr_ae (hKh.mono fun _ ht ↦ congrArg ENNReal.ofReal ht)
  have e₂ : volume.withDensity (fun t ↦ ENNReal.ofReal (finiteKernelDensityEstimator K h x t)) =
      volume.withDensity fun t ↦ ENNReal.ofReal (finiteKernelDensityEstimator K' h x t) :=
    withDensity_congr_ae (hest.mono fun _ ht ↦ congrArg ENNReal.ofReal ht)
  rw [e₁, e₂]
  exact conv_withDensity_eq_withDensity_finiteKernelDensityEstimator_of_measurable
    (fun _ ↦ le_max_right _ _) (hKm.measurable_mk.max measurable_const) h x

end TauCeti
