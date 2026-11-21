/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Probability.Process.EmpiricalMeasure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The kernel density estimator

For a kernel `K : ℝ → ℝ`, a bandwidth `h` and a finite sample `x`, the kernel density estimator
is `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)` at `t`, where `n` is the size of the sample (Tsybakov, (1.2)).
Its sequence form uses the first `n` observations of a sequence and a bandwidth `hₙ`.

For `h ≥ 0` the estimator of a nonnegative kernel is nonnegative, and for `h > 0` and a nonempty
sample it integrates to `∫ K` for an integrable kernel. For a nonnegative measurable kernel and any
bandwidth `h`, the convolution of the empirical measure of the sample with
`volume.withDensity (ENNReal.ofReal ∘ K_h)`, where `K_h(t) = h⁻¹ K(t / h)`, is
`volume.withDensity (ENNReal.ofReal ∘ fₙ)` for the estimator `fₙ`. For `h > 0` both `K_h` and `fₙ`
are nonnegative, so the clipping by `ENNReal.ofReal` does nothing and `fₙ` is the density of that
convolution; if moreover `K` is a probability density and the sample is nonempty, both measures
are probability laws (the empirical distribution of the sample convolved with the law of
density `K_h`). For `h < 0` both clipped densities vanish.

## Main definitions

* `TauCeti.finiteKernelDensityEstimator K h x t`: the estimator of a finite sample `x`.
* `TauCeti.kernelDensityEstimator K h X n ω t`: the estimator of the first `n` observations of
  the sequence `X`, with bandwidth `h n`.

## Main results

* `TauCeti.finiteKernelDensityEstimator_nonneg`: the estimator is nonnegative.
* `TauCeti.integral_finiteKernelDensityEstimator`: the estimator integrates to `∫ K`.
* `TauCeti.conv_withDensity_eq_withDensity_finiteKernelDensityEstimator`: the empirical measure
  convolved with `volume.withDensity (ENNReal.ofReal ∘ K_h)` is
  `volume.withDensity (ENNReal.ofReal ∘ fₙ)`; for `h > 0`, the estimator is the density of that
  convolution.

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
`n`, with kernel `K` and bandwidth `h`. -/
def finiteKernelDensityEstimator (K : ℝ → ℝ) (h : ℝ) (x : κ → ℝ) (t : ℝ) : ℝ :=
  (Fintype.card κ * h)⁻¹ * ∑ i, K ((t - x i) / h)

/-- The kernel density estimator is `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)`. -/
theorem finiteKernelDensityEstimator_def (K : ℝ → ℝ) (h : ℝ) (x : κ → ℝ) (t : ℝ) :
    finiteKernelDensityEstimator K h x t = (Fintype.card κ * h)⁻¹ * ∑ i, K ((t - x i) / h) :=
  (rfl)

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
  rw [kernelDensityEstimator_def, finiteKernelDensityEstimator_def, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range fun i ↦ K ((t - X i ω) / h n)]

/-- The kernel density estimator of a measurable kernel is measurable. -/
@[fun_prop]
theorem measurable_finiteKernelDensityEstimator {K : ℝ → ℝ} (hK : Measurable K) (h : ℝ)
    (x : κ → ℝ) : Measurable (finiteKernelDensityEstimator K h x) := by
  rw [funext (finiteKernelDensityEstimator_def K h x)]
  fun_prop

/-- The kernel density estimator of a nonnegative kernel is nonnegative. -/
theorem finiteKernelDensityEstimator_nonneg {K : ℝ → ℝ} (hK : ∀ u, 0 ≤ K u) {h : ℝ}
    (hh : 0 ≤ h) (x : κ → ℝ) (t : ℝ) : 0 ≤ finiteKernelDensityEstimator K h x t :=
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
  simp only [finiteKernelDensityEstimator_def]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint (x i)]
  simp only [hone, sum_const, card_univ, nsmul_eq_mul]
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- For a nonnegative measurable kernel `K` and any bandwidth `h`, the convolution of the empirical
measure of `x` with `volume.withDensity (ENNReal.ofReal ∘ K_h)`, `K_h(t) = h⁻¹ K(t / h)`, is
`volume.withDensity` of `ENNReal.ofReal` of the kernel density estimator of `x`. For `h > 0` both
functions are nonnegative, so the estimator itself is the density of the convolution; for
`h < 0` both clipped densities are zero, and for an empty sample both measures are zero. -/
theorem conv_withDensity_eq_withDensity_finiteKernelDensityEstimator {K : ℝ → ℝ}
    (hK : ∀ u, 0 ≤ K u) (hKm : Measurable K) (h : ℝ) (x : κ → ℝ) :
    (Probability.empiricalFiniteMeasure x : Measure ℝ) ∗
        volume.withDensity (fun t ↦ ENNReal.ofReal (h⁻¹ * K (t / h))) =
      volume.withDensity fun t ↦ ENNReal.ofReal (finiteKernelDensityEstimator K h x t) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp [finiteKernelDensityEstimator_def]
  rcases lt_or_ge h 0 with hneg | hh
  · -- For a negative bandwidth both densities are nonpositive, so both measures vanish.
    have hzero : ∀ t, h⁻¹ * K (t / h) ≤ 0 := fun t ↦
      mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 hneg.le) (hK _)
    have hzero' : ∀ t, finiteKernelDensityEstimator K h x t ≤ 0 := fun t ↦
      mul_nonpos_of_nonpos_of_nonneg
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
    rw [finiteKernelDensityEstimator_def, mul_inv, mul_assoc, mul_sum,
      ENNReal.ofReal_mul (inv_nonneg.2 hn.le),
      ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg (inv_nonneg.2 hh) (hK _),
      ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast, mul_sum]
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.lintegral_conv hf, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  simp only [Probability.empiricalFiniteMeasure_toMeasure, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, hdens, sum_mul, Pi.mul_apply]
  rw [lintegral_finsetSum _ fun i _ ↦ by fun_prop]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ hg (by fun_prop)]
  simp_rw [mul_assoc]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [← lintegral_add_left_eq_self (fun t ↦ g (t - x i) * f t) (x i)]
  simp

end TauCeti
