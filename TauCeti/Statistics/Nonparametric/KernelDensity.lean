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
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Haar.Rescale

/-!
# The kernel density estimator

For a kernel `K : ℝ → ℝ`, a bandwidth `h` and a finite sample `x`, the kernel density estimator
is `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)` at `t`, where `n` is the size of the sample (Tsybakov, (1.2)).
Its sequence form uses the first `n` observations of a sequence and a bandwidth `hₙ`.

The estimator is the average over the sample of the rescaled translates `h⁻¹ K((t - xᵢ) / h)`.
It vanishes for an empty sample and for `h = 0`. For `h ≥ 0` the estimator of a nonnegative kernel
is nonnegative (almost everywhere for an almost everywhere nonnegative kernel), it is integrable
for an integrable kernel, and for `h > 0` and a nonempty sample it integrates to `∫ K`. For a
Lebesgue-almost everywhere nonnegative, almost everywhere measurable kernel and any bandwidth `h`,
the convolution of the empirical measure of the sample with
`volume.withDensity (ENNReal.ofReal ∘ K_h)`, where `K_h(t) = h⁻¹ K(t / h)`, is
`volume.withDensity (ENNReal.ofReal ∘ fₙ)` for the estimator `fₙ`. For `h > 0` the almost
everywhere nonnegativity of `K` makes both `K_h` and `fₙ` almost everywhere nonnegative, so the
clipping by `ENNReal.ofReal` has no effect on the two measures and `fₙ` is a density of that
convolution; if moreover `K` is a probability density and the sample is nonempty, both measures
are probability laws (the empirical distribution of the sample convolved with the law of density
`K_h`). For `h < 0` both clipped densities vanish almost everywhere.

## Main definitions

* `TauCeti.finiteKernelDensityEstimator K h x t`: the estimator of a finite sample `x`.
* `TauCeti.kernelDensityEstimator K h X n ω t`: the estimator of the first `n` observations of
  the sequence `X`, with bandwidth `h n`.

## Main results

* `TauCeti.finiteKernelDensityEstimator_eq_mul_sum`: the closed form `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)`.
* `TauCeti.finiteKernelDensityEstimator_nonneg`,
  `TauCeti.ae_nonneg_finiteKernelDensityEstimator`: the estimator of a (Lebesgue-almost
  everywhere) nonnegative kernel with bandwidth `h ≥ 0` is (almost everywhere) nonnegative.
* `TauCeti.integrable_finiteKernelDensityEstimator`,
  `TauCeti.integral_finiteKernelDensityEstimator`: for an integrable kernel the estimator is
  integrable, and for `h > 0` and a nonempty sample it integrates to `∫ K`.
* `TauCeti.measurable_finiteKernelDensityEstimator_comp`,
  `TauCeti.measurable_kernelDensityEstimator_comp`: for a measurable kernel, the map
  `ω ↦ fₙ(t ω)` is measurable on `Ω` when the sample (its first `n` terms in the sequence form),
  the bandwidth (in the finite form) and the evaluation point `t ω` are measurable in `ω`. Joint
  measurability on a product `Ω × ℝ` is the special case of the projections `ω ↦ ω.1` and
  `t = Prod.snd`.
* `TauCeti.aemeasurable_finiteKernelDensityEstimator`: for an almost everywhere measurable kernel
  the estimator is almost everywhere measurable.
* `TauCeti.conv_withDensity_eq_withDensity_finiteKernelDensityEstimator`: for an almost everywhere
  nonnegative, almost everywhere measurable kernel, the empirical measure convolved with
  `volume.withDensity (ENNReal.ofReal ∘ K_h)` is `volume.withDensity (ENNReal.ofReal ∘ fₙ)`; for
  `h > 0` both densities are almost everywhere nonnegative, so the clipping has no effect and the
  estimator is a density of that convolution.

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

/-- The kernel density estimator of an empty sample vanishes. -/
@[simp]
theorem finiteKernelDensityEstimator_of_isEmpty [IsEmpty κ] (K : ℝ → ℝ) (h : ℝ) (x : κ → ℝ)
    (t : ℝ) : finiteKernelDensityEstimator K h x t = 0 := by
  simp [finiteKernelDensityEstimator_def]

/-- The kernel density estimator with bandwidth zero vanishes. -/
@[simp]
theorem finiteKernelDensityEstimator_zero_bandwidth (K : ℝ → ℝ) (x : κ → ℝ) (t : ℝ) :
    finiteKernelDensityEstimator K 0 x t = 0 := by
  simp [finiteKernelDensityEstimator_def]

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
theorem kernelDensityEstimator_eq_mul_sum_range {Ω : Type*} (K : ℝ → ℝ) (h : ℕ → ℝ)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : kernelDensityEstimator K h X n ω t =
      (n * h n)⁻¹ * ∑ i ∈ range n, K ((t - X i ω) / h n) := by
  rw [kernelDensityEstimator_def, finiteKernelDensityEstimator_eq_mul_sum, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range fun i ↦ K ((t - X i ω) / h n)]

/-- The kernel density estimator of no observations vanishes. -/
@[simp]
theorem kernelDensityEstimator_zero {Ω : Type*} (K : ℝ → ℝ) (h : ℕ → ℝ) (X : ℕ → Ω → ℝ) (ω : Ω)
    (t : ℝ) : kernelDensityEstimator K h X 0 ω t = 0 :=
  finiteKernelDensityEstimator_of_isEmpty _ _ _ _

/-- The kernel density estimator of a sequence vanishes when the bandwidth `h n` is zero. -/
@[simp]
theorem kernelDensityEstimator_of_bandwidth_eq_zero {Ω : Type*} (K : ℝ → ℝ) {h : ℕ → ℝ}
    (X : ℕ → Ω → ℝ) {n : ℕ} (hn : h n = 0) (ω : Ω) (t : ℝ) :
    kernelDensityEstimator K h X n ω t = 0 := by
  rw [kernelDensityEstimator_def, hn, finiteKernelDensityEstimator_zero_bandwidth]

/-- For a measurable kernel, the kernel density estimator evaluated at `t ω` is measurable in `ω`
when the sample `x ω`, the bandwidth `h ω` and the evaluation point `t ω` are. -/
@[fun_prop]
theorem measurable_finiteKernelDensityEstimator_comp {Ω : Type*} [MeasurableSpace Ω]
    {K : ℝ → ℝ} (hK : Measurable K) {h : Ω → ℝ} (hh : Measurable h) {x : Ω → κ → ℝ}
    (hx : ∀ i, Measurable fun ω ↦ x ω i) {t : Ω → ℝ} (ht : Measurable t) :
    Measurable fun ω ↦ finiteKernelDensityEstimator K (h ω) (x ω) (t ω) := by
  simp_rw [finiteKernelDensityEstimator_eq_mul_sum]
  fun_prop

/-- The kernel density estimator of a measurable kernel is measurable. -/
@[fun_prop]
theorem measurable_finiteKernelDensityEstimator {K : ℝ → ℝ} (hK : Measurable K) (h : ℝ)
    (x : κ → ℝ) : Measurable (finiteKernelDensityEstimator K h x) :=
  measurable_finiteKernelDensityEstimator_comp (x := fun _ ↦ x) hK measurable_const
    (fun _ ↦ measurable_const) measurable_id

/-- For a measurable kernel and measurable first `n` observations, the kernel density estimator
of a sequence evaluated at `t ω` is measurable in `ω` when the evaluation point `t ω` is. -/
@[fun_prop]
theorem measurable_kernelDensityEstimator_comp {Ω : Type*} [MeasurableSpace Ω] {K : ℝ → ℝ}
    (hK : Measurable K) (h : ℕ → ℝ) {X : ℕ → Ω → ℝ} {n : ℕ} (hX : ∀ i < n, Measurable (X i))
    {t : Ω → ℝ} (ht : Measurable t) :
    Measurable fun ω ↦ kernelDensityEstimator K h X n ω (t ω) := by
  simp_rw [kernelDensityEstimator_def]
  exact measurable_finiteKernelDensityEstimator_comp (x := fun ω (i : Fin n) ↦ X i ω) hK
    measurable_const (fun i ↦ hX i i.isLt) ht

/-- For a measurable kernel, the kernel density estimator of a sequence is measurable in `t`. -/
@[fun_prop]
theorem measurable_kernelDensityEstimator {Ω : Type*} {K : ℝ → ℝ} (hK : Measurable K)
    (h : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Measurable (kernelDensityEstimator K h X n ω) := by
  rw [funext (kernelDensityEstimator_def K h X n ω)]
  exact measurable_finiteKernelDensityEstimator hK (h n) _

/-- If two kernels agree Lebesgue-almost everywhere, so do their kernel density estimators. -/
theorem finiteKernelDensityEstimator_congr_ae {K K' : ℝ → ℝ} (hKK' : K =ᵐ[volume] K') (h : ℝ)
    (x : κ → ℝ) :
    finiteKernelDensityEstimator K h x =ᵐ[volume] finiteKernelDensityEstimator K' h x := by
  have hi (i : κ) := (measurePreserving_sub_right volume (x i)).quasiMeasurePreserving.ae_eq_comp
    (inv_mul_comp_div_ae_eq hKK' h)
  filter_upwards [ae_all_iff.2 hi] with t ht
  simp only [Function.comp_apply] at ht
  simp only [finiteKernelDensityEstimator_def, ht]

/-- The kernel density estimator of an almost everywhere measurable kernel is almost everywhere
measurable. -/
theorem aemeasurable_finiteKernelDensityEstimator {K : ℝ → ℝ} (hK : AEMeasurable K volume)
    (h : ℝ) (x : κ → ℝ) : AEMeasurable (finiteKernelDensityEstimator K h x) volume :=
  ⟨_, measurable_finiteKernelDensityEstimator hK.measurable_mk h x,
    finiteKernelDensityEstimator_congr_ae hK.ae_eq_mk h x⟩

/-- For an almost everywhere measurable kernel, the kernel density estimator of a sequence is
almost everywhere measurable in `t`. -/
theorem aemeasurable_kernelDensityEstimator {Ω : Type*} {K : ℝ → ℝ} (hK : AEMeasurable K volume)
    (h : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    AEMeasurable (kernelDensityEstimator K h X n ω) volume :=
  aemeasurable_finiteKernelDensityEstimator hK (h n) _

/-- The kernel density estimator of a nonnegative kernel with a nonnegative bandwidth is
nonnegative. -/
theorem finiteKernelDensityEstimator_nonneg {K : ℝ → ℝ} (hK : ∀ u, 0 ≤ K u) {h : ℝ}
    (hh : 0 ≤ h) (x : κ → ℝ) (t : ℝ) : 0 ≤ finiteKernelDensityEstimator K h x t :=
  expect_nonneg fun _ _ ↦ mul_nonneg (inv_nonneg.2 hh) (hK _)

/-- The kernel density estimator of a sequence, for a nonnegative kernel and a nonnegative
bandwidth `h n`, is nonnegative. -/
theorem kernelDensityEstimator_nonneg {Ω : Type*} {K : ℝ → ℝ} (hK : ∀ u, 0 ≤ K u) {h : ℕ → ℝ}
    (X : ℕ → Ω → ℝ) {n : ℕ} (hh : 0 ≤ h n) (ω : Ω) (t : ℝ) :
    0 ≤ kernelDensityEstimator K h X n ω t := by
  rw [kernelDensityEstimator_def]
  exact finiteKernelDensityEstimator_nonneg hK hh _ t

/-- The kernel density estimator of a Lebesgue-almost everywhere nonnegative kernel with a
nonnegative bandwidth is almost everywhere nonnegative. -/
theorem ae_nonneg_finiteKernelDensityEstimator {K : ℝ → ℝ} (hK : ∀ᵐ u ∂volume, 0 ≤ K u) {h : ℝ}
    (hh : 0 ≤ h) (x : κ → ℝ) : ∀ᵐ t ∂volume, 0 ≤ finiteKernelDensityEstimator K h x t := by
  have hKK' : K =ᵐ[volume] fun u ↦ max (K u) 0 := hK.mono fun u hu ↦ (max_eq_left hu).symm
  filter_upwards [finiteKernelDensityEstimator_congr_ae hKK' h x] with t ht
  exact ht ▸ finiteKernelDensityEstimator_nonneg (fun _ ↦ le_max_right _ _) hh x t

/-- The kernel density estimator of a sequence, for a Lebesgue-almost everywhere nonnegative
kernel and a nonnegative bandwidth `h n`, is almost everywhere nonnegative in `t`. -/
theorem ae_nonneg_kernelDensityEstimator {Ω : Type*} {K : ℝ → ℝ} (hK : ∀ᵐ u ∂volume, 0 ≤ K u)
    {h : ℕ → ℝ} (X : ℕ → Ω → ℝ) {n : ℕ} (hh : 0 ≤ h n) (ω : Ω) :
    ∀ᵐ t ∂volume, 0 ≤ kernelDensityEstimator K h X n ω t :=
  ae_nonneg_finiteKernelDensityEstimator hK hh _

/-- The kernel density estimator of an integrable kernel is integrable, for every bandwidth. -/
theorem integrable_finiteKernelDensityEstimator {K : ℝ → ℝ} (hK : Integrable K) (h : ℝ)
    (x : κ → ℝ) : Integrable (finiteKernelDensityEstimator K h x) := by
  rcases eq_or_ne h 0 with rfl | hh
  · have h0 : finiteKernelDensityEstimator K 0 x = 0 := funext fun t ↦ by simp
    rw [h0]
    exact integrable_zero _ _ _
  rw [funext (finiteKernelDensityEstimator_eq_mul_sum K h x)]
  exact (integrable_finsetSum _ fun i _ ↦ (hK.comp_div hh).comp_sub_right (x i)).const_mul _

/-- The kernel density estimator of a sequence, for an integrable kernel, is integrable. -/
theorem integrable_kernelDensityEstimator {Ω : Type*} {K : ℝ → ℝ} (hK : Integrable K)
    (h : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Integrable (kernelDensityEstimator K h X n ω) :=
  integrable_finiteKernelDensityEstimator hK (h n) _

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

/-- The kernel density estimator of `n ≥ 1` observations of a sequence, with an integrable kernel
and a positive bandwidth `h n`, integrates to `∫ K`. -/
theorem integral_kernelDensityEstimator {Ω : Type*} {K : ℝ → ℝ} (hK : Integrable K) {h : ℕ → ℝ}
    (X : ℕ → Ω → ℝ) {n : ℕ} (hn : n ≠ 0) (hh : 0 < h n) (ω : Ω) :
    ∫ t, kernelDensityEstimator K h X n ω t = ∫ u, K u := by
  have : NeZero n := ⟨hn⟩
  exact integral_finiteKernelDensityEstimator hK hh _

/-- For a Lebesgue-almost everywhere nonnegative, almost everywhere measurable kernel `K` and any
bandwidth `h`, the convolution of the empirical measure of `x` with
`volume.withDensity (ENNReal.ofReal ∘ K_h)`, `K_h(t) = h⁻¹ K(t / h)`, is `volume.withDensity` of
`ENNReal.ofReal` of the kernel density estimator of `x`. For `h > 0`, the almost everywhere
nonnegativity of `K` makes both `K_h` and the estimator almost everywhere nonnegative
(`ae_nonneg_finiteKernelDensityEstimator`), so the clipping by `ENNReal.ofReal` has no effect on
the two measures and the estimator is a density of the convolution; for `h < 0` both clipped
densities are almost everywhere zero, and for an empty sample both measures are zero. -/
theorem conv_withDensity_eq_withDensity_finiteKernelDensityEstimator {K : ℝ → ℝ}
    (hK : ∀ᵐ u ∂volume, 0 ≤ K u) (hKm : AEMeasurable K volume) (h : ℝ) (x : κ → ℝ) :
    (Probability.empiricalFiniteMeasure x : Measure ℝ) ∗
        volume.withDensity (fun t ↦ ENNReal.ofReal (h⁻¹ * K (t / h))) =
      volume.withDensity fun t ↦ ENNReal.ofReal (finiteKernelDensityEstimator K h x t) := by
  set K' : ℝ → ℝ := fun u ↦ max (hKm.mk K u) 0
  have hKK' : K =ᵐ[volume] K' := by
    filter_upwards [hKm.ae_eq_mk, hK] with u hu h0
    simp only [K', ← hu, max_eq_left h0]
  have e₁ : volume.withDensity (fun t ↦ ENNReal.ofReal (h⁻¹ * K (t / h))) =
      volume.withDensity fun t ↦ ENNReal.ofReal (h⁻¹ * K' (t / h)) :=
    withDensity_congr_ae ((inv_mul_comp_div_ae_eq hKK' h).mono fun _ ht ↦
      congrArg ENNReal.ofReal ht)
  have e₂ : volume.withDensity (fun t ↦ ENNReal.ofReal (finiteKernelDensityEstimator K h x t)) =
      volume.withDensity fun t ↦ ENNReal.ofReal (finiteKernelDensityEstimator K' h x t) :=
    withDensity_congr_ae ((finiteKernelDensityEstimator_congr_ae hKK' h x).mono fun _ ht ↦
      congrArg ENNReal.ofReal ht)
  rw [e₁, e₂]
  have hK' (u : ℝ) : 0 ≤ K' u := le_max_right _ _
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  rcases lt_or_ge h 0 with hneg | hh
  · -- For a negative bandwidth both densities are nonpositive, so both measures vanish.
    have hzero : ∀ t, h⁻¹ * K' (t / h) ≤ 0 := fun t ↦
      mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 hneg.le) (hK' _)
    have hzero' : ∀ t, finiteKernelDensityEstimator K' h x t ≤ 0 := fun t ↦
      (expect_le_expect fun i _ ↦ hzero (t - x i)).trans_eq (expect_const_zero _)
    simp [ENNReal.ofReal_of_nonpos (hzero _), ENNReal.ofReal_of_nonpos (hzero' _)]
  have hK'm : Measurable K' := hKm.measurable_mk.max measurable_const
  rw [Probability.empiricalFiniteMeasure_conv_withDensity x
    (by fun_prop : Measurable _).aemeasurable]
  congr 1
  funext t
  -- The estimator is the empirical average of the translates of `K'_h`.
  have hn : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  rw [finiteKernelDensityEstimator_eq_mul_sum, mul_inv, mul_assoc, mul_sum,
    ENNReal.ofReal_mul (inv_nonneg.2 hn.le),
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg (inv_nonneg.2 hh) (hK' _),
    ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast, mul_sum]

end TauCeti
