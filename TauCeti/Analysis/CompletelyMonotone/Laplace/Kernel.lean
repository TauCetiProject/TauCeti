/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Probability.Kernel.Defs

/-!
# The Laplace kernel on `ℝ≥0`

The exponential kernel `p ↦ e^{-xp}` of the Laplace transform on `ℝ≥0`, as a plain function
and as a bundled bounded continuous function, together with its basic bounds and its
integrability against finite measures. Its extended-nonnegative-valued integral against a measure
is `TauCeti.laplaceTransformENN`. Applying this transform fibrewise to a transition kernel gives
`ProbabilityTheory.Kernel.laplaceTransform`. This lightweight module is shared by the Chafaï
approximating-measure machinery and the Laplace-representation theory, which otherwise do not
depend on each other.

## Main declarations

* `TauCeti.laplaceKernelBoundedContinuous`: the kernel as a bounded continuous function.
* `TauCeti.integrable_exp_neg_mul`: the kernel is integrable against any finite measure.
* `TauCeti.laplaceTransformENN`: the extended-nonnegative-valued Laplace transform of a measure.
* `ProbabilityTheory.Kernel.laplaceTransform`: the fibrewise Laplace transform
  `q ↦ ∫⁻ p, exp (-t p) ∂(κ q)` of a transition kernel `κ` into `ℝ≥0`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace NNReal

/-- For fixed nonnegative `p`, the Laplace kernel is antitone in its real parameter. -/
lemma exp_neg_mul_antitone (p : ℝ≥0) :
    Antitone fun t : ℝ => Real.exp (-t * (p : ℝ)) :=
  fun _ _ htu => Real.exp_le_exp.mpr (by gcongr)

end NNReal

namespace TauCeti

/-- The Laplace kernel `p ↦ e^{-tp}` is continuous in the coordinate variable. -/
lemma continuous_exp_neg_mul (t : ℝ) :
    Continuous fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- For `0 ≤ x` the Laplace kernel is bounded by `1` on `ℝ≥0`. -/
lemma exp_neg_mul_le_one {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    Real.exp (-(x * (p : ℝ))) ≤ 1 :=
  Real.exp_le_one_iff.mpr <| neg_nonpos.mpr <| by positivity

/-- The Laplace kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed nonnegative `x`. -/
noncomputable def laplaceKernelBoundedContinuous {x : ℝ} (hx : 0 ≤ x) : ℝ≥0 →ᵇ ℝ :=
  .ofNormedAddCommGroup (fun p => Real.exp (-(x * (p : ℝ)))) (continuous_exp_neg_mul x) 1
    fun p => by simpa [Real.norm_eq_abs] using exp_neg_mul_le_one hx p

/-- The bundled Laplace kernel evaluates to the usual exponential kernel on `ℝ≥0`. -/
@[simp]
lemma laplaceKernelBoundedContinuous_apply {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    laplaceKernelBoundedContinuous hx p = Real.exp (-(x * (p : ℝ))) :=
  (rfl)

/-- **The Laplace kernel is integrable against a finite measure.** For `0 ≤ x` the kernel
`p ↦ e^{-xp}` is bounded and continuous on `ℝ≥0`, hence integrable against any finite measure. -/
lemma integrable_exp_neg_mul (μ : Measure ℝ≥0) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ := by
  have h := (laplaceKernelBoundedContinuous hx).integrable μ
  rwa [funext (laplaceKernelBoundedContinuous_apply hx)] at h

/-! ## The extended-nonnegative-valued Laplace transform -/

section Transform

/-- The extended-nonnegative-valued Laplace transform of a measure on `ℝ≥0`. -/
noncomputable def laplaceTransformENN (μ : Measure ℝ≥0) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp (-(t : ℝ) * (p : ℝ))) ∂μ

/-- The defining formula for `TauCeti.laplaceTransformENN`. -/
theorem laplaceTransformENN_apply (μ : Measure ℝ≥0) (t : ℝ≥0) :
    laplaceTransformENN μ t = ∫⁻ p, ENNReal.ofReal (Real.exp (-(t : ℝ) * (p : ℝ))) ∂μ :=
  (rfl)

/-- At time `0`, the extended-nonnegative-valued Laplace transform is the total mass. -/
@[simp]
theorem laplaceTransformENN_zero (μ : Measure ℝ≥0) :
    laplaceTransformENN μ 0 = μ Set.univ := by
  simp [laplaceTransformENN_apply]

/-- The extended-nonnegative-valued Laplace transform decreases in time. -/
theorem laplaceTransformENN_antitone (μ : Measure ℝ≥0) : Antitone (laplaceTransformENN μ) := by
  intro t u htu
  simp only [laplaceTransformENN_apply]
  exact lintegral_mono fun p => ENNReal.ofReal_le_ofReal (p.exp_neg_mul_antitone (mod_cast htu))

/-- The extended-nonnegative-valued Laplace transform is bounded by the total mass. -/
theorem laplaceTransformENN_le_apply_univ (μ : Measure ℝ≥0) (t : ℝ≥0) :
    laplaceTransformENN μ t ≤ μ Set.univ :=
  (laplaceTransformENN_antitone μ (zero_le : (0 : ℝ≥0) ≤ t)).trans_eq
    (laplaceTransformENN_zero μ)

/-- The extended-nonnegative-valued Laplace transform of a finite measure is finite. -/
@[simp]
theorem laplaceTransformENN_ne_top (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (t : ℝ≥0) :
    laplaceTransformENN μ t ≠ ⊤ :=
  ((laplaceTransformENN_le_apply_univ μ t).trans_lt (measure_lt_top _ _)).ne

end Transform

end TauCeti

/-! ## The fibrewise Laplace transform of a kernel -/

namespace ProbabilityTheory.Kernel

variable {V : Type*} [MeasurableSpace V]

/-- The **fibrewise Laplace transform** of a kernel `κ` from `V` to `ℝ≥0`: the function
`q ↦ ∫⁻ p, exp (-t p) ∂(κ q)` on `V`. -/
noncomputable def laplaceTransform (κ : Kernel V ℝ≥0) (t : ℝ≥0) (q : V) :
    ℝ≥0∞ :=
  TauCeti.laplaceTransformENN (κ q) t

/-- The defining formula for `ProbabilityTheory.Kernel.laplaceTransform`. -/
theorem laplaceTransform_apply (κ : Kernel V ℝ≥0) (t : ℝ≥0) (q : V) :
    laplaceTransform κ t q = TauCeti.laplaceTransformENN (κ q) t :=
  (rfl)

/-- The fibrewise Laplace transform of a kernel is measurable in the base point. -/
@[fun_prop]
theorem measurable_laplaceTransform (κ : Kernel V ℝ≥0) (t : ℝ≥0) :
    Measurable (laplaceTransform κ t) := by
  unfold laplaceTransform TauCeti.laplaceTransformENN
  fun_prop

/-- At time `0`, the fibrewise Laplace transform is the total mass of the fibre. -/
@[simp]
theorem laplaceTransform_zero (κ : Kernel V ℝ≥0) (q : V) :
    laplaceTransform κ 0 q = κ q Set.univ := by
  rw [laplaceTransform_apply, TauCeti.laplaceTransformENN_zero]

/-- The fibrewise Laplace transform decreases in time at each base point. -/
theorem laplaceTransform_antitone (κ : Kernel V ℝ≥0) (q : V) :
    Antitone fun t => laplaceTransform κ t q :=
  TauCeti.laplaceTransformENN_antitone (κ q)

/-- A Markov kernel has fibrewise Laplace transform `1` at time `0`. -/
@[simp]
theorem laplaceTransform_zero_of_isMarkovKernel (κ : Kernel V ℝ≥0)
    [IsMarkovKernel κ] :
    laplaceTransform κ 0 = 1 := by
  funext q
  simp

end ProbabilityTheory.Kernel
