/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# Wrapped normal laws

The wrapped normal law on `AddCircle (2 * π)` is a Gaussian angle read modulo `2 * π`.
Its parameters are a circle location and a nonnegative variance; zero variance gives a
Dirac mass. Rotation changes the location, and convolution adds locations and variances.

The integer Fourier moments are `fourier n m * exp (-v * n² / 2)`. In particular, the
first trigonometric moment has modulus `exp (-v / 2)`, giving circular variance
`1 - exp (-v / 2)`. These formulas use the characteristic kernel `exp (i t x)`.
The location is a circle element, so the law and its Fourier moments do not depend on a
chosen real representative.

The family is jointly measurable and weakly continuous, including its Dirac boundary.
The construction reuses Mathlib's Gaussian pushforward, characteristic-function and
convolution theorems, and follows the circle-law API of
`TauCeti.Probability.wrappedCauchyMeasure`.

## References

* K. V. Mardia and P. E. Jupp, *Directional Statistics*, Wiley, 2000, section 3.5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Topology
open scoped NNReal

namespace TauCeti.Probability

/-- A centred Gaussian of variance `v`, read modulo `2 * π` and translated by the circle
location `m`. -/
def wrappedNormalMeasure (m : AddCircle (2 * π)) (v : ℝ≥0) : Measure (AddCircle (2 * π)) :=
  (gaussianReal 0 v).map fun x : ℝ ↦ m + (x : AddCircle (2 * π))

/-- The wrapped normal law is a translated quotient pushforward of a centred Gaussian. -/
theorem wrappedNormalMeasure_def (m : AddCircle (2 * π)) (v : ℝ≥0) :
    wrappedNormalMeasure m v = (gaussianReal 0 v).map
      (fun x : ℝ ↦ m + (x : AddCircle (2 * π))) := by
  rw [wrappedNormalMeasure]

instance isProbabilityMeasure_wrappedNormalMeasure (m : AddCircle (2 * π)) (v : ℝ≥0) :
    IsProbabilityMeasure (wrappedNormalMeasure m v) := by
  rw [wrappedNormalMeasure_def]
  infer_instance

/-- A Gaussian with real mean `r` becomes wrapped normal with circle location `r` after
passing to the quotient. -/
theorem wrappedNormalMeasure_coe (r : ℝ) (v : ℝ≥0) :
    wrappedNormalMeasure r v = (gaussianReal r v).map ((↑) : ℝ → AddCircle (2 * π)) := by
  have h := gaussianReal_map_const_add (μ := 0) (v := v) r
  simp only [zero_add] at h
  rw [← h, Measure.map_map (by fun_prop) (by fun_prop), wrappedNormalMeasure_def]
  simp only [Function.comp_def, AddCircle.coe_add]

/-- Every wrapped normal law is the image of a standard Gaussian under the circle-valued
map `x ↦ m + √v * x`. -/
theorem wrappedNormalMeasure_eq_map_gaussianReal_zero_one (m : AddCircle (2 * π)) (v : ℝ≥0) :
    wrappedNormalMeasure m v =
      (gaussianReal 0 1).map fun x : ℝ ↦ m + ((√(v : ℝ) * x : ℝ) : AddCircle (2 * π)) := by
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (√(v : ℝ))
  have hv : NNReal.mk (√(v : ℝ) ^ 2) (sq_nonneg _) = v := by
    ext
    exact Real.sq_sqrt v.coe_nonneg
  simp only [mul_zero, mul_one, hv] at h
  rw [wrappedNormalMeasure_def, ← h, Measure.map_map (by fun_prop) (by fun_prop),
    Function.comp_def]

/-- Zero variance gives the Dirac law at the location. -/
@[simp]
theorem wrappedNormalMeasure_zero_var (m : AddCircle (2 * π)) :
    wrappedNormalMeasure m 0 = Measure.dirac m := by
  rw [wrappedNormalMeasure_def, gaussianReal_zero_var, Measure.map_dirac' (by fun_prop)]
  simp

/-- Rotating a wrapped normal law rotates its location. -/
@[simp]
theorem map_add_right_wrappedNormalMeasure (m : AddCircle (2 * π)) (v : ℝ≥0)
    (a : AddCircle (2 * π)) :
    (wrappedNormalMeasure m v).map (· + a) = wrappedNormalMeasure (m + a) v := by
  rw [wrappedNormalMeasure_def, Measure.map_map (by fun_prop) (by fun_prop),
    wrappedNormalMeasure_def]
  congr 1
  funext x
  simp only [Function.comp_apply, add_right_comm]

/-- The wrapped normal family is jointly measurable in circle location and variance. -/
@[fun_prop]
theorem measurable_wrappedNormalMeasure :
    Measurable fun p : AddCircle (2 * π) × ℝ≥0 ↦ wrappedNormalMeasure p.1 p.2 := by
  simp only [wrappedNormalMeasure_eq_map_gaussianReal_zero_one]
  exact MeasureTheory.measurable_map_of_measurable_uncurry (by fun_prop)

/-- Wrapped normal laws depend jointly weakly continuously on location and variance,
including zero variance. -/
theorem continuous_wrappedNormalMeasure :
    Continuous fun p : AddCircle (2 * π) × ℝ≥0 ↦
      (wrappedNormalMeasure p.1 p.2).toProbabilityMeasure := by
  let P := (gaussianReal 0 1).toProbabilityMeasure
  have h := P.continuous_map_of_forall_continuous
    (f := fun (p : AddCircle (2 * π) × ℝ≥0) (x : ℝ) ↦
      p.1 + ((√(p.2 : ℝ) * x : ℝ) : AddCircle (2 * π)))
    (fun _ ↦ by fun_prop) (fun _ ↦ by fun_prop)
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, P, Measure.coe_toProbabilityMeasure,
    wrappedNormalMeasure_eq_map_gaussianReal_zero_one]

/-- As variance tends to zero, the wrapped normal law tends weakly to the Dirac law at its
location. -/
theorem tendsto_wrappedNormalMeasure_nhds_zero_dirac (m : AddCircle (2 * π)) :
    Tendsto (fun v : ℝ≥0 ↦ (wrappedNormalMeasure m v).toProbabilityMeasure) (𝓝 0)
      (𝓝 (Measure.dirac m).toProbabilityMeasure) := by
  have h := (continuous_wrappedNormalMeasure.comp
    (continuous_const.prodMk continuous_id : Continuous fun v : ℝ≥0 ↦ (m, v))).tendsto 0
  simpa only [Function.comp_def, wrappedNormalMeasure_zero_var] using h

/-- The integer Fourier moments of a wrapped normal law are the Gaussian characteristic
function at integer frequencies, multiplied by the location character. -/
theorem integral_fourier_wrappedNormalMeasure (m : AddCircle (2 * π)) (v : ℝ≥0) (n : ℤ) :
    ∫ θ, fourier n θ ∂wrappedNormalMeasure m v =
      fourier n m * (Real.exp (-(v : ℝ) * (n : ℝ) ^ 2 / 2) : ℂ) := by
  have hexp (x : ℝ) :
      fourier n (x : AddCircle (2 * π)) = Complex.exp (((n : ℝ) : ℂ) * x * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  rw [wrappedNormalMeasure_def, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  simp_rw [← fourier_apply, hexp]
  rw [integral_const_mul]
  have h := charFun_gaussianReal (μ := 0) (v := v) n
  rw [charFun_apply_real] at h
  rw [h, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

/-- The first trigonometric moment has modulus `exp (-v / 2)`; hence the circular variance is
`1 - exp (-v / 2)`, including at zero variance. -/
theorem norm_integral_fourier_one_wrappedNormalMeasure (m : AddCircle (2 * π)) (v : ℝ≥0) :
    ‖∫ θ, fourier 1 θ ∂wrappedNormalMeasure m v‖ = Real.exp (-(v : ℝ) / 2) := by
  rw [integral_fourier_wrappedNormalMeasure, norm_mul, fourier_apply, Circle.norm_coe, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

/-- Convolution of wrapped normal laws adds their circle locations and their variances. -/
@[simp]
theorem wrappedNormalMeasure_conv_wrappedNormalMeasure (m₁ m₂ : AddCircle (2 * π))
    (v₁ v₂ : ℝ≥0) :
    wrappedNormalMeasure m₁ v₁ ∗ wrappedNormalMeasure m₂ v₂ =
      wrappedNormalMeasure (m₁ + m₂) (v₁ + v₂) := by
  induction m₁ using QuotientAddGroup.induction_on with | H r₁ => ?_
  induction m₂ using QuotientAddGroup.induction_on with | H r₂ => ?_
  have hmk : Measurable (QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * π))) :=
    measurable_quotient_mk''
  rw [← AddCircle.coe_add, wrappedNormalMeasure_coe, wrappedNormalMeasure_coe,
    wrappedNormalMeasure_coe, ← gaussianReal_conv_gaussianReal]
  exact (Measure.map_conv_addMonoidHom _ hmk).symm

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → AddCircle (2 * π)}
  {m m₁ m₂ : AddCircle (2 * π)} {v v₁ v₂ : ℝ≥0}

/-- Rotation of a wrapped normal random angle changes its location by the rotation. -/
theorem HasLaw.add_const_wrappedNormalMeasure (hX : HasLaw X (wrappedNormalMeasure m v) P)
    (a : AddCircle (2 * π)) :
    HasLaw (fun ω ↦ X ω + a) (wrappedNormalMeasure (m + a) v) P := by
  rw [← map_add_right_wrappedNormalMeasure]
  exact (hasLaw_map (measurable_add_const a).aemeasurable).comp hX

/-- Reading a real Gaussian variable modulo `2 * π` gives the wrapped normal law. -/
theorem HasLaw.coe_wrappedNormalMeasure {X : Ω → ℝ} {r : ℝ}
    (hX : HasLaw X (gaussianReal r v) P) :
    HasLaw (fun ω ↦ (X ω : AddCircle (2 * π))) (wrappedNormalMeasure r v) P := by
  rw [wrappedNormalMeasure_coe]
  exact (hasLaw_map (by fun_prop)).comp hX

/-- The sum of independent wrapped normal angles has wrapped normal law with added locations
and variances. -/
theorem IndepFun.hasLaw_add_wrappedNormalMeasure (hXY : IndepFun X Y P)
    (hX : HasLaw X (wrappedNormalMeasure m₁ v₁) P) (hY : HasLaw Y (wrappedNormalMeasure m₂ v₂) P) :
    HasLaw (X + Y) (wrappedNormalMeasure (m₁ + m₂) (v₁ + v₂)) P := by
  have := hX.isProbabilityMeasure
  rw [← wrappedNormalMeasure_conv_wrappedNormalMeasure]
  exact hXY.hasLaw_add hX hY

end ProbabilityTheory
