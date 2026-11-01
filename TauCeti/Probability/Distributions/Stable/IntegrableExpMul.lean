/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.CompoundPoisson.Transforms

/-!
# One-sided exponential integrability of totally skewed stable laws

At full skewness `|β| = 1` the stable Lévy measure `stableLevyMeasure α β` charges only one
half-line: the positive one for `β = 1` and the negative one for `β = -1`. For `t` on the
opposite half-line, that is `β * t ≤ 0`, the exponential `exp (t * x)` is therefore at most one
on almost every jump, and the real compensated kernel `exp (t * x) - 1 - t * sin x` is
integrable against the Lévy measure: it vanishes quadratically at zero and is bounded on the
jumps that occur.

For such `t` the compensated compound-Poisson approximations
`stableCompensatedPoissonMeasure α β ε` have the moment generating function
`exp (∫ x in {x | ε < |x|}, exp (t * x) - 1 - t * sin x ∂ν)`. This is bounded independently of
the cutoff by `exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂ν)`, at every such `t`, in particular at
parameters of larger absolute value on the same half-line. Lower semicontinuity of integrals
under weak convergence transfers the bound to the limiting stable law. Hence every totally
skewed stable law `stableMeasure α β s m` with `|β| = 1` has finite exponential moments on the
half-line `β * t ≤ 0`, at every shape `0 < α ≤ 2`, scale, and location.

## Main results

* `TauCeti.Probability.ae_mul_nonpos_stableLevyMeasure`: at full skewness, the Lévy measure
  lives on the half-line where `t * x ≤ 0`.
* `TauCeti.Probability.mgf_stableCompensatedPoissonMeasure`: the moment generating function of
  a compensated approximation as the exponential of a truncated compensated Lévy integral.
* `TauCeti.Probability.mgf_stableCompensatedPoissonMeasure_le`: the cutoff-independent bound.
* `TauCeti.Probability.integrable_exp_mul_stableMeasure` and
  `TauCeti.Probability.mem_integrableExpSet_id_stableMeasure`: one-sided exponential
  integrability of the stable law.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, section 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {α β ε t : ℝ}

/-- At full skewness the stable Lévy measure lives on one half-line: if `β * t ≤ 0`, then
`t * x ≤ 0` for almost every jump `x`. -/
theorem ae_mul_nonpos_stableLevyMeasure (hβ : |β| = 1) (ht : β * t ≤ 0) :
    ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0 := by
  -- The density vanishes wherever `0 < t * x`, since there the skewness weight is zero.
  have hzero (x : ℝ) (hx : 0 < t * x) : stableLevyDensity α β x = 0 := by
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    by_cases hα : α ∈ Ioo 0 2
    · rw [stableLevyDensity_of_ne_zero hα hβ.le hx0]
      rcases (abs_eq zero_le_one).mp hβ with rfl | rfl
      · have hx0 : ¬ 0 < x := fun h ↦ by nlinarith
        simp [hx0]
      · have hx0 : 0 < x := by nlinarith
        simp [hx0]
    · exact stableLevyDensity_eq_zero_of_not (fun h ↦ hα ⟨h.1, h.2.1⟩) x
  have hmeas : Measurable fun x ↦ ENNReal.ofReal (stableLevyDensity α β x) :=
    (measurable_stableLevyDensity.comp
      ((measurable_const (a := (α, β))).prodMk measurable_id)).ennreal_ofReal
  rw [stableLevyMeasure_def, ae_withDensity_iff hmeas]
  refine ae_of_all _ fun x hx ↦ not_lt.mp fun h ↦ hx ?_
  rw [hzero x h, ENNReal.ofReal_zero]

/-- On the half-line charged by the Lévy measure, the real compensated kernel
`exp (t * x) - 1 - t * sin x` is integrable against the stable Lévy measure. -/
theorem integrable_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Integrable (fun x : ℝ ↦ exp (t * x) - 1 - t * sin x) (stableLevyMeasure α β) := by
  have hcont : Continuous (fun x : ℝ ↦ exp (t * x) - 1 - t * sin x) := by fun_prop
  -- On the unit ball the kernel is dominated by a multiple of the square of the jump.
  have hsmall : IntegrableOn (fun x : ℝ ↦ exp (t * x) - 1 - t * sin x) (Metric.ball 0 1)
      (stableLevyMeasure α β) := by
    refine ((integrableOn_sq_stableLevyMeasure α β 1).const_mul
      (t ^ 2 * exp |t| + |t|)).mono' hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hx1 : |x| ≤ 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using (Metric.mem_ball.mp hx).le
    have hrem : |exp (t * x) - 1 - t * x| ≤ (|t| * |x|) ^ 2 * exp (|t| * |x|) := by
      have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((t * x : ℝ) : ℂ) 2
      have hc : Complex.exp ((t * x : ℝ) : ℂ) -
          ∑ m ∈ Finset.range 2, ((t * x : ℝ) : ℂ) ^ m / (m.factorial : ℂ) =
          ((exp (t * x) - 1 - t * x : ℝ) : ℂ) := by
        simp [Finset.sum_range_succ, Complex.ofReal_exp, sub_add_eq_sub_sub]
      rwa [hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul] at h
    have hsin : |x - sin x| ≤ x ^ 2 := by
      have := abs_sub_sin_le x
      have := mul_le_mul_of_nonneg_left hx1 (sq_nonneg |x|)
      nlinarith [sq_abs x]
    have he : exp (|t| * |x|) ≤ exp |t| :=
      exp_le_exp.mpr (by nlinarith [abs_nonneg t])
    have hsplit : exp (t * x) - 1 - t * sin x =
        (exp (t * x) - 1 - t * x) + t * (x - sin x) := by ring
    rw [Real.norm_eq_abs, hsplit]
    calc
      _ ≤ |exp (t * x) - 1 - t * x| + |t| * |x - sin x| := by
        rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (|t| * |x|) ^ 2 * exp |t| + |t| * x ^ 2 :=
        add_le_add (hrem.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _)))
          (mul_le_mul_of_nonneg_left hsin (abs_nonneg t))
      _ = (t ^ 2 * exp |t| + |t|) * x ^ 2 := by rw [mul_pow, sq_abs, sq_abs]; ring
  -- Away from zero the restricted Lévy measure is finite and the kernel is bounded, because
  -- `exp (t * x) ≤ 1` on almost every jump.
  have htail : IntegrableOn (fun x : ℝ ↦ exp (t * x) - 1 - t * sin x) {x | (1 : ℝ) / 2 < |x|}
      (stableLevyMeasure α β) := by
    have := isFiniteMeasure_stableLevyMeasure_restrict_abs_gt (α := α) (β := β)
      (by norm_num : (0 : ℝ) < 1 / 2)
    refine Integrable.of_bound hcont.aestronglyMeasurable.restrict (2 + |t|) ?_
    filter_upwards [ae_restrict_of_ae ht] with x hx
    have h1 : exp (t * x) ≤ 1 := exp_le_one_iff.mpr hx
    have h2 : |t * sin x| ≤ |t| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg t) (abs_sin_le_one x)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [exp_pos (t * x), abs_le.mp h2]
  have hcover : Metric.ball (0 : ℝ) 1 ∪ {x | (1 : ℝ) / 2 < |x|} = univ := by
    ext x
    simp only [mem_union, Metric.mem_ball, Real.dist_eq, sub_zero, mem_ofPred_eq,
      mem_univ, iff_true]
    by_cases hx : |x| < 1
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  exact integrableOn_univ.mp (hcover ▸ hsmall.union htail)

/-- The normalized jump law is absolutely continuous with respect to the Lévy measure, so on the
half-line charged by the Lévy measure `exp (t * x) ≤ 1` for almost every jump. -/
private theorem integrable_exp_mul_cond_stableLevyMeasure
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Integrable (fun x ↦ exp (t * AddMonoidHom.id ℝ x))
      (cond (stableLevyMeasure α β) {x | ε < |x|}) := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [cond_absolutelyContinuous.ae_le ht] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), AddMonoidHom.id_apply]
  exact exp_le_one_iff.mpr hx

/-- On the half-line charged by the Lévy measure, the exponential `exp (t * x)` is integrable
under every compensated stable approximation. -/
theorem integrable_exp_mul_stableCompensatedPoissonMeasure
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Integrable (fun x ↦ exp (t * x)) (stableCompensatedPoissonMeasure α β ε) := by
  rw [stableCompensatedPoissonMeasure_def]
  set ν := stableLevyMeasure α β
  set c := ∫ y in {y : ℝ | ε < |y|}, sin y ∂ν
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  refine ((integrable_exp_mul_compoundPoissonMeasure _ measurable_id
    (integrable_exp_mul_cond_stableLevyMeasure ht)).const_mul
    (exp (-(t * c)))).congr (ae_of_all _ fun x ↦ ?_)
  simp only [Function.comp_apply, AddMonoidHom.id_apply, ← exp_add]
  ring_nf

/-- On the half-line charged by the Lévy measure, the moment generating function of a
compensated stable approximation is the exponential of the truncated compensated Lévy
integral. -/
theorem mgf_stableCompensatedPoissonMeasure (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε)
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    mgf id (stableCompensatedPoissonMeasure α β ε) t =
      exp (∫ x in {x : ℝ | ε < |x|}, exp (t * x) - 1 - t * sin x ∂stableLevyMeasure α β) := by
  set ν := stableLevyMeasure α β
  set s : Set ℝ := {x | ε < |x|}
  have hm0 : ν s ≠ 0 := (stableLevyMeasure_abs_gt_pos hα hβ hε).ne'
  have hm_top : ν s ≠ ∞ := stableLevyMeasure_abs_gt_ne_top hε
  have hm_real : ν.real s ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hm0, hm_top⟩
  have := isFiniteMeasure_stableLevyMeasure_restrict_abs_gt (α := α) (β := β) hε
  have hexp : IntegrableOn (fun x ↦ exp (t * x)) s ν := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [ae_restrict_of_ae ht] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr hx
  have hsin : IntegrableOn (fun x ↦ t * sin x) s ν :=
    Integrable.of_bound (by fun_prop) |t| (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg t) (abs_sin_le_one x))
  have hone : IntegrableOn (fun _ ↦ (1 : ℝ)) s ν := integrableOn_const hm_top
  -- The compound-Poisson factor, with the normalized jump law written against `ν`.
  have hcp : mgf id (compoundPoissonMeasure (ν s).toNNReal (cond ν s)) t =
      exp (∫ x in s, exp (t * x) ∂ν - ν.real s) := by
    have hmgf := mgf_compoundPoissonMeasure (f := AddMonoidHom.id ℝ) (ν s).toNNReal
      measurable_id (μ := cond ν s) (t := t)
    rw [AddMonoidHom.coe_id] at hmgf
    rw [hmgf]
    · congr 1
      rw [mgf, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
        ENNReal.coe_toNNReal_eq_toReal, smul_eq_mul]
      simp only [id, measureReal_def] at hm_real ⊢
      field_simp
    · exact integrable_exp_mul_compoundPoissonMeasure _ measurable_id
        (integrable_exp_mul_cond_stableLevyMeasure ht)
  rw [mgf, stableCompensatedPoissonMeasure_def,
    integral_map (by fun_prop) (by fun_prop)]
  -- Translation contributes the factor `exp (-(t * c))`.
  have htrans : ∫ x, exp (t * id (x - ∫ y in s, sin y ∂ν))
        ∂compoundPoissonMeasure (ν s).toNNReal (cond ν s) =
      exp (-(t * ∫ y in s, sin y ∂ν)) *
        mgf id (compoundPoissonMeasure (ν s).toNNReal (cond ν s)) t := by
    rw [mgf, ← integral_const_mul]
    congr with x
    simp only [id, ← exp_add]
    ring_nf
  have hsub₁ := integral_sub (hexp.sub hone) hsin
  have hsub₂ := integral_sub hexp hone
  simp only [Pi.sub_apply] at hsub₁ hsub₂
  rw [htrans, hcp, ← exp_add, hsub₁, hsub₂, integral_const, integral_const_mul, smul_eq_mul,
    mul_one, measureReal_restrict_apply_univ]
  ring_nf

/-- On the half-line charged by the Lévy measure, the moment generating functions of the
compensated stable approximations are bounded independently of the cutoff. -/
theorem mgf_stableCompensatedPoissonMeasure_le (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    mgf id (stableCompensatedPoissonMeasure α β ε) t ≤
      exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂stableLevyMeasure α β) := by
  have hi := integrable_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure ht
  rw [mgf_stableCompensatedPoissonMeasure hα hβ hε ht, exp_le_exp]
  calc
    _ ≤ ∫ x in {x : ℝ | ε < |x|}, |exp (t * x) - 1 - t * sin x| ∂stableLevyMeasure α β :=
      setIntegral_mono hi.integrableOn hi.abs.integrableOn fun x ↦ le_abs_self _
    _ ≤ _ := setIntegral_le_integral hi.abs (ae_of_all _ fun x ↦ abs_nonneg _)

/-- A valid non-Gaussian stable law is the affine image of its standardized law. -/
private theorem stableMeasure_eq_map_one_zero (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (s : ℝ≥0)
    (m : ℝ) : stableMeasure α β s m = (stableMeasure α β 1 0).map fun x ↦ m + s * x := by
  have hα' : α ∈ Ioc 0 2 := ⟨hα.1, hα.2.le⟩
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_map_affine, charFun_stableMeasure hα' hβ, charFun_stableMeasure hα' hβ,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The standardized totally skewed stable law has finite exponential moments on the
half-line `β * t ≤ 0`, by lower semicontinuity along its compensated approximations. -/
private theorem integrable_exp_mul_stableMeasure_one_zero (hα : α ∈ Ioo 0 2) (hβ : |β| = 1)
    (ht : β * t ≤ 0) : Integrable (fun x ↦ exp (t * x)) (stableMeasure α β 1 0) := by
  have hae := ae_mul_nonpos_stableLevyMeasure (α := α) hβ ht
  have hle := le_liminf_lintegral_of_tendsto_probabilityMeasure
    (f := fun x : ℝ ↦ ENNReal.ofReal (exp (t * x)))
    (ENNReal.continuous_ofReal.comp (by fun_prop)).lowerSemicontinuous
    (tendsto_stableCompensatedPoissonMeasure_invTwoPow hα hβ.le)
  simp only [ProbabilityMeasure.coe_mk] at hle
  have hbound (n : ℕ) :
      ∫⁻ x, ENNReal.ofReal (exp (t * x))
          ∂stableCompensatedPoissonMeasure α β ((2 : ℝ)⁻¹ ^ n) ≤
        ENNReal.ofReal (exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂stableLevyMeasure α β)) := by
    have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_mul_stableCompensatedPoissonMeasure hae)
      (ae_of_all _ fun x ↦ (exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (mgf_stableCompensatedPoissonMeasure_le hα hβ.le hε hae)
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ (exp_pos _).le)).mpr
    ?_⟩
  exact hle.trans_lt ((liminf_le_of_frequently_le' (Frequently.of_forall hbound)).trans_lt
    ENNReal.ofReal_lt_top)

/-- A totally skewed stable law, `|β| = 1`, has finite exponential moments on the half-line
`β * t ≤ 0`, at every shape, scale, and location. Invalid shapes give the zero measure. -/
theorem integrable_exp_mul_stableMeasure (hβ : |β| = 1) (s : ℝ≥0) (m : ℝ) (ht : β * t ≤ 0) :
    Integrable (fun x ↦ exp (t * x)) (stableMeasure α β s m) := by
  by_cases hα : α ∈ Ioc 0 2
  swap
  · rw [stableMeasure_of_invalid (by grind)]
    exact integrable_zero_measure
  rcases hα.2.eq_or_lt with rfl | hα2
  · rw [stableMeasure_two hβ.le]
    exact integrable_exp_mul_gaussianReal t
  rw [stableMeasure_eq_map_one_zero ⟨hα.1, hα2⟩ hβ.le s m,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  have hts : β * (t * s) ≤ 0 := by
    rw [← mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg ht s.2
  refine ((integrable_exp_mul_stableMeasure_one_zero ⟨hα.1, hα2⟩ hβ hts).const_mul
    (exp (t * m))).congr (ae_of_all _ fun x ↦ ?_)
  simp only [Function.comp_apply, ← exp_add]
  ring_nf

/-- The half-line `β * t ≤ 0` lies in the exponential-integrability set of a totally skewed
stable law. -/
theorem mem_integrableExpSet_id_stableMeasure (hβ : |β| = 1) (s : ℝ≥0) (m : ℝ)
    (ht : β * t ≤ 0) : t ∈ integrableExpSet id (stableMeasure α β s m) :=
  integrable_exp_mul_stableMeasure hβ s m ht

end TauCeti.Probability
