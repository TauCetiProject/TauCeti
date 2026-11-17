/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Sign-flip symmetry, odd coordinate covariances, and second-moment tails of standard Gaussians

This file provides three tools for standard real Gaussian vectors on `EuclideanSpace ℝ ι`:

1. **Coordinatewise sign-flip invariance.** Multiplying the coordinates of `EuclideanSpace ℝ ι`
   by signs `ε : ι → ℤˣ` is a linear isometry equivalence (`signFlipEquiv`), so it preserves
   `stdGaussian (EuclideanSpace ℝ ι)` and every Bochner integral against it.
2. **Orthogonality of odd coordinate maps.** For any odd function `φ : ℝ → ℝ`, flipping a single
   coordinate shows `∫ g, φ (g i) * φ (g j) ∂stdGaussian = 0` for `i ≠ j` (with no measurability or
   integrability assumption). When `φ` is measurable and square-integrable under `gaussianReal 0 1`,
   it follows that `∫ g, (∑ i, a i * φ (g i)) ^ 2 ∂stdGaussian = (∑ i, a i ^ 2) * ∫ x, φ x ^ 2`,
   and for every `f : StrongDual ℝ (EuclideanSpace ℝ ι)`,
   `∫ g, (f (WithLp.toLp 2 fun i ↦ φ (g i))) ^ 2 ∂stdGaussian = ‖f‖ ^ 2 * ∫ x, φ x ^ 2`.
3. **Second-moment tail bound.** For any measure `μ` on `ℝ` with finite fourth moment and `t > 0`,
   the Chebyshev-style bound `∫ x in {x | t < |x|}, x ^ 2 ∂μ ≤ (∫ x, x ^ 4 ∂μ) / t ^ 2` holds; for
   `gaussianReal 0 v`, this gives `≤ 3 * v ^ 2 / t ^ 2` and hence decay to `0` as `t → ∞`.

## Main results

* `TauCeti.Probability.signFlipEquiv`: coordinatewise sign flip on `EuclideanSpace ℝ ι`.
* `TauCeti.Probability.stdGaussian_map_signFlipEquiv`: `stdGaussian` is sign-flip invariant.
* `TauCeti.Probability.integral_comp_signFlipEquiv_stdGaussian`: Bochner integral invariance under
  sign flips.
* `TauCeti.Probability.integral_comp_eval_stdGaussian`,
  `TauCeti.Probability.integral_eval_sq_stdGaussian`, and
  `TauCeti.Probability.integrable_eval_sq_stdGaussian`: single-coordinate integral reduction,
  unit second moment, and coordinate square integrability.
* `TauCeti.Probability.integrable_comp_eval_mul_stdGaussian`: integrability of pairwise products of
  square-integrable coordinate functions.
* `TauCeti.Probability.integral_sum_mul_odd_sq_stdGaussian` and
  `TauCeti.Probability.integral_strongDual_odd_sq_stdGaussian`: second moment of a linear
  combination or continuous functional applied to odd coordinate functions of a standard Gaussian.
* `TauCeti.Probability.setIntegral_sq_abs_gt_le_integral_pow_four_div`,
  `TauCeti.Probability.setIntegral_sq_abs_gt_gaussianReal_le`, and
  `TauCeti.Probability.tendsto_setIntegral_sq_abs_gt_gaussianReal`: second-moment tail bounds and
  decay to `0`.
* `TauCeti.Probability.integral_strongDual_tail_sq_stdGaussian`: second moment of a linear
  functional applied to the coordinatewise tail truncation of a standard Gaussian vector.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace TauCeti.Probability

section SignFlip

variable {ι : Type*} [Fintype ι]

private theorem units_int_cast_sq (u : ℤˣ) : ((u : ℤ) : ℝ) ^ 2 = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

private theorem units_int_cast_mul_self (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  simpa [sq] using units_int_cast_sq u

private theorem abs_units_int_cast (u : ℤˣ) : |((u : ℤ) : ℝ)| = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

/-- Coordinatewise sign flip on `EuclideanSpace ℝ ι` sending `g i` to `ε i * g i`, as a linear
isometry equivalence. -/
def signFlipEquiv (ε : ι → ℤˣ) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toFun g := WithLp.toLp 2 fun i ↦ ((ε i : ℤ) : ℝ) * g i
  invFun g := WithLp.toLp 2 fun i ↦ ((ε i : ℤ) : ℝ) * g i
  left_inv g := by
    ext i
    simp [← mul_assoc, units_int_cast_mul_self]
  right_inv g := by
    ext i
    simp [← mul_assoc, units_int_cast_mul_self]
  map_add' g h := by
    ext i
    simp [mul_add]
  map_smul' c g := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  norm_map' g := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Real.norm_eq_abs, abs_units_int_cast]

@[simp]
theorem signFlipEquiv_apply (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι) (i : ι) :
    signFlipEquiv ε g i = ((ε i : ℤ) : ℝ) * g i := (rfl)

@[simp]
theorem signFlipEquiv_symm (ε : ι → ℤˣ) :
    (signFlipEquiv ε).symm = signFlipEquiv ε := by
  ext g i
  rfl

/-- `stdGaussian (EuclideanSpace ℝ ι)` is invariant under coordinatewise sign flips. -/
theorem stdGaussian_map_signFlipEquiv (ε : ι → ℤˣ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (signFlipEquiv ε) =
      stdGaussian (EuclideanSpace ℝ ι) :=
  stdGaussian_map (signFlipEquiv ε)

/-- Bochner integrals against `stdGaussian (EuclideanSpace ℝ ι)` are invariant under coordinatewise
sign flips, with no measurability or integrability hypothesis on the integrand. -/
theorem integral_comp_signFlipEquiv_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ε : ι → ℤˣ) (f : EuclideanSpace ℝ ι → E) :
    ∫ g, f (signFlipEquiv ε g) ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ g, f g ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let e : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι :=
    (signFlipEquiv ε).toHomeomorph.toMeasurableEquiv
  have h := integral_map_equiv (μ := stdGaussian (EuclideanSpace ℝ ι)) e f
  have hmap : (stdGaussian (EuclideanSpace ℝ ι)).map e = stdGaussian (EuclideanSpace ℝ ι) :=
    stdGaussian_map_signFlipEquiv ε
  rw [hmap] at h
  exact h.symm

/-- Each coordinate of `stdGaussian (EuclideanSpace ℝ ι)` has law `gaussianReal 0 1`. -/
theorem measurePreserving_eval_stdGaussian (i : ι) :
    MeasurePreserving (fun g : EuclideanSpace ℝ ι ↦ g i)
      (stdGaussian (EuclideanSpace ℝ ι)) (gaussianReal 0 1) := by
  classical
  have h := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ ι)) (S := (1 : Matrix ι ι ℝ)) Matrix.PosSemidef.one (i := i)
  simpa [multivariateGaussian_zero_one] using h

/-- Integrating a measurable function of a single coordinate of `stdGaussian (EuclideanSpace ℝ ι)`
reduces to integrating against `gaussianReal 0 1`. -/
theorem integral_comp_eval_stdGaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) {f : ℝ → E} (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
    ∫ g : EuclideanSpace ℝ ι, f (g i) ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ x, f x ∂gaussianReal 0 1 := by
  have hmp := measurePreserving_eval_stdGaussian i
  have hm := integral_map (μ := stdGaussian (EuclideanSpace ℝ ι)) hmp.measurable.aemeasurable
    (hmp.map_eq.symm ▸ hf)
  rw [hmp.map_eq] at hm
  exact hm.symm

/-- Each coordinate of `stdGaussian (EuclideanSpace ℝ ι)` has second moment `1`. -/
@[simp]
theorem integral_eval_sq_stdGaussian (i : ι) :
    ∫ g : EuclideanSpace ℝ ι, g i ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) = 1 := by
  rw [integral_comp_eval_stdGaussian i (f := fun x : ℝ ↦ x ^ 2) (by fun_prop),
    integral_sq_gaussianReal]
  norm_num

/-- Each squared coordinate of `stdGaussian (EuclideanSpace ℝ ι)` is integrable. -/
theorem integrable_eval_sq_stdGaussian (i : ι) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦ g i ^ 2) (stdGaussian (EuclideanSpace ℝ ι)) := by
  have h : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_norm_pow (by norm_num)
  exact (measurePreserving_eval_stdGaussian i).integrable_comp_of_integrable h

end SignFlip

section OddCoordinate

variable {ι : Type*} [Fintype ι]

/-- For an odd function `φ : ℝ → ℝ` and distinct indices `i ≠ j`, the product `φ (g i) * φ (g j)`
has zero integral under `stdGaussian (EuclideanSpace ℝ ι)`, with no measurability or integrability
assumptions. -/
theorem integral_comp_eval_mul_eq_zero_of_odd {φ : ℝ → ℝ} (hφ : Function.Odd φ)
    {i j : ι} (hij : i ≠ j) :
    ∫ g : EuclideanSpace ℝ ι, φ (g i) * φ (g j) ∂stdGaussian (EuclideanSpace ℝ ι) = 0 := by
  classical
  let ε : ι → ℤˣ := Pi.mulSingle i (-1)
  have hflip := integral_comp_signFlipEquiv_stdGaussian ε
    (fun g : EuclideanSpace ℝ ι ↦ φ (g i) * φ (g j))
  have hpoint (g : EuclideanSpace ℝ ι) :
      φ (signFlipEquiv ε g i) * φ (signFlipEquiv ε g j) = -(φ (g i) * φ (g j)) := by
    simp [ε, hij.symm, hφ (g i)]
  simp_rw [hpoint, integral_neg] at hflip
  linarith

/-- If `φ : ℝ → ℝ` is measurable and square-integrable under `gaussianReal 0 1`, then
`g ↦ φ (g i) * φ (g j)` is integrable under `stdGaussian (EuclideanSpace ℝ ι)`. -/
theorem integrable_comp_eval_mul_stdGaussian {φ : ℝ → ℝ} (hφ_meas : Measurable φ)
    (hφ_int : Integrable (fun x : ℝ ↦ φ x ^ 2) (gaussianReal 0 1)) (i j : ι) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦ φ (g i) * φ (g j))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hi : Integrable (fun g : EuclideanSpace ℝ ι ↦ φ (g i) ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (measurePreserving_eval_stdGaussian i).integrable_comp_of_integrable hφ_int
  have hj : Integrable (fun g : EuclideanSpace ℝ ι ↦ φ (g j) ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (measurePreserving_eval_stdGaussian j).integrable_comp_of_integrable hφ_int
  have hdom : Integrable (fun g : EuclideanSpace ℝ ι ↦ (φ (g i) ^ 2 + φ (g j) ^ 2) / 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := (hi.add hj).div_const 2
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun g ↦ ?_)
  · exact ((hφ_meas.comp (EuclideanSpace.proj i).continuous.measurable).mul
      (hφ_meas.comp (EuclideanSpace.proj j).continuous.measurable)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|φ (g i)| - |φ (g j)|), sq_abs (φ (g i)), sq_abs (φ (g j))]

/-- The expected squared linear combination of odd coordinate functions of a standard Gaussian
vector equals `(∑ i, a i ^ 2) * ∫ x, φ x ^ 2 ∂gaussianReal 0 1`. -/
theorem integral_sum_mul_odd_sq_stdGaussian {φ : ℝ → ℝ} (hφ_odd : Function.Odd φ)
    (hφ_meas : Measurable φ) (hφ_int : Integrable (fun x : ℝ ↦ φ x ^ 2) (gaussianReal 0 1))
    (a : ι → ℝ) :
    ∫ g : EuclideanSpace ℝ ι, (∑ i, a i * φ (g i)) ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      (∑ i, a i ^ 2) * ∫ x, φ x ^ 2 ∂gaussianReal 0 1 := by
  classical
  have hexp (g : EuclideanSpace ℝ ι) :
      (∑ i, a i * φ (g i)) ^ 2 = ∑ i, ∑ j, (a i * a j) * (φ (g i) * φ (g j)) := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrable_comp_eval_mul_stdGaussian hφ_meas hφ_int i j).const_mul _]
  have hinner (i : ι) :
      ∫ g : EuclideanSpace ℝ ι, ∑ j, (a i * a j) * (φ (g i) * φ (g j))
          ∂stdGaussian (EuclideanSpace ℝ ι) =
        a i ^ 2 * ∫ x, φ x ^ 2 ∂gaussianReal 0 1 := by
    rw [integral_finsetSum _ fun j _ ↦
      (integrable_comp_eval_mul_stdGaussian hφ_meas hφ_int i j).const_mul _]
    have hdiag (j : ι) :
        ∫ g : EuclideanSpace ℝ ι, (a i * a j) * (φ (g i) * φ (g j))
            ∂stdGaussian (EuclideanSpace ℝ ι) =
          if j = i then a i ^ 2 * ∫ x, φ x ^ 2 ∂gaussianReal 0 1 else 0 := by
      rw [integral_const_mul]
      split_ifs with hji
      · subst j
        rw [← sq]
        have hsq (g : EuclideanSpace ℝ ι) : φ (g i) * φ (g i) = φ (g i) ^ 2 := (sq _).symm
        simp_rw [hsq]
        rw [integral_comp_eval_stdGaussian i (hφ_meas.pow_const 2).aestronglyMeasurable]
      · rw [integral_comp_eval_mul_eq_zero_of_odd hφ_odd (Ne.symm hji), mul_zero]
    simp_rw [hdiag, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [hinner, ← Finset.sum_mul]

/-- The expected square of a continuous linear functional applied to the coordinatewise odd image
of a standard Gaussian vector is `‖f‖ ^ 2 * ∫ x, φ x ^ 2 ∂gaussianReal 0 1`. -/
theorem integral_strongDual_odd_sq_stdGaussian {φ : ℝ → ℝ} (hφ_odd : Function.Odd φ)
    (hφ_meas : Measurable φ) (hφ_int : Integrable (fun x : ℝ ↦ φ x ^ 2) (gaussianReal 0 1))
    (f : StrongDual ℝ (EuclideanSpace ℝ ι)) :
    ∫ g : EuclideanSpace ℝ ι, (f (WithLp.toLp 2 fun i ↦ φ (g i))) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) =
      ‖f‖ ^ 2 * ∫ x, φ x ^ 2 ∂gaussianReal 0 1 := by
  classical
  have hrepr (g : EuclideanSpace ℝ ι) :
      f (WithLp.toLp 2 fun i ↦ φ (g i)) =
        ∑ i, f (EuclideanSpace.basisFun ι ℝ i) * φ (g i) := by
    have hvec : WithLp.toLp 2 (fun i ↦ φ (g i)) =
        ∑ i, φ (g i) • EuclideanSpace.basisFun ι ℝ i := by
      ext j
      simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
    conv_lhs => rw [hvec]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  simp_rw [hrepr]
  rw [integral_sum_mul_odd_sq_stdGaussian hφ_odd hφ_meas hφ_int]
  congr 1
  have hnorm := (EuclideanSpace.basisFun ι ℝ).sum_sq_norm_apply_eq_norm_sq f
  simpa [Real.norm_eq_abs, sq_abs] using hnorm

end OddCoordinate

section TailMoment

/-- Writing `(if t < |x| then x else 0) ^ 2` as a set integral over `{x | t < |x|}`. -/
theorem integral_ite_abs_gt_sq_eq_setIntegral (μ : Measure ℝ) (t : ℝ) :
    ∫ x, (if t < |x| then x else 0) ^ 2 ∂μ = ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂μ := by
  have hmeas : MeasurableSet {x : ℝ | t < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [← integral_indicator hmeas]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : t < |x| <;> simp [Set.indicator, hx]

/-- Chebyshev-style fourth-moment tail bound: for any measure `μ` on `ℝ` with finite fourth moment
and any `t > 0`, `∫ x in {x | t < |x|}, x ^ 2 ∂μ ≤ (∫ x, x ^ 4 ∂μ) / t ^ 2`. -/
theorem setIntegral_sq_abs_gt_le_integral_pow_four_div {μ : Measure ℝ}
    (h4 : Integrable (fun x : ℝ ↦ x ^ 4) μ) {t : ℝ} (ht : 0 < t) :
    ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂μ ≤ (∫ x, x ^ 4 ∂μ) / t ^ 2 := by
  have hmeas : MeasurableSet {x : ℝ | t < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [← integral_indicator hmeas, ← integral_div]
  have hle (x : ℝ) : ({x : ℝ | t < |x|}.indicator (fun x : ℝ ↦ x ^ 2)) x ≤ x ^ 4 / t ^ 2 := by
    by_cases hx : t < |x|
    · simp only [Set.indicator, Set.mem_ofPred_eq, hx, ↓reduceIte]
      rw [le_div_iff₀ (sq_pos_of_pos ht)]
      have ht2 : t ^ 2 ≤ x ^ 2 := by
        rw [← sq_abs x]
        exact sq_le_sq' (by linarith [abs_nonneg x]) hx.le
      nlinarith [sq_nonneg x]
    · simp only [Set.indicator, Set.mem_ofPred_eq, hx, ↓reduceIte]
      positivity
  have hint : Integrable ({x : ℝ | t < |x|}.indicator (fun x : ℝ ↦ x ^ 2)) μ :=
    (h4.div_const (t ^ 2)).mono'
      (((continuous_pow 2).measurable.indicator hmeas).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) x)]
        exact hle x)
  exact integral_mono hint (h4.div_const _) hle

/-- The second-moment tail of a centered real Gaussian satisfies
`∫ x in {x | t < |x|}, x ^ 2 ∂gaussianReal 0 v ≤ 3 * v ^ 2 / t ^ 2` for `t > 0`. -/
theorem setIntegral_sq_abs_gt_gaussianReal_le (v : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 v ≤ 3 * (v : ℝ) ^ 2 / t ^ 2 := by
  have h4 : Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 v) := by
    simpa [Real.norm_eq_abs, (by decide : Even 4).pow_abs] using
      (memLp_id_gaussianReal' (μ := 0) (v := v) 4 (by simp)).integrable_norm_pow (by norm_num)
  have hint : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
    simpa using integral_sub_pow_four_gaussianReal 0 v
  simpa [hint] using setIntegral_sq_abs_gt_le_integral_pow_four_div h4 ht

/-- The second-moment tail of a centered real Gaussian vanishes as the threshold tends to `∞`. -/
theorem tendsto_setIntegral_sq_abs_gt_gaussianReal (v : ℝ≥0) :
    Tendsto (fun t : ℝ ↦ ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 v) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun t : ℝ ↦ 3 * (v : ℝ) ^ 2 / t ^ 2) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg
      (measurableSet_lt measurable_const continuous_abs.measurable) fun _ _ ↦ sq_nonneg _)]
    exact setIntegral_sq_abs_gt_gaussianReal_le v ht
  · have hpow : Tendsto (fun t : ℝ ↦ t ^ 2) atTop atTop :=
      tendsto_pow_atTop (two_ne_zero)
    simpa using (tendsto_const_nhds (x := 3 * (v : ℝ) ^ 2)).div_atTop hpow

/-- Expected squared value of a continuous linear functional on the coordinatewise tail truncation
of a standard Gaussian vector. -/
theorem integral_strongDual_tail_sq_stdGaussian {ι : Type*} [Fintype ι]
    (f : StrongDual ℝ (EuclideanSpace ℝ ι)) (t : ℝ) :
    ∫ g : EuclideanSpace ℝ ι,
        (f (WithLp.toLp 2 fun i ↦ if t < |g i| then g i else 0)) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) =
      ‖f‖ ^ 2 * ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1 := by
  let φ : ℝ → ℝ := fun x ↦ if t < |x| then x else 0
  have hodd : Function.Odd φ := fun x ↦ by
    by_cases hx : t < |x| <;> simp [φ, hx]
  have hmeas : Measurable φ :=
    Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
      measurable_id measurable_const
  have hint_sq : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_norm_pow (by norm_num)
  have hint : Integrable (fun x : ℝ ↦ φ x ^ 2) (gaussianReal 0 1) := by
    refine hint_sq.mono' (hmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hx : t < |x| <;> simp [φ, hx, sq_nonneg]
  rw [← integral_ite_abs_gt_sq_eq_setIntegral (gaussianReal 0 1) t]
  exact integral_strongDual_odd_sq_stdGaussian hodd hmeas hint f

end TailMoment

end TauCeti.Probability
