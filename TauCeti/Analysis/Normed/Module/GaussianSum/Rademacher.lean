/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype

import TauCeti.Analysis.Normed.Module.RademacherSum.Contraction
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Pietsch
import TauCeti.Probability.Distributions.Gaussian.L2
import TauCeti.Probability.Distributions.Gaussian.Symmetry
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian sums are dominated by Rademacher sums under cotype `2`

If a real normed space `Y` has Gaussian cotype `2` with constant `C` (in particular if it has
Rademacher cotype `2` with constant `C`), then the Gaussian second moment of every finite family
`y` is controlled by its Rademacher second moment:
`G₂(y) = (𝔼_g ‖∑ i, gᵢ yᵢ‖²)^(1/2) ≤ 4 √3 C R₂(y)`.
Consequently every operator `U` from a finite-dimensional real inner product space with
orthonormal basis `(eᵢ)` into `Y` has `2`-summing norm `π₂(U) ≤ 4 √3 C² R₂(U eᵢ)`, a bound
independent of the dimension that involves only the Rademacher average of the images of the
basis vectors.

The proof truncates the Gaussian coefficients at height `t = 2 √3 C`. Since the standard Gaussian
measure is invariant under coordinate sign changes, the contraction principle bounds the second
moment of the bounded part by `t R₂(y)`. The tail part is `U b`, where `U eᵢ = yᵢ` and `b` is the
vector of large coordinates of the Gaussian vector; every functional of norm at most `1` has
second moment at most `3 / t²` on `b`, by comparison with the Gaussian fourth moment, so the
integrated form of Pietsch domination and the bound `π₂(U) ≤ C G₂(y)` give
`𝔼 ‖U b‖² ≤ C² G₂(y)² · 3 / t² = G₂(y)² / 4`. Splitting the Gaussian sum and absorbing this term
yields `G₂(y)² ≤ 48 C² R₂(y)²`.

## Main declarations

* `TauCeti.HasGaussianCotype.gaussianSecondMoment_le`, `TauCeti.HasCotype.gaussianSecondMoment_le`:
  `G₂(y) ≤ 4 √3 C R₂(y)` under Gaussian or Rademacher cotype `2` with constant `C`.
* `ContinuousLinearMap.summingENorm_two_le_mul_rademacherSecondMoment_of_hasGaussianCotype`,
  `ContinuousLinearMap.summingENorm_two_le_mul_rademacherSecondMoment_of_hasCotype`:
  `π₂(U) ≤ 4 √3 C² R₂(U eᵢ)`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*, CBMS Regional
  Conference Series in Mathematics 60, AMS, 1986, §3, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace TauCeti

variable {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "γ" => stdGaussian (EuclideanSpace ℝ ι)

/-- The coordinates of `g` of absolute value at most `t`, the others being replaced by `0`. -/
private def lowPart (t : ℝ) (g : EuclideanSpace ℝ ι) (i : ι) : ℝ :=
  if |g i| ≤ t then g i else 0

/-- The coordinates of `g` of absolute value larger than `t`, the others being replaced by `0`. -/
private def highPart (t : ℝ) (g : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if |g i| ≤ t then 0 else g i

private theorem measurable_lowPart (t : ℝ) : Measurable (lowPart (ι := ι) t) := by
  refine Measurable.of_eval fun i ↦ Measurable.ite ?_ ?_ measurable_const <;>
    [exact measurableSet_le (by fun_prop) measurable_const; fun_prop]

private theorem measurable_highPart [Finite ι] (t : ℝ) : Measurable (highPart (ι := ι) t) := by
  refine (PiLp.continuous_toLp 2 _).measurable.comp
    (Measurable.of_eval fun i ↦ Measurable.ite ?_ measurable_const ?_) <;>
    [exact measurableSet_le (by fun_prop) measurable_const; fun_prop]

private theorem lowPart_add_highPart (t : ℝ) (g : EuclideanSpace ℝ ι) (i : ι) :
    lowPart t g i + highPart t g i = g i := by
  by_cases h : |g i| ≤ t <;> simp [lowPart, highPart, h]

private theorem lowPart_signFlip [Fintype ι] (t : ℝ) (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι) (i : ι) :
    lowPart t (signFlip ε g) i = ε i • lowPart t g i := by
  simp only [lowPart, signFlip_apply, ← Real.norm_eq_abs, norm_units_zsmul]
  split_ifs <;> simp

private theorem highPart_signFlip [Fintype ι] (t : ℝ) (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι)
    (i : ι) :
    highPart t (signFlip ε g) i = ε i • highPart t g i := by
  simp only [highPart, PiLp.toLp_apply, signFlip_apply, ← Real.norm_eq_abs, norm_units_zsmul]
  split_ifs <;> simp

private theorem abs_lowPart_le (t : ℝ) (ht : 0 ≤ t) (g : EuclideanSpace ℝ ι) (i : ι) :
    |lowPart t g i| ≤ t := by
  unfold lowPart
  split_ifs with h
  · exact h
  · simpa using ht

variable [Fintype ι]

/-- The squared norm of the bounded part of a Gaussian sum is integrable. -/
private theorem integrable_norm_sum_lowPart_sq {t : ℝ} (ht : 0 ≤ t) (y : ι → Y) :
    Integrable (fun g ↦ ‖∑ i, lowPart t g i • y i‖ ^ 2) γ := by
  refine Integrable.of_bound
    ((by fun_prop : Continuous fun c : ι → ℝ ↦ ‖∑ i, c i • y i‖ ^ 2).measurable.comp
      (measurable_lowPart t)).aestronglyMeasurable ((∑ i, t * ‖y i‖) ^ 2)
    (ae_of_all _ fun g ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ ↦ ?_)) 2
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_lowPart_le t ht g i) (norm_nonneg _)

/-- **The bounded part.** Truncating the Gaussian coefficients at height `t` gives a sum whose
expected squared norm is at most `(t R₂(y))²`, by symmetry of the Gaussian coefficients and the
contraction principle. -/
private theorem integral_norm_sum_lowPart_sq_le [DecidableEq ι] {t : ℝ} (ht : 0 ≤ t) (y : ι → Y) :
    ∫ g, ‖∑ i, lowPart t g i • y i‖ ^ 2 ∂γ ≤ (t * rademacherSecondMoment y) ^ 2 := by
  rw [integral_eq_integral_expect_signFlip (integrable_norm_sum_lowPart_sq ht y)]
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ Finset.expect_nonneg fun _ _ ↦
    sq_nonneg _) (integrable_const ((t * rademacherSecondMoment y) ^ 2))
    (ae_of_all _ fun g ↦ ?_)).trans_eq (by simp)
  have h := pow_le_pow_left₀ (rademacherSecondMoment_nonneg _)
    (rademacherSecondMoment_smul_le (abs_lowPart_le t ht g) y) 2
  rw [rademacherSecondMoment_sq] at h
  simpa only [rademacherSum_eq_sum_units_smul, lowPart_signFlip, smul_assoc] using h

omit [Fintype ι] in
private theorem norm_highPart_apply_le (t : ℝ) (g : EuclideanSpace ℝ ι) (i : ι) :
    ‖highPart t g i‖ ≤ ‖g i‖ := by
  simp only [highPart, PiLp.toLp_apply]
  split_ifs <;> simp

/-- The tail part of a standard Gaussian vector is square integrable. -/
private theorem memLp_highPart (t : ℝ) : MemLp (highPart (ι := ι) t) 2 γ := by
  refine (IsGaussian.memLp_id γ 2 (by simp)).of_le (measurable_highPart t).aestronglyMeasurable
    (ae_of_all _ fun g ↦ ?_)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (norm_highPart_apply_le t g i) 2)

/-- Each coordinate of the tail part has second moment at most `3 / t ^ 2`, by comparison with
the fourth moment `3` of a standard Gaussian. -/
private theorem integral_highPart_apply_sq_le {t : ℝ} (ht : 0 < t) (i : ι) :
    ∫ g, highPart t g i ^ 2 ∂γ ≤ 3 / t ^ 2 := by
  classical
  have hcoord (g : EuclideanSpace ℝ ι) : g i = ⟪EuclideanSpace.single i 1, g⟫_ℝ := by
    simp [EuclideanSpace.inner_single_left]
  have h4 : ∫ g, g i ^ 4 ∂γ = 3 := by
    simpa [← hcoord] using
      Probability.integral_pow_four_inner_stdGaussian (EuclideanSpace.single i (1 : ℝ))
  have hint : Integrable (fun g : EuclideanSpace ℝ ι ↦ g i ^ 4) γ := by
    simpa [← hcoord, Real.norm_eq_abs, (by decide : Even 4).pow_abs] using
      (Probability.memLp_inner_stdGaussian (EuclideanSpace.single i (1 : ℝ)) 4
        (by simp)).integrable_norm_pow (by norm_num)
  calc ∫ g, highPart t g i ^ 2 ∂γ
      ≤ ∫ g, g i ^ 4 / t ^ 2 ∂γ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (hint.div_const _)
          (ae_of_all _ fun g ↦ ?_)
        simp only [highPart, PiLp.toLp_apply]
        split_ifs with h
        · rw [sq, zero_mul]
          positivity
        · rw [le_div_iff₀ (by positivity)]
          have : t ^ 2 ≤ g i ^ 2 := by
            simpa only [sq_abs] using pow_le_pow_left₀ ht.le (not_le.1 h).le 2
          nlinarith [sq_nonneg (g i)]
    _ = 3 / t ^ 2 := by rw [integral_div, h4]

/-- **The tail part.** Every functional of norm at most `1` has second moment at most
`3 / t ^ 2` on the tail part of a standard Gaussian vector. -/
private theorem integral_norm_apply_highPart_sq_le {t : ℝ} (ht : 0 < t)
    (f : StrongDual ℝ (EuclideanSpace ℝ ι)) (hf : ‖f‖ ≤ 1) :
    ∫ g, ‖f (highPart t g)‖ ^ 2 ∂γ ≤ 3 / t ^ 2 := by
  classical
  set b := EuclideanSpace.basisFun ι ℝ
  set w : ι → ℝ := fun i ↦ f (b i)
  have hf_apply (v : EuclideanSpace ℝ ι) : f v = ∑ i, v i * w i := by
    conv_lhs => rw [← b.sum_repr v]
    simp [b, w]
  have hint : Integrable (fun g ↦ ‖f (highPart t g)‖ ^ 2) γ :=
    (f.comp_memLp' (memLp_highPart t)).integrable_norm_pow (by norm_num)
  have hcoord (i : ι) : Integrable (fun g ↦ highPart t g i ^ 2) γ :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp_memLp'
      (memLp_highPart t)).integrable_sq
  calc ∫ g, ‖f (highPart t g)‖ ^ 2 ∂γ
      = ∫ g, ∑ i, w i ^ 2 * highPart t g i ^ 2 ∂γ := by
        rw [integral_eq_integral_expect_signFlip hint]
        refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
        have h := expect_norm_rademacherSum_sq (𝕜 := ℝ) fun i ↦ highPart t g i * w i
        simp only [rademacherSum_eq_sum_units_smul, hf_apply, highPart_signFlip,
          smul_mul_assoc] at h ⊢
        rw [h]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Real.norm_eq_abs, sq_abs]
        ring
    _ = ∑ i, w i ^ 2 * ∫ g, highPart t g i ^ 2 ∂γ := by
        rw [integral_finsetSum _ fun i _ ↦ (hcoord i).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ ∑ i, w i ^ 2 * (3 / t ^ 2) := by
        gcongr with i
        exact integral_highPart_apply_sq_le ht i
    _ = ‖f‖ ^ 2 * (3 / t ^ 2) := by rw [← Finset.sum_mul, b.norm_dual]
    _ ≤ 3 / t ^ 2 := mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) hf)

variable [DecidableEq ι] {C : ℝ≥0}

/-- **Truncation estimate.** Under Gaussian cotype `2` with constant `C`, splitting the Gaussian
coefficients at height `t > 0` bounds `G₂(y)²` by twice the bounded part `(t R₂(y))²` plus twice
the tail part `C² G₂(y)² · 3 / t²`. -/
private theorem gaussianSecondMoment_sq_le (h : HasGaussianCotype Y 2 C) (y : ι → Y) {t : ℝ}
    (ht : 0 < t) :
    gaussianSecondMoment y ^ 2 ≤
      2 * (t * rademacherSecondMoment y) ^ 2 +
        2 * ((C * gaussianSecondMoment y) ^ 2 * (3 / t ^ 2)) := by
  let U : EuclideanSpace ℝ ι →L[ℝ] Y := ∑ i, (EuclideanSpace.proj i).smulRight (y i)
  have hU (v : EuclideanSpace ℝ ι) : U v = ∑ i, v i • y i := by simp [U]
  -- The `2`-summing norm of `U` is at most `C G₂(y)`, which controls the tail part.
  have hπ : U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment y) := by
    simpa [hU] using
      U.summingENorm_two_le_of_hasGaussianCotype (EuclideanSpace.basisFun ι ℝ) h
  have htail : ∫ g, ‖U (highPart t g)‖ ^ 2 ∂γ ≤
      (C * gaussianSecondMoment y) ^ 2 * (3 / t ^ 2) := by
    simpa using U.integral_norm_apply_rpow_le_of_summingENorm_le (p := 2) (by simp)
      (mul_nonneg C.coe_nonneg (gaussianSecondMoment_nonneg y)) hπ (memLp_highPart t)
      (M := 3 / t ^ 2) fun f hf ↦ by simpa using integral_norm_apply_highPart_sq_le ht f hf
  have hsplit (g : EuclideanSpace ℝ ι) :
      ∑ i, g i • y i = ∑ i, lowPart t g i • y i + U (highPart t g) := by
    rw [hU, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← add_smul, lowPart_add_highPart]
  have hint_low := integrable_norm_sum_lowPart_sq ht.le y
  have hint_high : Integrable (fun g ↦ ‖U (highPart t g)‖ ^ 2) γ :=
    (U.comp_memLp' (memLp_highPart t)).integrable_norm_pow (by norm_num)
  rw [gaussianSecondMoment_sq]
  calc ∫ g, ‖∑ i, g i • y i‖ ^ 2 ∂γ
      ≤ ∫ g, (2 * ‖∑ i, lowPart t g i • y i‖ ^ 2 + 2 * ‖U (highPart t g)‖ ^ 2) ∂γ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _)
          ((hint_low.const_mul 2).add (hint_high.const_mul 2)) (ae_of_all _ fun g ↦ ?_)
        simp only
        rw [hsplit]
        nlinarith [norm_add_le (∑ i, lowPart t g i • y i) (U (highPart t g)),
          norm_nonneg (∑ i, lowPart t g i • y i + U (highPart t g)),
          sq_nonneg (‖∑ i, lowPart t g i • y i‖ - ‖U (highPart t g)‖)]
    _ = 2 * ∫ g, ‖∑ i, lowPart t g i • y i‖ ^ 2 ∂γ + 2 * ∫ g, ‖U (highPart t g)‖ ^ 2 ∂γ := by
        rw [integral_add (hint_low.const_mul 2) (hint_high.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        gcongr
        exact integral_norm_sum_lowPart_sq_le ht.le y

/-- **Gaussian sums under Gaussian cotype `2`.** If `Y` has Gaussian cotype `2` with constant
`C`, the Gaussian second moment of every finite family is at most `4 √3 C` times its
Rademacher second moment: `G₂(y) ≤ 4 √3 C R₂(y)`. -/
theorem HasGaussianCotype.gaussianSecondMoment_le (h : HasGaussianCotype Y 2 C) (y : ι → Y) :
    gaussianSecondMoment y ≤ 4 * √3 * C * rademacherSecondMoment y := by
  rcases eq_or_ne C 0 with rfl | hC
  · -- With constant `0` the cotype inequality forces `y = 0`.
    have hy : y = 0 := by
      simpa using h.norm_toLp_le y
    simp [hy]
  -- Truncate at height `t = 2 √3 C`, where the tail term is `G₂(y)² / 4`, and absorb it.
  have ht : 0 < 2 * √3 * (C : ℝ) := by positivity
  have ht2 : (2 * √3 * (C : ℝ)) ^ 2 = 12 * (C : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have key := gaussianSecondMoment_sq_le h y ht
  have habs : (C * gaussianSecondMoment y) ^ 2 * (3 / (2 * √3 * (C : ℝ)) ^ 2) =
      gaussianSecondMoment y ^ 2 / 4 := by
    rw [ht2]
    field_simp
    ring
  rw [habs, mul_pow, ht2] at key
  refine (pow_le_pow_iff_left₀ (gaussianSecondMoment_nonneg y)
    (mul_nonneg (by positivity) (rademacherSecondMoment_nonneg y)) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  linarith

/-- **Gaussian sums under cotype `2`.** If `Y` has Rademacher cotype `2` with constant `C`,
then `G₂(y) ≤ 4 √3 C R₂(y)` for every finite family `y`. -/
theorem HasCotype.gaussianSecondMoment_le (h : HasCotype Y 2 C) (y : ι → Y) :
    gaussianSecondMoment y ≤ 4 * √3 * C * rademacherSecondMoment y :=
  h.hasGaussianCotype_two.gaussianSecondMoment_le y

end TauCeti

namespace ContinuousLinearMap

open TauCeti

variable {ι E Y : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0}

/-- **The `2`-summing norm under Gaussian cotype `2`, by Rademacher averages.** If `Y` has
Gaussian cotype `2` with constant `C`, every operator `U` from a real inner product space with
orthonormal basis `(eᵢ)` into `Y` satisfies `π₂(U) ≤ 4 √3 C² R₂(U eᵢ)`. -/
theorem summingENorm_two_le_mul_rademacherSecondMoment_of_hasGaussianCotype (U : E →L[ℝ] Y)
    (b : OrthonormalBasis ι ℝ E) (h : HasGaussianCotype Y 2 C) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (4 * √3 * C ^ 2 * rademacherSecondMoment fun i ↦ U (b i)) := by
  refine (U.summingENorm_two_le_of_hasGaussianCotype b h).trans (ENNReal.ofReal_le_ofReal ?_)
  calc (C : ℝ) * gaussianSecondMoment (fun i ↦ U (b i))
      ≤ C * (4 * √3 * C * rademacherSecondMoment fun i ↦ U (b i)) :=
        mul_le_mul_of_nonneg_left (h.gaussianSecondMoment_le _) C.coe_nonneg
    _ = _ := by ring

/-- **The cotype-`2` summing bound.** If `Y` has Rademacher cotype `2` with constant `C`, every
operator `U` from a real inner product space with orthonormal basis `(eᵢ)` into `Y` satisfies
`π₂(U) ≤ 4 √3 C² R₂(U eᵢ)`, with a constant independent of the dimension. -/
theorem summingENorm_two_le_mul_rademacherSecondMoment_of_hasCotype (U : E →L[ℝ] Y)
    (b : OrthonormalBasis ι ℝ E) (h : HasCotype Y 2 C) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (4 * √3 * C ^ 2 * rademacherSecondMoment fun i ↦ U (b i)) :=
  U.summingENorm_two_le_mul_rademacherSecondMoment_of_hasGaussianCotype b
    h.hasGaussianCotype_two

end ContinuousLinearMap
