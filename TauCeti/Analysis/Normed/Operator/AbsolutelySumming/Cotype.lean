/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype
public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.Analysis.Normed.Module.GaussianSum.Comparison
import TauCeti.Analysis.Normed.Module.RademacherSum.Contraction
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Pietsch
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Distributions.Gaussian.OrthogonalSplitting

/-!
# Cotype-2 summing bounds and Gaussian–Rademacher comparison

Let `Y` be a normed space of cotype `2` with constant `C`, and let `U : E →L[𝕜] Y` be a bounded
operator from a finite-dimensional inner product space `E` with orthonormal basis `b` over
`𝕜 = ℝ` or `ℂ` (or any `RCLike` field). This file establishes Pisier's cotype-`2` `2`-summing
bounds and the comparison between Gaussian and Rademacher second moments in cotype-`2` spaces,
without completeness or separability assumptions on `Y`.

First, if `Y` has Gaussian cotype `2` with constant `C`, every finite family in `E` of weak `ℓ²`
norm `W` is weakly square-dominated by `(W • bᵢ)ᵢ` over `ℝ` (and by `(W • bᵢ, W • (I • bᵢ))ᵢ`
over any `RCLike` field via `StrongDual.extendRCLike`). Gaussian comparison
(`TauCeti.gaussianSecondMoment_le_of_weakTwo_le`) then gives the `2`-summing bounds
`π₂(U) ≤ C * G₂(U ∘ b)` over `ℝ` and `π₂(U) ≤ 2 * C * G₂(U ∘ b)` over any `RCLike` field
(Pisier, Proposition 3.7).

Second, applying the real `2`-summing bound and Pietsch domination to the canonical operator
`EuclideanSpace ℝ ι →L[ℝ] Y` associated to a finite family `y` in `Y`, and splitting each standard
Gaussian coordinate at a threshold `t` with `C * (𝔼[g² 1_{|g| > t}])^(1/2) ≤ 1 / 2`, bounds the
truncated sum by `t * R₂(y)` (by sign-flip invariance and Rademacher contraction) and the tail sum
by `(1 / 2) * G₂(y)` (by Pietsch domination and Fubini). Absorption yields `G₂(y) ≤ 2 * t * R₂(y)`
(Pisier, Lemma 3.8). Choosing `t = 4 * C` via `𝔼[g⁴] = 3` gives the explicit bound
`G₂(y) ≤ 8 * C * R₂(y)`, and hence Gaussian cotype `2` implies Rademacher cotype `2` with
constant `8 * C²`.

Combining these bounds with `TauCeti.HasCotype.hasGaussianCotype_two` (and passing to
`SeparationQuotient Y` for seminormed targets) yields Pisier's cotype-`2` summing bounds
`π₂(U) ≤ 2 * C * t * R₂(U ∘ b)` and `π₂(U) ≤ 8 * C² * R₂(U ∘ b)` over `ℝ`, and
`π₂(U) ≤ 4 * C * t * R₂(U ∘ b)` and `π₂(U) ≤ 16 * C² * R₂(U ∘ b)` over any `RCLike` field
(Pisier, Theorem 3.9).

## Main declarations

* `ContinuousLinearMap.summingENorm_two_le_ofReal_two_mul_gaussianSecondMoment`:
  `π₂(U) ≤ 2 * C * G₂(U ∘ b)` over any `RCLike` field under Gaussian cotype `2` (extending
  `ContinuousLinearMap.summingENorm_two_le_of_hasGaussianCotype` from the real case).
* `TauCeti.gaussianSecondMoment_le_two_mul_rademacherSecondMoment`:
  `G₂(y) ≤ 2 * t * R₂(y)` when `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`.
* `TauCeti.gaussianSecondMoment_le_eight_mul_rademacherSecondMoment`:
  `G₂(y) ≤ 8 * C * R₂(y)` under Gaussian cotype `2`.
* `TauCeti.HasGaussianCotype.hasCotype_two`: Gaussian cotype `2` implies Rademacher cotype `2`
  with constant `8 * C²`.
* `ContinuousLinearMap.summingENorm_two_le_ofReal_two_mul_rademacherSecondMoment`,
  `ContinuousLinearMap.summingENorm_two_le_ofReal_four_mul_rademacherSecondMoment`:
  threshold-form cotype-`2` summing bounds over `ℝ` and over any `RCLike` field.
* `ContinuousLinearMap.summingENorm_two_le_ofReal_eight_mul_sq_mul_rademacherSecondMoment`,
  `ContinuousLinearMap.summingENorm_two_le_ofReal_sixteen_mul_sq_mul_rademacherSecondMoment`:
  explicit-constant cotype-`2` summing bounds over `ℝ` and over any `RCLike` field.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Proposition 3.7, Lemma 3.8, and Theorem 3.9, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

/-! ### Gaussian cotype-2 summing bound (Pisier, Proposition 3.7) -/

namespace ContinuousLinearMap

/-- Every real continuous linear functional on `Y` is weakly square-dominated on `U ∘ x` by the
scaled basis image `(W • U (b i), W • (I • U (b i)))ᵢ`, where `W = weakLpNorm 2 x`. -/
private theorem weakTwo_dom_of_orthonormalBasis {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ Y]
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) {m : ℕ} (x : Fin m → E) (f : StrongDual ℝ Y) :
    let W := weakLpNorm (𝕜 := 𝕜) 2 x
    ∑ j, |f (U (x j))| ^ 2 ≤
      ∑ k, |f (Sum.elim (fun i ↦ W • (U ∘ b) i)
        (fun i ↦ W • ((RCLike.I : 𝕜) • (U ∘ b) i)) k)| ^ 2 := by
  intro W
  have hW : 0 ≤ W := apply_nonneg _ _
  let g : StrongDual 𝕜 Y := f.extendRCLike (𝕜 := 𝕜)
  have hre (v : Y) : |f v| ^ 2 ≤ ‖g v‖ ^ 2 := by
    rw [← f.re_extendRCLike_apply (𝕜 := 𝕜) v]
    exact pow_le_pow_left₀ (abs_nonneg _) (RCLike.abs_re_le_norm _) 2
  have hnorm (v : Y) : ‖g v‖ ^ 2 = |f v| ^ 2 + |f ((RCLike.I : 𝕜) • v)| ^ 2 := by
    rw [RCLike.norm_sq_eq_def, f.re_extendRCLike_apply, f.im_extendRCLike_apply]
    simp [pow_two]
  have hweak := sum_norm_eval_rpow_le_weakLpNorm (𝕜 := 𝕜) 2 (by simp) x (g.comp U)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, comp_apply] at hweak
  calc
    ∑ j, |f (U (x j))| ^ 2 ≤ ∑ j, ‖g (U (x j))‖ ^ 2 := Finset.sum_le_sum fun j _ ↦ hre _
    _ ≤ (W * ‖g.comp U‖) ^ 2 := hweak
    _ = W ^ 2 * ∑ i, ‖g (U (b i))‖ ^ 2 := by
      rw [mul_pow, ← b.sum_sq_norm_apply_eq_norm_sq (g.comp U)]
      rfl
    _ = ∑ k, |f (Sum.elim (fun i ↦ W • (U ∘ b) i)
          (fun i ↦ W • ((RCLike.I : 𝕜) • (U ∘ b) i)) k)| ^ 2 := by
      simp_rw [hnorm, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
        map_smul, smul_eq_mul, abs_mul, mul_pow, abs_of_nonneg hW, ← Finset.mul_sum,
        Finset.sum_add_distrib, mul_add]

/-- Unified Gaussian cotype-`2` summing bound over any `RCLike` field with constant
`(1 + ‖(RCLike.I : 𝕜)‖) * C`. -/
private theorem summingENorm_two_le_ofReal_one_add_norm_I_mul_gaussianSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal ((1 + ‖(RCLike.I : 𝕜)‖) * C * gaussianSecondMoment (U ∘ b)) := by
  have hconst_nonneg : 0 ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * gaussianSecondMoment (U ∘ b) :=
    mul_nonneg (mul_nonneg (by positivity) C.property) (gaussianSecondMoment_nonneg _)
  rw [summingENorm_le_ofReal_iff hconst_nonneg]
  intro m x
  set W := weakLpNorm (𝕜 := 𝕜) 2 x
  have hW : 0 ≤ W := apply_nonneg _ _
  let y : ι ⊕ ι → Y :=
    Sum.elim (fun i ↦ W • (U ∘ b) i) (fun i ↦ W • ((RCLike.I : 𝕜) • (U ∘ b) i))
  have hsmulI : gaussianSecondMoment (fun i ↦ (RCLike.I : 𝕜) • (U ∘ b) i) ≤
      ‖(RCLike.I : 𝕜)‖ * gaussianSecondMoment (U ∘ b) :=
    gaussianSecondMoment_map_le (LinearMap.lsmul 𝕜 Y (RCLike.I : 𝕜))
      (fun v ↦ by simp [norm_smul]) (U ∘ b)
  have hG : gaussianSecondMoment (U ∘ x) ≤
      (1 + ‖(RCLike.I : 𝕜)‖) * gaussianSecondMoment (U ∘ b) * W := calc
    gaussianSecondMoment (U ∘ x) ≤ gaussianSecondMoment y :=
      gaussianSecondMoment_le_of_weakTwo_le (U ∘ x) y (weakTwo_dom_of_orthonormalBasis b U x)
    _ ≤ gaussianSecondMoment (fun i ↦ W • (U ∘ b) i) +
          gaussianSecondMoment (fun i ↦ W • ((RCLike.I : 𝕜) • (U ∘ b) i)) :=
      gaussianSecondMoment_sumElim_le _ _
    _ = W * gaussianSecondMoment (U ∘ b) +
          W * gaussianSecondMoment (fun i ↦ (RCLike.I : 𝕜) • (U ∘ b) i) := by
      rw [gaussianSecondMoment_smul, gaussianSecondMoment_smul, abs_of_nonneg hW]
    _ ≤ W * gaussianSecondMoment (U ∘ b) +
          W * (‖(RCLike.I : 𝕜)‖ * gaussianSecondMoment (U ∘ b)) := by gcongr
    _ = (1 + ‖(RCLike.I : 𝕜)‖) * gaussianSecondMoment (U ∘ b) * W := by ring
  calc
    ‖WithLp.toLp 2 (fun j ↦ U (x j))‖ ≤ C * gaussianSecondMoment (U ∘ x) := hY.norm_toLp_le (U ∘ x)
    _ ≤ C * ((1 + ‖(RCLike.I : 𝕜)‖) * gaussianSecondMoment (U ∘ b) * W) := by gcongr
    _ = (1 + ‖(RCLike.I : 𝕜)‖) * C * gaussianSecondMoment (U ∘ b) * W := by ring

/-- **Pisier's Gaussian summing bound (`RCLike` case).** If `Y` has Gaussian cotype `2` with
constant `C`, then every bounded `𝕜`-linear operator `U : E →L[𝕜] Y` from an inner product space
with a finite orthonormal basis `b` satisfies `π₂(U) ≤ 2 * C * G₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_two_mul_gaussianSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (2 * C * gaussianSecondMoment (U ∘ b)) := by
  refine (summingENorm_two_le_ofReal_one_add_norm_I_mul_gaussianSecondMoment hY b U).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    rw [RCLike.norm_I]
    split_ifs <;> norm_num
  have hG : 0 ≤ (C : ℝ) * gaussianSecondMoment (U ∘ b) :=
    mul_nonneg C.property (gaussianSecondMoment_nonneg _)
  nlinarith

end ContinuousLinearMap

/-! ### Gaussian-to-Rademacher comparison (Pisier, Lemma 3.8) -/

namespace TauCeti

section TailHelpers

section Truncation

variable {ι : Type*}

/-- Coordinatewise truncation of a Euclidean vector to `[-t, t]`. -/
private def truncVec (t : ℝ) (g : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if |g i| ≤ t then g i else 0

/-- Coordinatewise tail of a Euclidean vector outside `[-t, t]`. -/
private def tailVec (t : ℝ) (g : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if t < |g i| then g i else 0

private theorem truncVec_add_tailVec (t : ℝ) (g : EuclideanSpace ℝ ι) :
    truncVec t g + tailVec t g = g := by
  ext i
  simp only [PiLp.add_apply, truncVec, tailVec]
  rcases le_or_gt |g i| t with h | h
  · simp [h, not_lt.2 h]
  · simp [h, not_le.2 h]

private theorem measurable_truncVec [Countable ι] (t : ℝ) : Measurable (truncVec (ι := ι) t) := by
  refine (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval fun i ↦ ?_)
  exact Measurable.ite
    (measurableSet_le (continuous_abs.comp (PiLp.continuous_apply 2 _ i)).measurable
      measurable_const)
    (PiLp.continuous_apply 2 _ i).measurable measurable_const

private theorem measurable_tailVec [Countable ι] (t : ℝ) : Measurable (tailVec (ι := ι) t) := by
  refine (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval fun i ↦ ?_)
  exact Measurable.ite
    (measurableSet_lt measurable_const
      (continuous_abs.comp (PiLp.continuous_apply 2 _ i)).measurable)
    (PiLp.continuous_apply 2 _ i).measurable measurable_const

private theorem truncVec_units_smul (t : ℝ) (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι) (i : ι) :
    truncVec t (WithLp.toLp 2 fun j ↦ ε j • g j) i = ε i • truncVec t g i := by
  simp only [truncVec, WithLp.ofLp_toLp]
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

private theorem tailVec_units_smul (t : ℝ) (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι) (i : ι) :
    tailVec t (WithLp.toLp 2 fun j ↦ ε j • g j) i = ε i • tailVec t g i := by
  simp only [tailVec, WithLp.ofLp_toLp]
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

end Truncation

variable {ι : Type*} [Fintype ι]

private theorem norm_truncVec_le (t : ℝ) (g : EuclideanSpace ℝ ι) : ‖truncVec t g‖ ≤ ‖g‖ := by
  refine PiLp.norm_mono fun i ↦ ?_
  simp only [truncVec, WithLp.ofLp_toLp]
  split_ifs <;> simp

private theorem norm_tailVec_le (t : ℝ) (g : EuclideanSpace ℝ ι) : ‖tailVec t g‖ ≤ ‖g‖ := by
  refine PiLp.norm_mono fun i ↦ ?_
  simp only [tailVec, WithLp.ofLp_toLp]
  split_ifs <;> simp

private theorem memLp_apply_truncVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) (t : ℝ) :
    MemLp (fun g ↦ U (truncVec t g)) 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hmeas : AEStronglyMeasurable (fun g ↦ U (truncVec t g))
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (U.continuous.comp_stronglyMeasurable (measurable_truncVec t).stronglyMeasurable)
      |>.aestronglyMeasurable
  refine (IsGaussian.memLp_two_id.norm.const_mul ‖U‖).mono' hmeas
    (Filter.Eventually.of_forall fun g ↦ ?_)
  exact (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_truncVec_le t g) (norm_nonneg U))

private theorem memLp_apply_tailVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) (t : ℝ) :
    MemLp (fun g ↦ U (tailVec t g)) 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hmeas : AEStronglyMeasurable (fun g ↦ U (tailVec t g))
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (U.continuous.comp_stronglyMeasurable (measurable_tailVec t).stronglyMeasurable)
      |>.aestronglyMeasurable
  refine (IsGaussian.memLp_two_id.norm.const_mul ‖U‖).mono' hmeas
    (Filter.Eventually.of_forall fun g ↦ ?_)
  exact (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_tailVec_le t g) (norm_nonneg U))

/-- Sign-flip invariance of the squared norm of `(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y ∘
truncVec t`. -/
private theorem integral_norm_sq_truncVec_units_smul {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (y : ι → Y) (t : ℝ) (ε : ι → ℤˣ) :
    ∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (truncVec t g)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ g, ‖∑ i, ε i • (truncVec t g i • y i)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let U := (EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
  have hmeas : StronglyMeasurable fun g : EuclideanSpace ℝ ι ↦ ‖U (truncVec t g)‖ ^ 2 :=
    (U.continuous.comp_stronglyMeasurable
      (measurable_truncVec t).stronglyMeasurable).norm.pow 2
  conv_lhs =>
    rw [← Probability.stdGaussian_map_units_smul ε,
      integral_map (μ := stdGaussian (EuclideanSpace ℝ ι)) (by fun_prop)
        hmeas.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  dsimp only
  simp only [U, Module.Basis.constrL_apply, EuclideanSpace.basisFun_toBasis]
  simp [truncVec_units_smul]

/-- Sign-flip invariance and Rademacher contraction bound the truncated Gaussian sum by
`t * R₂(y)`. -/
private theorem integral_norm_sq_truncVec_le [DecidableEq ι] {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (y : ι → Y) {t : ℝ} (ht : 0 ≤ t) :
    ∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (truncVec t g)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      (t * rademacherSecondMoment y) ^ 2 := by
  have hint_ε (ε : ι → ℤˣ) :
      Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖∑ i, ε i • (truncVec t g i • y i)‖ ^ 2)
        (stdGaussian (EuclideanSpace ℝ ι)) := by
    have heq (g : EuclideanSpace ℝ ι) :
        ∑ i, ε i • (truncVec t g i • y i) =
          (EuclideanSpace.basisFun ι ℝ).toBasis.constrL (fun i ↦ ε i • y i) (truncVec t g) := by
      simp only [Module.Basis.constrL_apply, EuclideanSpace.basisFun_toBasis,
        PiLp.basisFun_equivFun]
      exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
    simp_rw [heq]
    exact (memLp_apply_truncVec
      ((EuclideanSpace.basisFun ι ℝ).toBasis.constrL fun i ↦ ε i • y i) t).integrable_norm_pow
      (by norm_num)
  have havg : ∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (truncVec t g)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ g, 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • (truncVec t g i • y i)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
    simp_rw [Fintype.expect_eq_sum_div_card]
    rw [integral_div, integral_finsetSum _ fun ε _ ↦ hint_ε ε]
    simp_rw [← integral_norm_sq_truncVec_units_smul y t, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hcard : (Fintype.card (ι → ℤˣ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp [hcard]
  rw [havg]
  calc
    ∫ g, 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • (truncVec t g i • y i)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)
        ≤ ∫ _, (t * rademacherSecondMoment y) ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) := by
      refine integral_mono ?_ (integrable_const _) fun g ↦ ?_
      · simp_rw [Fintype.expect_eq_sum_div_card]
        exact (integrable_finsetSum _ fun ε _ ↦ hint_ε ε).div_const _
      · rw [← rademacherSecondMoment_sq]
        have hbd (i : ι) : |truncVec t g i| ≤ t := by
          simp only [truncVec, WithLp.ofLp_toLp]
          split_ifs with h
          · exact h
          · simpa using ht
        exact pow_le_pow_left₀ (rademacherSecondMoment_nonneg _)
          (rademacherSecondMoment_smul_le hbd y) 2
    _ = (t * rademacherSecondMoment y) ^ 2 := by simp

private theorem integrable_tailVec_mul (t : ℝ) (i j : ι) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦ tailVec t g i * tailVec t g j)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hmeas : Measurable (fun g : EuclideanSpace ℝ ι ↦ tailVec t g i * tailVec t g j) :=
    ((PiLp.continuous_apply 2 _ i).measurable.comp (measurable_tailVec t)).mul
      ((PiLp.continuous_apply 2 _ j).measurable.comp (measurable_tailVec t))
  refine (IsGaussian.memLp_two_id.integrable_norm_pow (by norm_num)).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g ↦ ?_)
  have hi : |tailVec t g i| ≤ ‖g‖ :=
    (PiLp.norm_apply_le (tailVec t g) i).trans (norm_tailVec_le t g)
  have hj : |tailVec t g j| ≤ ‖g‖ :=
    (PiLp.norm_apply_le (tailVec t g) j).trans (norm_tailVec_le t g)
  simp only [Real.norm_eq_abs, abs_mul, id_eq, sq]
  exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)

private theorem integral_tailVec_mul_of_ne (t : ℝ) {i j : ι} (hij : i ≠ j) :
    ∫ g, tailVec t g i * tailVec t g j ∂stdGaussian (EuclideanSpace ℝ ι) = 0 := by
  classical
  let ε : ι → ℤˣ := Pi.mulSingle i (-1)
  have hmeas : Measurable (fun g : EuclideanSpace ℝ ι ↦ tailVec t g i * tailVec t g j) :=
    ((PiLp.continuous_apply 2 _ i).measurable.comp (measurable_tailVec t)).mul
      ((PiLp.continuous_apply 2 _ j).measurable.comp (measurable_tailVec t))
  have hneg : ∫ g, tailVec t g i * tailVec t g j ∂stdGaussian (EuclideanSpace ℝ ι) =
      -(∫ g, tailVec t g i * tailVec t g j ∂stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [← integral_neg]
    conv_lhs =>
      rw [← Probability.stdGaussian_map_units_smul ε,
        integral_map (μ := stdGaussian (EuclideanSpace ℝ ι)) (by fun_prop)
          hmeas.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
    dsimp only
    rw [tailVec_units_smul, tailVec_units_smul]
    simp [ε, Pi.mulSingle_eq_of_ne hij.symm]
  linarith

private theorem integral_tailVec_sq (t : ℝ) (i : ι) :
    ∫ g, tailVec t g i * tailVec t g i ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  classical
  have hs : MeasurableSet {r : ℝ | t < |r|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hnorm : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  have hfun : (fun g : EuclideanSpace ℝ ι ↦ tailVec t g i * tailVec t g i) =
      fun g ↦ Set.indicator {r : ℝ | t < |r|} (fun r ↦ r ^ 2)
        ⟪g, EuclideanSpace.single i (1 : ℝ)⟫ := by
    ext g
    simp [tailVec, EuclideanSpace.inner_single_right, Set.indicator_apply]
    split_ifs <;> ring
  rw [hfun, ← integral_map (by fun_prop)
      (Measurable.indicator (by fun_prop) hs).aestronglyMeasurable,
    Probability.map_inner_stdGaussian_of_norm_eq_one hnorm, integral_indicator hs]

/-- On a real continuous linear functional `f`, the expected squared value on `tailVec t g`
equals `‖f‖²` times the one-dimensional Gaussian tail second moment. -/
private theorem integral_sq_apply_tailVec (f : StrongDual ℝ (EuclideanSpace ℝ ι)) (t : ℝ) :
    ∫ g, |f (tailVec t g)| ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      ‖f‖ ^ 2 * ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  classical
  have hexpand (v : EuclideanSpace ℝ ι) :
      f v = ∑ i, v i * f (EuclideanSpace.basisFun ι ℝ i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
    simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr]
  have hsq (g : EuclideanSpace ℝ ι) : |f (tailVec t g)| ^ 2 =
      ∑ i, ∑ j, (f (EuclideanSpace.basisFun ι ℝ i) * f (EuclideanSpace.basisFun ι ℝ j)) *
        (tailVec t g i * tailVec t g j) := by
    rw [sq_abs, hexpand, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [hsq]
  rw [integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ (integrable_tailVec_mul t i j).const_mul _]
  have hinner (i : ι) :
      ∫ g, ∑ j, (f (EuclideanSpace.basisFun ι ℝ i) * f (EuclideanSpace.basisFun ι ℝ j)) *
          (tailVec t g i * tailVec t g j) ∂stdGaussian (EuclideanSpace ℝ ι) =
        f (EuclideanSpace.basisFun ι ℝ i) ^ 2 *
          ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
    rw [integral_finsetSum _ fun j _ ↦ (integrable_tailVec_mul t i j).const_mul _]
    simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single i
        (fun j _ hji ↦ by rw [integral_tailVec_mul_of_ne t hji.symm, mul_zero])
        (fun hi ↦ (hi (Finset.mem_univ i)).elim),
      integral_tailVec_sq t i, sq]
  simp_rw [hinner, ← Finset.sum_mul, ← (EuclideanSpace.basisFun ι ℝ).norm_dual f]

private theorem measurable_eval_tailVec_sq [MeasurableSpace (WeakDual ℝ (EuclideanSpace ℝ ι))]
    [BorelSpace (WeakDual ℝ (EuclideanSpace ℝ ι))] (t : ℝ) :
    Measurable fun p : EuclideanSpace ℝ ι ×
        ContinuousLinearMap.dualBall ℝ (EuclideanSpace ℝ ι) ↦
      |(p.snd : WeakDual ℝ (EuclideanSpace ℝ ι)) (tailVec t p.fst)| ^ 2 := by
  classical
  have heval : Measurable fun p : EuclideanSpace ℝ ι ×
        ContinuousLinearMap.dualBall ℝ (EuclideanSpace ℝ ι) ↦
      (p.snd : WeakDual ℝ (EuclideanSpace ℝ ι)) (tailVec t p.fst) := by
    have hexp (p : EuclideanSpace ℝ ι × ContinuousLinearMap.dualBall ℝ (EuclideanSpace ℝ ι)) :
        (p.snd : WeakDual ℝ (EuclideanSpace ℝ ι)) (tailVec t p.fst) =
          ∑ i, tailVec t p.fst i *
            (p.snd : WeakDual ℝ (EuclideanSpace ℝ ι)) (EuclideanSpace.basisFun ι ℝ i) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr (tailVec t p.fst)]
      simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr]
    simp_rw [hexp]
    refine Finset.measurable_sum _ fun i _ ↦ Measurable.mul ?_ ?_
    · exact (PiLp.continuous_apply 2 _ i).measurable.comp
        ((measurable_tailVec t).comp measurable_fst)
    · exact ((WeakDual.eval_continuous (EuclideanSpace.basisFun ι ℝ i)).comp
        continuous_subtypeVal).measurable.comp measurable_snd
  exact (continuous_abs.measurable.comp heval).pow_const 2

private theorem integrable_eval_tailVec_sq [MeasurableSpace (WeakDual ℝ (EuclideanSpace ℝ ι))]
    [BorelSpace (WeakDual ℝ (EuclideanSpace ℝ ι))] (t : ℝ)
    (ν : Measure (ContinuousLinearMap.dualBall ℝ (EuclideanSpace ℝ ι))) [IsFiniteMeasure ν] :
    Integrable (fun p : EuclideanSpace ℝ ι ×
          ContinuousLinearMap.dualBall ℝ (EuclideanSpace ℝ ι) ↦
        |(p.snd : WeakDual ℝ (EuclideanSpace ℝ ι)) (tailVec t p.fst)| ^ 2)
      ((stdGaussian (EuclideanSpace ℝ ι)).prod ν) := by
  have hdom : Integrable (fun p : EuclideanSpace ℝ ι ×
        ContinuousLinearMap.dualBall ℝ (EuclideanSpace ℝ ι) ↦ ‖p.fst‖ ^ 2)
      ((stdGaussian (EuclideanSpace ℝ ι)).prod ν) := by
    simpa using (IsGaussian.memLp_two_id.integrable_norm_pow (by norm_num)).comp_fst ν
  refine hdom.mono' (measurable_eval_tailVec_sq t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ ?_)
  have hf1 : ‖WeakDual.toStrongDual (p.snd : WeakDual ℝ (EuclideanSpace ℝ ι))‖ ≤ 1 :=
    ContinuousLinearMap.norm_le_one_of_mem_dualBall p.snd
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hle : |(p.snd : WeakDual ℝ (EuclideanSpace ℝ ι)) (tailVec t p.fst)| ≤ ‖p.fst‖ := by
    rw [← WeakDual.toStrongDual_apply]
    exact ((WeakDual.toStrongDual (p.snd : WeakDual ℝ (EuclideanSpace ℝ ι))).le_opNorm
      (tailVec t p.fst)).trans ((mul_le_of_le_one_left (norm_nonneg _) hf1).trans
        (norm_tailVec_le t p.fst))
  exact pow_le_pow_left₀ (abs_nonneg _) hle 2

private theorem integral_sq_apply_tailVec_le_of_mem_dualBall
    (f : ContinuousLinearMap.dualBall ℝ (EuclideanSpace ℝ ι)) (t : ℝ) :
    ∫ g, |(f : WeakDual ℝ (EuclideanSpace ℝ ι)) (tailVec t g)| ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  simp_rw [← WeakDual.toStrongDual_apply]
  rw [integral_sq_apply_tailVec (WeakDual.toStrongDual (f : WeakDual ℝ (EuclideanSpace ℝ ι))) t]
  have hf1 : ‖WeakDual.toStrongDual (f : WeakDual ℝ (EuclideanSpace ℝ ι))‖ ≤ 1 :=
    ContinuousLinearMap.norm_le_one_of_mem_dualBall f
  exact mul_le_of_le_one_left (setIntegral_nonneg
    (measurableSet_lt measurable_const continuous_abs.measurable) fun _ _ ↦ sq_nonneg _)
    (by nlinarith [norm_nonneg (WeakDual.toStrongDual (f : WeakDual ℝ (EuclideanSpace ℝ ι)))])

/-- Pietsch domination and Fubini bound the tail Gaussian sum using Proposition 3.7. -/
private theorem integral_norm_sq_tailVec_le {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (y : ι → Y) (t : ℝ) :
    ∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (tailVec t g)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
        ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  let : MeasurableSpace (WeakDual ℝ (EuclideanSpace ℝ ι)) := borel _
  let : BorelSpace (WeakDual ℝ (EuclideanSpace ℝ ι)) := ⟨rfl⟩
  let U : EuclideanSpace ℝ ι →L[ℝ] Y := (EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
  have hU_basis : U ∘ EuclideanSpace.basisFun ι ℝ = y := by
    ext i
    exact Module.Basis.constrL_basis (EuclideanSpace.basisFun ι ℝ).toBasis y i
  have hsum : U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment y) := by
    simpa only [← Function.comp_def, hU_basis] using
      U.summingENorm_two_le_of_hasGaussianCotype (EuclideanSpace.basisFun ι ℝ) hY
  have hCG : 0 ≤ (C : ℝ) * gaussianSecondMoment y :=
    mul_nonneg C.property (gaussianSecondMoment_nonneg y)
  obtain ⟨ν, _, _, hν⟩ :=
    U.exists_isProbabilityMeasure_of_summingENorm_le_ofReal (p := 2)
      (by simp) hCG hsum
  let Φ : EuclideanSpace ℝ ι × ContinuousLinearMap.dualBall ℝ (EuclideanSpace ℝ ι) → ℝ :=
    fun p ↦ |(p.snd : WeakDual ℝ (EuclideanSpace ℝ ι)) (tailVec t p.fst)| ^ 2
  have hΦ_int : Integrable Φ ((stdGaussian (EuclideanSpace ℝ ι)).prod ν) :=
    integrable_eval_tailVec_sq t ν
  have hpt (g : EuclideanSpace ℝ ι) :
      ‖U (tailVec t g)‖ ^ 2 ≤
        ((C : ℝ) * gaussianSecondMoment y) ^ 2 * ∫ f, Φ (g, f) ∂ν := by
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hν (tailVec t g)) 2
    rw [mul_pow, ENNReal.toReal_ofNat, ← Real.rpow_mul_natCast
      (integral_nonneg fun _ ↦ by positivity)] at h2
    simpa [Φ, Real.norm_eq_abs] using h2
  calc
    ∫ g, ‖U (tailVec t g)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)
        ≤ ∫ g, ((C : ℝ) * gaussianSecondMoment y) ^ 2 * ∫ f, Φ (g, f) ∂ν
            ∂stdGaussian (EuclideanSpace ℝ ι) :=
      integral_mono ((memLp_apply_tailVec U t).integrable_norm_pow (by norm_num))
        (hΦ_int.integral_prod_left.const_mul _) hpt
    _ = ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
          ∫ g, ∫ f, Φ (g, f) ∂ν ∂stdGaussian (EuclideanSpace ℝ ι) :=
      integral_const_mul _ _
    _ = ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
          ∫ f, ∫ g, Φ (g, f) ∂stdGaussian (EuclideanSpace ℝ ι) ∂ν := by
      rw [integral_integral_swap hΦ_int]
    _ ≤ ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
          ∫ _, ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 ∂ν :=
      mul_le_mul_of_nonneg_left (integral_mono hΦ_int.integral_prod_right (integrable_const _)
        fun f ↦ integral_sq_apply_tailVec_le_of_mem_dualBall f t) (sq_nonneg _)
    _ = ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
          ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by simp

/-- The `L²` Minkowski triangle inequality splits `G₂(y)` into its truncated and tail parts. -/
private theorem gaussianSecondMoment_le_trunc_add_tail {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (y : ι → Y) (t : ℝ) :
    gaussianSecondMoment y ≤
      √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (truncVec t g)‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι)) +
        √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (tailVec t g)‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι)) := by
  let U : EuclideanSpace ℝ ι →L[ℝ] Y := (EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
  have hU (g : EuclideanSpace ℝ ι) : U g = ∑ i, g i • y i := by
    simp [U, Module.Basis.constrL_apply, EuclideanSpace.basisFun_toBasis]
  have hsplit : (fun g : EuclideanSpace ℝ ι ↦ U g) =
      (fun g ↦ U (truncVec t g)) + (fun g ↦ U (tailVec t g)) := by
    ext g
    simp only [Pi.add_apply, ← map_add, truncVec_add_tailVec]
  have h1 := memLp_apply_truncVec U t
  have h2 := memLp_apply_tailVec U t
  have hsum_mem : MemLp (fun g : EuclideanSpace ℝ ι ↦ U g) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [hU] using memLp_gaussianSum y 2 (by simp)
  have htri : eLpNorm (fun g ↦ U g) 2 (stdGaussian (EuclideanSpace ℝ ι)) ≤
      eLpNorm (fun g ↦ U (truncVec t g)) 2 (stdGaussian (EuclideanSpace ℝ ι)) +
        eLpNorm (fun g ↦ U (tailVec t g)) 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [hsplit]
    exact eLpNorm_add_le one_le_two
  rw [hsum_mem.eLpNorm_two_eq_ofReal_sqrt_integral, h1.eLpNorm_two_eq_ofReal_sqrt_integral,
    h2.eLpNorm_two_eq_ofReal_sqrt_integral,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at htri
  rw [gaussianSecondMoment_def]
  simpa only [← hU] using htri

end TailHelpers

/-- **Pisier's Gaussian-to-Rademacher comparison (threshold form).** If `Y` has Gaussian cotype `2`
with constant `C` and `t` satisfies `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every finite family
`y` in `Y` satisfies `G₂(y) ≤ 2 * t * R₂(y)`. -/
theorem gaussianSecondMoment_le_two_mul_rademacherSecondMoment
    {ι Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (y : ι → Y) :
    gaussianSecondMoment y ≤ 2 * t * rademacherSecondMoment y := by
  rcases lt_or_ge t 0 with ht_neg | ht0
  · -- When `t < 0`, the tail integral equals `1`, forcing `C ≤ 1 / 2 < 1` and `Subsingleton Y`.
    have huniv : {r : ℝ | t < |r|} = Set.univ :=
      Set.eq_univ_of_forall fun r ↦ ht_neg.trans_le (abs_nonneg r)
    rw [huniv, Measure.restrict_univ, TauCeti.Probability.integral_sq_gaussianReal] at ht
    simp only [NNReal.coe_one, zero_pow two_ne_zero, add_zero, Real.sqrt_one, mul_one] at ht
    have hC1 : C < 1 := by exact_mod_cast ht.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
    have : Subsingleton Y := hY.subsingleton_of_lt_one hC1
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  · have htri := gaussianSecondMoment_le_trunc_add_tail y t
    have htrunc :
        √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (truncVec t g)‖ ^ 2
            ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
          t * rademacherSecondMoment y :=
      Real.sqrt_le_iff.2 ⟨mul_nonneg ht0 (rademacherSecondMoment_nonneg y),
        integral_norm_sq_truncVec_le y ht0⟩
    have htail :
        √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (tailVec t g)‖ ^ 2
            ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
          (1 / 2) * gaussianSecondMoment y := calc
      √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (tailVec t g)‖ ^ 2
            ∂stdGaussian (EuclideanSpace ℝ ι))
          ≤ √(((C : ℝ) * gaussianSecondMoment y) ^ 2 *
              ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) :=
        Real.sqrt_le_sqrt (integral_norm_sq_tailVec_le hY y t)
      _ = (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) *
            gaussianSecondMoment y := by
        rw [Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (mul_nonneg (NNReal.coe_nonneg C) (gaussianSecondMoment_nonneg y))]
        ring
      _ ≤ (1 / 2) * gaussianSecondMoment y :=
        mul_le_mul_of_nonneg_right ht (gaussianSecondMoment_nonneg y)
    linarith

/-- **Pisier's Gaussian-to-Rademacher comparison (explicit constant).** In a real normed space of
Gaussian cotype `2` with constant `C`, the Gaussian second moment of every finite family is at most
`8 * C` times its Rademacher second moment. -/
theorem gaussianSecondMoment_le_eight_mul_rademacherSecondMoment
    {ι Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C) (y : ι → Y) :
    gaussianSecondMoment y ≤ 8 * C * rademacherSecondMoment y := by
  rcases eq_or_ne C 0 with rfl | hC
  · have : Subsingleton Y := hY.subsingleton_of_lt_one zero_lt_one
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  have hCpos : 0 < (C : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hC)
  have htpos : 0 < 4 * (C : ℝ) := by positivity
  have htail : (C : ℝ) * √(∫ r in {r : ℝ | 4 * (C : ℝ) < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤
      1 / 2 := by
    calc
      (C : ℝ) * √(∫ r in {r : ℝ | 4 * (C : ℝ) < |r|}, r ^ 2 ∂gaussianReal 0 1)
          ≤ (C : ℝ) * √(3 / (4 * (C : ℝ)) ^ 2) := by
        gcongr
        exact Probability.setIntegral_sq_tail_gaussianReal_le htpos
      _ = √3 / 4 := by
        rw [Real.sqrt_div (by norm_num), Real.sqrt_sq htpos.le]
        field_simp [hCpos.ne']
      _ ≤ 1 / 2 := by
        have h3 : √3 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
        linarith
  have h := gaussianSecondMoment_le_two_mul_rademacherSecondMoment hY htail y
  linarith

/-- Gaussian cotype `2` with constant `C` implies Rademacher cotype `2` with constant `8 * C²`. -/
theorem HasGaussianCotype.hasCotype_two {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C) : HasCotype Y 2 (8 * C ^ 2) := by
  rw [hasCotype_iff]
  intro n y
  calc
    ‖WithLp.toLp 2 y‖ ≤ C * gaussianSecondMoment y := hY.norm_toLp_le y
    _ ≤ C * (8 * C * rademacherSecondMoment y) := by
      gcongr
      exact gaussianSecondMoment_le_eight_mul_rademacherSecondMoment hY y
    _ = ((8 * C ^ 2 : ℝ≥0) : ℝ) * rademacherSecondMoment y := by push_cast; ring

end TauCeti

/-! ### Pisier's cotype-2 summing bounds (Pisier, Theorem 3.9) -/

namespace ContinuousLinearMap

/-- **Pisier's cotype-`2` summing bound (real case, threshold form).** If `Y` has Rademacher cotype
`2` with constant `C` and `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every bounded real-linear
operator `U : E →L[ℝ] Y` from an inner product space with a finite orthonormal basis `b` satisfies
`π₂(U) ≤ 2 * C * t * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_two_mul_rademacherSecondMoment
    {ι E Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (b : OrthonormalBasis ι ℝ E) (U : E →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (2 * C * t * rademacherSecondMoment (U ∘ b)) := by
  let Uq : E →L[ℝ] SeparationQuotient Y := (SeparationQuotient.mkCLM ℝ Y).comp U
  have hYq : HasGaussianCotype (SeparationQuotient Y) 2 C :=
    hY.separationQuotient.hasGaussianCotype_two
  have hrad : rademacherSecondMoment (Uq ∘ b) = rademacherSecondMoment (U ∘ b) := by
    simp [Uq, Function.comp_def]
  rw [← summingENorm_comp_separationQuotient U, ← hrad]
  refine (Uq.summingENorm_two_le_of_hasGaussianCotype b hYq).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hG := gaussianSecondMoment_le_two_mul_rademacherSecondMoment hYq ht (Uq ∘ b)
  calc
    (C : ℝ) * gaussianSecondMoment (Uq ∘ b)
        ≤ C * (2 * t * rademacherSecondMoment (Uq ∘ b)) := by gcongr
    _ = 2 * C * t * rademacherSecondMoment (Uq ∘ b) := by ring

/-- **Pisier's cotype-`2` summing bound (`RCLike` case, threshold form).** If `Y` has Rademacher
cotype `2` with constant `C` and `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every bounded
`𝕜`-linear operator `U : E →L[𝕜] Y` from an inner product space with a finite orthonormal basis `b`
satisfies `π₂(U) ≤ 4 * C * t * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_four_mul_rademacherSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (4 * C * t * rademacherSecondMoment (U ∘ b)) := by
  let : NormedSpace ℝ (SeparationQuotient Y) :=
    NormedSpace.restrictScalars ℝ 𝕜 (SeparationQuotient Y)
  let Uq : E →L[𝕜] SeparationQuotient Y := (SeparationQuotient.mkCLM 𝕜 Y).comp U
  have hYq : HasGaussianCotype (SeparationQuotient Y) 2 C :=
    hY.separationQuotient.hasGaussianCotype_two
  have hrad : rademacherSecondMoment (Uq ∘ b) = rademacherSecondMoment (U ∘ b) := by
    simp [Uq, Function.comp_def]
  rw [← summingENorm_comp_separationQuotient U, ← hrad]
  refine (Uq.summingENorm_two_le_ofReal_two_mul_gaussianSecondMoment hYq b).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hG := gaussianSecondMoment_le_two_mul_rademacherSecondMoment hYq ht (Uq ∘ b)
  calc
    2 * (C : ℝ) * gaussianSecondMoment (Uq ∘ b)
        ≤ 2 * C * (2 * t * rademacherSecondMoment (Uq ∘ b)) := by gcongr
    _ = 4 * C * t * rademacherSecondMoment (Uq ∘ b) := by ring

/-- **Pisier's cotype-`2` summing bound (real case, explicit constant).** If `Y` has Rademacher
cotype `2` with constant `C`, then every bounded real-linear operator `U : E →L[ℝ] Y` from an
inner product space with a finite orthonormal basis `b` satisfies
`π₂(U) ≤ 8 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_eight_mul_sq_mul_rademacherSecondMoment
    {ι E Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C)
    (b : OrthonormalBasis ι ℝ E) (U : E →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (8 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) := by
  let Uq : E →L[ℝ] SeparationQuotient Y := (SeparationQuotient.mkCLM ℝ Y).comp U
  have hYq : HasGaussianCotype (SeparationQuotient Y) 2 C :=
    hY.separationQuotient.hasGaussianCotype_two
  have hrad : rademacherSecondMoment (Uq ∘ b) = rademacherSecondMoment (U ∘ b) := by
    simp [Uq, Function.comp_def]
  rw [← summingENorm_comp_separationQuotient U, ← hrad]
  refine (Uq.summingENorm_two_le_of_hasGaussianCotype b hYq).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hG := gaussianSecondMoment_le_eight_mul_rademacherSecondMoment hYq (Uq ∘ b)
  calc
    (C : ℝ) * gaussianSecondMoment (Uq ∘ b)
        ≤ C * (8 * C * rademacherSecondMoment (Uq ∘ b)) := by gcongr
    _ = 8 * (C : ℝ) ^ 2 * rademacherSecondMoment (Uq ∘ b) := by ring

/-- **Pisier's cotype-`2` summing bound (`RCLike` case, explicit constant).** If `Y` has Rademacher
cotype `2` with constant `C`, then every bounded `𝕜`-linear operator `U : E →L[𝕜] Y` from an inner
product space with a finite orthonormal basis `b` satisfies `π₂(U) ≤ 16 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_sixteen_mul_sq_mul_rademacherSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (16 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) := by
  let : NormedSpace ℝ (SeparationQuotient Y) :=
    NormedSpace.restrictScalars ℝ 𝕜 (SeparationQuotient Y)
  let Uq : E →L[𝕜] SeparationQuotient Y := (SeparationQuotient.mkCLM 𝕜 Y).comp U
  have hYq : HasGaussianCotype (SeparationQuotient Y) 2 C :=
    hY.separationQuotient.hasGaussianCotype_two
  have hrad : rademacherSecondMoment (Uq ∘ b) = rademacherSecondMoment (U ∘ b) := by
    simp [Uq, Function.comp_def]
  rw [← summingENorm_comp_separationQuotient U, ← hrad]
  refine (Uq.summingENorm_two_le_ofReal_two_mul_gaussianSecondMoment hYq b).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hG := gaussianSecondMoment_le_eight_mul_rademacherSecondMoment hYq (Uq ∘ b)
  calc
    2 * (C : ℝ) * gaussianSecondMoment (Uq ∘ b)
        ≤ 2 * C * (8 * C * rademacherSecondMoment (Uq ∘ b)) := by gcongr
    _ = 16 * (C : ℝ) ^ 2 * rademacherSecondMoment (Uq ∘ b) := by ring

end ContinuousLinearMap
