/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.MeasureTheory.Function.LpSeminorm.Clipping

import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.Distributions.Gaussian.MixedMoments
import TauCeti.Probability.Distributions.Gaussian.OrthogonalSplitting

/-!
# The Gaussian embedding into `L²` and its clipping error

On a finite-dimensional real inner product space `E`, the random linear observable
`y ↦ ⟪x, y⟫` under the standard Gaussian measure has variance `‖x‖²` and fourth
moment `3 ‖x‖⁴`. Consequently these observables define a linear isometry from `E`
into `L²(stdGaussian E)`.

Clipping the observable at height `M > 0` gives a bounded `L²` function whose squared
error is at most `3 ‖x‖⁴ / (16 M²)`. For vectors in the unit ball this is the
`3 / (16 M²)` estimate, or the norm bound `√3 / (4 M)`, used in the Gaussian truncation proof of
Grothendieck's inequality. The construction also works in dimension zero.

We use Mathlib's basis-independent `ProbabilityTheory.stdGaussian`,
`IsGaussian.memLp_dual`, and the real Gaussian even-moment formula, rather than introducing
a second finite Gaussian probability space.

We also provide `Lᵖ` membership and coordinate-tail second moment identities for coordinatewise
masks (`PiLp.coordIndicator`, `EuclideanSpace.truncVec`, `EuclideanSpace.tailVec`) under
`stdGaussian (EuclideanSpace ℝ ι)`: `memLp_comp_coordIndicator`, `memLp_comp_truncVec`,
`memLp_comp_tailVec`, and `integral_sq_apply_tailVec`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Nat

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A standard Gaussian linear observable belongs to every finite `Lᵖ` space. -/
theorem memLp_inner_stdGaussian (x : E) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun y ↦ ⟪x, y⟫_ℝ) p (stdGaussian E) :=
  IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) p hp

/-- The even moments of a standard Gaussian linear observable. -/
theorem integral_pow_two_mul_inner_stdGaussian (x : E) (n : ℕ) :
    (∫ y, ⟪x, y⟫_ℝ ^ (2 * n) ∂stdGaussian E) =
      ‖x‖ ^ (2 * n) * (2 * n - 1 : ℕ)‼ := by
  have h := IsGaussian.integral_pow_two_mul_sub_dual (stdGaussian E) (innerSL ℝ x) n
  rw [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id,
    variance_dual_stdGaussian, innerSL_apply_norm] at h
  simpa only [id_eq, integral_id_stdGaussian, sub_zero, innerSL_apply_apply, pow_mul] using h

/-- The second moment of a standard Gaussian linear observable. -/
theorem integral_sq_inner_stdGaussian (x : E) :
    (∫ y, ⟪x, y⟫_ℝ ^ 2 ∂stdGaussian E) = ‖x‖ ^ 2 := by
  simpa using integral_pow_two_mul_inner_stdGaussian x 1

/-- The fourth moment of a standard Gaussian linear observable. -/
theorem integral_pow_four_inner_stdGaussian (x : E) :
    (∫ y, ⟪x, y⟫_ℝ ^ 4 ∂stdGaussian E) = 3 * ‖x‖ ^ 4 := by
  simpa [Nat.doubleFactorial, mul_comm] using integral_pow_two_mul_inner_stdGaussian x 2

/-- A finite-dimensional real inner product space embeds isometrically into Gaussian `L²`
by sending a vector to its random linear observable. -/
def gaussianL2 : E →ₗᵢ[ℝ] Lp ℝ 2 (stdGaussian E) := by
  let g (x : E) : Lp ℝ 2 (stdGaussian E) :=
    (memLp_inner_stdGaussian x 2 (by simp)).toLp (fun y ↦ ⟪x, y⟫_ℝ)
  have hg (x : E) : g x =ᵐ[stdGaussian E] fun y ↦ ⟪x, y⟫_ℝ := MemLp.coeFn_toLp _
  refine
    { toFun := g
      map_add' := ?_
      map_smul' := ?_
      norm_map' := ?_ }
  · intro x z
    apply Lp.ext
    filter_upwards [hg (x + z), Lp.coeFn_add (g x) (g z), hg x, hg z] with y h₁ h₂ h₃ h₄
    simp_all [inner_add_left]
  · intro c x
    apply Lp.ext
    filter_upwards [hg (c • x), Lp.coeFn_smul c (g x), hg x] with y h₁ h₂ h₃
    simp_all [real_inner_smul_left]
  · intro x
    have h : ‖g x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← Lp.integral_norm_sq_eq_norm_sq]
      calc
        _ = ∫ y, ⟪x, y⟫_ℝ ^ 2 ∂stdGaussian E := by
          apply integral_congr_ae
          filter_upwards [hg x] with y hy
          simp [hy, Real.norm_eq_abs]
        _ = _ := integral_sq_inner_stdGaussian x
    have hn : ‖g x‖ = ‖x‖ := by nlinarith [norm_nonneg (g x), norm_nonneg x]
    exact hn

/-- A representative of the canonical Gaussian `L²` observable. -/
theorem gaussianL2_ae_eq (x : E) : gaussianL2 x =ᵐ[stdGaussian E] fun y ↦ ⟪x, y⟫_ℝ :=
  (memLp_inner_stdGaussian x 2 (by simp)).coeFn_toLp

/-- A Gaussian observable clipped to `[-M, M]` for `M ≥ 0`, as an element of `L²`.
For negative `M`, the max-min formula gives the constant `-M`. -/
def clippedGaussianL2 (x : E) (M : ℝ) : Lp ℝ 2 (stdGaussian E) :=
  (MemLp.of_bound (by fun_prop) |M| (Filter.Eventually.of_forall fun y ↦ by
    simpa only [Real.norm_eq_abs] using TauCeti.abs_max_min_le M ⟪x, y⟫_ℝ)).toLp
      (fun y ↦ max (-M) (min M ⟪x, y⟫_ℝ))

/-- A bounded representative of the clipped Gaussian observable. -/
theorem clippedGaussianL2_ae_eq (x : E) (M : ℝ) :
    clippedGaussianL2 x M =ᵐ[stdGaussian E] fun y ↦ max (-M) (min M ⟪x, y⟫_ℝ) :=
  MemLp.coeFn_toLp _

/-- The clipped observable is almost everywhere bounded by its clipping height. -/
theorem ae_abs_clippedGaussianL2_le (x : E) (M : ℝ) (hM : 0 ≤ M) :
    ∀ᵐ y ∂stdGaussian E, |clippedGaussianL2 x M y| ≤ M := by
  filter_upwards [clippedGaussianL2_ae_eq x M] with y hy
  simpa only [hy, abs_of_nonneg hM] using TauCeti.abs_max_min_le M ⟪x, y⟫_ℝ

/-- Clipping does not increase the `L²` norm of the Gaussian observable. -/
theorem norm_clippedGaussianL2_le (x : E) (M : ℝ) (hM : 0 ≤ M) :
    ‖clippedGaussianL2 x M‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖gaussianL2 x‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [clippedGaussianL2_ae_eq x M, gaussianL2_ae_eq x] with y h₁ h₂
      simpa only [h₁, h₂, Real.norm_eq_abs] using TauCeti.abs_max_min_le_abs hM ⟪x, y⟫_ℝ
    _ = _ := gaussianL2.norm_map x

/-- Clipping a Gaussian linear observable has squared `L²` error at most
`3 ‖x‖⁴ / (16 M²)`. -/
theorem norm_sub_clippedGaussianL2_sq_le (x : E) {M : ℝ} (hM : 0 < M) :
    ‖gaussianL2 x - clippedGaussianL2 x M‖ ^ 2 ≤ 3 * ‖x‖ ^ 4 / (16 * M ^ 2) := by
  have hf₄ : Integrable (fun y ↦ ⟪x, y⟫_ℝ ^ 4) (stdGaussian E) := by
    simpa only [Real.norm_eq_abs, (by decide : Even 4).pow_abs] using
      (memLp_inner_stdGaussian x 4 (by simp)).integrable_norm_pow (by norm_num)
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  calc
    _ = ∫ y, (⟪x, y⟫_ℝ - max (-M) (min M ⟪x, y⟫_ℝ)) ^ 2 ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (gaussianL2 x) (clippedGaussianL2 x M),
        gaussianL2_ae_eq x, clippedGaussianL2_ae_eq x M] with y h₁ h₂ h₃
      simp only [h₁, Pi.sub_apply, h₂, h₃, Real.norm_eq_abs, sq_abs]
    _ ≤ _ := by
      simpa only [innerSL_apply_apply, integral_pow_four_inner_stdGaussian] using
        hf₄.integral_sq_sub_max_min_le hM

/-- The uniform clipping-error bound for Gaussian observables of unit-ball vectors. -/
theorem norm_sub_clippedGaussianL2_sq_le_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1)
    {M : ℝ} (hM : 0 < M) :
    ‖gaussianL2 x - clippedGaussianL2 x M‖ ^ 2 ≤ 3 / (16 * M ^ 2) := by
  refine (norm_sub_clippedGaussianL2_sq_le x hM).trans ?_
  have hx₄ : ‖x‖ ^ 4 ≤ 1 := by nlinarith [pow_le_pow_left₀ (norm_nonneg x) hx 4]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The clipping error of the Gaussian observable of a unit-ball vector has `L²` norm at most
`√3 / (4 * M)`. -/
theorem norm_sub_clippedGaussianL2_le_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) {M : ℝ}
    (hM : 0 < M) : ‖gaussianL2 x - clippedGaussianL2 x M‖ ≤ √3 / (4 * M) := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [div_pow, Real.sq_sqrt (by norm_num), mul_pow]
  exact (norm_sub_clippedGaussianL2_sq_le_of_norm_le_one hx hM).trans_eq (by ring)

section TailMoments

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

private theorem memLp_comp_of_norm_le {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) {f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hf : Measurable f) (hnorm : ∀ g, ‖f g‖ ≤ ‖g‖) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (f g)) p (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hmeas : AEStronglyMeasurable (fun g : EuclideanSpace ℝ ι ↦ U (f g))
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (U.continuous.comp_stronglyMeasurable hf.stronglyMeasurable).aestronglyMeasurable
  refine ((IsGaussian.memLp_id _ p hp).norm.const_mul ‖U‖).mono' hmeas
    (Filter.Eventually.of_forall fun g ↦ ?_)
  exact (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hnorm g) (norm_nonneg U))

/-- Composing a bounded linear map `U` on real Euclidean space with a measurable coordinate mask
belongs to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_coordIndicator {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) {s : Set ℝ} (hs : MeasurableSet s)
    {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (PiLp.coordIndicator s g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  memLp_comp_of_norm_le U (PiLp.measurable_coordIndicator hs) (PiLp.norm_coordIndicator_le s) hp

/-- Composing a bounded linear map `U` on real Euclidean space with coordinate truncation belongs
to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_truncVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) (t : ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (EuclideanSpace.truncVec t g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  memLp_comp_of_norm_le U (EuclideanSpace.measurable_truncVec t)
    (EuclideanSpace.norm_truncVec_le t) hp

/-- Composing a bounded linear map `U` on real Euclidean space with coordinate tail masking belongs
to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_tailVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) (t : ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (EuclideanSpace.tailVec t g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  memLp_comp_of_norm_le U (EuclideanSpace.measurable_tailVec t)
    (EuclideanSpace.norm_tailVec_le t) hp

/-- The product of two coordinates of the Gaussian tail vector `EuclideanSpace.tailVec` is
integrable under the standard Gaussian measure. -/
theorem integrable_tailVec_mul (t : ℝ) (i j : ι) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦
        EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hmeas : Measurable (fun g : EuclideanSpace ℝ ι ↦
        EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j) :=
    ((PiLp.continuous_apply 2 _ i).measurable.comp (EuclideanSpace.measurable_tailVec t)).mul
      ((PiLp.continuous_apply 2 _ j).measurable.comp (EuclideanSpace.measurable_tailVec t))
  refine (IsGaussian.memLp_two_id.integrable_norm_pow (by norm_num)).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g ↦ ?_)
  have hi : |EuclideanSpace.tailVec t g i| ≤ ‖g‖ :=
    (PiLp.norm_apply_le (EuclideanSpace.tailVec t g) i).trans (EuclideanSpace.norm_tailVec_le t g)
  have hj : |EuclideanSpace.tailVec t g j| ≤ ‖g‖ :=
    (PiLp.norm_apply_le (EuclideanSpace.tailVec t g) j).trans (EuclideanSpace.norm_tailVec_le t g)
  simp only [Real.norm_eq_abs, abs_mul, id_eq, sq]
  exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)

/-- Distinct coordinates of the Gaussian tail vector `EuclideanSpace.tailVec` are uncorrelated
under the standard Gaussian measure. -/
theorem integral_tailVec_mul_of_ne (t : ℝ) {i j : ι} (hij : i ≠ j) :
    ∫ g, EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j
        ∂stdGaussian (EuclideanSpace ℝ ι) = 0 := by
  classical
  let ε : ι → ℤˣ := Pi.mulSingle i (-1)
  have hmeas : Measurable (fun g : EuclideanSpace ℝ ι ↦
        EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j) :=
    ((PiLp.continuous_apply 2 _ i).measurable.comp (EuclideanSpace.measurable_tailVec t)).mul
      ((PiLp.continuous_apply 2 _ j).measurable.comp (EuclideanSpace.measurable_tailVec t))
  have hneg :
      ∫ g, EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j
          ∂stdGaussian (EuclideanSpace ℝ ι) =
        -(∫ g, EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j
          ∂stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [← integral_neg]
    conv_lhs =>
      rw [← stdGaussian_map_units_smul ε,
        integral_map (μ := stdGaussian (EuclideanSpace ℝ ι)) (by fun_prop)
          hmeas.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
    dsimp only
    rw [EuclideanSpace.tailVec_units_smul, EuclideanSpace.tailVec_units_smul]
    simp only [ε, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm, Units.smul_def,
      Units.val_neg, Units.val_one, neg_smul, one_smul, EuclideanSpace.tailVec_apply]
    split_ifs <;> ring
  linarith

/-- Each coordinate of `EuclideanSpace.tailVec t` has second moment equal to the one-dimensional
Gaussian tail second moment. -/
theorem integral_tailVec_sq (t : ℝ) (i : ι) :
    ∫ g, EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g i
        ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  classical
  have hs : MeasurableSet {r : ℝ | t < |r|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hnorm : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  have hfun : (fun g : EuclideanSpace ℝ ι ↦
        EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g i) =
      fun g ↦ Set.indicator {r : ℝ | t < |r|} (fun r ↦ r ^ 2)
        ⟪g, EuclideanSpace.single i (1 : ℝ)⟫_ℝ := by
    ext g
    simp [Set.indicator_apply]
    split_ifs <;> ring
  rw [hfun, ← integral_map (by fun_prop)
      (Measurable.indicator (by fun_prop) hs).aestronglyMeasurable,
    map_inner_stdGaussian_of_norm_eq_one hnorm, integral_indicator hs]

/-- On a real continuous linear functional `f`, the expected squared value on `tailVec t g`
equals `‖f‖²` times the one-dimensional Gaussian tail second moment. -/
theorem integral_sq_apply_tailVec (f : StrongDual ℝ (EuclideanSpace ℝ ι)) (t : ℝ) :
    ∫ g, |f (EuclideanSpace.tailVec t g)| ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      ‖f‖ ^ 2 * ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  classical
  have hexpand (v : EuclideanSpace ℝ ι) :
      f v = ∑ i, v i * f (EuclideanSpace.basisFun ι ℝ i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
    simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr]
  have hsq (g : EuclideanSpace ℝ ι) : |f (EuclideanSpace.tailVec t g)| ^ 2 =
      ∑ i, ∑ j, (f (EuclideanSpace.basisFun ι ℝ i) * f (EuclideanSpace.basisFun ι ℝ j)) *
        (EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j) := by
    rw [sq_abs, hexpand, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [hsq]
  rw [integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ (integrable_tailVec_mul t i j).const_mul _]
  have hinner (i : ι) :
      ∫ g, ∑ j, (f (EuclideanSpace.basisFun ι ℝ i) * f (EuclideanSpace.basisFun ι ℝ j)) *
          (EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j)
          ∂stdGaussian (EuclideanSpace ℝ ι) =
        f (EuclideanSpace.basisFun ι ℝ i) ^ 2 *
          ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
    rw [integral_finsetSum _ fun j _ ↦ (integrable_tailVec_mul t i j).const_mul _]
    simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single i
        (fun j _ hji ↦ by rw [integral_tailVec_mul_of_ne t hji.symm, mul_zero])
        (fun hi ↦ (hi (Finset.mem_univ i)).elim),
      integral_tailVec_sq t i, sq]
  simp_rw [hinner, ← Finset.sum_mul, ← (EuclideanSpace.basisFun ι ℝ).norm_dual f]

end TailMoments

end TauCeti.Probability
