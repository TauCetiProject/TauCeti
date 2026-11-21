/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Probability.Distributions.Gaussian.L2

/-!
# Second moments of finite Gaussian sums

The Gaussian second moment of a finite family in a real normed space is the square root
of the expected squared norm of its sum with independent standard Gaussian coefficients.
The coefficient space is the native Euclidean space with its standard Gaussian measure.
In particular the definition works for empty families and does not require completeness
of the target space.

We also record the basic structural properties of Gaussian sums: absolute homogeneity,
subadditivity (the `L²` triangle inequality), comparison along bounded additive maps, and the
exact value on constant and single-element families.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {ι Y : Type*} [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A finite Gaussian sum has every finite moment, even in an incomplete target. -/
theorem memLp_gaussianSum (x : ι → Y) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • x i) p
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let T : EuclideanSpace ℝ ι →L[ℝ] Y :=
    (EuclideanSpace.basisFun ι ℝ).toBasis.constrL x
  have hT (g : EuclideanSpace ℝ ι) : T g = ∑ i, g i • x i :=
    EuclideanSpace.basisFun_toBasis_constrL_apply x g
  simpa only [Function.comp_def, id_eq, hT] using
    T.comp_memLp' (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ ι)) p hp)

/-- The squared norm of a finite Gaussian sum is integrable. -/
theorem integrable_norm_sq_gaussianSum (x : ι → Y) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖∑ i, g i • x i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  (memLp_gaussianSum x 2 (by simp)).integrable_norm_pow (by norm_num)

/-- The Gaussian second moment of a finite family, with independent real standard Gaussian
coefficients. -/
def gaussianSecondMoment (x : ι → Y) : ℝ :=
  √(∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι))

/-- The defining integral of the Gaussian second moment. -/
theorem gaussianSecondMoment_def (x : ι → Y) :
    gaussianSecondMoment x =
      √(∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι)) :=
  (rfl)

/-- Gaussian second moments are nonnegative. -/
theorem gaussianSecondMoment_nonneg (x : ι → Y) : 0 ≤ gaussianSecondMoment x :=
  Real.sqrt_nonneg _

/-- Squaring the Gaussian second moment recovers the expected squared norm. -/
theorem gaussianSecondMoment_sq (x : ι → Y) :
    gaussianSecondMoment x ^ 2 =
      ∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) :=
  Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)

/-- Multiplying a family by a real scalar multiplies its Gaussian second moment by the
absolute value of that scalar. -/
theorem gaussianSecondMoment_smul (x : ι → Y) (c : ℝ) :
    gaussianSecondMoment (fun i ↦ c • x i) = |c| * gaussianSecondMoment x := by
  have hs (g : EuclideanSpace ℝ ι) :
      (∑ i, g i • (c • x i)) = c • ∑ i, g i • x i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
  apply (sq_eq_sq₀ (gaussianSecondMoment_nonneg _)
    (mul_nonneg (abs_nonneg _) (gaussianSecondMoment_nonneg _))).1
  rw [mul_pow, gaussianSecondMoment_sq, gaussianSecondMoment_sq]
  simp_rw [hs, norm_smul, mul_pow]
  rw [integral_const_mul, Real.norm_eq_abs]

@[simp]
theorem gaussianSecondMoment_zero : gaussianSecondMoment (0 : ι → Y) = 0 := by
  simp [gaussianSecondMoment]

/-- An empty Gaussian sum has second moment zero. -/
@[simp]
theorem gaussianSecondMoment_of_isEmpty [IsEmpty ι] (x : ι → Y) :
    gaussianSecondMoment x = 0 := by
  simp [gaussianSecondMoment]

/-- The Gaussian second moment satisfies the triangle inequality. -/
theorem gaussianSecondMoment_add_le (x y : ι → Y) :
    gaussianSecondMoment (x + y) ≤ gaussianSecondMoment x + gaussianSecondMoment y := by
  have hxy (g : EuclideanSpace ℝ ι) : ∑ i, g i • (x + y) i =
      ((fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • x i) +
        (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • y i)) g := by
    simp [smul_add, Finset.sum_add_distrib]
  simp only [gaussianSecondMoment_def, hxy]
  exact (memLp_gaussianSum x 2 (by simp)).sqrt_integral_norm_add_sq_le
    (memLp_gaussianSum y 2 (by simp))

/-- A bounded additive map `f` with `‖f y‖ ≤ M * ‖y‖` multiplies Gaussian second moments by at most
`M`. -/
theorem gaussianSecondMoment_map_le {F 𝓕 : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FunLike 𝓕 Y F] [AddMonoidHomClass 𝓕 Y F] (f : 𝓕) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M * ‖y‖)
    (x : ι → Y) :
    gaussianSecondMoment (fun i ↦ f (x i)) ≤ M * gaussianSecondMoment x := by
  rcases subsingleton_or_nontrivial Y with hY | hY
  · have hx : x = 0 := Subsingleton.elim _ _
    have hfx : (fun i ↦ f (x i)) = (0 : ι → F) := by ext i; simp [hx]
    rw [hfx, hx, gaussianSecondMoment_zero, gaussianSecondMoment_zero, mul_zero]
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : Y)
  have hM0 : 0 ≤ M := by
    have h0 := (norm_nonneg (f y₀)).trans (hM y₀)
    exact nonneg_of_mul_nonneg_left h0 (norm_pos_iff.2 hy₀)
  have hf_cont : Continuous f := AddMonoidHomClass.continuous_of_bound f M hM
  rw [gaussianSecondMoment_def, Real.sqrt_le_iff]
  refine ⟨mul_nonneg hM0 (gaussianSecondMoment_nonneg x), ?_⟩
  rw [mul_pow, gaussianSecondMoment_sq, ← integral_const_mul]
  refine integral_mono (integrable_norm_sq_gaussianSum _)
    ((integrable_norm_sq_gaussianSum x).const_mul _) fun g ↦ ?_
  have hsum : ∑ i, g i • f (x i) = f (∑ i, g i • x i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (map_real_smul f hf_cont (g i) (x i)).symm
  rw [hsum, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM _) 2

/-- The Gaussian second moment of `card ι` copies of a vector `y` is `√(card ι) * ‖y‖`. -/
theorem gaussianSecondMoment_const (y : Y) :
    gaussianSecondMoment (fun _ : ι ↦ y) = √(Fintype.card ι) * ‖y‖ := by
  have hs (g : EuclideanSpace ℝ ι) :
      ∑ i, g i • y = ⟪WithLp.toLp 2 (fun _ : ι ↦ (1 : ℝ)), g⟫ • y := by
    rw [← Finset.sum_smul]
    congr 1
    simp [PiLp.inner_apply, mul_comm]
  rw [gaussianSecondMoment_def]
  have hint : ∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • y‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      (Fintype.card ι : ℝ) * ‖y‖ ^ 2 := by
    simp_rw [hs, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [integral_mul_const, TauCeti.Probability.integral_sq_inner_stdGaussian]
    simp [PiLp.norm_sq_eq_of_L2]
  rw [hint, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- A one-element family has Gaussian second moment equal to the norm of its sole vector. -/
@[simp]
theorem gaussianSecondMoment_unique [Unique ι] (x : ι → Y) :
    gaussianSecondMoment x = ‖x default‖ := by
  have hx : x = fun _ ↦ x default := funext fun i ↦ congrArg x (Unique.eq_default i)
  rw [hx, gaussianSecondMoment_const]
  simp

end TauCeti
