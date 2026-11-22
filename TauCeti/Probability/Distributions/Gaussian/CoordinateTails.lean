/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Analysis.InnerProductSpace.PiL2

import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.Probability.Distributions.Gaussian.OrthogonalSplitting
import TauCeti.Probability.Distributions.Gaussian.Symmetry

/-!
# Coordinate-tail integrability and moments under the standard Gaussian measure

Under the standard Gaussian measure on `EuclideanSpace ℝ ι`, composing any bounded linear map
`U : EuclideanSpace ℝ ι →L[ℝ] Y` with a measurable coordinatewise mask (`PiLp.coordIndicator`,
`EuclideanSpace.truncVec`, or `EuclideanSpace.tailVec`) belongs to every finite `Lᵖ` space.

In particular, distinct coordinates of `EuclideanSpace.tailVec t` are uncorrelated, each diagonal
coordinate has second moment equal to the one-dimensional Gaussian tail second moment
`∫_{|r| > t} r² dγ₁`, and therefore `𝔼[|f (tailVec t g)|²] = ‖f‖² ∫_{|r| > t} r² dγ₁` for every
`f : StrongDual ℝ (EuclideanSpace ℝ ι)`.

## Main declarations

* `TauCeti.Probability.memLp_comp_coordIndicator`, `TauCeti.Probability.memLp_comp_truncVec`,
  `TauCeti.Probability.memLp_comp_tailVec`: finite `Lᵖ` membership of bounded linear images of
  coordinate masks under `stdGaussian`.
* `TauCeti.Probability.integrable_tailVec_mul`: integrability of pairwise products of tail
  coordinates.
* `TauCeti.Probability.integral_tailVec_mul_of_ne`: distinct tail coordinates are uncorrelated.
* `TauCeti.Probability.integral_tailVec_sq`: diagonal tail second moment.
* `TauCeti.Probability.integral_sq_apply_tailVec`: second moment of `f (tailVec t g)`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Composing a bounded linear map `U` on real Euclidean space with a measurable coordinate mask
belongs to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_coordIndicator {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) {s : Set ℝ} (hs : MeasurableSet s)
    {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (PiLp.coordIndicator s g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  (IsGaussian.memLp_id _ p hp).clm_comp_of_ae_norm_le U
    (PiLp.measurable_coordIndicator hs).aestronglyMeasurable
    (Filter.Eventually.of_forall (PiLp.norm_coordIndicator_le s))

/-- Composing a bounded linear map `U` on real Euclidean space with coordinate truncation belongs
to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_truncVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) (t : ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (EuclideanSpace.truncVec t g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  (IsGaussian.memLp_id _ p hp).clm_comp_of_ae_norm_le U
    (EuclideanSpace.measurable_truncVec t).aestronglyMeasurable
    (Filter.Eventually.of_forall (EuclideanSpace.norm_truncVec_le t))

/-- Composing a bounded linear map `U` on real Euclidean space with coordinate tail masking belongs
to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_tailVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) (t : ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (EuclideanSpace.tailVec t g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  (IsGaussian.memLp_id _ p hp).clm_comp_of_ae_norm_le U
    (EuclideanSpace.measurable_tailVec t).aestronglyMeasurable
    (Filter.Eventually.of_forall (EuclideanSpace.norm_tailVec_le t))

/-- The product of two coordinates of the Gaussian tail vector `EuclideanSpace.tailVec` is
integrable under the standard Gaussian measure. -/
theorem integrable_tailVec_mul (t : ℝ) (i j : ι) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦
        EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hmem : MemLp (EuclideanSpace.tailVec (ι := ι) t) 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa using memLp_comp_tailVec (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) t (by simp)
  have : ENNReal.HolderConjugate 2 2 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  exact (hmem.eval_piLp i).integrable_mul (hmem.eval_piLp j)

/-- Distinct coordinates of the Gaussian tail vector `EuclideanSpace.tailVec` are uncorrelated
under the standard Gaussian measure. -/
theorem integral_tailVec_mul_of_ne (t : ℝ) {i j : ι} (hij : i ≠ j) :
    ∫ g, EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j
        ∂stdGaussian (EuclideanSpace ℝ ι) = 0 := by
  classical
  let ε : ι → ℤˣ := Pi.mulSingle i (-1)
  have hneg :
      ∫ g, EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j
          ∂stdGaussian (EuclideanSpace ℝ ι) =
        -(∫ g, EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j
          ∂stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [← integral_neg]
    conv_lhs =>
      rw [← stdGaussian_map_units_smul ε,
        integral_map (μ := stdGaussian (EuclideanSpace ℝ ι)) (by fun_prop)
          (by rw [stdGaussian_map_units_smul ε]
              exact (integrable_tailVec_mul t i j).aestronglyMeasurable)]
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

end TauCeti.Probability
