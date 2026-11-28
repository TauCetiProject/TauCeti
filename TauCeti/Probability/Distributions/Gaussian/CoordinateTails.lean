/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.Distributions.Gaussian.Symmetry

import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Probability.Distributions.Gaussian.OrthogonalSplitting

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

* `TauCeti.Probability.memLp_coordIndicator`, `TauCeti.Probability.memLp_truncVec`,
  `TauCeti.Probability.memLp_tailVec`: finite `Lᵖ` membership of coordinate masks under
  `stdGaussian`.
* `ContinuousLinearMap.memLp_comp_coordIndicator`, `ContinuousLinearMap.memLp_comp_truncVec`,
  `ContinuousLinearMap.memLp_comp_tailVec`: finite `Lᵖ` membership of bounded linear images of
  coordinate masks under `stdGaussian`.
* `TauCeti.Probability.truncVec_signFlip`, `TauCeti.Probability.tailVec_signFlip`: coordinatewise
  truncation and tail masking commute with `TauCeti.Probability.signFlip`.
* `TauCeti.Probability.integrable_tailVec_mul`: integrability of pairwise products of tail
  coordinates.
* `TauCeti.Probability.integral_tailVec_mul_of_ne`: distinct tail coordinates are uncorrelated.
* `TauCeti.Probability.integral_tailVec_mul_self`: diagonal tail second moment.
* `ContinuousLinearMap.integral_sq_apply_tailVec`: second moment of `f (tailVec t g)`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Under the standard Gaussian measure on `EuclideanSpace ℝ ι`, a measurable coordinate mask
`PiLp.coordIndicator s` belongs to every finite `Lᵖ` space. -/
theorem memLp_coordIndicator {s : Set ℝ} (hs : MeasurableSet s) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (PiLp.coordIndicator s : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ ι)) p hp).of_le
    (PiLp.measurable_coordIndicator hs).aestronglyMeasurable
    (Filter.Eventually.of_forall (PiLp.norm_coordIndicator_le s))

/-- Under the standard Gaussian measure on `EuclideanSpace ℝ ι`, coordinate truncation
`EuclideanSpace.truncVec t` belongs to every finite `Lᵖ` space. -/
theorem memLp_truncVec (t : ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (EuclideanSpace.truncVec (ι := ι) t) p (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [funext (EuclideanSpace.truncVec_def t)]
  exact memLp_coordIndicator (measurableSet_le continuous_abs.measurable measurable_const) hp

/-- Under the standard Gaussian measure on `EuclideanSpace ℝ ι`, coordinate tail masking
`EuclideanSpace.tailVec t` belongs to every finite `Lᵖ` space. -/
theorem memLp_tailVec (t : ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (EuclideanSpace.tailVec (ι := ι) t) p (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [funext (EuclideanSpace.tailVec_def t)]
  exact memLp_coordIndicator (measurableSet_lt measurable_const continuous_abs.measurable) hp

end TauCeti.Probability

namespace ContinuousLinearMap

variable {ι : Type*} [Fintype ι]

/-- Composing a bounded linear map `U` on real Euclidean space with a measurable coordinate mask
belongs to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_coordIndicator {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) {s : Set ℝ} (hs : MeasurableSet s)
    {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (PiLp.coordIndicator s g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  U.comp_memLp' (TauCeti.Probability.memLp_coordIndicator hs hp)

/-- Composing a bounded linear map `U` on real Euclidean space with coordinate truncation belongs
to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_truncVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) (t : ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (EuclideanSpace.truncVec t g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  U.comp_memLp' (TauCeti.Probability.memLp_truncVec t hp)

/-- Composing a bounded linear map `U` on real Euclidean space with coordinate tail masking belongs
to every finite `Lᵖ` space under the standard Gaussian measure. -/
theorem memLp_comp_tailVec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : EuclideanSpace ℝ ι →L[ℝ] Y) (t : ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ U (EuclideanSpace.tailVec t g)) p
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  U.comp_memLp' (TauCeti.Probability.memLp_tailVec t hp)

end ContinuousLinearMap

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise truncation commutes with `TauCeti.Probability.signFlip`. -/
theorem truncVec_signFlip (t : ℝ) (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι) (i : ι) :
    EuclideanSpace.truncVec t (signFlip ε g) i = ε i • EuclideanSpace.truncVec t g i := by
  simp only [EuclideanSpace.truncVec_apply, signFlip_apply, ← Real.norm_eq_abs, norm_units_zsmul]
  split_ifs <;> simp

/-- Coordinatewise tail masking commutes with `TauCeti.Probability.signFlip`. -/
theorem tailVec_signFlip (t : ℝ) (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι) (i : ι) :
    EuclideanSpace.tailVec t (signFlip ε g) i = ε i • EuclideanSpace.tailVec t g i := by
  simp only [EuclideanSpace.tailVec_apply, signFlip_apply, ← Real.norm_eq_abs, norm_units_zsmul]
  split_ifs <;> simp

/-- The product of two coordinates of the Gaussian tail vector `EuclideanSpace.tailVec` is
integrable under the standard Gaussian measure. -/
theorem integrable_tailVec_mul (t : ℝ) (i j : ι) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦
        EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hmem := memLp_tailVec (ι := ι) t (p := 2) (by simp)
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
      rw [← (signFlip ε).integral_comp_stdGaussian]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
    dsimp only
    rw [tailVec_signFlip, tailVec_signFlip]
    simp only [ε, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm, Units.smul_def,
      Units.val_neg, Units.val_one, neg_smul, one_smul, neg_mul]
  linarith

/-- Each coordinate of `EuclideanSpace.tailVec t` has second moment equal to the one-dimensional
Gaussian tail second moment. -/
theorem integral_tailVec_mul_self (t : ℝ) (i : ι) :
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
    simp only [EuclideanSpace.tailVec_apply, Set.indicator_apply, Set.mem_ofPred_eq,
      EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    split_ifs <;> simp [sq]
  rw [hfun, ← integral_map (by fun_prop)
      (Measurable.indicator (by fun_prop) hs).aestronglyMeasurable,
    map_inner_stdGaussian_of_norm_eq_one hnorm, integral_indicator hs]

end TauCeti.Probability

namespace ContinuousLinearMap

variable {ι : Type*} [Fintype ι]

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
  have hmem := TauCeti.Probability.memLp_tailVec (ι := ι) t (p := 2) (by simp)
  let X : ι → EuclideanSpace ℝ ι → ℝ :=
    fun i g ↦ EuclideanSpace.tailVec t g i * f (EuclideanSpace.basisFun ι ℝ i)
  have hX (i : ι) (_ : i ∈ Finset.univ) : MemLp (X i) 2 (stdGaussian (EuclideanSpace ℝ ι)) :=
    (hmem.eval_piLp i).mul_const (f (EuclideanSpace.basisFun ι ℝ i))
  have horth : (↑(Finset.univ : Finset ι) : Set ι).Pairwise fun i j ↦
      (∫ g, X i g * X j g ∂stdGaussian (EuclideanSpace ℝ ι)) = 0 := by
    intro i _ j _ hij
    have hmul (g : EuclideanSpace ℝ ι) : X i g * X j g =
        (f (EuclideanSpace.basisFun ι ℝ i) * f (EuclideanSpace.basisFun ι ℝ j)) *
          (EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g j) := by
      simp only [X]; ring
    simp_rw [hmul, integral_const_mul, TauCeti.Probability.integral_tailVec_mul_of_ne t hij,
      mul_zero]
  have hsq (g : EuclideanSpace ℝ ι) :
      |f (EuclideanSpace.tailVec t g)| ^ 2 = (∑ i, X i g) ^ 2 := by
    rw [sq_abs, hexpand]
  simp_rw [hsq]
  rw [TauCeti.integral_sq_sum_of_pairwise_integral_mul_eq_zero hX horth]
  have hdiag (i : ι) :
      ∫ g, X i g ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
        f (EuclideanSpace.basisFun ι ℝ i) ^ 2 *
          ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
    have hsq (g : EuclideanSpace ℝ ι) : X i g ^ 2 =
        f (EuclideanSpace.basisFun ι ℝ i) ^ 2 *
          (EuclideanSpace.tailVec t g i * EuclideanSpace.tailVec t g i) := by
      simp only [X]; ring
    simp_rw [hsq, integral_const_mul, TauCeti.Probability.integral_tailVec_mul_self]
  simp_rw [hdiag, ← Finset.sum_mul, ← (EuclideanSpace.basisFun ι ℝ).norm_dual f]

end ContinuousLinearMap
