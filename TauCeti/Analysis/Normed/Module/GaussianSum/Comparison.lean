/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Basic

import TauCeti.Analysis.Normed.Module.GaussianSum.WeakTwo

import TauCeti.Probability.Distributions.Gaussian.Defect
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian comparison under weak square domination

Contractions of the finite Euclidean coefficient space decrease the second moment
of a normed-space-valued Gaussian sum. Consequently, domination of all scalar square
functions implies domination of the Gaussian second moments. The target need not be
complete: integration of vector-valued functions is performed only in the finite-dimensional
coefficient space.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Lemma 3.5, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace ContinuousLinearMap

variable {E F Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A contraction of a finite-dimensional standard Gaussian coefficient vector decreases
the expected squared norm after applying any continuous linear map into a real normed space. -/
theorem integral_norm_sq_comp_le_stdGaussian (U : E →L[ℝ] Y) (D : F →L[ℝ] E)
    (hD : ‖D‖ ≤ 1) :
    (∫ g, ‖U (D g)‖ ^ 2 ∂stdGaussian F) ≤
      ∫ g, ‖U g‖ ^ 2 ∂stdGaussian E := by
  let S : E →L[ℝ] E := CFC.sqrt (1 - D ∘L D.adjoint)
  let T : F × E →L[ℝ] E := D.comp (.fst ℝ F E) + S.comp (.snd ℝ F E)
  have hT : ((stdGaussian F).prod (stdGaussian E)).map T = stdGaussian E :=
    D.map_add_defect_stdGaussian hD
  have hi : Integrable (fun p : F × E ↦ ‖U (T p)‖ ^ 2)
      ((stdGaussian F).prod (stdGaussian E)) := by
    exact ((U.comp T).comp_memLp'
      (IsGaussian.memLp_two_id (μ := (stdGaussian F).prod (stdGaussian E)))).integrable_norm_pow
      (by norm_num)
  have hc : ConvexOn ℝ Set.univ (fun z : E ↦ ‖U z‖ ^ 2) := by
    simpa only [Function.comp_def, Pi.pow_apply, Set.preimage_univ] using!
      ((convexOn_univ_norm (E := Y)).pow (fun _ _ ↦ norm_nonneg _) 2).comp_linearMap
      U.toLinearMap
  calc
    (∫ g, ‖U (D g)‖ ^ 2 ∂stdGaussian F)
        ≤ ∫ g, ∫ z, ‖U (D g + S z)‖ ^ 2 ∂stdGaussian E ∂stdGaussian F := by
      apply integral_mono_ae
        (((U.comp D).comp_memLp' (IsGaussian.memLp_two_id)).integrable_norm_pow (by norm_num))
        hi.integral_prod_left
      filter_upwards [hi.prod_right_ae] with g hg
      have hvec : Integrable (fun z : E ↦ D g + S z) (stdGaussian E) :=
        (integrable_const _).add (S.integrable_comp IsGaussian.integrable_id)
      have hj := hc.map_integral_le (by fun_prop) isClosed_univ
        (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _) hvec hg
      have hint : (∫ z, D g + S z ∂stdGaussian E) = D g := by
        rw [integral_add (integrable_const _) (S.integrable_comp IsGaussian.integrable_fun_id),
          S.integral_comp_comm IsGaussian.integrable_fun_id]
        simp
      simpa only [hint, T, add_apply, comp_apply, coe_fst', coe_snd',
        Function.comp_def, id_eq] using hj
    _ = ∫ g, ‖U (T g)‖ ^ 2 ∂((stdGaussian F).prod (stdGaussian E)) :=
      (integral_prod _ hi).symm
    _ = ∫ g, ‖U g‖ ^ 2 ∂stdGaussian E := by
      conv_rhs => rw [← hT, integral_map (by fun_prop) (by fun_prop)]

end ContinuousLinearMap

namespace TauCeti

variable {ι κ Y : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Domination of the square sums of all real continuous functionals implies domination
of the Gaussian second moments. -/
theorem gaussianSecondMoment_le_of_weakTwo_le (x : ι → Y) (y : κ → Y)
    (h : ∀ f : StrongDual ℝ Y,
      ∑ i, |f (x i)| ^ 2 ≤ ∑ j, |f (y j)| ^ 2) :
    gaussianSecondMoment x ≤ gaussianSecondMoment y := by
  obtain ⟨D, hD, hxy⟩ := exists_contraction_of_weakTwo_le x y h
  let U : EuclideanSpace ℝ κ →L[ℝ] Y :=
    ∑ j, (EuclideanSpace.proj j).smulRight (y j)
  rw [gaussianSecondMoment_def, gaussianSecondMoment_def]
  apply Real.sqrt_le_sqrt
  simpa only [U, sum_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.coe_proj, ← hxy] using
    U.integral_norm_sq_comp_le_stdGaussian D.adjoint (ContinuousLinearMap.adjoint.norm_map D ▸ hD)

end TauCeti
