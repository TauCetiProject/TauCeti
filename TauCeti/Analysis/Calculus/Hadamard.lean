/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Smooth Hadamard factorization

This file develops the first-order factorization of a smooth map through displacement from a
basepoint. It is the analytic input for identifying point derivations on a finite-dimensional
smooth manifold with tangent vectors.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff unitInterval

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The weighted average of `g` along the segment from `x` to `x + v`. -/
noncomputable def segmentAverage (w : ℝ → ℝ) (g : E → F) (x v : E) : F :=
  ∫ t in (0 : ℝ)..1, w t • g (x + t • v)

/-- A weighted segment average written as an integral over the compact unit interval. -/
theorem segmentAverage_eq_integral_Icc (w : ℝ → ℝ) (g : E → F) (x : E) :
    segmentAverage w g x = fun v ↦ ∫ t in Set.Icc (0 : ℝ) 1, w t • g (x + t • v) := by
  funext v
  rw [segmentAverage, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]

/-- A weighted segment average is `C^n` in its displacement when the integrand is `C^n` and the
weight is interval integrable. -/
theorem ContDiff.contDiff_segmentAverage {n : ℕ∞} {w : ℝ → ℝ} {g : E → F}
    (hg : ContDiff ℝ n g) (hw : IntervalIntegrable w volume 0 1) (x : E) :
    ContDiff ℝ n (segmentAverage w g x) := by
  have hwi : IntegrableOn w (Set.Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hw
  rw [← contDiffOn_univ]
  refine (TauCeti.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    ((integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hwi)
    continuous_subtype_val isOpen_univ
    ((hg.comp (by fun_prop : ContDiff ℝ n (fun p : E × ℝ ↦ x + p.2 • p.1))).contDiffOn)
    isOpen_univ (fun _ _ _ ↦ Set.mem_univ _)).congr fun v _ ↦ ?_
  rw [segmentAverage, TauCeti.intervalIntegral_eq_integral_unitInterval]
  rfl

/-- A continuous linear map commutes with a weighted segment average. -/
theorem ContinuousLinearMap.segmentAverage_apply
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : F →L[ℝ] G) (w : ℝ → ℝ) (g : E → F) (x v : E)
    (h : IntervalIntegrable (fun t : ℝ ↦ w t • g (x + t • v)) volume 0 1) :
    L (segmentAverage w g x v) = ∫ t in (0 : ℝ)..1, L (w t • g (x + t • v)) := by
  rw [segmentAverage]
  exact (L.intervalIntegral_comp_comm h).symm

/-- At zero displacement, a weighted segment average is the integral of the weight times the
value of the integrand at the basepoint. -/
@[simp]
theorem segmentAverage_zero [CompleteSpace F] (w : ℝ → ℝ) (g : E → F) (x : E) :
    segmentAverage w g x 0 = (∫ t in (0 : ℝ)..1, w t) • g x := by
  rw [segmentAverage]
  simp only [smul_zero, add_zero]
  exact intervalIntegral.integral_smul_const w (g x)

/-- The averaged derivative along the segment from `x` to `y`. -/
noncomputable def hadamardFactor (f : E → F) (x y : E) : E →L[ℝ] F :=
  segmentAverage (fun _ ↦ 1) (fderiv ℝ f) x (y - x)

/-- The averaged derivative written as an integral over the compact unit interval. -/
theorem hadamardFactor_eq_integral_Icc (f : E → F) (x : E) :
    hadamardFactor f x = fun y ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      fderiv ℝ f (x + t • (y - x)) := by
  funext y
  simp only [hadamardFactor, segmentAverage_eq_integral_Icc, one_smul]

/-- At the basepoint, the averaged derivative is the ordinary derivative. -/
@[simp]
theorem hadamardFactor_self [CompleteSpace F] (f : E → F) (x : E) :
    hadamardFactor f x x = fderiv ℝ f x := by
  simp [hadamardFactor]

/-- If `f` is `n + 1` times continuously differentiable, its Hadamard factor is `n` times
continuously differentiable in the endpoint. -/
theorem ContDiff.contDiff_hadamardFactor_of_succ
    (n : ℕ∞) (f : E → F) (hf : ContDiff ℝ (n + 1) f) (x : E) :
    ContDiff ℝ n (hadamardFactor f x) := by
  have hd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (m := n) (by norm_num)
  exact (hd.contDiff_segmentAverage intervalIntegrable_const x).comp (by fun_prop)

/-- First-order Taylor expansion along a segment, with its coefficient bundled as a continuous
linear map. -/
theorem ContDiff.sub_eq_hadamardFactor_apply [CompleteSpace F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (x y : E) :
    f y - f x = hadamardFactor f x y (y - x) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (x := x) (y := y - x)
    (fun _ _ ↦ hf.contDiffAt)
  have hIntegrable : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ f (x + t • (y - x)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (hf.fderiv_right (m := 0) (by norm_num)).continuous.comp (by fun_prop)
  rw [hadamardFactor, segmentAverage]
  simp only [one_smul]
  rw [ContinuousLinearMap.intervalIntegral_apply hIntegrable (y - x)]
  simpa [sub_eq_iff_eq_add, add_comm] using hTaylor

/-- For a smooth function, the averaged derivative in Hadamard's factorization depends smoothly on
the endpoint. -/
theorem ContDiff.contDiff_hadamardFactor (f : E → F)
    (hf : ContDiff ℝ ∞ f)
    (x : E) : ContDiff ℝ ∞ (hadamardFactor f x) := by
  simpa using ContDiff.contDiff_hadamardFactor_of_succ (⊤ : ℕ∞) f (by simpa using hf) x
