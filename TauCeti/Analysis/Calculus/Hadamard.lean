/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import TauCeti.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Smooth Hadamard factorization

This file develops the first-order factorization of a smooth map through displacement from a
basepoint. It is the analytic input for identifying point derivations on a finite-dimensional
smooth manifold with tangent vectors.

Its higher-order analogue is `TauCeti.taylorRemainderFactor n f x y`, the averaged `(n + 1)`-st
derivative of `f` along the segment from `x` to `y` with the weight of Taylor's integral remainder.
Evaluated on `n + 1` copies of `y - x`, it is the remainder of the Taylor expansion of order `n`
of `f` at `x`, and it depends smoothly on `y`. Expanding the increment in a basis turns this
remainder into a combination of products of `n + 1` coordinate functions vanishing at `x`, which
is how the powers of the vanishing ideal of a point are described by vanishing derivatives.
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

/-- Weighted segment averages of a jointly `C^n` family are jointly `C^n` in the parameter and
the displacement. -/
theorem ContDiff.contDiff_segmentAverage_param
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ∞} {w : ℝ → ℝ} {g : P × E → F}
    (hg : ContDiff ℝ n g) (hw : IntervalIntegrable w volume 0 1) (x : E) :
    ContDiff ℝ n (fun p : P × E ↦ segmentAverage w (fun y ↦ g (p.1, y)) x p.2) := by
  have hwi : IntegrableOn w (Set.Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hw
  rw [← contDiffOn_univ]
  refine (TauCeti.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    ((integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hwi)
    continuous_subtype_val isOpen_univ
    ((hg.comp (by fun_prop :
      ContDiff ℝ n (fun p : (P × E) × ℝ ↦ (p.1.1, x + p.2 • p.1.2)))).contDiffOn)
    (fun _ _ _ ↦ Set.mem_univ _)).congr fun v _ ↦ ?_
  rw [segmentAverage, TauCeti.intervalIntegral_eq_integral_unitInterval]
  rfl

/-- A weighted segment average is `C^n` in its displacement when the integrand is `C^n` and the
weight is interval integrable. -/
theorem ContDiff.contDiff_segmentAverage {n : ℕ∞} {w : ℝ → ℝ} {g : E → F}
    (hg : ContDiff ℝ n g) (hw : IntervalIntegrable w volume 0 1) (x : E) :
    ContDiff ℝ n (segmentAverage w g x) := by
  exact ((hg.comp contDiff_snd).contDiff_segmentAverage_param hw x).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ n (fun v : E ↦ ((0 : E), v)))

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

namespace TauCeti

open scoped Nat in
/-- The averaged `(n + 1)`-st derivative of `f` along the segment from `x` to `y`, with the weight
`(1 - t) ^ n / n!` of the integral form of Taylor's remainder. Evaluated on `n + 1` copies of
`y - x`, it is the remainder of the Taylor expansion of order `n` of `f` at `x`
(`ContDiff.eq_sum_add_taylorRemainderFactor_apply`). -/
noncomputable def taylorRemainderFactor (n : ℕ) (f : E → F) (x y : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) F :=
  (n ! : ℝ)⁻¹ • segmentAverage (fun t ↦ (1 - t) ^ n) (iteratedFDeriv ℝ (n + 1) f) x (y - x)

open scoped Nat in
/-- At the basepoint, the Taylor remainder factor of order `n` is the leading Taylor coefficient
`iteratedFDeriv ℝ (n + 1) f x / (n + 1)!`. -/
@[simp]
theorem taylorRemainderFactor_self [CompleteSpace F] (n : ℕ) (f : E → F) (x : E) :
    taylorRemainderFactor n f x x = ((n + 1)! : ℝ)⁻¹ • iteratedFDeriv ℝ (n + 1) f x := by
  have hint : ∫ t in (0 : ℝ)..1, (1 - t) ^ n = ((n : ℝ) + 1)⁻¹ := by
    simp [intervalIntegral.integral_comp_sub_left fun t : ℝ ↦ t ^ n, integral_pow]
  rw [taylorRemainderFactor, sub_self, segmentAverage_zero, hint, smul_smul, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ, mul_inv, mul_comm]

end TauCeti

open TauCeti

/-- If `f` is `k + (n + 1)` times continuously differentiable, its Taylor remainder factor of
order `n` is `k` times continuously differentiable in the endpoint. -/
theorem ContDiff.contDiff_taylorRemainderFactor {f : E → F} {k : ℕ∞} {n : ℕ}
    (hf : ContDiff ℝ (k + (n + 1) : ℕ∞) f) (x : E) :
    ContDiff ℝ k (taylorRemainderFactor n f x) := by
  have hd : ContDiff ℝ k (iteratedFDeriv ℝ (n + 1) f) :=
    hf.iteratedFDeriv_right (by push_cast; exact le_rfl)
  exact ((hd.contDiff_segmentAverage
    ((by fun_prop : Continuous fun t : ℝ ↦ (1 - t) ^ n).intervalIntegrable 0 1) x).comp
      (contDiff_id.sub contDiff_const)).const_smul _

open scoped Nat in
/-- **Taylor's formula with the remainder as an averaged derivative.** A `C^(n + 1)` function is
its Taylor polynomial of order `n` at `x` plus the Taylor remainder factor evaluated on `n + 1`
copies of the increment. -/
theorem ContDiff.eq_sum_add_taylorRemainderFactor_apply [CompleteSpace F] {f : E → F} {n : ℕ}
    (hf : ContDiff ℝ (n + 1) f) (x y : E) :
    f y = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ y - x) +
      taylorRemainderFactor n f x y (fun _ ↦ y - x) := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := n) (x := x) (y := y - x)
    (fun _ _ ↦ hf.contDiffAt)
  rw [add_sub_cancel] at h
  rw [h, taylorRemainderFactor, smul_apply]
  congr 2
  have hcont : Continuous fun t : ℝ ↦
      (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • (y - x)) :=
    (by fun_prop : Continuous fun t : ℝ ↦ (1 - t) ^ n).smul
      ((hf.continuous_iteratedFDeriv le_rfl).comp (by fun_prop))
  have hApply := ContinuousLinearMap.segmentAverage_apply
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) ↦ E) F fun _ ↦ y - x)
    (fun t ↦ (1 - t) ^ n) (iteratedFDeriv ℝ (n + 1) f) x (y - x) (hcont.intervalIntegrable 0 1)
  simpa using hApply.symm
