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

The same weighted segment averages give the integral remainder of the Taylor expansion of every
order: `TauCeti.taylorRemainderFactor n f x y` is a continuous multilinear map in `n + 1`
variables, depending smoothly on `y`, which evaluated on `n + 1` copies of `y - x` is the
difference between `f y` and the order-`n` Taylor polynomial of `f` at `x`. When the derivatives
of `f` of order at most `n` vanish at `x`, this writes `f` as a smooth multilinear function of
`n + 1` copies of the displacement, the higher-order Hadamard lemma.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff Nat unitInterval

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
    isOpen_univ (fun _ _ _ ↦ Set.mem_univ _)).congr fun v _ ↦ ?_
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

/-- The integral remainder of the order-`n` Taylor expansion of `f` at `x`, as a function of the
endpoint `y`: the weighted average `(n!)⁻¹ ∫₀¹ (1 - t) ^ n D^(n+1) f (x + t (y - x)) dt` of the
`(n + 1)`-st iterated derivative of `f` along the segment from `x` to `y`. Evaluated on `n + 1`
copies of `y - x`, it is the difference between `f y` and the order-`n` Taylor polynomial of `f`
at `x` (`ContDiff.eq_sum_add_taylorRemainderFactor_apply`). For `n = 0` it is `hadamardFactor`,
seen as a multilinear map in one variable. -/
noncomputable def taylorRemainderFactor (n : ℕ) (f : E → F) (x y : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) F :=
  segmentAverage (fun t ↦ (n ! : ℝ)⁻¹ * (1 - t) ^ n) (iteratedFDeriv ℝ (n + 1) f) x (y - x)

/-- At the basepoint, the order-`n` Taylor remainder factor is `((n + 1)!)⁻¹` times the
`(n + 1)`-st iterated derivative. -/
@[simp]
theorem taylorRemainderFactor_self [CompleteSpace F] (n : ℕ) (f : E → F) (x : E) :
    taylorRemainderFactor n f x x = ((n + 1)! : ℝ)⁻¹ • iteratedFDeriv ℝ (n + 1) f x := by
  have hw : ∫ t in (0 : ℝ)..1, (n ! : ℝ)⁻¹ * (1 - t) ^ n = ((n + 1)! : ℝ)⁻¹ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
      (fun t : ℝ ↦ t ^ n), integral_pow]
    simp [Nat.factorial_succ, mul_comm]
  rw [taylorRemainderFactor, sub_self, segmentAverage_zero, hw]

/-- If `f` is `C^(m + n + 1)`, the order-`n` Taylor remainder factor of `f` at `x` is `C^m` in the
endpoint. -/
theorem _root_.ContDiff.contDiff_taylorRemainderFactor {m : ℕ∞} {n : ℕ} {f : E → F}
    (hf : ContDiff ℝ (m + (n + 1 : ℕ)) f) (x : E) :
    ContDiff ℝ m (taylorRemainderFactor n f x) := by
  have hd : ContDiff ℝ m (iteratedFDeriv ℝ (n + 1) f) := hf.iteratedFDeriv_right le_rfl
  exact (hd.contDiff_segmentAverage (Continuous.intervalIntegrable (by fun_prop) _ _) x).comp
    (by fun_prop)

/-- **Taylor's formula with integral remainder**, with the remainder written through the smooth
multilinear factor `taylorRemainderFactor n f x y` evaluated on `n + 1` copies of `y - x`. -/
theorem _root_.ContDiff.eq_sum_add_taylorRemainderFactor_apply [CompleteSpace F] {n : ℕ}
    {f : E → F} (hf : ContDiff ℝ (n + 1) f) (x y : E) :
    f y = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ y - x) +
      taylorRemainderFactor n f x y (fun _ ↦ y - x) := by
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := n) (x := x) (y := y - x)
    (fun _ _ ↦ hf.contDiffAt)
  have hint : IntervalIntegrable (fun t : ℝ ↦ ((n ! : ℝ)⁻¹ * (1 - t) ^ n) •
      iteratedFDeriv ℝ (n + 1) f (x + t • (y - x))) volume 0 1 :=
    Continuous.intervalIntegrable ((by fun_prop : Continuous fun t : ℝ ↦
      (n ! : ℝ)⁻¹ * (1 - t) ^ n).smul
      ((hf.continuous_iteratedFDeriv le_rfl).comp (by fun_prop))) _ _
  -- Evaluation on `n + 1` copies of `y - x` commutes with the integral.
  have happ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) ↦ E) F
      (fun _ ↦ y - x)).intervalIntegral_comp_comm hint
  simp only [ContinuousMultilinearMap.apply_apply] at happ
  rw [add_sub_cancel] at hT
  rw [hT, taylorRemainderFactor, segmentAverage, ← happ]
  simp only [smul_apply, mul_smul, intervalIntegral.integral_smul]

end TauCeti
