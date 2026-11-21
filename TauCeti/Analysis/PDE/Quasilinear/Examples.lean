/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem.Interval
public import TauCeti.Analysis.PDE.Quasilinear.Interval

/-!
# An example: the quasilinear coefficient `1 + u² / (1 + u²)` on an interval

The coefficient `A(y) = 1 + y² / (1 + y²)` lies between `1` and `2`. For `f = 1` on `(0, 1)` with
zero boundary values, the decay bound
`TauCeti.PDE.abs_intervalRepresentativeL_sub_le_min_mul_div_of_forall_setIntegral_eq` gives a
solution with `|ū y| ≤ min y (1 - y) ≤ 1 / 2`
(`TauCeti.PDE.exists_intervalTraceL_eq_zero_and_forall_setIntegral_one_add_sq_div_and_abs_le_min`),
and the same bound shows that the frozen-coefficient map sends all of `C([0, 1])` into the closed
ball of radius `1 / 2` (`TauCeti.PDE.norm_intervalDirichletSolution_one_add_sq_div_le`).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Distributions

namespace TauCeti.PDE

variable {p : ENNReal} [Fact (1 ≤ p)]

/-- The coefficient `1 + y² / (1 + y²)` lies between `1` and `2`. -/
private theorem one_le_one_add_sq_div_and_le_two (y : ℝ) :
    1 ≤ 1 + y ^ 2 / (1 + y ^ 2) ∧ 1 + y ^ 2 / (1 + y ^ 2) ≤ 2 := by
  have h : 0 < 1 + y ^ 2 := by positivity
  refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
  have : y ^ 2 / (1 + y ^ 2) ≤ 1 := (div_le_one h).2 (by linarith)
  linarith

/-- The data `f = 1`, `F = 0` on `(0, 1)` give `G t = ∫_0^t 1 + 0 = t`. -/
private theorem intervalIntegral_one_add_zero :
    (fun t : ℝ => (∫ _ in (0 : ℝ)..t, (1 : ℝ)) + 0) = fun t => t := by
  ext t
  simp

/-- For the data `f = 1`, `F = 0`, the function `G t = ∫_0^t 1 + 0 = t` lies in `[0, 1]` on
`(0, 1)`. -/
private theorem ae_intervalIntegral_one_add_zero_mem_Icc :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      0 ≤ (∫ _ in (0 : ℝ)..t, (1 : ℝ)) + 0 ∧ (∫ _ in (0 : ℝ)..t, (1 : ℝ)) + 0 ≤ 0 + 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [congrFun intervalIntegral_one_add_zero t]
  exact ⟨ht.1.le, by linarith [ht.2]⟩

/-- **The quasilinear problem `-((1 + u² / (1 + u²)) u')' = 1` on `(0, 1)`.** Its coefficient
`1 + y² / (1 + y²)` lies between `1` and `2`, so the problem with zero boundary values
`u(0) = u(1) = 0` has a solution `u ∈ W^{1,p}(0, 1)`. Its continuous representative `ū` satisfies
`|ū y| ≤ min y (1 - y)`, in particular `|ū| ≤ 1 / 2`; by
`abs_intervalRepresentativeL_sub_le_min_mul_div_of_forall_setIntegral_eq` the same bound holds
for every solution. -/
theorem exists_intervalTraceL_eq_zero_and_forall_setIntegral_one_add_sq_div_and_abs_le_min :
    ∃ u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p,
      W1p.intervalTraceL zero_lt_one u = (0, 0) ∧
      (∀ φ : 𝓓(⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo (0 : ℝ) 1,
            (1 + W1p.intervalRepresentativeL zero_lt_one u (projIcc 0 1 zero_le_one t) ^ 2 /
              (1 + W1p.intervalRepresentativeL zero_lt_one u (projIcc 0 1 zero_le_one t) ^ 2)) *
              W1p.gradient u t * deriv φ t =
          ∫ t in Ioo (0 : ℝ) 1, φ t) ∧
      ∀ y : Icc (0 : ℝ) 1,
        |W1p.intervalRepresentativeL zero_lt_one u y| ≤ min (y : ℝ) (1 - y) := by
  set A : ℝ → ℝ → ℝ := fun _ y => 1 + y ^ 2 / (1 + y ^ 2)
  have hAm : ∀ y, AEStronglyMeasurable (fun t => A t y) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun _ => aestronglyMeasurable_const
  have hAc : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), Continuous (A t) :=
    ae_of_all _ fun _ => continuous_const.add <| (continuous_pow 2).div
      (continuous_const.add (continuous_pow 2)) fun y => by positivity
  have hA : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ y, 1 ≤ A t y ∧ A t y ≤ 2 :=
    ae_of_all _ fun _ => one_le_one_add_sq_div_and_le_two
  have hf : IntegrableOn (fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    integrableOn_const measure_Ioo_lt_top.ne
  obtain ⟨u, htr, hu⟩ := exists_intervalTraceL_eq_and_forall_setIntegral_eq (p := p) zero_lt_one
    one_pos hAm hAc hA hf (MemLp.zero' (p := p)) 0 0
  refine ⟨u, htr, fun φ => by simpa using hu φ, fun y => ?_⟩
  simpa using abs_intervalRepresentativeL_sub_le_min_mul_div_of_forall_setIntegral_eq
    zero_lt_one one_pos hAm hAc hA hf integrableOn_zero hu htr
    ae_intervalIntegral_one_add_zero_mem_Icc y

/-- **The frozen-coefficient map of the example preserves the ball of radius `1 / 2`.** For every
`v ∈ C([0, 1])`, the explicit solution of the linear problem `-((1 + v² / (1 + v²)) u')' = 1`,
`u(0) = u(1) = 0`, has supremum norm at most `1 / 2`. So the frozen-coefficient map
`v ↦ intervalDirichletSolution` sends `C([0, 1])` into the closed ball of radius `1 / 2`, to which
Schauder's theorem applies. -/
theorem norm_intervalDirichletSolution_one_add_sq_div_le (v : C(Icc (0 : ℝ) 1, ℝ))
    (hs : IntegrableOn (intervalDirichletSlope 0 1 0 0 (fun t => t) fun t =>
      1 + v (projIcc 0 1 zero_le_one t) ^ 2 / (1 + v (projIcc 0 1 zero_le_one t) ^ 2))
      (Ioo 0 1)) :
    ‖intervalDirichletSolution zero_le_one 0 0 hs‖ ≤ 1 / 2 := by
  have hv : Continuous fun t : ℝ => v (projIcc 0 1 zero_le_one t) :=
    v.continuous.comp continuous_projIcc
  have ha : Continuous fun t : ℝ =>
      1 + v (projIcc 0 1 zero_le_one t) ^ 2 / (1 + v (projIcc 0 1 zero_le_one t) ^ 2) :=
    continuous_const.add ((hv.pow 2).div (continuous_const.add (hv.pow 2)) fun t => by positivity)
  -- The decay bound is stated for `G t = ∫_0^t 1 + 0`; rewrite the solution to that form of `G`.
  obtain ⟨hs', hsol⟩ : ∃ hs' : IntegrableOn
      (intervalDirichletSlope 0 1 0 0 (fun t => (∫ _ in (0 : ℝ)..t, (1 : ℝ)) + 0) fun t =>
        1 + v (projIcc 0 1 zero_le_one t) ^ 2 / (1 + v (projIcc 0 1 zero_le_one t) ^ 2))
      (Ioo 0 1),
      intervalDirichletSolution zero_le_one 0 0 hs =
        intervalDirichletSolution zero_le_one 0 0 hs' := by
    rw [intervalIntegral_one_add_zero]
    exact ⟨hs, rfl⟩
  refine (ContinuousMap.norm_le _ (by norm_num)).2 fun y => ?_
  have h := abs_intervalDirichletSolution_sub_le_min_mul_div zero_lt_one one_pos
    ha.aestronglyMeasurable (ae_of_all _ fun t => one_le_one_add_sq_div_and_le_two _)
    (integrableOn_const (C := (1 : ℝ)) measure_Ioo_lt_top.ne) integrableOn_zero 0
    ae_intervalIntegral_one_add_zero_mem_Icc hs' y
  rw [← hsol] at h
  simp only [sub_zero, mul_one, div_one] at h
  have hmin : min (y : ℝ) (1 - y) ≤ 1 / 2 := by
    rcases le_or_gt (y : ℝ) (1 / 2) with hy | hy
    · exact (min_le_left _ _).trans hy
    · exact (min_le_right _ _).trans (by linarith)
  rw [Real.norm_eq_abs]
  exact h.trans hmin

end TauCeti.PDE
