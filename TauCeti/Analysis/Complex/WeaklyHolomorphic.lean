/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
public import TauCeti.MeasureTheory.Integral.CircleIntegral

/-!
# Weakly holomorphic functions are holomorphic

Let `E` be a complex Banach space, `U ⊆ ℂ` open and `f : ℂ → E`. If `z ↦ ℓ (f z)` is complex
differentiable on `U` for every continuous linear functional `ℓ` on `E`, then `f` itself is
complex differentiable on `U`. This lets holomorphy of vector-valued functions, such as resolvents
and other operator-valued functions, be checked one scalar functional at a time.

The proof has three steps.

* On a compact subset of `U` every scalar function `z ↦ ℓ (f z)` is bounded, so the uniform
  boundedness principle (`TauCeti.NormedSpace.isBounded_iff_forall_dual_isBounded`) bounds the
  norm of `f` there.
* The scalar Cauchy estimate for the derivative of `z ↦ ℓ (f z)` and the mean value inequality
  give a Lipschitz estimate for each `ℓ ∘ f` with constant proportional to `‖ℓ‖`. By Hahn–Banach
  (`NormedSpace.norm_le_dual_bound`) this is a Lipschitz estimate for `f` itself, so `f` is
  continuous on `U`.
* Being continuous, `f` has a Banach-valued Cauchy integral over every small circle in `U`, and
  this integral is analytic inside the circle. Continuous linear functionals commute with circle
  integrals (`ContinuousLinearMap.circleIntegral_comp_comm`), so the scalar Cauchy integral formula
  shows that every functional takes the same value on `f` and on its Cauchy integral. These
  functionals separate points, so `f` agrees with its Cauchy integral near each point of `U`.

Completeness of `E` is used only in the last step, where the vector-valued integral is formed.

## Main results

* `TauCeti.continuousOn_of_forall_dual`: weak holomorphy on an open set implies continuity, even
  when `E` is not complete.
* `TauCeti.differentiableOn_of_forall_dual`: weak holomorphy on an open set implies holomorphy.
* `TauCeti.differentiableOn_iff_forall_dual`, `TauCeti.differentiable_iff_forall_dual`: the
  equivalence of holomorphy and weak holomorphy.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Theorem 3.31.
-/

public section

open Complex Metric Set

open scoped Real NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace TauCeti

variable {f : ℂ → E} {U : Set ℂ}

/-- A weakly holomorphic function bounded by `M` on `closedBall c (2 * r)` is Lipschitz with
constant `M / r` on `ball c r`. -/
private theorem norm_sub_le_of_forall_dual {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z ↦ ℓ (f z)) (closedBall c (2 * r)))
    (hM : ∀ z ∈ closedBall c (2 * r), ‖f z‖ ≤ M) {z w : ℂ} (hz : z ∈ ball c r)
    (hw : w ∈ ball c r) : ‖f z - f w‖ ≤ M / r * ‖z - w‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_closedBall_self (by positivity)))
  have hball : ball c r ⊆ ball c (2 * r) := ball_subset_ball (by linarith)
  refine NormedSpace.norm_le_dual_bound ℂ _ (by positivity) fun ℓ ↦ ?_
  -- The Cauchy estimate on `ball x r ⊆ ball c (2 * r)` bounds the derivative of `ℓ ∘ f`.
  have hderiv : ∀ x ∈ ball c r, ‖deriv (fun z ↦ ℓ (f z)) x‖ ≤ ‖ℓ‖ * M / r := fun x hx ↦
    norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le (hf ℓ) hr Subset.rfl
      (fun y hy ↦ (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM y hy) (norm_nonneg ℓ))) hx
  have hdiff : ∀ x ∈ ball c r, DifferentiableAt ℂ (fun z ↦ ℓ (f z)) x := fun x hx ↦
    (hf ℓ).differentiableAt <|
      Filter.mem_of_superset (isOpen_ball.mem_nhds (hball hx)) ball_subset_closedBall
  have := (convex_ball c r).norm_image_sub_le_of_norm_deriv_le hdiff hderiv hw hz
  rw [map_sub]
  calc ‖ℓ (f z) - ℓ (f w)‖ ≤ ‖ℓ‖ * M / r * ‖z - w‖ := this
    _ = M / r * ‖z - w‖ * ‖ℓ‖ := by ring

/-- A weakly holomorphic function on an open set is continuous there. This needs no completeness
of `E`. -/
theorem continuousOn_of_forall_dual
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z ↦ ℓ (f z)) U) (hU : IsOpen U) :
    ContinuousOn f U := by
  intro c hc
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU c hc
  have hr : 0 < ε / 3 := by positivity
  have hsub : closedBall c (2 * (ε / 3)) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  -- By uniform boundedness, `f` is norm bounded on the compact ball `closedBall c (2 * (ε / 3))`.
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ closedBall c (2 * (ε / 3)), ‖f z‖ ≤ M := by
    have hbdd : Bornology.IsBounded (f '' closedBall c (2 * (ε / 3))) := by
      refine (NormedSpace.isBounded_iff_forall_dual_isBounded ℂ).2 fun ℓ ↦ ?_
      rw [image_image]
      exact ((isCompact_closedBall c _).image_of_continuousOn
        ((hf ℓ).continuousOn.mono hsub)).isBounded
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hbdd
    exact ⟨M, fun z hz ↦ hM _ (mem_image_of_mem f hz)⟩
  have hLip : LipschitzOnWith (M / (ε / 3)).toNNReal f (ball c (ε / 3)) :=
    LipschitzOnWith.of_dist_le' fun z hz w hw ↦ by
      simpa only [dist_eq_norm] using
        norm_sub_le_of_forall_dual hr (fun ℓ ↦ (hf ℓ).mono hsub) hM hz hw
  exact (hLip.continuousOn.continuousAt
    (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousWithinAt

/-- **Weak holomorphy implies holomorphy.** If `E` is a complex Banach space and
`z ↦ ℓ (f z)` is complex differentiable on the open set `U` for every continuous linear
functional `ℓ` on `E`, then `f` is complex differentiable on `U`. -/
theorem differentiableOn_of_forall_dual [CompleteSpace E]
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z ↦ ℓ (f z)) U) (hU : IsOpen U) :
    DifferentiableOn ℂ f U := by
  have hcont := continuousOn_of_forall_dual hf hU
  intro c hc
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU c hc
  obtain ⟨R, hR, hRε⟩ : ∃ R : ℝ≥0, 0 < R ∧ (R : ℝ) < ε :=
    ⟨(ε / 2).toNNReal, by simpa using hε, by rw [Real.coe_toNNReal _ (by positivity)]; linarith⟩
  have hRU : closedBall c R ⊆ U := (closedBall_subset_ball hRε).trans hεU
  have hsphere : sphere c R ⊆ U := sphere_subset_closedBall.trans hRU
  -- On `ball c R`, `f` agrees with its Banach-valued Cauchy integral, because every continuous
  -- linear functional does by the scalar Cauchy integral formula.
  have heq : ∀ z ∈ ball c R,
      (2 * π * I : ℂ)⁻¹ • ∮ w in C(c, R), (w - z)⁻¹ • f w = f z := by
    intro z hz
    have hne : ∀ w ∈ sphere c (R : ℝ), w - z ≠ 0 := fun w hw ↦
      sub_ne_zero.2 fun h ↦ (mem_ball.1 hz).ne (h ▸ mem_sphere.1 hw)
    have hint : CircleIntegrable (fun w ↦ (w - z)⁻¹ • f w) c R :=
      (((continuousOn_id.sub continuousOn_const).inv₀ hne).smul
        (hcont.mono hsphere)).circleIntegrable R.coe_nonneg
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_
    rw [map_smul, ← ℓ.circleIntegral_comp_comm hint]
    simp only [map_smul]
    exact ((hf ℓ).mono (closure_ball c (NNReal.coe_ne_zero.2 hR.ne') ▸ hRU)).diffContOnCl
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz
  have hps := hasFPowerSeriesOn_cauchy_integral
    ((hcont.mono hsphere).circleIntegrable R.coe_nonneg) hR
  refine (hps.analyticAt.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (NNReal.coe_pos.2 hR))] with z hz
  exact (heq z hz).symm

/-- A function into a complex Banach space is complex differentiable on an open set if and only if
it is weakly so: its composite with every continuous linear functional is complex
differentiable there. -/
theorem differentiableOn_iff_forall_dual [CompleteSpace E] (hU : IsOpen U) :
    DifferentiableOn ℂ f U ↔ ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z ↦ ℓ (f z)) U :=
  ⟨fun h ℓ ↦ ℓ.differentiable.comp_differentiableOn h,
    fun h ↦ differentiableOn_of_forall_dual h hU⟩

/-- A function into a complex Banach space is entire if and only if its composite with every
continuous linear functional is entire. -/
theorem differentiable_iff_forall_dual [CompleteSpace E] :
    Differentiable ℂ f ↔ ∀ ℓ : StrongDual ℂ E, Differentiable ℂ fun z ↦ ℓ (f z) := by
  rw [← differentiableOn_univ, differentiableOn_iff_forall_dual isOpen_univ]
  simp only [differentiableOn_univ]

end TauCeti
