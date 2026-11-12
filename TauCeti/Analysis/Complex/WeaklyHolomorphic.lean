/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
public import TauCeti.MeasureTheory.Integral.Circle.Integral

/-!
# Weakly holomorphic functions are holomorphic

Let `E` be a complex Banach space, `U ⊆ ℂ` open and `f : ℂ → E`. If `z ↦ ℓ (f z)` is complex
differentiable on `U` for every continuous linear functional `ℓ` on `E`, then `f` itself is
complex differentiable on `U`. This lets holomorphy of vector-valued functions, such as resolvents
and other operator-valued functions, be checked one scalar functional at a time.

The proof has two steps.

* Weak differentiability gives continuity, on any set `U`. Along a sequence `zₙ → c` in `U` the
  difference quotients of `f` at `c` are bounded after applying any functional, so the uniform
  boundedness principle (`TauCeti.NormedSpace.isBounded_iff_forall_dual_isBounded`) bounds their
  norms, which makes `f` continuous at `c`.
* For `U` open, being continuous, `f` has a Banach-valued Cauchy integral over every small circle
  in `U`, and this integral is analytic inside the circle. Continuous linear functionals commute
  with circle integrals (`ContinuousLinearMap.circleIntegral_comp_comm`), so the scalar Cauchy
  integral formula shows that every functional takes the same value on `f` and on its Cauchy
  integral. These functionals separate points, so `f` agrees with its Cauchy integral near each
  point of `U`.

Completeness of `E` is used only in the last step, where the vector-valued integral is formed.

## Main results

* `TauCeti.continuousWithinAt_of_forall_dual`: weak differentiability within a set at a point
  implies continuity within the set at that point.
* `TauCeti.continuousOn_of_forall_dual`: weak differentiability on any set implies continuity,
  even when `E` is not complete.
* `TauCeti.differentiableOn_of_forall_dual`: weak holomorphy on an open set implies holomorphy.
* `TauCeti.differentiableOn_iff_forall_dual`, `TauCeti.differentiable_iff_forall_dual`: the
  equivalence of holomorphy and weak holomorphy.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Theorem 3.31.
-/

public section

open Complex Metric Set Filter Topology

open scoped Real NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace TauCeti

variable {f : ℂ → E} {U : Set ℂ}

/-- A function that is weakly differentiable within `U` at `c` is continuous within `U` at `c`.
This needs neither openness of `U` nor completeness of `E`. -/
theorem continuousWithinAt_of_forall_dual {c : ℂ}
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableWithinAt ℂ (fun z ↦ ℓ (f z)) U c) :
    ContinuousWithinAt f U c := by
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro z hz
  -- The difference quotients `w n` are weakly bounded, hence norm bounded by uniform boundedness.
  set w : ℕ → E := fun n ↦ ((‖z n - c‖ : ℂ))⁻¹ • (f (z n) - f c)
  have hzc : Tendsto (fun n ↦ ‖z n - c‖) atTop (𝓝 0) := by
    have h1 : Tendsto z atTop (𝓝 c) := (tendsto_nhdsWithin_iff.1 hz).1
    simpa using (h1.sub_const c).norm
  have hbdd : Bornology.IsBounded (range w) := by
    refine (NormedSpace.isBounded_iff_forall_dual_isBounded ℂ).2 fun ℓ ↦ ?_
    obtain ⟨C, hC⟩ := (hf ℓ).isBigO_sub.bound
    have hev : ∀ᶠ n in atTop, ‖ℓ (w n)‖ ≤ max C 0 := by
      filter_upwards [hz.eventually hC] with n hn
      simp only [w, map_smul, map_sub]
      rcases eq_or_ne (z n) c with h | h
      · simp [h]
      · have hpos : 0 < ‖z n - c‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
        rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_le_iff₀ hpos, mul_comm]
        exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
    obtain ⟨B, hB⟩ := (IsBoundedUnder.bddAbove_range (f := fun n ↦ ‖ℓ (w n)‖) ⟨max C 0, hev⟩)
    refine isBounded_iff_forall_norm_le.2 ⟨B, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact hB ⟨n, rfl⟩
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hbdd
  have key : ∀ n, ‖f (z n) - f c‖ ≤ M * ‖z n - c‖ := fun n ↦ by
    rcases eq_or_ne (z n) c with h | h
    · simp [h]
    · have hpos : 0 < ‖z n - c‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
      have := hM _ ⟨n, rfl⟩
      simp only [w, norm_smul, norm_inv, Complex.norm_real, norm_norm] at this
      rwa [inv_mul_le_iff₀ hpos, mul_comm] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) key ?_
  simpa using hzc.const_mul M

/-- A function that is weakly differentiable on a set `U` is continuous on `U`. This needs neither
openness of `U` nor completeness of `E`. -/
theorem continuousOn_of_forall_dual
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z ↦ ℓ (f z)) U) :
    ContinuousOn f U := fun c hc ↦ continuousWithinAt_of_forall_dual fun ℓ ↦ hf ℓ c hc

/-- **Weak holomorphy implies holomorphy.** If `E` is a complex Banach space and
`z ↦ ℓ (f z)` is complex differentiable on the open set `U` for every continuous linear
functional `ℓ` on `E`, then `f` is complex differentiable on `U`. -/
theorem differentiableOn_of_forall_dual [CompleteSpace E]
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z ↦ ℓ (f z)) U) (hU : IsOpen U) :
    DifferentiableOn ℂ f U := by
  have hcont := continuousOn_of_forall_dual hf
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
