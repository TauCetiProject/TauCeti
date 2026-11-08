/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Local
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Local invariant graphs for differentiable vector fields

At a zero `x` of a finite-dimensional `C^n` vector field `V`, suppose its derivative `A`
admits an exponential dichotomy with commuting stable projection `P`. Confined forward
solutions in displacement coordinates, restricted to a small stable parameter window, form a
`C^n` graph over `range P`; confined backward solutions, restricted to a small unstable
parameter window, form a `C^n` graph over `range (1 - P)`. Both graphs are tangent to their
linear subspaces at the origin. No inner product, symmetry of `A`, gradient representation,
or completeness of the nonlinear flow is required.

The radii of confinement and of the graph domain are chosen from local regularity of `V`.
The graph descriptions include every confined solution whose initial stable or unstable
coordinate lies in the respective parameter window, not just the solutions constructed by
the fixed-point argument. Each confined solution tends to the equilibrium in the
appropriate time direction. These are local graph theorems, not assertions that global
stable sets are embedded or that graphs depend differentiably on a vector-field parameter.

The construction uses the cutoff graphs of
`ContinuousLinearMap.localStableGraphMap` and `ContinuousLinearMap.localUnstableGraphMap`.
It applies their small-nonlinearity estimates to `V (x + z) - A z`, whose derivative at zero
vanishes. This is the vector-field form of the localization argument used for gradients in
`TauCeti.Analysis.Calculus.Morse.LocalInvariantManifold`.

## References

* C. Chicone, *Ordinary Differential Equations with Applications*, second edition,
  Springer, 2006, §4.3 (the stable-manifold theorem).
* W. A. Coppel, *Dichotomies in Stability Theory*, Springer, 1978, Chapter 5
  (the Lyapunov–Perron construction).
-/

public section

open Filter Metric Set Topology
open scoped NNReal

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : E → E} {x : E} {n : ℕ} {A : E →L[ℝ] E} {K α : ℝ≥0}

/-- Local regularity makes the nonlinear remainder small on a ball and uniformly smooth
there; the smaller graph-parameter ball stays strictly inside that ball. -/
private theorem exists_vectorField_remainder_data (hn : 1 ≤ n) (hV : ContDiffAt ℝ n V x)
    (hA : HasFDerivAt V A x) (hα : 0 < α) :
    ∃ ε : ℝ≥0, ∃ r > 0, ∃ ρ > 0,
      LipschitzOnWith ε (fun z ↦ V (x + z) - A z) (closedBall 0 r) ∧
      HasFDerivAt (fun z ↦ V (x + z) - A z) (0 : E →L[ℝ] E) 0 ∧
      2 * K * (ε * 2) < α ∧
      UniformContDiffOn ℝ n (fun z ↦ V (x + z) - A z) (ball 0 r) ∧
      (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r ∧
      (∀ z ∈ closedBall (0 : E) ρ,
        (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ‖z‖ < r) := by
  let N : E → E := fun z ↦ V (x + z) - A z
  have hN : ContDiffAt ℝ n N 0 := by
    have hVx : ContDiffAt ℝ n V (x + 0) := by simpa using hV
    exact (hVx.comp 0 (contDiffAt_const.add contDiffAt_id)).sub A.contDiff.contDiffAt
  have hVx : HasFDerivAt (fun z ↦ V (x + z)) A 0 := by
    rw [hasFDerivAt_comp_add_left]
    simpa using hA
  have hN' : HasFDerivAt N (0 : E →L[ℝ] E) 0 := by
    simpa only [N, Pi.sub_def, sub_self] using hVx.sub A.hasFDerivAt
  let ε : ℝ≥0 := α / (8 * (K + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : 2 * K * (ε * 2) < α := by
    have hαR : (0 : ℝ) < α := hα
    apply NNReal.coe_lt_coe.1
    dsimp [ε]
    rw [div_mul_eq_mul_div, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg α.coe_nonneg K.coe_nonneg]
  have hN1 : ContDiffAt ℝ 1 N 0 := hN.of_le (by exact_mod_cast hn)
  obtain ⟨s, hs, hNs⟩ := (hN1.hasStrictFDerivAt hN' one_ne_zero).exists_lipschitzOnWith_of_nnnorm_lt
    ε (by simpa using hε)
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨r₂, hr₂, hNn⟩ := hN.exists_uniformContDiffOn_closedBall
  let r := min (r₁ / 2) r₂
  have hr : 0 < r := lt_min (by positivity) hr₂
  have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
  have hbound : 0 ≤ (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) :=
    div_nonneg K.coe_nonneg (by have := (div_lt_one (show (0 : ℝ) < α from hα)).2 hsmallR; linarith)
  obtain ⟨ρ, hρ, hρr⟩ := exists_pos_mul_lt hr
    ((K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α))
  refine ⟨ε, r, hr, ρ, hρ, hNs.mono ?_, hN', hsmall, hNn.mono ?_, hρr, ?_⟩
  · exact (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hr₁s
  · exact ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_right _ _))
  · intro z hz
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hz) hbound).trans_lt hρr

end TauCeti

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (A P : E →L[ℝ] E) {V : E → E} {x : E} {n : ℕ} {K α : ℝ≥0}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ z : E,
    ‖NormedSpace.exp (t • A) (P z)‖ ≤ K * Real.exp (-α * t) * ‖z‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ z : E,
    ‖NormedSpace.exp (t • A) (z - P z)‖ ≤ K * Real.exp (α * t) * ‖z‖)
  (hα : 0 < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
  (hn : 1 ≤ n) (hV : ContDiffAt ℝ n V x) (hx : V x = 0) (hA : HasFDerivAt V A x)

include hs hu hα hP hAP hn hV hx hA

/-- **Local stable graph for a `C^n` vector field.** At an equilibrium whose derivative has
an exponential dichotomy, all forward solutions confined to a sufficiently small ball,
truncated in the stable coordinate, form a Lipschitz `C^n` graph tangent to `range P`.
Every forward solution confined to that ball tends to the equilibrium. -/
theorem exists_localStableGraph_of_contDiffAt :
    ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ C : ℝ≥0,
      LipschitzWith C g ∧ g 0 = 0 ∧ HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ n g z) ∧
      (∀ z, P (g z) = 0) ∧ (∀ z, g (P z) = g z) ∧
      {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) ∧
        y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range P ∩ closedBall 0 ρ) ∧
      (∀ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) →
        MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (𝓝 0)) := by
  obtain ⟨ε, r, hr, ρ, hρ, hN, hN', hsmall, hNn, hρbound, hball⟩ :=
    TauCeti.exists_vectorField_remainder_data (K := K) hn hV hA hα
  let N : E → E := fun z ↦ V (x + z) - A z
  have hN0 : N 0 = 0 := by simp [N, hx]
  have hfield : (fun (_ : ℝ) z ↦ A z + N z) = fun (_ : ℝ) z ↦ V (x + z) := by
    funext t z
    simp [N]
  let g := localStableGraphMap A P N r hs hu hr.le hN hsmall
  refine ⟨r, hr, ρ, hρ, g, _, lipschitzWith_localStableGraphMap hs hu hr.le hN hsmall,
    localStableGraphMap_zero hs hu hr.le hN hsmall hN0,
    hasFDerivAt_localStableGraphMap_zero hs hu hr.le hN hsmall hr hN0 hN',
    fun z hz ↦ contDiffAt_localStableGraphMap_of_uniformContDiffOn hs hu hr.le hN hsmall
      hN0 hNn (hball z hz),
    apply_localStableGraphMap hs hu hr.le hN hsmall hP hAP,
    localStableGraphMap_map hs hu hr.le hN hsmall hP, ?_, ?_⟩
  · have hset := setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hr.le hN
      hsmall hN0 hP hAP hρbound.le
    rwa [hfield] at hset
  · intro y hy hmaps
    exact tendsto_of_isIntegralCurveOn_mapsTo_closedBall hs hu hr.le hN hsmall hN0 hP hAP
      (hfield ▸ hy) hmaps

/-- **Local unstable graph for a `C^n` vector field.** At the same equilibrium as in the
stable graph theorem, backward solutions confined to a sufficiently small ball, truncated
in the unstable coordinate, form a Lipschitz `C^n` graph tangent to `range (1 - P)`.
Every backward solution confined to that ball tends to the equilibrium as time tends to
negative infinity. -/
theorem exists_localUnstableGraph_of_contDiffAt :
    ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ C : ℝ≥0,
      LipschitzWith C g ∧ g 0 = 0 ∧ HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ n g z) ∧
      (∀ z, (ContinuousLinearMap.id ℝ E - P) (g z) = 0) ∧
      (∀ z, g ((ContinuousLinearMap.id ℝ E - P) z) = g z) ∧
      {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Iic 0) ∧
        y 0 = z ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧ ‖z - P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range (ContinuousLinearMap.id ℝ E - P) ∩ closedBall 0 ρ) ∧
      (∀ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Iic 0) →
        MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (𝓝 0)) := by
  obtain ⟨ε, r, hr, ρ, hρ, hN, hN', hsmall, hNn, hρbound, hball⟩ :=
    TauCeti.exists_vectorField_remainder_data (K := K) hn hV hA hα
  let N : E → E := fun z ↦ V (x + z) - A z
  have hN0 : N 0 = 0 := by simp [N, hx]
  have hfield : (fun (_ : ℝ) z ↦ A z + N z) = fun (_ : ℝ) z ↦ V (x + z) := by
    funext t z
    simp [N]
  let g := localUnstableGraphMap A P N r hs hu hr.le hN hsmall
  refine ⟨r, hr, ρ, hρ, g, _, lipschitzWith_localUnstableGraphMap hs hu hr.le hN hsmall,
    localUnstableGraphMap_zero hs hu hr.le hN hsmall hN0,
    hasFDerivAt_localUnstableGraphMap_zero hs hu hr.le hN hsmall hr hN0 hN',
    fun z hz ↦ contDiffAt_localUnstableGraphMap_of_uniformContDiffOn hs hu hr.le hN hsmall
      hN0 hNn (hball z hz), ?_,
    localUnstableGraphMap_sub_map hs hu hr.le hN hsmall hP, ?_, ?_⟩
  · intro z
    simp only [sub_apply, id_apply, sub_eq_zero]
    exact (apply_localUnstableGraphMap hs hu hr.le hN hsmall hP hAP z).symm
  · have hset := setOf_exists_isIntegralCurveOn_Iic_mapsTo_closedBall_eq_image hs hu hr.le hN
      hsmall hN0 hP hAP hρbound.le
    rwa [hfield] at hset
  · intro y hy hmaps
    exact tendsto_atBot_of_isIntegralCurveOn_mapsTo_closedBall hs hu hr.le hN hsmall hN0 hP hAP
      (hfield ▸ hy) hmaps

end ContinuousLinearMap
