/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.Analysis.ODE.LyapunovPerron.Graph

/-!
# The local stable set at a hyperbolic equilibrium

`TauCeti/Analysis/ODE/LyapunovPerron/Graph.lean` describes the stable set of the equilibrium `0`
of `y' = A y + N y` for a nonlinearity `N` that is **globally** Lipschitz with a constant small
compared to the spectral gap of `A`. A nonlinearity coming from a vector field with a hyperbolic
equilibrium is not of that form: it is only small near the equilibrium, where the field is close
to its linearization. This file bridges the two by **cutting the nonlinearity off** outside a
closed ball of radius `r`, using the radial retraction of
`TauCeti/Analysis/Normed/Module/Ball/Retraction.lean`.

Cutting off replaces `N` by `N ∘ radialRetraction r`, which agrees with `N` on the ball, fixes the
origin, and is globally Lipschitz with twice the constant that `N` has on the ball. Feeding it to
the Lyapunov--Perron machinery produces `ContinuousLinearMap.localStableGraphMap`, a Lipschitz map
into the kernel of `P`. Under the stated bound on `ρ`, the local stable set truncated by
`‖P x‖ ≤ ρ` is its graph over `range P ∩ closedBall 0 ρ`: these are the initial values of the
forward solutions of `y' = A y + N y` that never leave the ball of radius `r`. Confinement already
forces such a solution to tend to `0`, so the set deserves its name.

The two descriptions match exactly where the cutoff is invisible. A confined forward solution of
the original equation solves the cut-off equation as well, so it always lies on the graph; and
conversely a point of the graph whose `P`-component `v` is small enough that the uniform bound
`‖y t‖ ≤ K / (1 - 2 K ε / α) ‖v‖` on Lyapunov--Perron solutions keeps `y` inside the ball carries a
confined solution. This is the Lipschitz half of the local stable-manifold theorem; the
differentiability of the graph map and its tangency to the range of `P` are not established here.

## Main declarations

* `ContinuousLinearMap.localStableGraphMap`: the Lyapunov--Perron graph map of the cut-off
  nonlinearity, with `ContinuousLinearMap.lipschitzWith_localStableGraphMap` and
  `ContinuousLinearMap.norm_localStableGraphMap_le` for its Lipschitz constant and cone bound.
* `ContinuousLinearMap.tendsto_of_isIntegralCurveOn_mapsTo_closedBall`: a forward solution that
  never leaves the ball of radius `r` tends to the equilibrium.
* `ContinuousLinearMap.setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image`: the local
  stable set, cut down to where the `P`-component has norm at most `ρ`, is the graph of that map
  over the closed ball of radius `ρ` in the range of `P`, for every `ρ` small enough.
* `ContinuousLinearMap.exists_setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image`: such a
  `ρ` exists as soon as the ball of confinement has positive radius.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  Section 4.3.
-/

public section

open Filter Metric NormedSpace Set Topology

open scoped NNReal

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K α ε : ℝ≥0} {N : X → X} {r : ℝ}

/-- The constant `K / (1 - 2 K ε / α)` bounding a Lyapunov--Perron solution in terms of its input
parameter is nonnegative. -/
private theorem lyapunovPerronBound_nonneg (hα : 0 < α) (hsmall : 2 * K * (ε * 2) < α) :
    0 ≤ (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) := by
  have hαR : (0 : ℝ) < α := hα
  have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
  have := (div_lt_one hαR).2 hsmallR
  exact div_nonneg K.coe_nonneg (by linarith)

variable (A P : X →L[ℝ] X) (N : X → X) (r : ℝ)
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
  (hsmall : 2 * K * (ε * 2) < α)

/-- The **local stable graph map**: the Lyapunov--Perron graph map of the nonlinearity `N` cut off
outside the closed ball of radius `r`.

Under the bound on `ρ` in
`ContinuousLinearMap.setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image`, its graph over
`range P ∩ closedBall 0 ρ` is the local stable set of the equilibrium `0` of `y' = A y + N y`
truncated by `‖P x‖ ≤ ρ`. -/
def localStableGraphMap : X → X :=
  lyapunovPerronGraphMap A P (N ∘ TauCeti.radialRetraction r) hs hu hα
    (hN.comp_radialRetraction hr) hsmall

variable {A P N r}

theorem localStableGraphMap_def :
    localStableGraphMap A P N r hs hu hα hr hN hsmall =
      lyapunovPerronGraphMap A P (N ∘ TauCeti.radialRetraction r) hs hu hα
        (hN.comp_radialRetraction hr) hsmall :=
  (rfl)

/-- The local stable graph map takes values in the kernel of `P`, so its graph over the range of
`P` really is a graph. -/
@[simp]
theorem apply_localStableGraphMap (hP : IsIdempotentElem P) (hAP : Commute A P) (ξ : X) :
    P (localStableGraphMap A P N r hs hu hα hr hN hsmall ξ) = 0 :=
  apply_lyapunovPerronGraphMap hs hu hα (hN.comp_radialRetraction hr) hsmall hP hAP ξ

/-- The local stable graph map depends only on the `P`-component of its argument. -/
@[simp]
theorem localStableGraphMap_map (hP : IsIdempotentElem P) (ξ : X) :
    localStableGraphMap A P N r hs hu hα hr hN hsmall (P ξ) =
      localStableGraphMap A P N r hs hu hα hr hN hsmall ξ :=
  lyapunovPerronGraphMap_map hs hu hα (hN.comp_radialRetraction hr) hsmall hP ξ

/-- If the nonlinearity fixes the equilibrium, so does the local stable graph map. -/
@[simp]
theorem localStableGraphMap_zero (hN0 : N 0 = 0) :
    localStableGraphMap A P N r hs hu hα hr hN hsmall 0 = 0 :=
  lyapunovPerronGraphMap_zero hs hu hα (hN.comp_radialRetraction hr) hsmall (by simp [hN0])

/-- **The local stable graph map is Lipschitz**, with a constant that tends to `0` with the
Lipschitz constant of the nonlinearity on the ball of confinement. -/
theorem lipschitzWith_localStableGraphMap :
    LipschitzWith (2 * K * (ε * 2) / α * (K / (1 - 2 * K * (ε * 2) / α)))
      (localStableGraphMap A P N r hs hu hα hr hN hsmall) :=
  lipschitzWith_lyapunovPerronGraphMap hs hu hα (hN.comp_radialRetraction hr) hsmall

/-- If the nonlinearity fixes the equilibrium, the local stable set lies in a cone around the
range of `P` whose opening tends to `0` with the Lipschitz constant of the nonlinearity. -/
theorem norm_localStableGraphMap_le (hN0 : N 0 = 0) (ξ : X) :
    ‖localStableGraphMap A P N r hs hu hα hr hN hsmall ξ‖ ≤
      ((2 * K * (ε * 2) / α * (K / (1 - 2 * K * (ε * 2) / α)) : ℝ≥0) : ℝ) * ‖ξ‖ :=
  norm_lyapunovPerronGraphMap_le hs hu hα (hN.comp_radialRetraction hr) hsmall (by simp [hN0]) ξ

omit [CompleteSpace X] in
/-- **Cutting off is invisible to a confined solution.** A forward solution of `y' = A y + N y`
that never leaves the closed ball of radius `r` solves the cut-off equation as well. -/
theorem isIntegralCurveOn_comp_radialRetraction {y : ℝ → X}
    (hy : IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Ici 0))
    (hmaps : MapsTo y (Ici 0) (closedBall 0 r)) :
    IsIntegralCurveOn y (fun _ z ↦ A z + (N ∘ TauCeti.radialRetraction r) z) (Ici 0) :=
  fun t ht ↦ by
    simpa only [Function.comp_apply,
      TauCeti.radialRetraction_of_norm_le (mem_closedBall_zero_iff.1 (hmaps ht))] using hy t ht

section LocalStable

variable (hN0 : N 0 = 0) (hP : IsIdempotentElem P) (hAP : Commute A P)

include hs hu hα hr hN hsmall hN0 hP hAP

/-- **A confined forward solution tends to the equilibrium.** The ball of confinement is where the
nonlinearity is small, so a solution that never leaves it is a Lyapunov--Perron solution of the
cut-off equation, and those decay. This is what makes the set below a *stable* set. -/
theorem tendsto_of_isIntegralCurveOn_mapsTo_closedBall {y : ℝ → X}
    (hy : IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Ici 0))
    (hmaps : MapsTo y (Ici 0) (closedBall 0 r)) :
    Tendsto y atTop (𝓝 0) := by
  have hMlip : LipschitzWith (ε * 2) (N ∘ TauCeti.radialRetraction r) :=
    hN.comp_radialRetraction hr
  refine (tendsto_lyapunovPerronSolution hs hu hα hMlip hsmall (by simp [hN0]) (y 0)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (eqOn_lyapunovPerronSolution_of_isIntegralCurveOn hs hu hα hMlip hsmall hP hAP
    (isIntegralCurveOn_comp_radialRetraction hy hmaps)
    (fun u hu' ↦ mem_closedBall_zero_iff.1 (hmaps hu')) (mem_Ici.2 ht)).symm

/-- **The local stable set at a hyperbolic equilibrium is a Lipschitz graph.** The initial values
of the solutions of `y' = A y + N y` on `[0, ∞)` that never leave the closed ball of radius `r`,
restricted to those whose `P`-component has norm at most `ρ`, are exactly the points
`v + localStableGraphMap v` with `v` in the range of `P` of norm at most `ρ`. Such solutions
automatically tend to the equilibrium, by
`ContinuousLinearMap.tendsto_of_isIntegralCurveOn_mapsTo_closedBall`.

The hypothesis on `ρ` is that the uniform bound `K / (1 - 2 K ε / α)` for Lyapunov--Perron
solutions carries the ball of radius `ρ` into the ball of radius `r`; it is what makes the cutoff
invisible to the solutions concerned. -/
theorem setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image {ρ : ℝ}
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ ≤ r) :
    {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Ici 0) ∧ y 0 = x ∧
        MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P x‖ ≤ ρ} =
      (fun v ↦ v + localStableGraphMap A P N r hs hu hα hr hN hsmall v) ''
        (range P ∩ closedBall 0 ρ) := by
  have hMlip : LipschitzWith (ε * 2) (N ∘ TauCeti.radialRetraction r) :=
    hN.comp_radialRetraction hr
  have hM0 : (N ∘ TauCeti.radialRetraction r) 0 = 0 := by simp [hN0]
  have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
  -- The uniform bound on the Lyapunov--Perron solutions of the cut-off equation.
  have hbound : ∀ (ξ : X) (t : ℝ≥0),
      ‖lyapunovPerronSolution A P (N ∘ TauCeti.radialRetraction r) hs hu hα hMlip hsmall ξ t‖ ≤
        (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ‖ξ‖ := fun ξ t ↦ by
    have h := norm_lyapunovPerronSolution_le hs hu hα hMlip hsmall hM0 (β := 0) le_rfl
      (by push_cast; linarith) ξ t
    simpa using h
  ext x
  simp only [mem_ofPred_eq, mem_image, mem_inter_iff, mem_range, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨⟨y, hy, rfl, hmaps⟩, hPx⟩
    have hfix := (exists_isIntegralCurveOn_bounded_iff hs hu hα hMlip hsmall hP hAP (y 0)).1
      ⟨y, isIntegralCurveOn_comp_radialRetraction hy hmaps, rfl, r,
        fun t ht ↦ mem_closedBall_zero_iff.1 (hmaps ht)⟩
    exact ⟨P (y 0), ⟨⟨y 0, rfl⟩, hPx⟩,
      (invOn_add_lyapunovPerronGraphMap hs hu hα hMlip hsmall hP hAP).1 hfix⟩
  · rintro ⟨v, ⟨⟨w, rfl⟩, hv⟩, rfl⟩
    have hPP : P (P w) = P w := by rw [← mul_apply_eq_comp P P, hP.eq]
    set γ := lyapunovPerronSolution A P (N ∘ TauCeti.radialRetraction r) hs hu hα hMlip hsmall
      (P w) with hγ
    have hγ0 : γ 0 = P w + localStableGraphMap A P N r hs hu hα hr hN hsmall (P w) := by
      rw [hγ, lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap hs hu hα hMlip hsmall,
        hPP, localStableGraphMap_def]
    have hmaps : MapsTo (fun t : ℝ ↦ γ t.toNNReal) (Ici 0) (closedBall 0 r) := fun t _ ↦ by
      rw [mem_closedBall_zero_iff]
      calc ‖γ t.toNNReal‖ ≤ (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ‖P w‖ := hbound _ _
        _ ≤ (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ :=
            mul_le_mul_of_nonneg_left hv (lyapunovPerronBound_nonneg hα hsmall)
        _ ≤ r := hρ
    refine ⟨⟨fun t : ℝ ↦ γ t.toNNReal, fun t ht ↦ ?_, by simpa using hγ0, hmaps⟩, ?_⟩
    · refine (isIntegralCurveOn_lyapunovPerronSolution hs hu hα hMlip hsmall (P w) t
        ht).congr_deriv ?_
      exact congrArg (A (γ t.toNNReal) + ·)
        (congrArg N (TauCeti.radialRetraction_of_norm_le
          (mem_closedBall_zero_iff.1 (hmaps ht))))
    · rw [map_add, apply_localStableGraphMap hs hu hα hr hN hsmall hP hAP, add_zero, hPP]
      exact hv

/-- **The local stable-manifold theorem, Lipschitz form.** Near a hyperbolic equilibrium the
initial values of the forward solutions that stay in a fixed small ball form the graph of a
Lipschitz map over a ball in the stable subspace `range P`. -/
theorem exists_setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image (hr0 : 0 < r) :
    ∃ ρ > 0,
      {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Ici 0) ∧ y 0 = x ∧
          MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P x‖ ≤ ρ} =
        (fun v ↦ v + localStableGraphMap A P N r hs hu hα hr hN hsmall v) ''
          (range P ∩ closedBall 0 ρ) := by
  have hC := lyapunovPerronBound_nonneg hα hsmall
  refine ⟨r / ((K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) + 1), div_pos hr0 (by linarith),
    setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hα hr hN hsmall hN0 hP hAP ?_⟩
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith

end LocalStable

end ContinuousLinearMap

end
