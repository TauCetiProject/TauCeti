/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import TauCeti.Analysis.Calculus.FDeriv.Smul
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Radially rescaled graphs via the inverse function theorem

Let `a : F → A` and `b : F → B` be strictly differentiable at `0`, with `‖a 0‖ = ε > 0`,
`b 0 = 0`, and the derivative of `b` invertible. Moving each pair `(a z, b z)` radially so that
its first component lands on the sphere of radius `ε`, while the second is scaled by the inverse
factor, gives the pair `((ε / ‖a z‖) • a z, (‖a z‖ / ε) • b z)`. The rescaling factor is only
Lipschitz, not differentiable, for a general norm, but it equals `1` at `0`, so the rescaled second
component still has the strict derivative of `b` there
(`TauCeti.hasStrictFDerivAt_smul_of_isBigO_sub`). The inverse function theorem then shows that the
rescaled pairs near `0` form a Lipschitz graph over a closed ball of `B`. The Lipschitz bound on
the graph uses that the radial projection to the sphere is Lipschitz away from the origin, as a
multiple of `TauCeti.radialRetraction`.

This is how the traces of transverse discs on the faces of a hyperbolic box are produced in Morse
gluing, where the rescaling is the flow to the entry or exit time.

## Main results

* `TauCeti.exists_lipschitzOnWith_rescale_graph`: near `0`, the radially rescaled pairs form a
  Lipschitz graph `y ↦ (g y, y)` with `g 0 = a 0`, each of whose points is attained.
-/

public section

open Asymptotics Filter Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {F A B : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {ε : ℝ}

/-- **Radial rescaling of a graph through the inverse function theorem.** Let `a` be strictly
differentiable at `0` with `‖a 0‖ = ε > 0`, and `b` strictly differentiable at `0` with `b 0 = 0`
and invertible derivative. Rescale each pair `(a z, b z)` by the factor `ε / ‖a z‖` in the first
component and its inverse in the second. Near `0`, the rescaled pairs
`((ε / ‖a z‖) • a z, (‖a z‖ / ε) • b z)` lie on a Lipschitz graph `y ↦ (g y, y)` over a closed
ball of `B`, with `g 0 = a 0`; every point of the graph is the rescaled pair of some `z` in a
prescribed neighbourhood `U` of `0` with `a z ≠ 0`. -/
theorem exists_lipschitzOnWith_rescale_graph {a : F → A} {b : F → B} {a' : F →L[ℝ] A}
    {L : F ≃L[ℝ] B} (ha : HasStrictFDerivAt a a' 0) (hb : HasStrictFDerivAt b (L : F →L[ℝ] B) 0)
    (ha₀ : ‖a 0‖ = ε) (hb₀ : b 0 = 0) (hε : 0 < ε) {U : Set F} (hU : U ∈ 𝓝 0) :
    ∃ δ > 0, ∃ (K : ℝ≥0) (g : B → A), LipschitzOnWith K g (closedBall 0 δ) ∧ g 0 = a 0 ∧
      (∀ y ∈ closedBall (0 : B) δ, ∃ z ∈ U, a z ≠ 0 ∧
        (ε / ‖a z‖) • a z = g y ∧ (‖a z‖ / ε) • b z = y) ∧
      ∀ᶠ z in 𝓝 0, (ε / ‖a z‖) • a z = g ((‖a z‖ / ε) • b z) := by
  set Φ : F → B := fun z ↦ (‖a z‖ / ε) • b z with hΦdef
  -- The rescaling factor `‖a z‖ / ε` is Lipschitz near `0` and equals `1` there, so the
  -- rescaled second component has the same strict derivative as `b`.
  have hc : (fun p : F × F ↦ (‖a p.1‖ / ε - 1) - (‖a p.2‖ / ε - 1)) =O[𝓝 (0, 0)]
      fun p ↦ p.1 - p.2 := by
    refine (IsBigO.of_bound ε⁻¹ (Eventually.of_forall fun p ↦ ?_)).trans ha.isBigO_sub
    rw [show ‖a p.1‖ / ε - 1 - (‖a p.2‖ / ε - 1) = ε⁻¹ * (‖a p.1‖ - ‖a p.2‖) by ring,
      Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hε)]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (inv_pos.2 hε).le
  have hΦ : HasStrictFDerivAt Φ (L : F →L[ℝ] B) 0 := by
    have h := hb.add (hasStrictFDerivAt_smul_of_isBigO_sub (c := fun z ↦ ‖a z‖ / ε - 1) hc
      hb.isBigO_sub (by rw [ha₀, div_self hε.ne', sub_self]) hb₀)
    rw [add_zero] at h
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
    simp [hΦdef, sub_smul]
  have hΦ₀ : Φ 0 = 0 := by simp [hΦdef, hb₀]
  set σ := hΦ.localInverse Φ L 0
  obtain ⟨Kσ, s, hs, hσL⟩ := hΦ.to_localInverse.exists_lipschitzOnWith
  obtain ⟨Ka, s', hs', haL⟩ := ha.exists_lipschitzOnWith
  rw [hΦ₀] at hs
  have hfar : {z | ε / 2 ≤ ‖a z‖} ∈ 𝓝 (0 : F) :=
    ha.continuousAt.norm.eventually (eventually_ge_nhds (by linarith))
  have hσ : Tendsto σ (𝓝 0) (𝓝 0) := by simpa [hΦ₀] using hΦ.localInverse_tendsto
  have hright : ∀ᶠ y in 𝓝 (0 : B), Φ (σ y) = y := by
    simpa [hΦ₀] using hΦ.eventually_right_inverse
  obtain ⟨δ, hδ, hδV⟩ := nhds_basis_closedBall.mem_iff.1
    (inter_mem hs (inter_mem (hσ (inter_mem (inter_mem hs' hU) hfar)) hright))
  -- Away from the origin, the radial projection to the sphere of radius `ε` is a multiple of the
  -- radial retraction onto a smaller ball, hence Lipschitz.
  have hN : LipschitzOnWith (‖(2 : ℝ)‖₊ * 2) (fun u : A ↦ (ε / ‖u‖) • u) {u | ε / 2 ≤ ‖u‖} := by
    have h := ((lipschitzWith_smul (2 : ℝ)).comp
      (lipschitzWith_radialRetraction (E := A) (by positivity : 0 ≤ ε / 2))).lipschitzOnWith
      (s := {u | ε / 2 ≤ ‖u‖})
    intro u hu v hv
    have huv := h hu hv
    simp only [Function.comp_apply, mem_ofPred_eq] at huv hu hv
    rwa [radialRetraction_of_le_norm hu, radialRetraction_of_le_norm hv, smul_smul, smul_smul,
      show (2 : ℝ) * (ε / 2 / ‖u‖) = ε / ‖u‖ by ring,
      show (2 : ℝ) * (ε / 2 / ‖v‖) = ε / ‖v‖ by ring] at huv
  refine ⟨δ, hδ, ‖(2 : ℝ)‖₊ * 2 * (Ka * Kσ), fun y ↦ (ε / ‖a (σ y)‖) • a (σ y), ?_, ?_, ?_, ?_⟩
  · exact hN.comp
      (haL.comp (hσL.mono fun y hy ↦ (hδV hy).1) fun y hy ↦ (hδV hy).2.1.1.1)
      fun y hy ↦ (hδV hy).2.1.2
  · have hσ₀ : σ 0 = 0 := by simpa [hΦ₀] using hΦ.localInverse_apply_image
    simp only [hσ₀, ha₀, div_self hε.ne', one_smul]
  · intro y hy
    obtain ⟨-, ⟨⟨-, hU⟩, hfar⟩, hy⟩ := hδV hy
    exact ⟨σ y, hU, norm_pos_iff.1 (by simp only [mem_ofPred_eq] at hfar; linarith), rfl, hy⟩
  · filter_upwards [hΦ.eventually_left_inverse] with z hz
    exact (congrArg (fun w ↦ (ε / ‖a w‖) • a w) hz).symm

end TauCeti
