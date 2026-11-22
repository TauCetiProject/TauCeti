/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
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
(`TauCeti.hasStrictFDerivAt_norm_div_smul`, through
`TauCeti.hasStrictFDerivAt_smul_of_isBigO_sub`). The inverse function theorem then shows that the
rescaled pairs near `0` form a Lipschitz graph over a closed ball of `B`. The Lipschitz bound on
the graph uses that the radial projection to the sphere is Lipschitz away from the origin, as a
multiple of `TauCeti.radialRetraction`.

The same holds for families. If a third map `c : F → P`, strictly differentiable at `0` with
`c 0 = 0`, is kept unchanged as a parameter, and the derivative of `z ↦ (c z, b z)` is invertible,
the rescaled pairs with parameter `c z = s` form the graphs `y ↦ (g (s, y), y)` of one map `g`,
Lipschitz jointly in the parameter and the point.

This is how the traces of transverse discs on the faces of a hyperbolic box are produced in Morse
gluing, where the rescaling is the flow to the entry or exit time; the parameter labels the
members of a family of discs.

## Main results

* `TauCeti.hasStrictFDerivAt_norm_div_smul`: the rescaled second component `(‖a z‖ / ε) • b z`
  has the strict derivative of `b` at a point where `‖a‖ = ε` and `b = 0`.
* `TauCeti.exists_lipschitzOnWith_rescale_graph_prod`: near `0`, the radially rescaled pairs with
  parameter `s` form the graphs `y ↦ (g (s, y), y)` of a map `g` Lipschitz on a ball of `P × B`,
  with `g 0 = a 0`, each of whose points is attained.
* `TauCeti.exists_lipschitzOnWith_rescale_graph`: the case without parameter, a Lipschitz graph
  `y ↦ (g y, y)` with `g 0 = a 0`.
-/

public section

open Asymptotics Filter Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {F A B : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {ε : ℝ}

omit [CompleteSpace F] in
/-- **Rescaling by a factor equal to `1` keeps the strict derivative of a map vanishing at the
point.** If `a` is strictly differentiable at `x` with `‖a x‖ = ε > 0` and `b` is strictly
differentiable at `x` with `b x = 0`, then `z ↦ (‖a z‖ / ε) • b z` has the strict derivative of `b`
at `x`: the factor is Lipschitz near `x`, though not differentiable for a general norm, and equals
`1` at `x`. -/
theorem hasStrictFDerivAt_norm_div_smul {a : F → A} {b : F → B} {a' : F →L[ℝ] A}
    {b' : F →L[ℝ] B} {x : F} (ha : HasStrictFDerivAt a a' x) (hb : HasStrictFDerivAt b b' x)
    (ha₀ : ‖a x‖ = ε) (hb₀ : b x = 0) (hε : 0 < ε) :
    HasStrictFDerivAt (fun z ↦ (‖a z‖ / ε) • b z) b' x := by
  have hd : (fun p : F × F ↦ (‖a p.1‖ / ε - 1) - (‖a p.2‖ / ε - 1)) =O[𝓝 (x, x)]
      fun p ↦ p.1 - p.2 := by
    refine (IsBigO.of_bound ε⁻¹ (Eventually.of_forall fun p ↦ ?_)).trans ha.isBigO_sub
    rw [show ‖a p.1‖ / ε - 1 - (‖a p.2‖ / ε - 1) = ε⁻¹ * (‖a p.1‖ - ‖a p.2‖) by ring,
      Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hε)]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (inv_pos.2 hε).le
  have h := hb.add (hasStrictFDerivAt_smul_of_isBigO_sub (c := fun z ↦ ‖a z‖ / ε - 1) hd
    hb.isBigO_sub (by rw [ha₀, div_self hε.ne', sub_self]) hb₀)
  rw [add_zero] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp [sub_smul]

/-- **Radial rescaling of a family of graphs through the inverse function theorem.** Let `a` be
strictly differentiable at `0` with `‖a 0‖ = ε > 0`, and `b` and `c` strictly differentiable at `0`
with `b 0 = 0`, `c 0 = 0`, and the derivative of `z ↦ (c z, b z)` invertible. Rescale each pair
`(a z, b z)` by the factor `ε / ‖a z‖` in the first component and its inverse in the second, and
keep the parameter `c z` unchanged. Near `0`, the rescaled pairs
`((ε / ‖a z‖) • a z, (‖a z‖ / ε) • b z)` with parameter `c z = s` lie on the graph
`y ↦ (g (s, y), y)` of a map `g` Lipschitz on a closed ball of `P × B`, with `g 0 = a 0`; every
point of the graph is the rescaled pair of some `z` in a prescribed neighbourhood `U` of `0` with
`a z ≠ 0` and parameter `s`. -/
theorem exists_lipschitzOnWith_rescale_graph_prod {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {a : F → A} {b : F → B} {c : F → P} {a' : F →L[ℝ] A} {b' : F →L[ℝ] B}
    {c' : F →L[ℝ] P} (ha : HasStrictFDerivAt a a' 0) (hb : HasStrictFDerivAt b b' 0)
    (hc : HasStrictFDerivAt c c' 0) (hcb : (c'.prod b').IsInvertible) (ha₀ : ‖a 0‖ = ε)
    (hb₀ : b 0 = 0) (hc₀ : c 0 = 0) (hε : 0 < ε) {U : Set F} (hU : U ∈ 𝓝 0) :
    ∃ δ > 0, ∃ (K : ℝ≥0) (g : P × B → A), LipschitzOnWith K g (closedBall 0 δ) ∧ g 0 = a 0 ∧
      (∀ q ∈ closedBall (0 : P × B) δ, ∃ z ∈ U, a z ≠ 0 ∧
        (ε / ‖a z‖) • a z = g q ∧ c z = q.1 ∧ (‖a z‖ / ε) • b z = q.2) ∧
      ∀ᶠ z in 𝓝 0, (ε / ‖a z‖) • a z = g (c z, (‖a z‖ / ε) • b z) := by
  obtain ⟨L, hL⟩ := hcb
  set Φ : F → P × B := fun z ↦ (c z, (‖a z‖ / ε) • b z) with hΦdef
  have hΦ : HasStrictFDerivAt Φ (L : F →L[ℝ] P × B) 0 :=
    hL ▸ hc.prodMk (hasStrictFDerivAt_norm_div_smul ha hb ha₀ hb₀ hε)
  have hΦ₀ : Φ 0 = 0 := by simp [hΦdef, hb₀, hc₀]
  set σ := hΦ.localInverse Φ L 0
  obtain ⟨Kσ, s, hs, hσL⟩ := hΦ.to_localInverse.exists_lipschitzOnWith
  obtain ⟨Ka, s', hs', haL⟩ := ha.exists_lipschitzOnWith
  rw [hΦ₀] at hs
  have hfar : {z | ε / 2 ≤ ‖a z‖} ∈ 𝓝 (0 : F) :=
    ha.continuousAt.norm.eventually (eventually_ge_nhds (by linarith))
  have hσ : Tendsto σ (𝓝 0) (𝓝 0) := by simpa [hΦ₀] using hΦ.localInverse_tendsto
  have hright : ∀ᶠ q in 𝓝 (0 : P × B), Φ (σ q) = q := by
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
  refine ⟨δ, hδ, ‖(2 : ℝ)‖₊ * 2 * (Ka * Kσ), fun q ↦ (ε / ‖a (σ q)‖) • a (σ q), ?_, ?_, ?_, ?_⟩
  · exact hN.comp
      (haL.comp (hσL.mono fun q hq ↦ (hδV hq).1) fun q hq ↦ (hδV hq).2.1.1.1)
      fun q hq ↦ (hδV hq).2.1.2
  · have hσ₀ : σ 0 = 0 := by simpa [hΦ₀] using hΦ.localInverse_apply_image
    simp only [hσ₀, ha₀, div_self hε.ne', one_smul]
  · intro q hq
    obtain ⟨-, ⟨⟨-, hU⟩, hfar⟩, hq⟩ := hδV hq
    simp only [mem_ofPred_eq] at hfar hq
    exact ⟨σ q, hU, norm_pos_iff.1 (by linarith), rfl, congrArg Prod.fst hq,
      congrArg Prod.snd hq⟩
  · filter_upwards [hΦ.eventually_left_inverse] with z hz
    exact (congrArg (fun w ↦ (ε / ‖a w‖) • a w) hz).symm

/-- **Radial rescaling of a graph through the inverse function theorem.** Let `a` be strictly
differentiable at `0` with `‖a 0‖ = ε > 0`, and `b` strictly differentiable at `0` with `b 0 = 0`
and invertible derivative. Rescale each pair `(a z, b z)` by the factor `ε / ‖a z‖` in the first
component and its inverse in the second. Near `0`, the rescaled pairs
`((ε / ‖a z‖) • a z, (‖a z‖ / ε) • b z)` lie on a Lipschitz graph `y ↦ (g y, y)` over a closed
ball of `B`, with `g 0 = a 0`; every point of the graph is the rescaled pair of some `z` in a
prescribed neighbourhood `U` of `0` with `a z ≠ 0`. This is the case of a trivial parameter in
`TauCeti.exists_lipschitzOnWith_rescale_graph_prod`. -/
theorem exists_lipschitzOnWith_rescale_graph {a : F → A} {b : F → B} {a' : F →L[ℝ] A}
    {L : F ≃L[ℝ] B} (ha : HasStrictFDerivAt a a' 0) (hb : HasStrictFDerivAt b (L : F →L[ℝ] B) 0)
    (ha₀ : ‖a 0‖ = ε) (hb₀ : b 0 = 0) (hε : 0 < ε) {U : Set F} (hU : U ∈ 𝓝 0) :
    ∃ δ > 0, ∃ (K : ℝ≥0) (g : B → A), LipschitzOnWith K g (closedBall 0 δ) ∧ g 0 = a 0 ∧
      (∀ y ∈ closedBall (0 : B) δ, ∃ z ∈ U, a z ≠ 0 ∧
        (ε / ‖a z‖) • a z = g y ∧ (‖a z‖ / ε) • b z = y) ∧
      ∀ᶠ z in 𝓝 0, (ε / ‖a z‖) • a z = g ((‖a z‖ / ε) • b z) := by
  -- Read `B` as `Unit × B`, with the constant parameter `0`.
  have hcb : ((0 : F →L[ℝ] Unit).prod (L : F →L[ℝ] B)).IsInvertible :=
    ⟨L.trans (ContinuousLinearEquiv.uniqueProd ℝ B Unit).symm, by ext; simp⟩
  obtain ⟨δ, hδ, K, g, hg, hg₀, hpts, hev⟩ := exists_lipschitzOnWith_rescale_graph_prod
    ha hb (hasStrictFDerivAt_const (0 : Unit) 0) hcb ha₀ hb₀ rfl hε hU
  have hmk : MapsTo (Prod.mk (0 : Unit)) (closedBall (0 : B) δ) (closedBall 0 δ) := fun y hy ↦ by
    simpa [Prod.norm_def] using hy
  refine ⟨δ, hδ, K * 1, fun y ↦ g (0, y), hg.comp (LipschitzWith.prodMk_left 0).lipschitzOnWith hmk,
    hg₀, fun y hy ↦ ?_, hev⟩
  obtain ⟨z, hzU, hz₀, hzg, -, hzy⟩ := hpts _ (hmk hy)
  exact ⟨z, hzU, hz₀, hzg, hzy⟩

omit [CompleteSpace F] [NormedSpace ℝ F] [NormedSpace ℝ A] in
/-- Near `0`, the first component `a z` of a pair continuous at `0` with `‖a 0‖ = ε > 0` is nonzero,
and, when the second component `b` is continuous at `0` with `b 0 = 0`, the radially rescaled second
component `(‖a z‖ / ε) • b z` has norm at most `r₀ * ε` for any `r₀ > 0`. -/
theorem eventually_ne_zero_and_norm_rescale_smul_le {a : F → A} {b : F → B}
    (ha : ContinuousAt a 0) (hb : ContinuousAt b 0) (ha₀ : ‖a 0‖ = ε) (hb₀ : b 0 = 0)
    (hε : 0 < ε) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    (∀ᶠ z in 𝓝 (0 : F), a z ≠ 0) ∧ ∀ᶠ z in 𝓝 (0 : F), ‖(‖a z‖ / ε) • b z‖ ≤ r₀ * ε := by
  refine ⟨ha.eventually_ne (by simpa [← norm_pos_iff, ha₀] using hε), ?_⟩
  have h : Tendsto (fun z ↦ (‖a z‖ / ε) • b z) (𝓝 0) (𝓝 0) := by
    simpa [hb₀] using (ha.norm.div_const ε).tendsto.smul hb.tendsto
  simpa [dist_zero_right] using h.eventually (closedBall_mem_nhds 0 (by positivity : 0 < r₀ * ε))

end TauCeti
