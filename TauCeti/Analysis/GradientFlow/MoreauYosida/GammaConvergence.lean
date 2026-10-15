/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Existence
public import TauCeti.Topology.Semicontinuity.GammaConvergence
import TauCeti.Algebra.Order.Field.Basic

/-!
# Stability of resolvents under Γ-convergence

Let `Φ n` be energies on a pseudometric space `X` that Γ-converge to an energy `φ`, let
`x n → x₀` be base points and `τ > 0` a time step. A resolvent step `J_τ x` minimizes the
penalized energy `y ↦ φ y + d(x, y)² / (2τ)`. The penalties `d(x n, ·)² / (2τ)` converge
continuously to `d(x₀, ·)² / (2τ)`, so the penalized energies of `Φ n` at `x n` Γ-converge to the
penalized energy of `φ` at `x₀`, and the fundamental theorem of Γ-convergence applies to them:

* the Moreau–Yosida approximations converge, `(Φ n)_τ (x n) → φ_τ (x₀)`, once the penalized
  energies are equicoercive;
* cluster points of resolvent steps `y n ∈ J^{Φ n}_τ (x n)` are resolvent steps of `φ` from `x₀`;
* under equicoercivity, and if `φ` is not identically `⊤`, every sequence of resolvent steps has a
  subsequence converging to a resolvent step of `φ` from `x₀`.

This is the static half of the stability theory of gradient flows under Γ-convergence: one
implicit Euler step of the limit energy is the limit of implicit Euler steps of the approximating
energies.

Equicoercivity of the penalized energies is a hypothesis of the convergence results. On a proper
space it holds as soon as the base points stay bounded and the energies are uniformly coercive,
`(Φ n)_{τ₀}(z) ≥ c` for a time step `τ₀ > τ`, a point `z` and a real `c`
(`TauCeti.equicoercive_add_edist_sq_div`). This is the uniform version of the coercivity
hypothesis under which resolvent steps exist (`TauCeti.moreauYosidaResolvent_nonempty`).

## Main results

* `TauCeti.TendstoGamma.add_edist_sq_div`: the penalized energies Γ-converge.
* `TauCeti.TendstoGamma.tendsto_moreauYosida`: convergence of the Moreau–Yosida approximations.
* `TauCeti.TendstoGamma.mem_moreauYosidaResolvent_of_tendsto`: cluster points of resolvent steps
  are resolvent steps.
* `TauCeti.TendstoGamma.exists_tendsto_mem_moreauYosidaResolvent`: resolvent steps have a
  subsequence converging to a resolvent step.
* `TauCeti.equicoercive_add_edist_sq_div`: equicoercivity of the penalized energies on a proper
  space.

## References

* A. Braides, *Γ-convergence for Beginners*, Oxford University Press 2002, Chapter 1.
* H. Attouch, *Variational Convergence for Functions and Operators*, Pitman 1984.
* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 2.
-/

public section

noncomputable section

open Filter Set Topology Metric
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {Φ : ℕ → X → EReal} {φ : X → EReal} {τ τ₀ : ℝ≥0}
  {x : ℕ → X} {x₀ : X}

namespace TendstoGamma

/-- If `Φ n` Γ-converges to `φ` and `x n → x₀`, then for every time step `τ > 0` the penalized
energies `Φ n + d(x n, ·)² / (2τ)` Γ-converge to `φ + d(x₀, ·)² / (2τ)`. -/
theorem add_edist_sq_div (h : TendstoGamma Φ φ) (hx : Tendsto x atTop (𝓝 x₀)) (hτ : 0 < τ) :
    TendstoGamma (fun n y ↦ Φ n y + (edist (x n) y ^ 2 / (2 * τ) : ℝ≥0∞))
      (fun y ↦ φ y + (edist x₀ y ^ 2 / (2 * τ) : ℝ≥0∞)) := by
  simp_rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ]
  exact h.add_tendsto fun _ _ hu ↦ ((hx.dist hu).pow 2).div_const _

/-- **Convergence of Moreau–Yosida approximations.** If `Φ n` Γ-converges to `φ`, `x n → x₀`,
and the penalized energies `Φ n + d(x n, ·)² / (2τ)` are equicoercive, then
`(Φ n)_τ (x n) → φ_τ (x₀)`. -/
theorem tendsto_moreauYosida (h : TendstoGamma Φ φ) (hx : Tendsto x atTop (𝓝 x₀)) (hτ : 0 < τ)
    (hc : Equicoercive fun n y ↦ Φ n y + (edist (x n) y ^ 2 / (2 * τ) : ℝ≥0∞)) :
    Tendsto (fun n ↦ moreauYosida (Φ n) τ (x n)) atTop (𝓝 (moreauYosida φ τ x₀)) := by
  simpa only [moreauYosida_eq_iInf] using (h.add_edist_sq_div hx hτ).tendsto_iInf hc

/-- **Cluster points of resolvent steps are resolvent steps.** If `Φ n` Γ-converges to `φ`,
`x n → x₀`, `y n ∈ J^{Φ n}_τ (x n)` for every `n`, and `y (ψ k) → y₀` along a sequence of
indices `ψ k → ∞`, then `y₀ ∈ J^φ_τ x₀`. -/
theorem mem_moreauYosidaResolvent_of_tendsto (h : TendstoGamma Φ φ) (hx : Tendsto x atTop (𝓝 x₀))
    (hτ : 0 < τ) {y : ℕ → X} (hy : ∀ n, y n ∈ moreauYosidaResolvent (Φ n) τ (x n))
    {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) {y₀ : X} (hy₀ : Tendsto (y ∘ ψ) atTop (𝓝 y₀)) :
    y₀ ∈ moreauYosidaResolvent φ τ x₀ :=
  mem_moreauYosidaResolvent_iff_isMinOn.2 <| (h.add_edist_sq_div hx hτ).isMinOn_of_tendsto
    (fun n ↦ mem_moreauYosidaResolvent_iff_isMinOn.1 (hy n)) hψ hy₀

/-- **Compactness of resolvent steps.** If `Φ n` Γ-converges to `φ`, `x n → x₀`, the penalized
energies `Φ n + d(x n, ·)² / (2τ)` are equicoercive and `φ` is not identically `⊤`, then every
sequence of resolvent steps `y n ∈ J^{Φ n}_τ (x n)` has a subsequence converging to a resolvent
step `y₀ ∈ J^φ_τ x₀`. -/
theorem exists_tendsto_mem_moreauYosidaResolvent (h : TendstoGamma Φ φ)
    (hx : Tendsto x atTop (𝓝 x₀)) (hτ : 0 < τ)
    (hc : Equicoercive fun n y ↦ Φ n y + (edist (x n) y ^ 2 / (2 * τ) : ℝ≥0∞))
    (hφ : ∃ z, φ z ≠ ⊤) {y : ℕ → X} (hy : ∀ n, y n ∈ moreauYosidaResolvent (Φ n) τ (x n)) :
    ∃ y₀, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (y ∘ ψ) atTop (𝓝 y₀) ∧
      y₀ ∈ moreauYosidaResolvent φ τ x₀ := by
  -- The limit `φ_τ(x₀)` is below `⊤`, so the penalized energies at the resolvent steps, which are
  -- the Moreau–Yosida approximations `(Φ n)_τ (x n)`, eventually lie below a real level `t`.
  obtain ⟨z, hz⟩ := hφ
  have hlt : moreauYosida φ τ x₀ < ⊤ := (moreauYosida_le φ τ (edist_ne_top x₀ z)).trans_lt <| by
    rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ]
    exact EReal.add_lt_top hz (EReal.coe_ne_top _)
  obtain ⟨t, ht, -⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hev : ∀ᶠ n in atTop, Φ n (y n) + (edist (x n) (y n) ^ 2 / (2 * τ) : ℝ≥0∞) ≤ t :=
    ((h.tendsto_moreauYosida hx hτ hc).eventually (gt_mem_nhds ht)).mono fun n hn ↦
      (mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 (hy n)).2.trans_le hn.le
  obtain ⟨K, hK, hFK⟩ := equicoercive_def.1 hc t
  obtain ⟨y₀, -, ψ, hψ, hψy₀⟩ :=
    hK.tendsto_subseq' (hev.mono fun n hn ↦ hFK n (y n) hn).frequently
  exact ⟨y₀, ψ, hψ, hψy₀,
    h.mem_moreauYosidaResolvent_of_tendsto hx hτ hy hψ.tendsto_atTop hψy₀⟩

end TendstoGamma

/-- **Equicoercivity of the penalized energies.** On a proper space, let the base points `x n`
stay in a bounded set and let the energies be uniformly coercive: `c ≤ (Φ n)_{τ₀}(z)` for all `n`,
for a time step `τ₀`, a point `z` and a real `c`. Then for every time step `0 < τ < τ₀` the
penalized energies `Φ n + d(x n, ·)² / (2τ)` are equicoercive. -/
theorem equicoercive_add_edist_sq_div [ProperSpace X] (hx : Bornology.IsBounded (range x))
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) {z : X} {c : ℝ}
    (hΦ : ∀ n, (c : EReal) ≤ moreauYosida (Φ n) τ₀ z) :
    Equicoercive fun n y ↦ Φ n y + (edist (x n) y ^ 2 / (2 * τ) : ℝ≥0∞) := by
  obtain ⟨R, hR⟩ := hx.subset_closedBall z
  have hτ₀ : 0 < τ₀ := hτ.trans hττ₀
  refine equicoercive_def.2 fun t ↦ ⟨closedBall z
    (max R 0 + 1 + (2 * τ₀ * max R 0 + 2 * τ * τ₀ * |t - c|) / (τ₀ - τ)),
    isCompact_closedBall _ _, fun n y hy ↦ ?_⟩
  -- Combine the sublevel bound with the coercivity bound `c ≤ Φ n y + d(z, y)² / (2τ₀)`.
  have h : ((c + dist (x n) y ^ 2 / (2 * τ) : ℝ) : EReal) ≤
      ((t + dist z y ^ 2 / (2 * τ₀) : ℝ) : EReal) := by
    have h₀ := (hΦ n).trans (moreauYosida_le (Φ n) τ₀ (edist_ne_top z y))
    rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ₀] at h₀
    rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ] at hy
    rw [EReal.coe_add, EReal.coe_add]
    calc (c : EReal) + (dist (x n) y ^ 2 / (2 * τ) : ℝ)
        ≤ Φ n y + (dist z y ^ 2 / (2 * τ₀) : ℝ) + (dist (x n) y ^ 2 / (2 * τ) : ℝ) :=
          add_le_add_left h₀ _
      _ = Φ n y + (dist (x n) y ^ 2 / (2 * τ) : ℝ) + (dist z y ^ 2 / (2 * τ₀) : ℝ) :=
          add_right_comm _ _ _
      _ ≤ t + (dist z y ^ 2 / (2 * τ₀) : ℝ) := add_le_add_left hy _
  rw [EReal.coe_le_coe_iff] at h
  have hxn : dist z (x n) ≤ max R 0 := by
    rw [dist_comm]
    exact (mem_closedBall.1 (hR (mem_range_self n))).trans (le_max_left _ _)
  rw [mem_closedBall, dist_comm]
  exact le_of_sq_div_sub_sq_div_le (b := dist (x n) y) (NNReal.coe_pos.2 hτ)
    (NNReal.coe_lt_coe.2 hττ₀) (le_max_right _ _)
    ((dist_triangle z (x n) y).trans (by linarith)) (by linarith)

end TauCeti
