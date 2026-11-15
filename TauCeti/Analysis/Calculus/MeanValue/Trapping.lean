/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Maps whose coordinate reading has bounded derivative stay in the coordinate patch

Let `u` be a continuous map from a ball `B_s(y₀)` of a real normed space `F` to a topological space
`M`, and let `ψ : M → V` be a coordinate into a normed space `V`, continuous on a closed set
`C ⊆ M` containing `u y₀`. Suppose that the points of `C` that are within `η` of `u y₀`, as
measured by `ψ`, lie in an open set `O ⊆ C`. If the reading `ψ ∘ u` has derivative of norm at most
`κ` wherever `u` takes values in `C`, and `κ s ≤ η`, then `u` maps the whole ball into `C`, and
`ψ ∘ u` is `κ`-Lipschitz from the centre (`TauCeti.mapsTo_ball_of_norm_fderiv_comp_le`).

For a map `u` into a manifold and a partial diffeomorphism `φ` onto an open subset of `V`, the case
`ψ = φ` is `PartialDiffeomorph.mapsTo_ball_of_norm_fderiv_comp_le` in
`TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv`.

This is the continuity argument that keeps the image of a small disc in a single chart of a
manifold once the derivative of the map, read in that chart, is controlled: the derivative bound
is only available while the image stays in the chart, and the proof follows each segment from the
centre for as long as it stays in `C`. It applies to maps into manifolds whose derivative is
bounded in terms of an intrinsic quantity, such as the energy density of a Floer solution.
-/

public section

open Filter Metric Set Topology

namespace TauCeti

variable {F M V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **A map whose coordinate reading has bounded derivative stays in the coordinate patch.** Let
`u` be continuous on the ball `B_s(y₀)` with `u y₀ ∈ C`, where `C` is closed and `ψ` is continuous
on `C`. Let `O ⊆ C` be open and contain every `x ∈ C` with `‖ψ x - ψ (u y₀)‖ < η`. If `ψ ∘ u` is
differentiable with derivative of norm at most `κ` at every point of the ball where `u` takes values
in `C`, and `κ s ≤ η` with `0 < η`, then `u` maps the ball into `C` and
`‖ψ (u y) - ψ (u y₀)‖ ≤ κ ‖y - y₀‖` on the ball. -/
theorem mapsTo_ball_of_norm_fderiv_comp_le {u : F → M} {ψ : M → V} {C O : Set M} {y₀ : F}
    {s κ η : ℝ} (hC : IsClosed C) (hO : IsOpen O) (hOC : O ⊆ C) (hψ : ContinuousOn ψ C)
    (hu : ContinuousOn u (ball y₀ s)) (hy₀ : u y₀ ∈ C)
    (hCO : ∀ x ∈ C, ‖ψ x - ψ (u y₀)‖ < η → x ∈ O)
    (hd : ∀ y ∈ ball y₀ s, u y ∈ C →
      DifferentiableAt ℝ (ψ ∘ u) y ∧ ‖fderiv ℝ (ψ ∘ u) y‖ ≤ κ)
    (hη : 0 < η) (hκs : κ * s ≤ η) :
    MapsTo u (ball y₀ s) C ∧ ∀ y ∈ ball y₀ s, ‖ψ (u y) - ψ (u y₀)‖ ≤ κ * ‖y - y₀‖ := by
  -- Along the segment `p τ = y₀ + τ (y - y₀)`, the set `S` of times `τ` at which `u (p τ) ∈ C`
  -- with the Lipschitz bound is closed in `[0, 1]`, contains `0`, and extends to the right from
  -- each of its points below `1`, since there `u (p τ) ∈ O` and the derivative bound holds on a
  -- ball about `p τ`. So `S ⊇ [0, 1]`, and `τ = 1` gives the claim at `y`.
  suffices h : ∀ y ∈ ball y₀ s, u y ∈ C ∧ ‖ψ (u y) - ψ (u y₀)‖ ≤ κ * ‖y - y₀‖ from
    ⟨fun y hy ↦ (h y hy).1, fun y hy ↦ (h y hy).2⟩
  intro y hy
  have hys : ‖y - y₀‖ < s := by simpa [dist_eq_norm] using hy
  -- The bound at the centre, where `u y₀ ∈ C`, shows `0 ≤ κ`.
  have hκ : 0 ≤ κ :=
    (norm_nonneg _).trans (hd y₀ (mem_ball_self ((norm_nonneg _).trans_lt hys)) hy₀).2
  -- Follow the segment `p τ = y₀ + τ (y - y₀)` from the centre.
  set p : ℝ → F := fun τ ↦ y₀ + τ • (y - y₀) with hp_def
  have hp : Continuous p := continuous_const.add (continuous_id.smul continuous_const)
  have hpball {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : p τ ∈ ball y₀ s := by
    rw [mem_ball, dist_eq_norm, hp_def, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hτ.2).trans_lt hys
  have hpsub (τ σ : ℝ) : p σ - p τ = (σ - τ) • (y - y₀) := by
    simp only [hp_def, sub_smul]
    abel
  have hgc : ContinuousOn (u ∘ p) (Icc 0 1) :=
    hu.comp hp.continuousOn fun _ hτ ↦ hpball hτ
  set S : Set ℝ := {τ | u (p τ) ∈ C ∧ ‖ψ (u (p τ)) - ψ (u y₀)‖ ≤ κ * (τ * ‖y - y₀‖)}
  have hclosed : IsClosed (S ∩ Icc 0 1) := by
    have hZ : IsClosed (Icc (0 : ℝ) 1 ∩ (u ∘ p) ⁻¹' C) :=
      hgc.preimage_isClosed_of_isClosed isClosed_Icc hC
    have hF : ContinuousOn (fun τ ↦ ‖ψ (u (p τ)) - ψ (u y₀)‖ - κ * (τ * ‖y - y₀‖))
        (Icc 0 1 ∩ (u ∘ p) ⁻¹' C) :=
      (((hψ.comp (hgc.mono inter_subset_left) fun _ hτ ↦ hτ.2).sub continuousOn_const).norm.sub
        (continuousOn_const.mul (continuousOn_id.mul continuousOn_const)))
    convert hF.preimage_isClosed_of_isClosed hZ (isClosed_Iic (a := (0 : ℝ))) using 1
    ext τ
    simp only [S, mem_inter_iff, mem_ofPred_eq, mem_preimage, Function.comp_apply, mem_Iic,
      sub_nonpos]
    tauto
  have h0 : (0 : ℝ) ∈ S := by simp [S, hp_def, hy₀]
  have hlt : κ * ‖y - y₀‖ < η := by
    rcases hκ.eq_or_lt with h | h
    · rw [← h, zero_mul]
      exact hη
    · exact (mul_lt_mul_of_pos_left hys h).trans_le hκs
  have hstep : ∀ τ ∈ S ∩ Ico 0 1, S ∈ 𝓝[>] τ := by
    rintro τ ⟨⟨hτC, hτψ⟩, hτ0, hτ1⟩
    -- `u (p τ)` lies in the open set `O`, and `u` keeps a ball about `p τ` in `O`.
    have hτO : u (p τ) ∈ O := hCO _ hτC (hτψ.trans_lt ((mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) hτ1.le) hκ).trans_lt hlt))
    have hpτ : p τ ∈ ball y₀ s := hpball ⟨hτ0, hτ1.le⟩
    have hev : ∀ᶠ w in 𝓝 (p τ), w ∈ ball y₀ s ∧ u w ∈ O :=
      Filter.Eventually.and (isOpen_ball.mem_nhds hpτ)
        ((hu.continuousAt (isOpen_ball.mem_nhds hpτ)).preimage_mem_nhds (hO.mem_nhds hτO))
    obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff_ball.1 hev
    -- On that ball the derivative bound holds, so `ψ ∘ u` is `κ`-Lipschitz there.
    have hmvt : ∀ w ∈ ball (p τ) ε, ‖ψ (u w) - ψ (u (p τ))‖ ≤ κ * ‖w - p τ‖ := fun w hw ↦
      (convex_ball (p τ) ε).norm_image_sub_le_of_norm_fderiv_le (f := ψ ∘ u)
        (fun x hx ↦ (hd x (hεsub x hx).1 (hOC (hεsub x hx).2)).1)
        (fun x hx ↦ (hd x (hεsub x hx).1 (hOC (hεsub x hx).2)).2) (mem_ball_self hε) hw
    have hn1 : 0 < ‖y - y₀‖ + 1 := by positivity
    refine mem_of_superset (Ioo_mem_nhdsGT (lt_add_of_pos_right τ
      (div_pos hε hn1))) fun σ hσ ↦ ?_
    have hστ : 0 ≤ σ - τ := by linarith [hσ.1]
    have hσball : p σ ∈ ball (p τ) ε := by
      rw [mem_ball, dist_eq_norm, hpsub, norm_smul, Real.norm_of_nonneg hστ]
      have h1 : σ - τ < ε / (‖y - y₀‖ + 1) := by linarith [hσ.2]
      calc (σ - τ) * ‖y - y₀‖ ≤ (σ - τ) * (‖y - y₀‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hστ
        _ < ε / (‖y - y₀‖ + 1) * (‖y - y₀‖ + 1) := mul_lt_mul_of_pos_right h1 hn1
        _ = ε := div_mul_cancel₀ _ hn1.ne'
    refine ⟨hOC (hεsub _ hσball).2, ?_⟩
    calc ‖ψ (u (p σ)) - ψ (u y₀)‖
        ≤ ‖ψ (u (p σ)) - ψ (u (p τ))‖ + ‖ψ (u (p τ)) - ψ (u y₀)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ κ * ‖p σ - p τ‖ + κ * (τ * ‖y - y₀‖) := add_le_add (hmvt _ hσball) hτψ
      _ = κ * (σ * ‖y - y₀‖) := by
        rw [hpsub, norm_smul, Real.norm_of_nonneg hστ]
        ring
  obtain ⟨h1C, h1ψ⟩ := IsClosed.Icc_subset_of_forall_mem_nhdsWithin hclosed h0 hstep
    ⟨zero_le_one, le_rfl⟩
  have hp1 : p 1 = y := by simp [hp_def]
  rw [hp1] at h1C h1ψ
  exact ⟨h1C, by simpa using h1ψ⟩

end TauCeti
