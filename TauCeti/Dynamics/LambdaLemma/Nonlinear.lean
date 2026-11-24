/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The λ-lemma for nonlinear maps near a hyperbolic fixed point

Let `F` be a map of a product `Eₛ × Eᵤ` of a normed group `Eₛ` and a real Banach space `Eᵤ`,
defined near the origin. Write `x` for the stable and `y` for the unstable coordinate, and work on
the box `‖x‖ ≤ r`, `‖y‖ ≤ r`. Suppose that on this box

* the unstable axis `x = 0` and the stable axis `y = 0` are invariant: `(F (0, y)).1 = 0` and
  `(F (x, 0)).2 = 0`;
* the stable component contracts: `(F p).1` is `k`-Lipschitz in `x` with `k < 1`, and its
  dependence on `y` is `ε`-Lipschitz on the box and `η`-Lipschitz for every `η > 0` on a thin
  enough slab `‖x‖ ≤ δ` around the unstable axis;
* the unstable component expands: `y ↦ (F p).2` differs from an invertible linear map `B` by an
  `ε`-Lipschitz error, with `‖B⁻¹‖⁻¹` larger than `1` plus a multiple of `ε`.

These are the conditions satisfied, on a small enough box, by a map with a hyperbolic fixed point at
the origin and uniformly continuous derivative near it, in coordinates that straighten its local
stable and unstable manifolds onto the two axes and for a norm on `Eₛ` adapted to the contraction:
the derivative of `(F p).1` in `y` vanishes on the unstable axis, so the `y`-dependence is small
near that axis.

The **λ-lemma** (inclination lemma) says that the forward images of a disc crossing the stable axis
accumulate on the unstable axis, as graphs converging in `C¹`. This file proves it in Lipschitz
form (`TauCeti.exists_graph_mem_image_iterate_lipschitzOnWith_tendstoUniformlyOn`): if `g₀` is a
map on the ball of radius `ρ₀` of `Eᵤ` whose Lipschitz constant is at most a slope bound `S`
preserved by `F`, its graph `D = {(g₀ y, y)}` is a disc through the point `(g₀ 0, 0)` of the stable
axis. Then for every large `n`, the image `Fⁿ(D)` contains the graph of a map `gₙ` on the whole
ball of radius `r`, and the maps `gₙ` tend to zero uniformly with Lipschitz constants tending to
zero. Unlike the λ-lemma for linear hyperbolic maps
(`TauCeti.exists_graph_tendstoUniformlyOn_iteratedFDeriv`), no linearizing chart is assumed.

The proof is the graph transform. The image under `F` of the graph of a map `g` on the ball of
radius `ρ` is the graph of a map on the ball of radius `m ρ`, where `m > 1` bounds the expansion
of `y ↦ (F (g y, y)).2`. This map approximates `B` on the ball, so it is onto a ball of radius
`m ρ` and expands distances by at least `m` (`ApproximatesLinearOn`); composing `F` with a right
inverse of it gives the new graph map. Its sup norm is at most `k` times that of `g`, so it tends
to zero geometrically. Its Lipschitz constant is at most `(k L + η) / m` when `g` is
`L`-Lipschitz and takes values in the slab where the `y`-dependence of `(F p).1` is
`η`-Lipschitz. Once the graphs are in that slab, the Lipschitz constants therefore approach
`η / (m - k)`, and `η` is arbitrary. The domains grow by the factor `m` until they fill the ball of
radius `r`.

## Main results

* `TauCeti.exists_graph_mem_image_iterate_lipschitzOnWith_tendstoUniformlyOn`: **the λ-lemma**
  in Lipschitz form.

## References

* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2,
  §7 (the λ-lemma and its proof by the graph transform).
-/

public section

open Filter Function Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]
  {F : Eₛ × Eᵤ → Eₛ × Eᵤ} {B : Eᵤ ≃L[ℝ] Eᵤ} {r : ℝ} {k ε : ℝ≥0}

/-- The graph transform: the map whose graph over `Eᵤ` is the image under `F` of the graph
`{(g y, y)}` of `g` over the closed ball of radius `ρ`. It reads the image point over `z` through a
preimage of `z` under `y ↦ (F (g y, y)).2`, and is meaningful where such a preimage exists. -/
private noncomputable def graphTransform (F : Eₛ × Eᵤ → Eₛ × Eᵤ) (ρ : ℝ) (g : Eᵤ → Eₛ) :
    Eᵤ → Eₛ :=
  fun z ↦ (F (g (invFunOn (fun y ↦ (F (g y, y)).2) (closedBall 0 ρ) z),
    invFunOn (fun y ↦ (F (g y, y)).2) (closedBall 0 ρ) z)).1

/-- Along the graph of an `S`-Lipschitz map `g` over the ball of radius `ρ`, the unstable
component `y ↦ (F (g y, y)).2` expands distances by at least `m` and covers the ball of radius
`m ρ`. -/
private theorem mul_norm_sub_le_and_exists_snd_eq [CompleteSpace Eᵤ]
    (hF₂₀ : ∀ x ∈ closedBall (0 : Eₛ) r, (F (x, 0)).2 = 0)
    (hF₂ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).2 - (F q).2 - B (p.2 - q.2)‖ ≤ ε * (‖p.1 - q.1‖ + ‖p.2 - q.2‖))
    {m S : ℝ≥0} (hm : 0 < m) (hmS : m + ε * (1 + S) ≤ ‖(B.symm : Eᵤ →L[ℝ] Eᵤ)‖₊⁻¹)
    {g : Eᵤ → Eₛ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ ≤ r)
    (hgS : LipschitzOnWith S g (closedBall 0 ρ))
    (hgr : MapsTo g (closedBall 0 ρ) (closedBall 0 r)) :
    (∀ y ∈ closedBall (0 : Eᵤ) ρ, ∀ y' ∈ closedBall (0 : Eᵤ) ρ,
      (m : ℝ) * ‖y - y'‖ ≤ ‖(F (g y, y)).2 - (F (g y', y')).2‖) ∧
    ∀ z ∈ closedBall (0 : Eᵤ) (m * ρ), ∃ y ∈ closedBall (0 : Eᵤ) ρ, (F (g y, y)).2 = z := by
  set h : Eᵤ → Eᵤ := fun y ↦ (F (g y, y)).2
  have hbox : ∀ y ∈ closedBall (0 : Eᵤ) ρ,
      (g y, y) ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r := fun y hy ↦
    ⟨hgr hy, closedBall_subset_closedBall hρr hy⟩
  -- The unstable component along the graph approximates `B`.
  have happrox : ApproximatesLinearOn h (B : Eᵤ →L[ℝ] Eᵤ) (closedBall 0 ρ) (ε * (1 + S)) := by
    intro y hy y' hy'
    calc ‖h y - h y' - (B : Eᵤ →L[ℝ] Eᵤ) (y - y')‖
        ≤ ε * (‖g y - g y'‖ + ‖y - y'‖) := hF₂ _ (hbox y hy) _ (hbox y' hy')
      _ ≤ ε * (S * ‖y - y'‖ + ‖y - y'‖) := by
        gcongr; exact lipschitzOnWith_iff_norm_sub_le.1 hgS hy hy'
      _ = ↑(ε * (1 + S)) * ‖y - y'‖ := by push_cast; ring
  have hc : ε * (1 + S) < ‖(B.symm : Eᵤ →L[ℝ] Eᵤ)‖₊⁻¹ :=
    (lt_add_of_pos_left _ hm).trans_le hmS
  have hmle : (m : ℝ) ≤ (‖(B.symm : Eᵤ →L[ℝ] Eᵤ)‖₊ : ℝ)⁻¹ - ↑(ε * (1 + S)) := by
    have := NNReal.coe_le_coe.2 (le_tsub_of_add_le_right hmS)
    rwa [NNReal.coe_sub hc.le, NNReal.coe_inv] at this
  refine ⟨fun y hy y' hy' ↦ ?_, fun z hz ↦ ?_⟩
  · have := (happrox.antilipschitzWith (Or.inr hc)).mul_le_dist ⟨y, hy⟩ ⟨y', hy'⟩
    rw [inv_inv, NNReal.coe_sub hc.le, NNReal.coe_inv] at this
    simp only [Subtype.dist_eq, domRestrict_apply, dist_eq_norm] at this
    exact (mul_le_mul_of_nonneg_right hmle (norm_nonneg _)).trans this
  · have h0 : h 0 = 0 := hF₂₀ _ (hgr (mem_closedBall_self hρ))
    have := happrox.surjOn_closedBall_of_nonlinearRightInverse B.toNonlinearRightInverse hρ
      subset_rfl
    rw [h0] at this
    exact this (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hmle hρ) hz)

/-- One step of the graph transform. Over the ball of radius `m ρ`, the image under `F` of the
graph of `g` over the ball of radius `ρ` is the graph of `graphTransform F ρ g`, whose Lipschitz
constant is at most `(k L + η) / m` and whose sup norm is at most `k s`, when `g` is `L`-Lipschitz
with sup norm at most `s`, and `η` bounds the `y`-dependence of `(F p).1` on the slab of width
`δ ≥ s`. -/
private theorem graphTransform_spec [CompleteSpace Eᵤ]
    (hF₁₀ : ∀ y ∈ closedBall (0 : Eᵤ) r, (F (0, y)).1 = 0)
    (hF₂₀ : ∀ x ∈ closedBall (0 : Eₛ) r, (F (x, 0)).2 = 0)
    {η : ℝ≥0} {δ : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r, ‖p.1‖ ≤ δ → ‖q.1‖ ≤ δ →
        ‖(F p).1 - (F q).1‖ ≤ k * ‖p.1 - q.1‖ + η * ‖p.2 - q.2‖)
    (hF₂ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).2 - (F q).2 - B (p.2 - q.2)‖ ≤ ε * (‖p.1 - q.1‖ + ‖p.2 - q.2‖))
    {m S L : ℝ≥0} (hm : 0 < m) (hmS : m + ε * (1 + S) ≤ ‖(B.symm : Eᵤ →L[ℝ] Eᵤ)‖₊⁻¹)
    {g : Eᵤ → Eₛ} {ρ s : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ ≤ r) (hsδ : s ≤ δ) (hsr : s ≤ r)
    (hgS : LipschitzOnWith S g (closedBall 0 ρ)) (hgL : LipschitzOnWith L g (closedBall 0 ρ))
    (hgs : ∀ y ∈ closedBall (0 : Eᵤ) ρ, ‖g y‖ ≤ s) :
    (∀ z ∈ closedBall (0 : Eᵤ) (m * ρ), ∃ y ∈ closedBall (0 : Eᵤ) ρ,
      F (g y, y) = (graphTransform F ρ g z, z)) ∧
    LipschitzOnWith ((k * L + η) / m) (graphTransform F ρ g) (closedBall 0 (m * ρ)) ∧
    ∀ z ∈ closedBall (0 : Eᵤ) (m * ρ), ‖graphTransform F ρ g z‖ ≤ k * s := by
  have hgr : MapsTo g (closedBall 0 ρ) (closedBall 0 r) := fun y hy ↦
    mem_closedBall_zero_iff.2 ((hgs y hy).trans hsr)
  have hbox : ∀ y ∈ closedBall (0 : Eᵤ) ρ,
      (g y, y) ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r := fun y hy ↦
    ⟨hgr hy, closedBall_subset_closedBall hρr hy⟩
  obtain ⟨hlow, hsurj⟩ := mul_norm_sub_le_and_exists_snd_eq hF₂₀ hF₂ hm hmS hρ hρr hgS hgr
  refine ⟨fun z hz ↦ ?_, LipschitzOnWith.of_dist_le_mul fun z hz z' hz' ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨hy, hhy⟩ := invFunOn_pos (hsurj z hz)
    exact ⟨_, hy, Prod.ext rfl hhy⟩
  · obtain ⟨hy, hhy⟩ := invFunOn_pos (hsurj z hz)
    obtain ⟨hy', hhy'⟩ := invFunOn_pos (hsurj z' hz')
    set y := invFunOn (fun y ↦ (F (g y, y)).2) (closedBall 0 ρ) z
    set y' := invFunOn (fun y ↦ (F (g y, y)).2) (closedBall 0 ρ) z'
    have hyz : (m : ℝ) * ‖y - y'‖ ≤ ‖z - z'‖ := by
      simpa only [hhy, hhy'] using hlow y hy y' hy'
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖graphTransform F ρ g z - graphTransform F ρ g z'‖
        ≤ k * ‖g y - g y'‖ + η * ‖y - y'‖ :=
          hη _ (hbox y hy) _ (hbox y' hy') ((hgs y hy).trans hsδ) ((hgs y' hy').trans hsδ)
      _ ≤ k * (L * ‖y - y'‖) + η * ‖y - y'‖ := by
        gcongr; exact lipschitzOnWith_iff_norm_sub_le.1 hgL hy hy'
      _ = (k * L + η) * ‖y - y'‖ := by ring
      _ ≤ (k * L + η) * (‖z - z'‖ / m) := by
        gcongr
        rw [le_div_iff₀ (by exact_mod_cast hm), mul_comm]
        exact hyz
      _ = ↑((k * L + η) / m) * ‖z - z'‖ := by push_cast; ring
  · obtain ⟨hy, -⟩ := invFunOn_pos (hsurj z hz)
    set y := invFunOn (fun y ↦ (F (g y, y)).2) (closedBall 0 ρ) z
    have h0y : ((0 : Eₛ), y) ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r :=
      ⟨mem_closedBall_self (hρ.trans hρr), (hbox y hy).2⟩
    have := hη _ (hbox y hy) _ h0y ((hgs y hy).trans hsδ) (by simpa using hδ)
    rw [hF₁₀ y (hbox y hy).2] at this
    simp only [sub_zero, sub_self, norm_zero, mul_zero, add_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hgs y hy) k.coe_nonneg)

/-- The iterated graph transform, starting from `g₀` on the ball of radius `ρ₀` and transforming
the `n`-th map on the ball of radius `min (m ^ n * ρ₀) r`. -/
private noncomputable def graphIter (F : Eₛ × Eᵤ → Eₛ × Eᵤ) (m : ℝ≥0) (ρ₀ r : ℝ)
    (g₀ : Eᵤ → Eₛ) : ℕ → Eᵤ → Eₛ
  | 0 => g₀
  | n + 1 => graphTransform F (min (m ^ n * ρ₀) r) (graphIter F m ρ₀ r g₀ n)

/-- One step of the iterated graph transform, from the ball of radius `min (m ^ n * ρ₀) r` to the
ball of radius `min (m ^ (n + 1) * ρ₀) r`. -/
private theorem graphIter_succ [CompleteSpace Eᵤ]
    (hF₁₀ : ∀ y ∈ closedBall (0 : Eᵤ) r, (F (0, y)).1 = 0)
    (hF₂₀ : ∀ x ∈ closedBall (0 : Eₛ) r, (F (x, 0)).2 = 0)
    {η : ℝ≥0} {δ : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r, ‖p.1‖ ≤ δ → ‖q.1‖ ≤ δ →
        ‖(F p).1 - (F q).1‖ ≤ k * ‖p.1 - q.1‖ + η * ‖p.2 - q.2‖)
    (hF₂ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).2 - (F q).2 - B (p.2 - q.2)‖ ≤ ε * (‖p.1 - q.1‖ + ‖p.2 - q.2‖))
    {m S L : ℝ≥0} (hm : 1 ≤ m) (hmS : m + ε * (1 + S) ≤ ‖(B.symm : Eᵤ →L[ℝ] Eᵤ)‖₊⁻¹)
    {g₀ : Eᵤ → Eₛ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρ₀r : ρ₀ ≤ r) {n : ℕ} {s : ℝ} (hsδ : s ≤ δ)
    (hsr : s ≤ r)
    (hgS : LipschitzOnWith S (graphIter F m ρ₀ r g₀ n) (closedBall 0 (min ((m : ℝ) ^ n * ρ₀) r)))
    (hgL : LipschitzOnWith L (graphIter F m ρ₀ r g₀ n) (closedBall 0 (min ((m : ℝ) ^ n * ρ₀) r)))
    (hgs : ∀ y ∈ closedBall (0 : Eᵤ) (min ((m : ℝ) ^ n * ρ₀) r), ‖graphIter F m ρ₀ r g₀ n y‖ ≤ s) :
    (∀ z ∈ closedBall (0 : Eᵤ) (min ((m : ℝ) ^ (n + 1) * ρ₀) r),
      ∃ y ∈ closedBall (0 : Eᵤ) (min ((m : ℝ) ^ n * ρ₀) r),
        F (graphIter F m ρ₀ r g₀ n y, y) = (graphIter F m ρ₀ r g₀ (n + 1) z, z)) ∧
    LipschitzOnWith ((k * L + η) / m) (graphIter F m ρ₀ r g₀ (n + 1))
      (closedBall 0 (min ((m : ℝ) ^ (n + 1) * ρ₀) r)) ∧
    ∀ z ∈ closedBall (0 : Eᵤ) (min ((m : ℝ) ^ (n + 1) * ρ₀) r),
      ‖graphIter F m ρ₀ r g₀ (n + 1) z‖ ≤ k * s := by
  have hr : 0 ≤ r := hρ₀.trans hρ₀r
  obtain ⟨h₁, h₂, h₃⟩ := graphTransform_spec hF₁₀ hF₂₀ hδ hη hF₂ (zero_lt_one.trans_le hm) hmS
    (le_min (by positivity) hr) (min_le_right _ _) hsδ hsr hgS hgL hgs
  -- The next domain lies in the ball of radius `m` times the current one.
  have hsub : closedBall (0 : Eᵤ) (min ((m : ℝ) ^ (n + 1) * ρ₀) r) ⊆
      closedBall 0 (m * min ((m : ℝ) ^ n * ρ₀) r) := by
    refine closedBall_subset_closedBall ?_
    rw [mul_min_of_nonneg _ _ m.coe_nonneg, pow_succ, mul_comm _ (m : ℝ), mul_assoc]
    exact min_le_min le_rfl (le_mul_of_one_le_left hr (by exact_mod_cast hm))
  exact ⟨fun z hz ↦ h₁ z (hsub hz), h₂.mono hsub, fun z hz ↦ h₃ z (hsub hz)⟩

/-- The invariants of the iterated graph transform: the `n`-th map is defined on the ball of
radius `min (m ^ n * ρ₀) r`, its graph lies in the `n`-th image of the initial graph, it is
`S`-Lipschitz, and its sup norm is at most `k ^ n * r`. -/
private theorem graphIter_spec [CompleteSpace Eᵤ]
    (hF₁₀ : ∀ y ∈ closedBall (0 : Eᵤ) r, (F (0, y)).1 = 0)
    (hF₂₀ : ∀ x ∈ closedBall (0 : Eₛ) r, (F (x, 0)).2 = 0)
    (hF₁ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).1 - (F q).1‖ ≤ k * ‖p.1 - q.1‖ + ε * ‖p.2 - q.2‖)
    (hF₂ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).2 - (F q).2 - B (p.2 - q.2)‖ ≤ ε * (‖p.1 - q.1‖ + ‖p.2 - q.2‖))
    {m S : ℝ≥0} (hk : k ≤ 1) (hm : 1 ≤ m)
    (hmS : m + ε * (1 + S) ≤ ‖(B.symm : Eᵤ →L[ℝ] Eᵤ)‖₊⁻¹) (hS : k * S + ε ≤ m * S)
    {g₀ : Eᵤ → Eₛ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρ₀r : ρ₀ ≤ r)
    (hg₀ : LipschitzOnWith S g₀ (closedBall 0 ρ₀))
    (hg₀r : MapsTo g₀ (closedBall 0 ρ₀) (closedBall 0 r)) (n : ℕ) :
    (∀ z ∈ closedBall (0 : Eᵤ) (min ((m : ℝ) ^ n * ρ₀) r),
      (graphIter F m ρ₀ r g₀ n z, z) ∈ F^[n] '' ((fun y ↦ (g₀ y, y)) '' closedBall 0 ρ₀)) ∧
    LipschitzOnWith S (graphIter F m ρ₀ r g₀ n) (closedBall 0 (min ((m : ℝ) ^ n * ρ₀) r)) ∧
    ∀ z ∈ closedBall (0 : Eᵤ) (min ((m : ℝ) ^ n * ρ₀) r),
      ‖graphIter F m ρ₀ r g₀ n z‖ ≤ (k : ℝ) ^ n * r := by
  have hr : 0 ≤ r := hρ₀.trans hρ₀r
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, min_eq_left hρ₀r, iterate_zero, image_id]
    exact ⟨fun z hz ↦ ⟨z, hz, rfl⟩, hg₀, fun z hz ↦ mem_closedBall_zero_iff.1 (hg₀r hz)⟩
  | succ n ih =>
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    have hkn : (k : ℝ) ^ n * r ≤ r :=
      mul_le_of_le_one_left hr (pow_le_one₀ k.coe_nonneg (by exact_mod_cast hk))
    obtain ⟨h₁, h₂, h₃⟩ := graphIter_succ (L := S) hF₁₀ hF₂₀ hr
      (fun p hp q hq _ _ ↦ hF₁ p hp q hq) hF₂ hm hmS hρ₀ hρ₀r hkn hkn ih₂ ih₂ ih₃
    refine ⟨fun z hz ↦ ?_, h₂.weaken ?_, fun z hz ↦ ?_⟩
    · obtain ⟨y, hy, hFy⟩ := h₁ z hz
      obtain ⟨w, hw, hwy⟩ := ih₁ y hy
      exact ⟨w, hw, by rw [iterate_succ_apply', hwy, hFy]⟩
    · rw [div_le_iff₀ (zero_lt_one.trans_le hm), mul_comm S]
      exact hS
    · calc ‖graphIter F m ρ₀ r g₀ (n + 1) z‖ ≤ k * ((k : ℝ) ^ n * r) := h₃ z hz
        _ = (k : ℝ) ^ (n + 1) * r := by ring

/-- Once the iterated graphs lie in a slab `‖x‖ ≤ δ` on which the `y`-dependence of `(F p).1` is
`η`-Lipschitz, their Lipschitz constants approach `η / (m - k)` geometrically. -/
private theorem graphIter_lipschitzOnWith [CompleteSpace Eᵤ]
    (hF₁₀ : ∀ y ∈ closedBall (0 : Eᵤ) r, (F (0, y)).1 = 0)
    (hF₂₀ : ∀ x ∈ closedBall (0 : Eₛ) r, (F (x, 0)).2 = 0)
    (hF₁ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).1 - (F q).1‖ ≤ k * ‖p.1 - q.1‖ + ε * ‖p.2 - q.2‖)
    (hF₂ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).2 - (F q).2 - B (p.2 - q.2)‖ ≤ ε * (‖p.1 - q.1‖ + ‖p.2 - q.2‖))
    {m S : ℝ≥0} (hk : k < 1) (hm : 1 < m)
    (hmS : m + ε * (1 + S) ≤ ‖(B.symm : Eᵤ →L[ℝ] Eᵤ)‖₊⁻¹) (hS : k * S + ε ≤ m * S)
    {g₀ : Eᵤ → Eₛ} {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρ₀r : ρ₀ ≤ r)
    (hg₀ : LipschitzOnWith S g₀ (closedBall 0 ρ₀))
    (hg₀r : MapsTo g₀ (closedBall 0 ρ₀) (closedBall 0 r))
    {η : ℝ≥0} {δ : ℝ} (hδ : 0 ≤ δ)
    (hη : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r, ‖p.1‖ ≤ δ → ‖q.1‖ ≤ δ →
        ‖(F p).1 - (F q).1‖ ≤ k * ‖p.1 - q.1‖ + η * ‖p.2 - q.2‖)
    {N : ℕ} (hN : (k : ℝ) ^ N * r ≤ δ) (j : ℕ) :
    LipschitzOnWith (S * (k / m) ^ j + η / (m - k)) (graphIter F m ρ₀ r g₀ (N + j))
      (closedBall 0 (min ((m : ℝ) ^ (N + j) * ρ₀) r)) := by
  have hr : 0 ≤ r := hρ₀.trans hρ₀r
  have hspec := graphIter_spec hF₁₀ hF₂₀ hF₁ hF₂ hk.le hm.le hmS hS hρ₀ hρ₀r hg₀ hg₀r
  induction j with
  | zero =>
    refine (hspec N).2.1.weaken ?_
    simp
  | succ j ih =>
    have hk1 : (k : ℝ) ≤ 1 := by exact_mod_cast hk.le
    have hkn : (k : ℝ) ^ (N + j) * r ≤ (k : ℝ) ^ N * r := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (by positivity) (pow_le_one₀ k.coe_nonneg hk1)) hr
    obtain ⟨-, h₂, -⟩ := graphIter_succ hF₁₀ hF₂₀ hδ hη hF₂ hm.le hmS hρ₀ hρ₀r (hkn.trans hN)
      (hkn.trans (mul_le_of_le_one_left hr (pow_le_one₀ k.coe_nonneg hk1)))
      (hspec (N + j)).2.1 ih (hspec (N + j)).2.2
    refine h₂.weaken (le_of_eq ?_)
    have hkm : k ≤ m := hk.le.trans hm.le
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hmk : (m : ℝ) - k ≠ 0 := sub_ne_zero.2 (ne_of_gt (by exact_mod_cast hk.trans hm))
    rw [← NNReal.coe_inj]
    push_cast [NNReal.coe_sub hkm]
    simp only [div_pow]
    field_simp
    ring

/-- **The λ-lemma** near a hyperbolic fixed point, in Lipschitz form. Let `F` preserve the stable
axis `y = 0` and the unstable axis `x = 0` of the box `‖x‖, ‖y‖ ≤ r` in `Eₛ × Eᵤ`, contract the
stable coordinate by `k < 1`, and expand the unstable one by at least `m > 1`, up to the errors
bounded by `ε` and, near the unstable axis, by arbitrarily small `η`. Let `g₀` be `S`-Lipschitz on
the ball of radius `ρ₀`, for a slope bound `S` preserved by `F` (`k S + ε ≤ m S`), with values in
the box. Then for every large `n` the `n`-th image of the graph `{(g₀ y, y)}` contains the graph
of a map `g n` on the whole ball of radius `r`, the maps `g n` tend to zero uniformly, and their
Lipschitz constants tend to zero: the images of the disc converge to the unstable axis. -/
theorem exists_graph_mem_image_iterate_lipschitzOnWith_tendstoUniformlyOn [CompleteSpace Eᵤ]
    (hF₁₀ : ∀ y ∈ closedBall (0 : Eᵤ) r, (F (0, y)).1 = 0)
    (hF₂₀ : ∀ x ∈ closedBall (0 : Eₛ) r, (F (x, 0)).2 = 0)
    (hF₁ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).1 - (F q).1‖ ≤ k * ‖p.1 - q.1‖ + ε * ‖p.2 - q.2‖)
    (hF₁' : ∀ η : ℝ≥0, 0 < η → ∃ δ > 0, ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r, ‖p.1‖ ≤ δ → ‖q.1‖ ≤ δ →
        ‖(F p).1 - (F q).1‖ ≤ k * ‖p.1 - q.1‖ + η * ‖p.2 - q.2‖)
    (hF₂ : ∀ p ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
      ∀ q ∈ closedBall (0 : Eₛ) r ×ˢ closedBall (0 : Eᵤ) r,
        ‖(F p).2 - (F q).2 - B (p.2 - q.2)‖ ≤ ε * (‖p.1 - q.1‖ + ‖p.2 - q.2‖))
    {m S : ℝ≥0} (hk : k < 1) (hm : 1 < m)
    (hmS : m + ε * (1 + S) ≤ ‖(B.symm : Eᵤ →L[ℝ] Eᵤ)‖₊⁻¹) (hS : k * S + ε ≤ m * S)
    {g₀ : Eᵤ → Eₛ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀r : ρ₀ ≤ r)
    (hg₀ : LipschitzOnWith S g₀ (closedBall 0 ρ₀))
    (hg₀r : MapsTo g₀ (closedBall 0 ρ₀) (closedBall 0 r)) :
    ∃ g : ℕ → Eᵤ → Eₛ,
      (∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : Eᵤ) r,
        (g n z, z) ∈ F^[n] '' ((fun y ↦ (g₀ y, y)) '' closedBall 0 ρ₀)) ∧
      (∀ τ : ℝ≥0, 0 < τ → ∀ᶠ n in atTop, LipschitzOnWith τ (g n) (closedBall 0 r)) ∧
      TendstoUniformlyOn g 0 atTop (closedBall 0 r) := by
  have hspec := graphIter_spec hF₁₀ hF₂₀ hF₁ hF₂ hk.le hm.le hmS hS hρ₀.le hρ₀r hg₀ hg₀r
  -- The domains eventually fill the ball of radius `r`.
  have hfill : ∀ᶠ n in atTop, min ((m : ℝ) ^ n * ρ₀) r = r :=
    (((tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hm)).atTop_mul_const
      hρ₀).eventually_ge_atTop r).mono fun n hn ↦ min_eq_right hn
  -- The sup norms `k ^ n * r` tend to zero.
  have hsup : Tendsto (fun n ↦ (k : ℝ) ^ n * r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one k.coe_nonneg
      (by exact_mod_cast hk)).mul_const r
  refine ⟨graphIter F m ρ₀ r g₀, ?_, fun τ hτ ↦ ?_, ?_⟩
  · filter_upwards [hfill] with n hn z hz
    exact (hspec n).1 z (by rwa [hn])
  · have hkm : k < m := hk.trans hm
    set η : ℝ≥0 := (m - k) * (τ / 2) with hη_def
    have hη : 0 < η := mul_pos (tsub_pos_of_lt hkm) (half_pos hτ)
    obtain ⟨δ, hδ, hδη⟩ := hF₁' η hη
    obtain ⟨N, hN⟩ := (hsup.eventually (ge_mem_nhds hδ)).exists
    have hgeom : Tendsto (fun j : ℕ ↦ S * (k / m) ^ j) atTop (𝓝 0) := by
      simpa using (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        ((div_lt_one (zero_lt_one.trans hm)).2 hkm)).const_mul S
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hgeom.eventually (ge_mem_nhds (half_pos hτ)))
    filter_upwards [hfill, eventually_ge_atTop (N + J)] with n hn hnN
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (le_of_add_le_left hnN)
    have hlip := graphIter_lipschitzOnWith hF₁₀ hF₂₀ hF₁ hF₂ hk hm hmS hS hρ₀.le hρ₀r hg₀ hg₀r
      hδ.le hδη hN j
    rw [hn, hη_def, mul_div_cancel_left₀ _ (tsub_pos_of_lt hkm).ne'] at hlip
    refine hlip.weaken ?_
    calc S * (k / m) ^ j + τ / 2 ≤ τ / 2 + τ / 2 := by
          gcongr; exact hJ j (by omega)
      _ = τ := add_halves τ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    filter_upwards [hfill, hsup.eventually (gt_mem_nhds he)] with n hn hne z hz
    rw [Pi.zero_apply, dist_zero_left]
    exact ((hspec n).2.2 z (by rwa [hn])).trans_lt hne

end TauCeti
