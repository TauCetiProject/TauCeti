/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.HopfLemma
public import TauCeti.Analysis.Normed.Affine.AddTorsor.TangentBall

/-!
# Boundary contact for elliptic subsolutions

A nonpositive subsolution that vanishes at an interior sphere contact and has nonpositive
outward derivative there has zeros inside the ball arbitrarily close to that point. Shrinking
the tangent ball makes Hopf's boundary-point lemma applicable with smoothness, sign and
coefficient bounds valid only near the contact within the ball.
-/

public section

namespace TauCeti.PDE

open Filter Metric Set Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E(" ι ")" => EuclideanSpace ℝ ι

variable {x₀ y : E(ι)} {R : ℝ} {w : E(ι) → ℝ}
  {A : E(ι) → Matrix ι ι ℝ} {b : E(ι) → E(ι)} {c : E(ι) → ℝ}
  (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R)
  (hw₀ : w x₀ = 0) (hd : DifferentiableAt ℝ w x₀) (hD : fderiv ℝ w x₀ (x₀ - y) ≤ 0)
  (hlocal : ∃ lam > (0 : ℝ), ∃ Λ β γ : ℝ, ∀ᶠ z in 𝓝[ball y R] x₀,
    w z ≤ 0 ∧ ContDiffAt ℝ 2 w z ∧
    (∀ ξ : E(ι), lam * ‖ξ‖ ^ 2 ≤ (A z).toQuadraticForm' ξ) ∧
    (A z).trace ≤ Λ ∧ ‖b z‖ ≤ β ∧ c z ≤ γ ∧
    (c z * w z ≤ ∑ i, ∑ j, A z i j * fderiv ℝ (fderiv ℝ w) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ w z (b z)))

include hR hx₀ hw₀ hd hD hlocal

/-- Every neighborhood of a boundary zero with nonpositive outward derivative contains a
zero in the open tangent ball when the elliptic subsolution hypotheses hold near the contact
within the ball. -/
theorem exists_mem_ball_eq_zero_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv
    {U : Set E(ι)} (hU : U ∈ 𝓝 x₀) :
    ∃ z ∈ ball y R, z ∈ U ∧ w z = 0 := by
  obtain ⟨lam, hlam, Λ, β, γ, hcoeff⟩ := hlocal
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff_ball.mp
    ((eventually_nhdsWithin_iff.mp hcoeff).and hU)
  obtain ⟨r, hr, p, hp, hxp, hB, hεB⟩ := exists_tangent_subball hR hx₀ hε
  have hdata (z : E(ι)) (hz : z ∈ ball p r) := (hnear z (hεB hz)).1 (hB hz)
  have hUball : ball p r ⊆ U := fun z hz ↦ (hnear z (hεB hz)).2
  choose hle hcd hA htr hb hc hsub using hdata
  by_contra hnone
  have hlt (z) (hz : z ∈ ball p r) : w z < w x₀ := by
    rw [hw₀]
    exact lt_of_le_of_ne (hle z hz) fun heq ↦ hnone ⟨z, hB hz, hUball hz, heq⟩
  have hpos := fderiv_pos_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv
    (a := A) (b := b) (c := c) (u := w) hr hxp hlam hA htr hb hc
    hcd hd hsub hlt (Or.inr (Or.inr hw₀))
  have hdir : x₀ - p = (r / R) • (x₀ - y) := by
    rw [hp]
    simpa only [vsub_eq_sub] using AffineMap.left_vsub_lineMap x₀ y (r / R)
  rw [hdir, map_smul, smul_eq_mul] at hpos
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hr.le hR.le) hD)) hpos

end TauCeti.PDE
