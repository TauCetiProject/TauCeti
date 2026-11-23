/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.HopfLemma
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Boundary contact for elliptic subsolutions

A nonpositive subsolution that vanishes to first order at an interior sphere contact has
zeros inside the ball arbitrarily close to that point. Shrinking the tangent ball makes
Hopf's boundary-point lemma applicable with coefficient bounds valid only near the contact.
-/

public section

namespace TauCeti.PDE

open Filter Metric Set Topology

private theorem exists_tangent_subball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x₀ y : E} {R ε : ℝ} (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hε : 0 < ε) :
    ∃ p : E, ∃ r > 0, x₀ ∈ sphere p r ∧ ball p r ⊆ ball y R ∧ ball p r ⊆ ball x₀ ε := by
  let r := min R (ε / 2)
  have hr : 0 < r := lt_min hR (half_pos hε)
  have ht : r / R ≤ 1 := (div_le_one hR).2 (min_le_left _ _)
  let p := AffineMap.lineMap x₀ y (r / R)
  have hx : dist x₀ p = r := by
    dsimp only [p]
    rw [dist_left_lineMap, Real.norm_of_nonneg (div_nonneg hr.le hR.le), mem_sphere.mp hx₀,
      div_mul_cancel₀ _ hR.ne']
  have hy : dist p y = R - r := by
    dsimp only [p]
    rw [dist_lineMap_right, Real.norm_of_nonneg (sub_nonneg.mpr ht), mem_sphere.mp hx₀,
      sub_mul, one_mul, div_mul_cancel₀ _ hR.ne']
  refine ⟨p, r, hr, mem_sphere.mpr hx, ball_subset_ball' ?_, ball_subset_ball' ?_⟩
  · rw [hy]
    linarith
  · rw [dist_comm, hx]
    linarith [show r ≤ ε / 2 from min_le_right _ _]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E(" ι ")" => EuclideanSpace ℝ ι

variable {S : Set E(ι)} {x₀ y : E(ι)} {R : ℝ} {w : E(ι) → ℝ}
  {A : E(ι) → Matrix ι ι ℝ} {b : E(ι) → E(ι)} {c : E(ι) → ℝ}
  (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hball : ball y R ⊆ S)
  (hw₀ : w x₀ = 0) (hd : DifferentiableAt ℝ w x₀) (hD : fderiv ℝ w x₀ = 0)
  (hcd : ContDiffOn ℝ 2 w S) (hle : ∀ z ∈ S, w z ≤ 0)
  (hlocal : ∃ lam > (0 : ℝ), ∃ Λ β γ : ℝ, ∀ᶠ z in 𝓝 x₀,
    (∀ ξ : E(ι), lam * ‖ξ‖ ^ 2 ≤ (A z).toQuadraticForm' ξ) ∧
    (A z).trace ≤ Λ ∧ ‖b z‖ ≤ β ∧ c z ≤ γ ∧
    (z ∈ S → c z * w z ≤ ∑ i, ∑ j, A z i j * fderiv ℝ (fderiv ℝ w) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ w z (b z)))

include hR hx₀ hball hw₀ hd hD hcd hle hlocal

/-- Every neighborhood of a first-order boundary contact contains a zero in the open
interior tangent ball when the elliptic subsolution hypotheses hold near the contact. -/
theorem exists_mem_ball_eq_zero_of_fderiv_eq_zero {U : Set E(ι)} (hU : U ∈ 𝓝 x₀) :
    ∃ z ∈ ball y R, z ∈ U ∧ w z = 0 := by
  obtain ⟨lam, hlam, Λ, β, γ, hcoeff⟩ := hlocal
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff_ball.mp (hcoeff.and hU)
  obtain ⟨p, r, hr, hxp, hB, hεB⟩ := exists_tangent_subball hR hx₀ hε
  have hS := hB.trans hball
  have hdata (z : E(ι)) (hz : z ∈ ball p r) := (hnear z (hεB hz)).1
  by_contra hnone
  have hlt (z) (hz : z ∈ ball p r) : w z < w x₀ := by
    rw [hw₀]
    exact lt_of_le_of_ne (hle z (hS hz)) fun heq ↦ hnone ⟨z, hB hz, (hnear z (hεB hz)).2, heq⟩
  let ν := r⁻¹ • (x₀ - p)
  have hline : HasDerivAt (fun t : ℝ ↦ x₀ + t • ν) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add x₀
  have hwline := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  rw [hD] at hwline
  have hpos := pos_of_hasDerivWithinAt_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv
    (a := A) (b := b) (c := c) (u := w) hr hxp hlam
    (fun z hz ↦ (hdata z hz).1) (fun z hz ↦ (hdata z hz).2.1)
    (fun z hz ↦ (hdata z hz).2.2.1) (fun z hz ↦ (hdata z hz).2.2.2.1)
    (fun z hz ↦ (hcd.mono hS).contDiffAt (isOpen_ball.mem_nhds hz))
    hd.continuousAt.continuousWithinAt (fun z hz ↦ (hdata z hz).2.2.2.2 (hS hz))
    hlt (Or.inr (Or.inr hw₀)) hwline.hasDerivWithinAt
  exact (lt_irrefl (0 : ℝ)) hpos

/-- A nonpositive elliptic subsolution with first-order contact at an interior tangent sphere
has a zero in the domain. -/
theorem exists_eq_zero_of_fderiv_eq_zero : ∃ z ∈ S, w z = 0 := by
  obtain ⟨z, hz, -, hwz⟩ := exists_mem_ball_eq_zero_of_fderiv_eq_zero hR hx₀ hball hw₀ hd hD
    hcd hle hlocal univ_mem
  exact ⟨z, hball hz, hwz⟩

end TauCeti.PDE
