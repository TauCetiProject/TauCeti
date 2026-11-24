/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.CurvedBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Topology.Frontier
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Schauder estimate on a bounded domain with `C^{2,α}` boundary

Let `0 < α < 1`, and let `Ω ⊆ ℝ^{n+1}` be a bounded open set whose boundary is `C^{2,α}`: near every
point `z ∈ ∂Ω`, in a ball `B(z, r)`, the set `Ω` is the region `{x | γ x < ⟪x, ν⟫}` above the graph
of a `C^{2,α}` function over the hyperplane `ν^⊥`, for a unit vector `ν` and a `C²` function `γ`
invariant along `ν` whose first and second derivatives are bounded and whose second derivative is
`α`-Hölder. Let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` have coefficients that are `α`-Hölder with constant `L` and
bounded by `M` on `closure Ω`, and uniformly elliptic there with constants `0 < λ ≤ Λ`. This file
proves the global form of the Schauder estimate
(`exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`): there is `C`,
depending on `Ω`, `α`, `λ`, `Λ`, `L` and `M` but not on the coefficients beyond these bounds or on
the solution, such that every `u` that is `C²` near `closure Ω`, vanishes on `∂Ω` and has an
`α`-Hölder Hessian on `closure Ω` satisfies

`[D²u]_{α; closure Ω} ≤ C ([L u]_{α; Ω} + N)`,

where `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on `closure Ω`. The Hölder constant of the Hessian enters
only qualitatively. This is the covering step of Gilbarg–Trudinger, Theorem 6.6. Their statement has
only the supremum of `u` on the right, the derivatives of order one and two being absorbed by the
global interpolation inequalities of `C^{2,α}(closure Ω)` (their Lemma 6.35); that absorption is not
part of this file.

## The argument

The estimate is assembled from two local ones, each with a constant that does not depend on the
centre of the ball it is applied on.

* **Near the boundary.** For `z ∈ ∂Ω` with chart `(ν, γ)` on `B(z, r)`, the estimate near a curved
  boundary
  (`exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_graph`)
  applies at every centre `x ∈ closure Ω ∩ B(z, r / 2)` with a radius `R ≤ r / 2`, since then
  `B(x, R) ⊆ B(z, r)`, and inside `B(z, r)` the set `closure Ω` is the closed region
  `{x | γ x ≤ ⟪x, ν⟫}` and the boundary `∂Ω` is the graph `{x | γ x = ⟪x, ν⟫}`. It bounds the
  Hölder constant of `D²u` on `closedBall x ρ_z ∩ closure Ω` by `C_z (K + N)`.
* **Away from the boundary.** If `B(x, ε) ⊆ Ω`, the interior estimate on small balls
  (`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`),
  applied on a ball whose radius is small enough for the scale condition on the coefficients,
  bounds the Hölder constant of `D²u` on `closedBall x ρ₀` by `C₀ (K + N)`.

The boundary is compact, so finitely many balls `B(zᵢ, rᵢ / 4)` cover it. If `ε` is at most every
`rᵢ / 4` and every `ρ_{zᵢ}`, a point of `closure Ω` within `ε` of `∂Ω` lies in some `B(zᵢ, rᵢ / 2)`,
and a point of `closure Ω` at distance at least `ε` from `∂Ω` has `B(x, ε) ⊆ Ω`, since a ball
meeting `Ω` and its complement meets `∂Ω`. So `D²u` satisfies the Hölder bound with constant
`max C₀ Cᵢ (K + N)` between points of `closure Ω` closer than `ρ₀ < ε`, and between farther points
it moves by at most `2 N` (`HolderOnWith.of_dist_lt_of_dist_le`).

## Main declaration

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`: the
  global Schauder estimate on a bounded domain with `C^{2,α}` boundary.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2: the global estimate (Theorem 6.6) from the interior estimate and the boundary
  estimate after flattening the boundary (Lemma 6.5).
-/

public section

open Metric Set Filter Topology
open scoped NNReal Matrix InnerProductSpace

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### The boundary chart -/

section Chart

/-- Every point of the closed region `{x | γ x ≤ ⟪x, ν⟫}` in an open ball is a limit of points of
the open region `{x | γ x < ⟪x, ν⟫}` in that ball, approached along `ν`. -/
private theorem setOf_le_inter_ball_subset_closure {z ν : E} {γ : E → ℝ} {r : ℝ} (hν : ‖ν‖ = 1)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    {x | γ x ≤ ⟪x, ν⟫_ℝ} ∩ ball z r ⊆ closure ({x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r) := by
  intro y ⟨hy, hyz⟩
  have ht : Tendsto (fun t : ℝ => y + t • ν) (𝓝[>] 0) (𝓝 y) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 y (by simp))
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [ht.eventually (isOpen_ball.mem_nhds hyz), self_mem_nhdsWithin] with t hball ht0
  refine ⟨?_, hball⟩
  have hlt : γ y < ⟪y, ν⟫_ℝ + t := hy.trans_lt (lt_add_of_pos_right _ ht0)
  simpa only [mem_ofPred_eq, hγν, TauCeti.real_inner_add_smul_self_of_norm_eq_one hν] using hlt

/-- In a chart ball, the closed region `{x | γ x ≤ ⟪x, ν⟫}` lies in the closure of `Ω`. -/
private theorem setOf_le_inter_ball_subset_closure_of_chart {Ω : Set E} {z ν : E} {γ : E → ℝ}
    {r : ℝ} (hΩz : Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r) (hν : ‖ν‖ = 1)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    {x | γ x ≤ ⟪x, ν⟫_ℝ} ∩ ball z r ⊆ closure Ω := by
  refine (setOf_le_inter_ball_subset_closure hν hγν).trans (closure_mono ?_)
  rw [← hΩz]
  exact inter_subset_left

/-- In a chart ball, the closure of `Ω` lies in the closed region `{x | γ x ≤ ⟪x, ν⟫}`. -/
private theorem closure_inter_ball_subset_setOf_le {Ω : Set E} {z ν : E} {γ : E → ℝ} {r : ℝ}
    (hΩz : Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r) (hγ : Continuous γ) :
    closure Ω ∩ ball z r ⊆ {x | γ x ≤ ⟪x, ν⟫_ℝ} := by
  intro x ⟨hx, hxz⟩
  have hx' : x ∈ closure (Ω ∩ ball z r) := by
    rw [inter_comm]
    exact isOpen_ball.inter_closure ⟨hxz, hx⟩
  rw [hΩz] at hx'
  exact closure_lt_subset_le hγ (continuous_id.inner continuous_const)
    (closure_mono inter_subset_left hx')

/-- In a chart ball, the points of the graph `{x | γ x = ⟪x, ν⟫}` lie on the boundary of `Ω`. -/
private theorem mem_frontier_of_chart {Ω : Set E} {z ν : E} {γ : E → ℝ} {r : ℝ}
    (hΩz : Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r) (hΩ : IsOpen Ω) (hν : ‖ν‖ = 1)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {y : E} (hy : y ∈ ball z r)
    (hyγ : ⟪y, ν⟫_ℝ = γ y) : y ∈ frontier Ω := by
  refine ⟨setOf_le_inter_ball_subset_closure_of_chart hΩz hν hγν ⟨hyγ.ge, hy⟩, ?_⟩
  rw [hΩ.interior_eq]
  intro hyΩ
  have h : y ∈ {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r := by
    rw [← hΩz]
    exact ⟨hyΩ, hy⟩
  exact lt_irrefl _ (h.1.trans_eq hyγ)

end Chart

/-! ### The two local estimates -/

/-- **The boundary estimate in a chart, at every nearby centre.** Let `Ω` coincide on `B(z, r)` with
the region above the graph of a `C^{2,α}` function `γ` over `ν^⊥`. Then there are `ρ > 0` and `C`
such that, under the hypotheses of the global estimate on `closure Ω`, the Hessian of `u` is
`α`-Hölder with constant `C (K + N)` on `closedBall x ρ ∩ closure Ω` for every
`x ∈ closure Ω ∩ B(z, r / 2)`. -/
private theorem exists_holderOnWith_closedBall_inter_closure_of_chart {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {Ω : Set E} (hΩ : IsOpen Ω) {z ν : E} {γ : E → ℝ} {G : ℝ≥0} {r : ℝ}
    (hν : ‖ν‖ = 1) (hγ : ContDiff ℝ 2 γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hG1 : ∀ x, ‖fderiv ℝ γ x‖ ≤ G) (hG2 : ∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G)
    (hG3 : HolderWith G α (fderiv ℝ (fderiv ℝ γ))) (hr : 0 < r)
    (hΩz : Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r) {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0)
    (hlam : 0 < lam) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ x ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) →
      (∀ x ∈ closure Ω, ∀ ξ : E, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closure Ω)) →
      (∀ x ∈ closure Ω, ∀ i j, |a x i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ x ∈ frontier Ω, u x = 0) →
        (∀ x ∈ closure Ω, |u x| ≤ N) → (∀ x ∈ closure Ω, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        ∀ x ∈ closure Ω ∩ ball z (r / 2),
          HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x ρ ∩ closure Ω) := by
  obtain ⟨R₀, hR₀, hcurved⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_graph
      hα hα1 hν hγ hγν hG1 hG2 hG3 Lam L M hlam
  set R : ℝ := min R₀ (r / 2)
  have hR : 0 < R := lt_min hR₀ (half_pos hr)
  set ρ : ℝ := R / (4 * (1 + G) ^ 2)
  have hρR : 2 * (1 + (G : ℝ)) ^ 2 * ρ < R := by
    have h : 2 * (1 + (G : ℝ)) ^ 2 * ρ = R / 2 := by
      simp only [ρ]
      field_simp
      ring
    linarith
  obtain ⟨C, hC⟩ := hcurved (min_le_left _ _) hρR
  refine ⟨ρ, by positivity, C, fun {a} hEll hEll' hL hM {U u N K V} hU hΩU hu hu0 hN0 hN1 hN2 hV
    hK x hx => ?_⟩
  -- The closed ball of radius `R` about `x` stays in the chart ball.
  have hRz : closedBall x R ⊆ ball z r :=
    closedBall_subset_ball' (by linarith [min_le_right R₀ (r / 2), mem_ball.1 hx.2])
  have hle := setOf_le_inter_ball_subset_closure_of_chart hΩz hν hγν
  have hge := closure_inter_ball_subset_setOf_le hΩz hγ.continuous
  have hcl : closedBall x R ∩ {y | γ y ≤ ⟪y, ν⟫_ℝ} ⊆ closure Ω :=
    fun y hy => hle ⟨hy.2, hRz hy.1⟩
  have hcl' : ball x R ∩ {y | γ y ≤ ⟪y, ν⟫_ℝ} ⊆ closure Ω :=
    (inter_subset_inter_left _ ball_subset_closedBall).trans hcl
  have hx₀ : γ x ≤ ⟪x, ν⟫_ℝ := hge ⟨hx.1, hRz (mem_closedBall_self hR.le)⟩
  refine (hC hx₀ (hEll x hx.1) (hEll' x hx.1) (fun i j => (hL i j).mono hcl)
    (fun y hy i j => hM y (hcl' hy) i j) hU (hcl'.trans hΩU) hu
    (fun y hy hyγ => hu0 y (mem_frontier_of_chart hΩz hΩ hν hγν (hRz (ball_subset_closedBall hy))
      hyγ)) (fun y hy => hN0 y (hcl' hy)) (fun y hy => hN1 y (hcl' hy))
    (fun y hy => hN2 y (hcl' hy)) (hV.mono hcl') (hK.mono fun y hy => ?_)).mono fun y hy => ?_
  · have h : y ∈ Ω ∩ ball z r := by
      rw [hΩz]
      exact ⟨hy.2, hRz (ball_subset_closedBall hy.1)⟩
    exact h.1
  · have hρR' : ρ ≤ R := div_le_self hR.le (by nlinarith [G.coe_nonneg])
    exact ⟨hy.1, hge ⟨hy.2, hRz (closedBall_subset_closedBall hρR' hy.1)⟩⟩

/-- **The interior estimate at a fixed distance from the boundary.** For every `ε > 0` there are
`0 < ρ < ε` and `C` such that, under the hypotheses of the global estimate on `Ω`, the Hessian of
`u` is `α`-Hölder with constant `C (K + N)` on `closedBall x ρ` whenever `B(x, ε) ⊆ Ω`. -/
private theorem exists_holderOnWith_closedBall_of_ball_subset {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {Ω : Set E} {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0)
    (hlam : 0 < lam) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ x ∈ Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) →
      (∀ x ∈ Ω, ∀ ξ : E, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) Ω) →
      (∀ x ∈ Ω, ∀ i j, |a x i j| ≤ M) →
      ∀ {u : E → ℝ} {N K V : ℝ≥0}, ContDiffOn ℝ 2 u Ω →
        (∀ x ∈ Ω, |u x| ≤ N) → (∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ Ω, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) Ω →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        ∀ x, ball x ε ⊆ Ω →
          HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x ρ) := by
  obtain ⟨C₀, -, hint⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  -- A radius `R < ε` small enough for the scale condition of the interior estimate.
  set c : ℝ := 2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
    ((1 + 2 ^ (α : ℝ)) * L)
  have hlim : Tendsto (fun R : ℝ => c * R ^ (α : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 α (Or.inr α.coe_nonneg)).tendsto).const_mul c
    rw [Real.zero_rpow (by exact_mod_cast hα.ne'), mul_zero] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  obtain ⟨R, hsmall, hR⟩ :=
    ((hlim.eventually (gt_mem_nhds hlam)).and (Ioo_mem_nhdsGT hε)).exists
  have hsmall' : 2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
      ((1 + 2 ^ (α : ℝ)) * L * R ^ (α : ℝ)) ≤ lam := by
    convert hsmall.le using 1
    simp only [c]
    ring
  obtain ⟨C, hC⟩ := hint hlam hsmall' (half_lt_self hR.1)
  refine ⟨R / 2, half_pos hR.1, (half_lt_self hR.1).trans hR.2, C,
    fun {a} hEll hEll' hL hM {u N K V} hu hN0 hN1 hN2 hV hK x hx => ?_⟩
  have hRΩ : closedBall x R ⊆ Ω := (closedBall_subset_ball hR.2).trans hx
  have hRΩ' : ball x R ⊆ Ω := ball_subset_closedBall.trans hRΩ
  have hx₀ : x ∈ Ω := hRΩ (mem_closedBall_self hR.1.le)
  exact hC (hEll x hx₀) (hEll' x hx₀) (fun i j => (hL i j).mono hRΩ)
    (fun y hy i j => hM y (hRΩ hy) i j) (hu.mono hRΩ') (fun y hy => hN0 y (hRΩ' hy))
    (fun y hy => hN1 y (hRΩ' hy)) (fun y hy => hN2 y (hRΩ' hy)) (hV.mono hRΩ') (hK.mono hRΩ')

/-- **The boundary estimate near the whole boundary.** On a bounded open set with `C^{2,α}` boundary
there are `ε > 0` and `C` such that, under the hypotheses of the global estimate, the Hessian of `u`
is `α`-Hölder with constant `C (K + N)` on `closedBall x ε ∩ closure Ω` for every `x ∈ closure Ω`
within `ε` of `∂Ω`. The boundary is compact, so finitely many chart balls `B(z, r_z / 4)` cover it,
and `ε` is taken below every `r_z / 4` and every radius `ρ_z` of the chart estimates. -/
private theorem exists_holderOnWith_closedBall_inter_closure_of_dist_lt {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hchart : ∀ z ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      ContDiff ℝ 2 γ ∧ (∀ x (t : ℝ), γ (x + t • ν) = γ x) ∧ (∀ x, ‖fderiv ℝ γ x‖ ≤ G) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r)
    {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ x ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) →
      (∀ x ∈ closure Ω, ∀ ξ : E, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closure Ω)) →
      (∀ x ∈ closure Ω, ∀ i j, |a x i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ x ∈ frontier Ω, u x = 0) →
        (∀ x ∈ closure Ω, |u x| ≤ N) → (∀ x ∈ closure Ω, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        ∀ x ∈ closure Ω, ∀ w ∈ frontier Ω, dist x w < ε →
          HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x ε ∩ closure Ω) := by
  -- The boundary estimate in the chart of each boundary point.
  choose! ν γ G r hν hγ hγν hG1 hG2 hG3 hr hΩz using hchart
  choose! ρ hρ C hC using fun z (hz : z ∈ frontier Ω) =>
    exists_holderOnWith_closedBall_inter_closure_of_chart hα hα1 hΩ (hν z hz) (hγ z hz)
      (hγν z hz) (hG1 z hz) (hG2 z hz) (hG3 z hz) (hr z hz) (hΩz z hz) Lam L M hlam
  -- Finitely many chart balls `B(z, r z / 4)` cover the compact boundary.
  have hcpt : IsCompact (frontier Ω) :=
    isCompact_of_isClosed_isBounded isClosed_frontier (hΩb.closure.subset frontier_subset_closure)
  obtain ⟨b, hb, hbfin, hcover⟩ := hcpt.elim_finite_subcover_image (c := fun z => ball z (r z / 4))
    (fun _ _ => isOpen_ball) fun z hz =>
      mem_biUnion hz (mem_ball_self (by linarith [hr z hz] : (0 : ℝ) < r z / 4))
  -- A distance `ε` to the boundary below every `r z / 4` and every `ρ z`, `z ∈ b`.
  obtain ⟨ε, hεb, hε⟩ := (((hbfin.eventually_all).2 fun z hz =>
    Ioo_mem_nhdsGT (lt_min (by linarith [hr z (hb hz)] : (0 : ℝ) < r z / 4) (hρ z (hb hz)))).and
      self_mem_nhdsWithin).exists
  obtain ⟨C₁, hC₁⟩ := (hbfin.image C).bddAbove
  refine ⟨ε, hε, C₁, fun {a} hEll hEll' hL hM {U u N K V} hU hΩU hu hu0 hN0 hN1 hN2 hV hK x hx w hw
    hxw => ?_⟩
  -- The chart ball of a covering point `z ∈ b` contains `x`.
  obtain ⟨z, hzb, hwz⟩ := mem_iUnion₂.1 (hcover hw)
  have hz := hb hzb
  have hεz := hεb z hzb
  have hxz : x ∈ ball z (r z / 2) := by
    rw [mem_ball] at hwz ⊢
    linarith [dist_triangle x w z, min_le_left (r z / 4) (ρ z), hεz.2]
  have hερ : ε ≤ ρ z := hεz.2.le.trans (min_le_right _ _)
  exact ((hC z hz hEll hEll' hL hM hU hΩU hu hu0 hN0 hN1 hN2 hV hK x ⟨hx, hxz⟩).mono
    (inter_subset_inter_left _ (closedBall_subset_closedBall hερ))).mono_const
    (by gcongr; exact hC₁ (mem_image_of_mem C hzb))

/-! ### The global estimate -/

/-- **The global Schauder estimate on a bounded domain with `C^{2,α}` boundary.** Let `0 < α < 1`
and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary: every `z ∈ ∂Ω` has a ball
`B(z, r)` in which `Ω` is the region `{x | γ x < ⟪x, ν⟫}` above the graph of a `C^{2,α}` function,
for a unit vector `ν` and a `C²` function `γ` invariant along `ν` with `‖Dγ‖ ≤ G`, `‖D²γ‖ ≤ G` and
`D²γ` `α`-Hölder with constant `G`. Let `0 < λ`, `Λ`, `L` and `M` be given. Then there is `C` with
the following property. Let `a` be `α`-Hölder entrywise with constant `L`, bounded entrywise by `M`
and elliptic with constants `λ, Λ` on `closure Ω`, and put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on
an open set containing `closure Ω`, vanishing on `∂Ω`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N`
on `closure Ω` and with `D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `Ω`
with constant `K`, then `D²u` is `α`-Hölder on `closure Ω` with constant `C (K + N)`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L` and `M`: not on the coefficients beyond the
stated bounds, or on `u`. This is Gilbarg–Trudinger, Theorem 6.6, with the lower-order norms of `u`
kept on the right instead of being absorbed by interpolation. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hchart : ∀ z ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      ContDiff ℝ 2 γ ∧ (∀ x (t : ℝ), γ (x + t • ν) = γ x) ∧ (∀ x, ‖fderiv ℝ γ x‖ ≤ G) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r)
    {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ x ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) →
      (∀ x ∈ closure Ω, ∀ ξ : E, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closure Ω)) →
      (∀ x ∈ closure Ω, ∀ i j, |a x i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ x ∈ frontier Ω, u x = 0) →
        (∀ x ∈ closure Ω, |u x| ≤ N) → (∀ x ∈ closure Ω, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closure Ω) := by
  obtain ⟨ε, hε, C₁, hC₁⟩ :=
    exists_holderOnWith_closedBall_inter_closure_of_dist_lt hα hα1 hΩ hΩb hchart Lam L M hlam
  -- The interior estimate at distance `ε` from the boundary.
  obtain ⟨ρ₀, hρ₀, hρ₀ε, C₀, hC₀⟩ :=
    exists_holderOnWith_closedBall_of_ball_subset (Ω := Ω) hα hα1 hε Lam L M hlam
  set δ : ℝ≥0 := ⟨ρ₀, hρ₀.le⟩
  refine ⟨max C₀ C₁ + 2 * δ ^ (-(α : ℝ)), fun {a} hEll hEll' hL hM {U u N K V} hU hΩU hu hu0 hN0
    hN1 hN2 hV hK => ?_⟩
  have hΩcl : Ω ⊆ closure Ω := subset_closure
  -- Between points of `closure Ω` closer than `δ`, one of the two local estimates applies.
  have hloc : ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, dist x y < δ →
      dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤
        (max C₀ C₁ * (K + N) : ℝ≥0) * dist x y ^ (α : ℝ) := by
    intro x hx y hy hxy
    have hxy' : dist y x ≤ ρ₀ := by rw [dist_comm]; exact hxy.le
    by_cases hnear : ∃ w ∈ frontier Ω, dist x w < ε
    · -- Near the boundary: the boundary estimate on `closedBall x ε ∩ closure Ω`.
      obtain ⟨w, hw, hxw⟩ := hnear
      refine ((hC₁ hEll hEll' hL hM hU hΩU hu hu0 hN0 hN1 hN2 hV hK x hx w hw hxw).dist_le
        ⟨mem_closedBall_self hε.le, hx⟩ ⟨mem_closedBall.2 (hxy'.trans hρ₀ε.le), hy⟩).trans ?_
      gcongr
      exact le_max_right _ _
    · -- Away from the boundary: the ball `B(x, ε)` misses `∂Ω`, so it lies in `Ω`.
      push Not at hnear
      have hxΩ : x ∈ Ω := by
        by_contra hxΩ
        exact (hnear x ⟨hx, by rwa [hΩ.interior_eq]⟩).not_gt (by rwa [dist_self])
      have hball : ball x ε ⊆ Ω := isPreconnected_ball.subset_of_disjoint_frontier
        (disjoint_left.2 fun p hp hpf => (hnear p hpf).not_gt (mem_ball'.1 hp))
        ⟨x, mem_ball_self hε, hxΩ⟩
      refine ((hC₀ (fun x hx => hEll x (hΩcl hx)) (fun x hx => hEll' x (hΩcl hx))
        (fun i j => (hL i j).mono hΩcl) (fun x hx => hM x (hΩcl hx))
        (hu.mono (hΩcl.trans hΩU)) (fun x hx => hN0 x (hΩcl hx)) (fun x hx => hN1 x (hΩcl hx))
        (fun x hx => hN2 x (hΩcl hx)) (hV.mono hΩcl) hK x hball).dist_le
        (mem_closedBall_self hρ₀.le) (mem_closedBall.2 hxy')).trans ?_
      gcongr
      exact le_max_left _ _
  -- Between farther points, `D²u` moves by at most `2 N`.
  have hosc : ∀ x ∈ closure Ω, ∀ y ∈ closure Ω,
      dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤ (2 * N : ℝ≥0) := fun x hx y hy =>
    (dist_le_norm_add_norm _ _).trans (by push_cast; linarith [hN2 x hx, hN2 y hy])
  refine (HolderOnWith.of_dist_lt_of_dist_le (by exact hρ₀ : (0 : ℝ≥0) < δ) hloc hosc).mono_const ?_
  have h : 2 * N * δ ^ (-(α : ℝ)) ≤ 2 * δ ^ (-(α : ℝ)) * (K + N) := by
    rw [mul_assoc, mul_assoc, mul_comm N]
    gcongr
    exact le_add_self
  rw [add_mul]
  exact add_le_add le_rfl h

end TauCeti.PDE
