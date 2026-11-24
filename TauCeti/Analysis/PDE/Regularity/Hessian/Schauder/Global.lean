/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.CurvedBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
import TauCeti.Analysis.Calculus.GraphFlattening.Direction
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Schauder estimate on a domain with `C^{2,α}` boundary

Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary: near each
point `x` of its frontier, `Ω` is the region above the graph of a `C^{2,α}` function. Precisely,
there are a radius `r > 0`, a unit vector `ν` and a `C²` function `γ`, invariant under translation
along `ν`, with `‖Dγ‖`, `‖D²γ‖` and the `α`-Hölder constant of `D²γ` bounded by some `G`, such that

`Ω ∩ B(x, r) = {y | γ y < ⟪y, ν⟫} ∩ B(x, r)`.

Let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` have coefficients with ellipticity bounds `λ, Λ`, `0 < λ`, at every
point of `closure Ω`, `α`-Hölder with constant `L` there and bounded by `M`. This file proves the
global Schauder estimate
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`): there is
a constant `C`, depending on `Ω`, `n`, `α`, `λ`, `Λ`, `L` and `M` but on nothing else, such that
every `u` which is `C²` on an open set containing `closure Ω`, vanishes on the frontier of `Ω` and
has `|u|`, `‖Du‖`, `‖D²u‖` bounded by `N` on `closure Ω` satisfies

`[D²u]_{α; closure Ω} ≤ C ([L u]_{α; Ω} + N)`,

where `[·]_{α; S}` is the `α`-Hölder constant on `S`. As in the local estimates, the Hölder
continuity of `D²u` on `closure Ω` enters only qualitatively. The constant does not depend on the
coefficient field beyond its bounds, so the estimate applies uniformly to a family of operators
with common bounds, as in the method of continuity.

This is Gilbarg–Trudinger's Theorem 6.6 with the supremum bound `N` of `u`, `Du` and `D²u` still
on the right; an interpolation inequality up to the boundary replaces it by the supremum of `|u|`.

## The argument

Each point `x` of `closure Ω` has a closed ball around it on whose part in `closure Ω` the Hölder
constant of `D²u` is at most `Cₓ ([L u]_α + N)`:

* at a point of the frontier, by the estimate near a curved boundary (`TauCeti.PDE.`
  `exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_graph`),
  applied to the graph region describing `Ω` near `x`, on a ball inside the one where `Ω` agrees
  with that region;
* at a point of `Ω`, by the interior estimate on small balls
  (`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`),
  on a ball inside `Ω` small enough for its scale condition.

Finitely many of the corresponding open balls cover the compact set `closure Ω`, and these local
bounds, together with `‖D²u‖ ≤ N`, give one Hölder bound on `closure Ω` with a constant depending
only on the cover (`IsCompact.exists_holderOnWith_of_forall_holderOnWith_ball_inter`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2, Theorem 6.6 (the global Schauder estimate) and Lemma 6.5 (the boundary estimate
  it is assembled from).
-/

public section

noncomputable section

open Metric Set Filter Topology
open scoped NNReal InnerProductSpace

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **The estimate near a frontier point.** At a point `x` of the frontier near which `Ω` is the
region above the graph of a `C^{2,α}` function, there are a radius `ρ > 0` and a constant `C` such
that the Hölder constant of `D²u` on `closedBall x ρ ∩ closure Ω` is at most `C ([L u]_{α; Ω} + N)`
for all coefficients and functions as in the global estimate. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_closure_of_mem_frontier
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω) {x : E}
    (hx : x ∈ frontier Ω) {r : ℝ} (hr : 0 < r) {ν : E} (hν : ‖ν‖ = 1) {γ : E → ℝ} {G : ℝ≥0}
    (hγ : ContDiff ℝ 2 γ) (hγν : ∀ y (t : ℝ), γ (y + t • ν) = γ y)
    (hG1 : ∀ y, ‖fderiv ℝ γ y‖ ≤ G) (hG2 : ∀ y, ‖fderiv ℝ (fderiv ℝ γ) y‖ ≤ G)
    (hG3 : HolderWith G α (fderiv ℝ (fderiv ℝ γ)))
    (hΩx : Ω ∩ ball x r = {y | γ y < ⟪y, ν⟫_ℝ} ∩ ball x r) {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0)
    (hlam : 0 < lam) :
    ∃ ρ > 0, ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ y ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a y).toQuadraticForm' ξ) →
      (∀ y ∈ closure Ω, ∀ ξ : E, (a y).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun y => a y i j) (closure Ω)) →
      (∀ y ∈ closure Ω, ∀ i j, |a y i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ y ∈ frontier Ω, u y = 0) →
        (∀ y ∈ closure Ω, |u y| ≤ N) → (∀ y ∈ closure Ω, ‖fderiv ℝ u y‖ ≤ N) →
        (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u y‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun y => ∑ i, ∑ j, a y i j • fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x ρ ∩ closure Ω) := by
  -- Inside `B(x, r)`, the closure of `Ω` is the region on or above the graph, and its frontier is
  -- the graph.
  have hcl := closure_setOf_lt_real_inner hν hγ.continuous hγν
  have hle : closure Ω ∩ ball x r ⊆ {y | γ y ≤ ⟪y, ν⟫_ℝ} := fun y hy =>
    hcl ▸ closure_mono inter_subset_left (hΩx ▸ isOpen_ball.closure_inter hy)
  have hge : {y | γ y ≤ ⟪y, ν⟫_ℝ} ∩ ball x r ⊆ closure Ω := fun y hy =>
    closure_mono inter_subset_left
      (hΩx ▸ inter_comm (ball x r) _ ▸ isOpen_ball.inter_closure ⟨hy.2, hcl ▸ hy.1⟩)
  have hfr : ∀ y ∈ ball x r, ⟪y, ν⟫_ℝ = γ y → y ∈ frontier Ω := fun y hy hyν => by
    refine hΩo.frontier_eq ▸ ⟨hge ⟨hyν.ge, hy⟩, fun hyΩ => ?_⟩
    exact (hΩx.subset ⟨hyΩ, hy⟩).1.ne hyν.symm
  -- The estimate near the curved boundary, on a ball `B(x, R)` with `R ≤ r / 2`.
  obtain ⟨R₀, hR₀, hest⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_graph
      hα hα1 hν hγ hγν hG1 hG2 hG3 Lam L M hlam
  set R := min R₀ (r / 2)
  have hR : 0 < R := lt_min hR₀ (half_pos hr)
  have hRr : closedBall x R ⊆ ball x r := closedBall_subset_ball ((min_le_right _ _).trans_lt
    (half_lt_self hr))
  have hρR : 2 * (1 + G) ^ 2 * (R / (4 * (1 + G) ^ 2)) < R := by
    field_simp
    linarith
  obtain ⟨C, hC⟩ := hest (min_le_left _ _) hρR
  refine ⟨R / (4 * (1 + G) ^ 2), by positivity, C,
    fun {a} hEll hEll' hL hM {U u N K V} hU hBU hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  have hsub : closedBall x R ∩ {y | γ y ≤ ⟪y, ν⟫_ℝ} ⊆ closure Ω := fun y hy => hge ⟨hy.2, hRr hy.1⟩
  have hsub' : ball x R ∩ {y | γ y ≤ ⟪y, ν⟫_ℝ} ⊆ closure Ω :=
    (inter_subset_inter_left _ ball_subset_closedBall).trans hsub
  have hxΩ : x ∈ closure Ω := frontier_subset_closure hx
  refine (hC (hle ⟨hxΩ, mem_ball_self hr⟩) (hEll x hxΩ) (hEll' x hxΩ)
    (fun i j => (hL i j).mono hsub) (fun y hy => hM y (hsub' hy)) hU (hsub'.trans hBU) hu
    (fun y hy hyν => hu0 y (hfr y (ball_subset_ball (min_le_right _ _ |>.trans
      (half_le_self hr.le)) hy) hyν))
    (fun y hy => hN0 y (hsub' hy)) (fun y hy => hN1 y (hsub' hy)) (fun y hy => hN2 y (hsub' hy))
    (hV.mono hsub') (hK.mono fun y hy => (hΩx.superset ⟨hy.2, hRr (ball_subset_closedBall hy.1)⟩).1)
    ).mono fun y hy => ⟨hy.1, hle ⟨hy.2, hRr (closedBall_subset_closedBall ?_ hy.1)⟩⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (G : ℝ), G.coe_nonneg]

/-- **The estimate near an interior point.** At a point `x ∈ Ω` there are a radius `ρ > 0` and a
constant `C` such that the Hölder constant of `D²u` on `closedBall x ρ ∩ closure Ω` is at most
`C ([L u]_{α; Ω} + N)` for all coefficients and functions as in the global estimate. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_closure_of_mem
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω) {x : E} (hx : x ∈ Ω)
    {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ ρ > 0, ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ y ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a y).toQuadraticForm' ξ) →
      (∀ y ∈ closure Ω, ∀ ξ : E, (a y).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun y => a y i j) (closure Ω)) →
      (∀ y ∈ closure Ω, ∀ i j, |a y i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, closure Ω ⊆ U → ContDiffOn ℝ 2 u U →
        (∀ y ∈ closure Ω, |u y| ≤ N) → (∀ y ∈ closure Ω, ‖fderiv ℝ u y‖ ≤ N) →
        (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u y‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun y => ∑ i, ∑ j, a y i j • fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x ρ ∩ closure Ω) := by
  obtain ⟨C₀, -, hball⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  -- A radius `R` with `closedBall x R ⊆ Ω` satisfying the scale condition `c R^α < λ` of the
  -- interior estimate, which holds for all small `R` because `R^α → 0` as `R → 0`.
  set c : ℝ := 2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
    ((1 + 2 ^ (α : ℝ)) * L)
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩo x hx
  have h₁ : ∀ᶠ R in 𝓝[>] (0 : ℝ), R < ε := eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds hε)
  have h₂ : ∀ᶠ R in 𝓝[>] (0 : ℝ), c * R ^ (α : ℝ) < lam := by
    have ht : Tendsto (fun R : ℝ => c * R ^ (α : ℝ)) (𝓝 0) (𝓝 (c * 0 ^ (α : ℝ))) :=
      ((Real.continuous_rpow_const α.coe_nonneg).tendsto 0).const_mul c
    rw [Real.zero_rpow (by exact_mod_cast hα.ne'), mul_zero] at ht
    exact eventually_nhdsWithin_of_eventually_nhds (ht.eventually (eventually_lt_nhds hlam))
  obtain ⟨R, hRε, hscale, hR⟩ := (h₁.and (h₂.and self_mem_nhdsWithin)).exists
  have hR : 0 < R := hR
  have hRΩ : closedBall x R ⊆ Ω := (closedBall_subset_ball hRε).trans hεΩ
  have hRcl : closedBall x R ⊆ closure Ω := hRΩ.trans subset_closure
  have hBcl : ball x R ⊆ closure Ω := ball_subset_closedBall.trans hRcl
  obtain ⟨C, hC⟩ := hball (L := L) (M := M) hlam (by simpa only [c, mul_assoc] using hscale.le)
    (half_lt_self hR)
  refine ⟨R / 2, half_pos hR, C,
    fun {a} hEll hEll' hL hM {U u N K V} hBU hu hN0 hN1 hN2 hV hK => ?_⟩
  have hxΩ : x ∈ closure Ω := subset_closure hx
  exact (hC (hEll x hxΩ) (hEll' x hxΩ) (fun i j => (hL i j).mono hRcl)
    (fun y hy => hM y (hRcl hy)) (hu.mono (hBcl.trans hBU)) (fun y hy => hN0 y (hBcl hy))
    (fun y hy => hN1 y (hBcl hy)) (fun y hy => hN2 y (hBcl hy)) (hV.mono hBcl)
    (hK.mono (ball_subset_closedBall.trans hRΩ))).mono inter_subset_left

/-- **The estimate near a point of the closure.** At each point `x` of `closure Ω` there are a
radius `ρ > 0` and a constant `C` such that the Hölder constant of `D²u` on
`closedBall x ρ ∩ closure Ω` is at most `C ([L u]_{α; Ω} + N)` for all coefficients and functions as
in the global estimate. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_closure
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ r > 0, ∃ ν : E, ‖ν‖ = 1 ∧ ∃ γ : E → ℝ, ∃ G : ℝ≥0,
      ContDiff ℝ 2 γ ∧ (∀ y (t : ℝ), γ (y + t • ν) = γ y) ∧ (∀ y, ‖fderiv ℝ γ y‖ ≤ G) ∧
      (∀ y, ‖fderiv ℝ (fderiv ℝ γ) y‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧
      Ω ∩ ball x r = {y | γ y < ⟪y, ν⟫_ℝ} ∩ ball x r)
    {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) {x : E} (hx : x ∈ closure Ω) :
    ∃ ρ > 0, ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ y ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a y).toQuadraticForm' ξ) →
      (∀ y ∈ closure Ω, ∀ ξ : E, (a y).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun y => a y i j) (closure Ω)) →
      (∀ y ∈ closure Ω, ∀ i j, |a y i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ y ∈ frontier Ω, u y = 0) →
        (∀ y ∈ closure Ω, |u y| ≤ N) → (∀ y ∈ closure Ω, ‖fderiv ℝ u y‖ ≤ N) →
        (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u y‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun y => ∑ i, ∑ j, a y i j • fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x ρ ∩ closure Ω) := by
  by_cases hxΩ : x ∈ Ω
  · obtain ⟨ρ, hρ, C, hC⟩ := exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_closure_of_mem
      hα hα1 hΩo hxΩ Lam L M hlam (n := n)
    exact ⟨ρ, hρ, C, fun {_} hEll hEll' hL hM {_ _ _ _ _} _ hBU hu _ => hC hEll hEll' hL hM hBU hu⟩
  · have hxf : x ∈ frontier Ω := hΩo.frontier_eq ▸ ⟨hx, hxΩ⟩
    obtain ⟨r, hr, ν, hν, γ, G, hγ, hγν, hG1, hG2, hG3, hΩx⟩ := hbdry x hxf
    exact exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_closure_of_mem_frontier hα hα1
      hΩo hxf hr hν hγ hγν hG1 hG2 hG3 hΩx Lam L M hlam

/-- **The global Schauder estimate on a domain with `C^{2,α}` boundary.** Let `0 < α < 1` and let
`Ω ⊆ ℝ^{n+1}` be a bounded open set which, near each point `x` of its frontier, is the region
`{y | γ y < ⟪y, ν⟫}` above the graph of a function `γ` over the hyperplane `ν^⊥`: `γ` is `C²`,
invariant under translation along the unit vector `ν`, with `‖Dγ‖`, `‖D²γ‖` and the `α`-Hölder
constant of `D²γ` bounded. Let `0 < λ`, `Λ`, `L` and `M` be given. Then there is a constant `C`
with the following property. Let `a` have ellipticity bounds `λ, Λ` at every point of `closure Ω`,
be `α`-Hölder entrywise with constant `L` on `closure Ω` and bounded entrywise by `M` there, and
put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an open set containing `closure Ω`, vanishing on the
frontier of `Ω`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `closure Ω` and with `D²u`
`α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `Ω` with constant `K`, then `D²u`
is `α`-Hölder on `closure Ω` with constant `C (K + N)`.

The constant depends only on `Ω`, the dimension, `α`, `λ`, `Λ`, `L` and `M`: not on the
coefficients `a` beyond the stated bounds, or on `u`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ r > 0, ∃ ν : E, ‖ν‖ = 1 ∧ ∃ γ : E → ℝ, ∃ G : ℝ≥0,
      ContDiff ℝ 2 γ ∧ (∀ y (t : ℝ), γ (y + t • ν) = γ y) ∧ (∀ y, ‖fderiv ℝ γ y‖ ≤ G) ∧
      (∀ y, ‖fderiv ℝ (fderiv ℝ γ) y‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧
      Ω ∩ ball x r = {y | γ y < ⟪y, ν⟫_ℝ} ∩ ball x r)
    {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ y ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a y).toQuadraticForm' ξ) →
      (∀ y ∈ closure Ω, ∀ ξ : E, (a y).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun y => a y i j) (closure Ω)) →
      (∀ y ∈ closure Ω, ∀ i j, |a y i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ y ∈ frontier Ω, u y = 0) →
        (∀ y ∈ closure Ω, |u y| ≤ N) → (∀ y ∈ closure Ω, ‖fderiv ℝ u y‖ ≤ N) →
        (∀ y ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u y‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun y => ∑ i, ∑ j, a y i j • fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closure Ω) := by
  -- Around each point of `closure Ω`, a ball carrying the estimate on its part in `closure Ω`;
  -- the covering lemma assembles these finitely many local estimates.
  choose! ρ hρ C hC using fun x (hx : x ∈ closure Ω) =>
    exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_closure hα hα1 hΩo hbdry Lam L M hlam
      hx
  obtain ⟨A, hA⟩ := hΩ.isCompact_closure.exists_holderOnWith_of_forall_holderOnWith_ball_inter
    hρ C (α := α) (Y := E [×2]→L[ℝ] ℝ)
  exact ⟨A, fun {_} hEll hEll' hL hM {_ _ _ _ _} hU hBU hu hu0 hN0 hN1 hN2 hV hK =>
    hA (fun x hx => (hN2 x hx).trans (by push_cast; exact le_add_of_nonneg_left (by positivity)))
      fun x hx => (hC x hx hEll hEll' hL hM hU hBU hu hu0 hN0 hN1 hN2 hV hK).mono
        (inter_subset_inter_left _ ball_subset_closedBall)⟩

end TauCeti.PDE
