/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.C2HolderBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.CurvedBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.LowerOrder
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Holder.BoundaryInterpolation
import TauCeti.Analysis.Holder.LipschitzDomain
import TauCeti.Analysis.InnerProductSpace.GraphPatch
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.GraphPatch
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Schauder estimate on a bounded domain with `C^{2,α}` boundary

Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary Ω α`): near each point `x` of its frontier, `Ω` is the region
`{z | γ z < ⟪z, ν⟫}` above the graph of a `C^{2,α}` function over a hyperplane `ν^⊥`, that is

`Ω ∩ ball x r = {z | γ z < ⟪z, ν⟫} ∩ ball x r`

for a unit vector `ν`, a radius `r > 0` and a `C²` function `γ` invariant under translation along
`ν`, with `Dγ` and `D²γ` bounded and `D²γ` `α`-Hölder. Such a set is open
(`Set.HasC2HolderBoundary.isOpen`). This file proves the global `C^{2,α}`
estimate up to the boundary for the non-divergence-form operator `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`): there is
a constant `C` such that every `u` that is `C²` near `closure Ω`, vanishes on `∂Ω` and has `|u|`,
`‖Du‖` and `‖D²u‖` bounded by `N` on `closure Ω` satisfies

`[D²u]_{α; closure Ω} ≤ C ([L u]_{α; Ω} + N)`.

The constant depends only on `Ω`, `α`, the ellipticity constants `λ, Λ` of `a` on `closure Ω`,
the Hölder constant `L` and the bound `M` of the entries of `a` there; it does not depend on `a`
beyond these bounds, nor on `u`. This uniformity in the coefficients is what the method of
continuity for the Dirichlet problem uses. As in the local estimates it is assembled from, the
Hölder continuity of `D²u` is assumed qualitatively (with any constant), and the estimate bounds
its Hölder constant.

The interpolation inequalities on `closure Ω`
(`TauCeti.exists_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded`) then remove `‖Du‖`
and `‖D²u‖` from the right side
(`exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_sum_smul_fderiv_fderiv`):
if only `|u| ≤ N` on `closure Ω`, then

`[D²u]_{α; closure Ω} + sup_{closure Ω} ‖Du‖ + sup_{closure Ω} ‖D²u‖ ≤ C ([L u]_{α; Ω} + N)`.

The same estimates hold for the general operator `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + b · ∇u + c u`, with a
drift `b` and a potential `c` that are `α`-Hölder and bounded on `Ω`, the constant now depending
also on their bounds (in the `TauCeti.PDE` namespace,
`exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul` with
the norms of `Du` and `D²u` on the right, and
`exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_add_fderiv_add_mul` with `sup |u|`
alone). No sign condition on `c` is needed.

With `c ≤ 0`, the maximum principle bounds `sup |u|` by a multiple of `sup_Ω |L u|`, and the
estimate becomes an a priori bound by the data
(`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos`). As
in all the estimates here, `u` is `C²` on an open set containing `closure Ω` and vanishes on `∂Ω`,
and `D²u` is assumed `α`-Hölder on `closure Ω` with some constant: the theorem bounds that constant,
it does not prove that `D²u` is Hölder. Under these hypotheses, if `L u` is `α`-Hölder on `Ω` with
constant `K` and bounded there by `F`, then `|u| ≤ C F` on `closure Ω`, and
`[D²u]_{α; closure Ω}`, `sup ‖Du‖` and `sup ‖D²u‖` are at most `C (K + F)`. The constant depends
only on `Ω`, `α` and the bounds on the coefficients, which is the uniform estimate the method of
continuity needs to solve the Dirichlet problem (Gilbarg–Trudinger, Theorem 6.8).

For the principal part (`b = c = 0`) this is the a priori estimate
(`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`)

`|u|_{0; Ω} + |Du|_{0; Ω} + |D²u|_{0; Ω} + [D²u]_{α; Ω} ≤ C (sup_Ω |L u| + [L u]_{α; Ω})`,

Gilbarg–Trudinger's global estimate, Theorem 6.6, for zero boundary values.

## The argument

* **Boundary patches.** At a frontier point `x`, the estimate near a curved boundary
  (`exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_graph`)
  bounds the Hölder constant of `D²u` on `closedBall x ρ ∩ closure Ω` for a small `ρ > 0`. Inside
  `ball x r` the closure of `Ω` is the closed region `{z | γ z ≤ ⟪z, ν⟫}` and the frontier of `Ω`
  is the graph `{z | γ z = ⟪z, ν⟫}` (`TauCeti.inter_closure_eq_inter_setOf_le_inner`,
  `TauCeti.inter_frontier_eq_inter_setOf_inner_eq`), so the hypotheses on `closure Ω` give those
  of the local estimate.
* **The interior.** Finitely many of the balls `ball x ρ` cover the compact frontier of `Ω`, and
  the rest of `closure Ω` is a compact subset `K₀` of `Ω`. The interior estimate on small balls
  (`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`) has
  a constant independent of the centre, so one radius and one constant serve at every point of
  `K₀`.
* **Gluing.** The balls of both kinds form an open cover of the compact set `closure Ω`. Between
  points closer than a Lebesgue number `δ` of the cover the local estimates apply; between points
  farther apart `‖D²u z - D²u w‖ ≤ 2 N ≤ 2 N δ^(-α) ‖z - w‖^α`
  (`lebesgue_number_lemma_of_metric`, `HolderOnWith.of_dist_lt_of_dist_le`).
* **Interpolation.** At a scale `ε ≤ 1`, the interpolation inequalities bound `|u|`, `‖Du‖` and
  `‖D²u‖` on `closure Ω` by `N₁ = (1 + C₂ ε⁻²) N + C₂ H ε^α`, where `H` is the Hölder norm of
  `D²u` on `closure Ω` (`nnHolderNorm`), finite by hypothesis. The first estimate with `N₁` in
  place of `N` gives `H ≤ C₁ (K + N₁)`, and for `ε` so small that `C₁ C₂ ε^α ≤ 1 / 2` the
  multiple of `H` on the right is absorbed into the left side.
* **Lower-order terms.** A domain with Lipschitz graph boundary is a Lipschitz domain
  (`Set.HasLipschitzGraphBoundary.isLipschitzDomain`), so on the bounded domain `Ω` the bounds
  `N` on `u`, `Du` and `D²u` make `u` and `Du` `α`-Hölder with constant a multiple of `N`
  (`Set.IsLipschitzDomain.exists_holderOnWith_of_norm_fderiv_le`,
  `TauCeti.PDE.exists_holderOnWith_and_holderOnWith_fderiv_of_norm_le`). The Hölder constant of
  `b · ∇u + c u` on `Ω` is then a multiple of `N`
  (`TauCeti.PDE.holderOnWith_fderiv_apply_add_mul`), and the estimate for the principal part
  applies to `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = L u - b · ∇u - c u`. The interpolation step then removes the norms of
  `Du` and `D²u` from the right side, as for the principal part.
* **Nonpositive potential.** The interior of `closure Ω` is `Ω`, since a Lipschitz domain is regular
  open (`Set.IsLipschitzDomain.interior_closure`), so the maximum principle for zero boundary values
  (`TauCeti.PDE.abs_le_mul_of_abs_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_eq_zero_frontier`)
  gives `|u| ≤ D sup |L u|` with `D` depending only on `λ`, the bound on `b` and the diameter of
  `Ω`, and the previous estimate applies with `N = D sup |L u|`.
* **The principal part.** The estimates for `∑ᵢⱼ aᵢⱼ ∂ᵢⱼu` in terms of `sup |u|` and of the data are
  the case `b = c = 0` of those with lower-order terms.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`: the
  global Schauder estimate on a bounded domain with `C^{2,α}` boundary, with the norms of `Du` and
  `D²u` on the right.
* `exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_sum_smul_fderiv_fderiv`:
  the same estimate in terms of `[L u]_α` and `sup |u|` alone, with bounds on `‖Du‖` and `‖D²u‖`.
* `exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`:
  the a priori estimate of `u` in `C^{2,α}(closure Ω)` by `L u` in `C^{0,α}(Ω)`.
* `exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul`,
  in the `TauCeti.PDE` namespace: the first estimate with lower-order terms.
* `exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_add_fderiv_add_mul`: the second
  estimate with lower-order terms.
* `exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos`: for
  `c ≤ 0`, the bound of `u` in `C^{2,α}(closure Ω)` by `L u` in `C^{0,α}(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.3, Theorem 3.7 (the bound on `sup |u|`, also for `c ≤ 0`); Section 6.2: Lemma 6.5
  (the boundary estimate) and Theorem 6.6 (the global estimate, obtained from the interior and
  boundary estimates by a finite covering and interpolation), and Section 6.8 (interpolation
  inequalities on domains); the proof of Theorem 6.8 (the a priori estimate of the method of
  continuity).
-/

public section

open Metric Set Filter Topology
open scoped NNReal Matrix InnerProductSpace

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### A boundary patch -/

section Graph

variable {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} {x : EuclideanSpace ℝ (Fin (n + 1))}

/-- **The Schauder estimate on a boundary patch.** At a point `x` of the closure of a set
`Ω` with a boundary patch `ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}`, `γ` of class `C^{2,α}`
and invariant along the unit vector `ν`, there are a radius `ρ > 0` and a constant `C`, depending
only on the patch, `α`, `λ`, `Λ`, `L` and `M`, such that the Hölder constant of `D²u` on
`ball x ρ ∩ closure Ω` is at most `C (K + N)` under the hypotheses of the global estimate. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_ball_inter_closure {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1)
    (hpatch : ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧ ContDiff ℝ 2 γ ∧
      (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ (∀ z, ‖fderiv ℝ γ z‖ ≤ G) ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ γ) z‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ})
    (hx : x ∈ closure Ω) {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) →
        (∀ z ∈ closure Ω, |u z| ≤ N) → (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ N) →
        (∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (ball x ρ ∩ closure Ω) := by
  obtain ⟨ν, γ, G, r, hν, hγ, hγν, hG1, hG2, hG3, hr, hΩ⟩ := hpatch
  obtain ⟨R₀, hR₀, hloc⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_graph
      hα hα1 hν hγ hγν hG1 hG2 hG3 Lam L M hlam
  -- The radii: `R ≤ r / 2` keeps the local estimate inside the patch, and `ρ` is admissible.
  set R : ℝ := min R₀ (r / 2)
  have hR : 0 < R := lt_min hR₀ (half_pos hr)
  have hRr : R < r := (min_le_right _ _).trans_lt (half_lt_self hr)
  set ρ : ℝ := R / (4 * (1 + G) ^ 2) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρR : 2 * (1 + (G : ℝ)) ^ 2 * ρ < R := by
    have h2 : 2 * (1 + (G : ℝ)) ^ 2 * ρ = R / 2 := by
      rw [hρdef]
      field_simp
      ring
    linarith
  have hρr : ρ < r := by
    have h1 : (1 : ℝ) ≤ 2 * (1 + G) ^ 2 := by nlinarith [G.coe_nonneg]
    nlinarith
  obtain ⟨C, hC⟩ := hloc (min_le_left _ _) hρR
  refine ⟨ρ, hρ, C, fun {a} hEll hEll' hL hM {U u N K V} hU hΩU hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  -- Inside the patch, `closure Ω` is the closed region above the graph and `frontier Ω` is the
  -- graph.
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (by rw [hν]; exact one_ne_zero)
  have hcl := Set.ext_iff.1 (inter_closure_eq_inter_setOf_le_inner isOpen_ball hν0
    hγ.continuous.continuousOn hγν hΩ)
  have hfr := Set.ext_iff.1 (inter_frontier_eq_inter_setOf_inner_eq isOpen_ball hν0
    hγ.continuous.continuousOn hγν hΩ)
  have hsub : ball x R ∩ {z | γ z ≤ ⟪z, ν⟫_ℝ} ⊆ closure Ω := fun z hz =>
    ((hcl z).2 ⟨ball_subset_ball hRr.le hz.1, hz.2⟩).2
  have hsub' : closedBall x R ∩ {z | γ z ≤ ⟪z, ν⟫_ℝ} ⊆ closure Ω := fun z hz =>
    ((hcl z).2 ⟨closedBall_subset_ball hRr hz.1, hz.2⟩).2
  -- The open region above the graph lies in `Ω`, and the graph in the frontier of `Ω`.
  have hsubΩ : ball x R ∩ {z | γ z < ⟪z, ν⟫_ℝ} ⊆ Ω := fun z hz => by
    have hz' : z ∈ ball x r ∩ Ω := by
      rw [hΩ]
      exact ⟨ball_subset_ball hRr.le hz.1, hz.2⟩
    exact hz'.2
  have hbdry : ∀ z ∈ ball x R, ⟪z, ν⟫_ℝ = γ z → u z = 0 := fun z hz heq =>
    hu0 z ((hfr z).2 ⟨ball_subset_ball hRr.le hz, heq⟩).2
  have hest := hC (a := a) (x₀ := x)
    ((hcl x).1 ⟨mem_ball_self hr, hx⟩).2 (hEll x hx)
    (hEll' x hx) (fun i j => (hL i j).mono hsub') (fun z hz => hM z (hsub hz)) hU
    (hsub.trans hΩU) hu hbdry (fun z hz => hN0 z (hsub hz)) (fun z hz => hN1 z (hsub hz))
    (fun z hz => hN2 z (hsub hz)) (hV.mono hsub) (hK.mono hsubΩ)
  -- `ball x ρ ∩ closure Ω` lies in the region where the local estimate holds.
  exact hest.mono fun z hz => ⟨ball_subset_closedBall hz.1,
    ((hcl z).1 ⟨ball_subset_ball hρr.le hz.1, hz.2⟩).2⟩

end Graph

/-! ### The interior -/

/-- **The Schauder estimate near a compact subset of `Ω`.** For a compact subset `K₀` of an open
set `Ω` there are a radius `ρ > 0` and a constant `C`, depending only on `K₀`, `Ω`, `α`, `λ`, `Λ`,
`L` and `M`, such that the Hölder constant of `D²u` on `ball y ρ` is at most `C (K + N)` for every
`y ∈ K₀`, under hypotheses on `Ω` like those of the global estimate. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_ball_of_isCompact {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {Ω K₀ : Set E} (hΩo : IsOpen Ω) (hK₀ : IsCompact K₀) (hK₀Ω : K₀ ⊆ Ω)
    {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ z ∈ Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) Ω) →
      (∀ z ∈ Ω, ∀ i j, |a z i j| ≤ M) →
      ∀ {u : E → ℝ} {N K V : ℝ≥0}, ContDiffOn ℝ 2 u Ω →
        (∀ z ∈ Ω, |u z| ≤ N) → (∀ z ∈ Ω, ‖fderiv ℝ u z‖ ≤ N) →
        (∀ z ∈ Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) Ω →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        ∀ y ∈ K₀, HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (ball y ρ) := by
  obtain ⟨C₀, -, hint⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  obtain ⟨δ, hδ, hδΩ⟩ := hK₀.exists_cthickening_subset_open hΩo hK₀Ω
  -- A radius `R ≤ δ` satisfying the scale condition of the interior estimate.
  set κ : ℝ := 2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
    ((1 + 2 ^ (α : ℝ)) * L) with hκdef
  obtain ⟨R₁, hR₁, -, hR₁κ⟩ := Real.exists_pos_le_one_mul_rpow_le κ (α := α) hα hlam
  set R : ℝ := min δ R₁
  have hR : 0 < R := lt_min hδ hR₁
  have hsmall : 2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
      ((1 + 2 ^ (α : ℝ)) * L * R ^ (α : ℝ)) ≤ lam := by
    have hRα : R ^ (α : ℝ) ≤ R₁ ^ (α : ℝ) :=
      Real.rpow_le_rpow hR.le (min_le_right _ _) α.coe_nonneg
    calc _ = κ * R ^ (α : ℝ) := by rw [hκdef]; ring
      _ ≤ lam := by
        rcases le_or_gt κ 0 with hκ | hκ
        · nlinarith [Real.rpow_nonneg hR.le (α : ℝ)]
        · exact (mul_le_mul_of_nonneg_left hRα hκ.le).trans hR₁κ
  obtain ⟨C, hC⟩ := hint hlam hsmall (half_lt_self hR)
  refine ⟨R / 2, half_pos hR, C,
    fun {a} hEll hEll' hL hM {u N K V} hu hN0 hN1 hN2 hV hK y hy => ?_⟩
  -- The closed ball of radius `R` about a point of `K₀` lies in `Ω`.
  have hB : closedBall y R ⊆ Ω :=
    ((closedBall_subset_cthickening hy R).trans (cthickening_mono (min_le_left _ _) K₀)).trans hδΩ
  have hB' : ball y R ⊆ Ω := ball_subset_closedBall.trans hB
  exact (hC (hEll y (hK₀Ω hy)) (hEll' y (hK₀Ω hy)) (fun i j => (hL i j).mono hB)
    (fun z hz => hM z (hB hz)) (hu.mono hB') (fun z hz => hN0 z (hB' hz))
    (fun z hz => hN1 z (hB' hz)) (fun z hz => hN2 z (hB' hz)) (hV.mono hB')
    (hK.mono hB')).mono ball_subset_closedBall

/-! ### The global estimate -/

/-- **The Schauder estimate at a small scale.** Under the hypotheses of the global estimate there
are a scale `δ > 0` and a constant `A`, depending only on `Ω`, `α`, `λ`, `Λ`, `L` and `M`, such
that `‖D²u z - D²u w‖ ≤ A (K + N) ‖z - w‖^α` for all `z, w ∈ closure Ω` closer than `δ`. The scale
is a Lebesgue number of a cover of `closure Ω` by boundary patch balls and interior balls. -/
private theorem exists_dist_iteratedFDeriv_two_le_of_dist_lt {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      ContDiff ℝ 2 γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ (∀ z, ‖fderiv ℝ γ z‖ ≤ G) ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ γ) z‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ})
    {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ A : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) →
        (∀ z ∈ closure Ω, |u z| ≤ N) → (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ N) →
        (∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        ∀ z ∈ closure Ω, ∀ w ∈ closure Ω, dist z w < δ →
          dist (iteratedFDeriv ℝ 2 u z) (iteratedFDeriv ℝ 2 u w) ≤
            (A * (K + N) : ℝ≥0) * dist z w ^ (α : ℝ) := by
  have hcl : IsCompact (closure Ω) := hΩ.isCompact_closure
  -- Boundary patches: a radius and a constant at each frontier point.
  have hloc := fun x (hx : x ∈ frontier Ω) =>
    exists_holderOnWith_iteratedFDeriv_two_ball_inter_closure hα hα1 (hbdry x hx)
      (frontier_subset_closure hx) Lam L M hlam
  choose! ρ hρ C hC using hloc
  -- Finitely many patch balls cover the compact frontier.
  obtain ⟨t, htfr, hcov⟩ :=
    (hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure).elim_nhds_subcover
      (fun x => ball x (ρ x)) fun x hx => ball_mem_nhds x (hρ x hx)
  -- The rest of `closure Ω` is a compact subset of `Ω`, handled by the interior estimate.
  set K₀ : Set E := closure Ω \ ⋃ x ∈ t, ball x (ρ x)
  have hK₀ : IsCompact K₀ := hcl.diff (isOpen_biUnion fun x _ => isOpen_ball)
  have hK₀Ω : K₀ ⊆ Ω := fun z hz => by
    by_contra hzΩ
    exact hz.2 (hcov (by rw [hΩo.frontier_eq]; exact ⟨hz.1, hzΩ⟩))
  obtain ⟨ρ₀, hρ₀, C₀, hC₀⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_ball_of_isCompact hα hα1 hΩo hK₀ hK₀Ω Lam L M hlam
  -- The balls of both kinds cover `closure Ω`; take a Lebesgue number `δ` of this cover.
  set c : t ⊕ K₀ → Set E := Sum.elim (fun x => ball (x : E) (ρ x)) (fun y => ball (y : E) ρ₀)
  have hcopen : ∀ i, IsOpen (c i) := by rintro (x | y) <;> exact isOpen_ball
  have hccov : closure Ω ⊆ ⋃ i, c i := fun z hz => by
    by_cases hzt : z ∈ ⋃ x ∈ t, ball x (ρ x)
    · obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 hzt
      exact mem_iUnion.2 ⟨Sum.inl ⟨x, hxt⟩, hzx⟩
    · exact mem_iUnion.2 ⟨Sum.inr ⟨z, hz, hzt⟩, mem_ball_self hρ₀⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hcl hcopen hccov
  lift δ to ℝ≥0 using hδ.le
  set A : ℝ≥0 := ∑ x ∈ t, C x + C₀
  refine ⟨δ, NNReal.coe_pos.1 hδ, A,
    fun {a} hEll hEll' hL hM {U u N K V} hU hΩU hu hu0 hN0 hN1 hN2 hV hK z hz w hw hzw => ?_⟩
  -- Each piece of the cover carries the Hölder bound with constant `A (K + N)`.
  have hpiece : ∀ i, HolderOnWith (A * (K + N)) α (iteratedFDeriv ℝ 2 u) (c i ∩ closure Ω) := by
    rintro (⟨x, hxt⟩ | ⟨y, hy⟩)
    · refine (hC x (htfr x hxt) hEll hEll' hL hM hU hΩU hu hu0 hN0 hN1 hN2 hV hK).mono_const ?_
      gcongr
      exact (Finset.single_le_sum (fun _ _ => zero_le) hxt).trans le_self_add
    · have hΩcl : Ω ⊆ closure Ω := subset_closure
      refine ((hC₀ (fun z hz => hEll z (hΩcl hz)) (fun z hz => hEll' z (hΩcl hz))
        (fun i j => (hL i j).mono hΩcl) (fun z hz => hM z (hΩcl hz)) (hu.mono (hΩcl.trans hΩU))
        (fun z hz => hN0 z (hΩcl hz)) (fun z hz => hN1 z (hΩcl hz))
        (fun z hz => hN2 z (hΩcl hz)) (hV.mono hΩcl) hK y hy).mono
        inter_subset_left).mono_const ?_
      gcongr
      exact le_add_self
  -- Points of `closure Ω` closer than `δ` lie in a common piece.
  obtain ⟨i, hi⟩ := hleb z hz
  exact (hpiece i).dist_le ⟨hi (mem_ball_self hδ), hz⟩
    ⟨hi (mem_ball.2 (by rw [dist_comm]; exact hzw)), hw⟩

/-- **The global Schauder estimate on a bounded domain with `C^{2,α}` boundary.** Let
`0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary`): near each point `z` of its frontier,
`Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫} ∩ ball z r` for a unit vector `ν`, a radius `r > 0` and a `C²`
function `γ` invariant under translation along `ν`, with `‖Dγ‖ ≤ G`, `‖D²γ‖ ≤ G` and `D²γ`
`α`-Hölder with constant `G`. Such a set is open (`Set.HasC2HolderBoundary.isOpen`). Let
`0 < λ`, `Λ`, `L` and `M` be given. Then there is a constant `C` with the following property.
Let `a` have ellipticity bounds `λ, Λ` at every point of `closure Ω`, and entries `α`-Hölder
with constant `L` and bounded by `M` on `closure Ω`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on
an open set containing `closure Ω`,
vanishing on the frontier of `Ω`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `closure Ω` and
with `D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `Ω` with constant `K`,
then `D²u` is `α`-Hölder on `closure Ω` with constant `C (K + N)`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L` and `M`: not on `a` beyond the stated bounds,
nor on `u` (Gilbarg–Trudinger, Theorem 6.6, with the norms of `Du` and `D²u` on the right). -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω)
    (hbdry : Ω.HasC2HolderBoundary α) {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) →
        (∀ z ∈ closure Ω, |u z| ≤ N) → (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ N) →
        (∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closure Ω) := by
  have hbdry' : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      ContDiff ℝ 2 γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ (∀ z, ‖fderiv ℝ γ z‖ ≤ G) ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ γ) z‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ} := by
    intro x hx
    obtain ⟨ν, γ, G, r, hν, hγ, hγν, hG1, hG2, hG3, hr, hΩr⟩ :=
      Set.hasC2HolderBoundary_iff.1 hbdry x hx
    exact ⟨ν, γ, G, r, hν, hγ, hγν, hG1, hG2, hG3, hr, by rw [inter_comm, hΩr, inter_comm]⟩
  obtain ⟨δ, hδ, A, hA⟩ :=
    exists_dist_iteratedFDeriv_two_le_of_dist_lt hα hα1 hbdry.isOpen hΩ hbdry' Lam L M hlam
  refine ⟨A + 2 * δ ^ (-(α : ℝ)),
    fun {a} hEll hEll' hL hM {U u N K V} hU hΩU hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  -- Values of `D²u` on `closure Ω` lie within `2 N` of each other.
  have hfar : ∀ z ∈ closure Ω, ∀ w ∈ closure Ω,
      dist (iteratedFDeriv ℝ 2 u z) (iteratedFDeriv ℝ 2 u w) ≤ ((2 * N : ℝ≥0) : ℝ) := by
    intro z hz w hw
    push_cast
    linarith [hN2 z hz, hN2 w hw,
      dist_le_norm_add_norm (iteratedFDeriv ℝ 2 u z) (iteratedFDeriv ℝ 2 u w)]
  refine (HolderOnWith.of_dist_lt_of_dist_le hδ
    (hA hEll hEll' hL hM hU hΩU hu hu0 hN0 hN1 hN2 hV hK) hfar).mono_const ?_
  calc A * (K + N) + 2 * N * δ ^ (-(α : ℝ))
      ≤ A * (K + N) + 2 * (K + N) * δ ^ (-(α : ℝ)) := by
        gcongr
        exact le_add_self
    _ = (A + 2 * δ ^ (-(α : ℝ))) * (K + N) := by ring

/-- **The lower-order bound from interpolation.** Under the hypotheses of the global estimate, let
`C₂` and `ε₀` be the constants of the interpolation inequalities on `closure Ω`, let
`0 < ε ≤ min ε₀ 1`, and let `H` be a Hölder constant of `D²u` on `closure Ω`. If `|u| ≤ N` on
`closure Ω`, then `|u|`, `‖Du‖` and `‖D²u‖` are bounded on `closure Ω` by
`N + C₂ ε⁻² N + C₂ H ε^α`. -/
private theorem forall_norm_le_of_interpolation {α C₂ : ℝ≥0} {Ω U : Set E} {u : E → ℝ}
    {ε ε₀ : ℝ} {N H : ℝ≥0}
    (hint : ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {U : Set E} {u : E → ℝ} {M : ℝ} {H : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ closure Ω, ‖u z‖ ≤ M) →
        HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closure Ω) → ∀ z ∈ closure Ω,
          ‖fderiv ℝ u z‖ ≤ C₂ * (M / ε + H * ε ^ (1 + (α : ℝ))) ∧
            ‖iteratedFDeriv ℝ 2 u z‖ ≤ C₂ * (M / ε ^ 2 + H * ε ^ (α : ℝ)))
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hε1 : ε ≤ 1) (hU : IsOpen U) (hΩU : closure Ω ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hN : ∀ z ∈ closure Ω, |u z| ≤ N)
    (hH : HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closure Ω)) :
    ∀ z ∈ closure Ω, |u z| ≤ N + C₂ / ε ^ 2 * N + C₂ * H * ε ^ (α : ℝ) ∧
      ‖fderiv ℝ u z‖ ≤ N + C₂ / ε ^ 2 * N + C₂ * H * ε ^ (α : ℝ) ∧
      ‖iteratedFDeriv ℝ 2 u z‖ ≤ N + C₂ / ε ^ 2 * N + C₂ * H * ε ^ (α : ℝ) := by
  intro z hz
  obtain ⟨h1, h2⟩ := hint ε hε hεε₀ hU hΩU hu (fun z hz => by rw [Real.norm_eq_abs]; exact hN z hz)
    hH z hz
  have hc : 0 ≤ C₂ / ε ^ 2 * N := by positivity
  have hHε : 0 ≤ C₂ * H * ε ^ (α : ℝ) := by positivity
  -- At scale `ε ≤ 1`, `N / ε ≤ N / ε²` and `ε^(1 + α) ≤ ε^α`.
  have hNε : (N : ℝ) / ε ≤ N / ε ^ 2 := div_le_div_of_nonneg_left N.coe_nonneg (by positivity)
    (by nlinarith)
  have hεα : ε ^ (1 + (α : ℝ)) ≤ ε ^ (α : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hC : (C₂ : ℝ) * (N / ε ^ 2 + H * ε ^ (α : ℝ)) = C₂ / ε ^ 2 * N + C₂ * H * ε ^ (α : ℝ) := by
    ring
  refine ⟨by linarith [hN z hz], h1.trans ?_, h2.trans (by rw [hC]; linarith [N.coe_nonneg])⟩
  calc (C₂ : ℝ) * (N / ε + H * ε ^ (1 + (α : ℝ)))
      ≤ C₂ * (N / ε ^ 2 + H * ε ^ (α : ℝ)) := by gcongr
    _ ≤ _ := by rw [hC]; linarith [N.coe_nonneg]

/-- **Absorption.** If `H ≤ C₁ (K + N₁)` for `N₁ = N + c N + C₂ H e` with `C₁ C₂ e ≤ 1 / 2`,
`0 ≤ c` and `e ≤ 1`, then `H ≤ A (K + N)` and `N₁ ≤ (1 + A + c + C₂ A) (K + N)`, where
`A = 2 C₁ (2 + c)`. -/
private theorem le_mul_add_and_le_mul_add_of_le_mul_add {C₁ C₂ H K N : ℝ≥0} {c e : ℝ} (hc : 0 ≤ c)
    (he : e ≤ 1) (hC : C₁ * C₂ * e ≤ 1 / 2) (hH : (H : ℝ) ≤ C₁ * (K + (N + c * N + C₂ * H * e))) :
    (H : ℝ) ≤ 2 * C₁ * (2 + c) * (K + N) ∧
      N + c * N + C₂ * H * e ≤ (1 + 2 * C₁ * (2 + c) + c + C₂ * (2 * C₁ * (2 + c))) * (K + N) := by
  set A : ℝ := 2 * C₁ * (2 + c)
  -- The shared absorption step, with `K₀ = K + c N + C₂ H e`, `γ = 1 + c` and `β = C₂ / 2`.
  have hHA : (H : ℝ) ≤ A * (K + N) := by
    have hHle : (H : ℝ) ≤ C₁ * ((K + c * N + C₂ * H * e) + N) := hH.trans_eq (by ring)
    have habs : 2 * C₁ * (C₂ / 2) * e * H ≤ 1 / 2 * (H : ℝ) :=
      calc 2 * C₁ * (C₂ / 2) * e * H = C₁ * C₂ * e * H := by ring
        _ ≤ 1 / 2 * H := mul_le_mul_of_nonneg_right hC H.coe_nonneg
    exact (hHle.trans (mul_add_le_two_mul_one_add_mul_add C₁.coe_nonneg K.coe_nonneg
      N.coe_nonneg (by linarith : (0 : ℝ) ≤ 1 + c) (by ring) hHle habs)).trans_eq
        (by simp only [A]; ring)
  refine ⟨hHA, ?_⟩
  have h1 : (C₂ : ℝ) * H * e ≤ C₂ * (A * (K + N)) := by
    calc (C₂ : ℝ) * H * e ≤ C₂ * H := mul_le_of_le_one_right (by positivity) he
      _ ≤ C₂ * (A * (K + N)) := by gcongr
  have hA : 0 ≤ A * (K + N) := by positivity
  have hcK : 0 ≤ c * K := by positivity
  have hexp : (1 + A + c + C₂ * A) * (K + N) =
      (K + N) + A * (K + N) + c * K + c * N + C₂ * (A * (K + N)) := by ring
  rw [hexp]
  linarith [K.coe_nonneg]

/-- **Absorbing the lower-order norms by interpolation.** Let `Ω` be a bounded set with `C^{2,α}`
boundary and `C₁` a constant. Then there is a constant `C`, depending only on `Ω`, `α` and `C₁`,
with the following property. Let `u` be `C²` on an open set containing `closure Ω`, with `|u| ≤ N`
on `closure Ω` and with `D²u` `α`-Hölder there (with any constant). If `D²u` is `α`-Hölder on
`closure Ω` with constant `C₁ (K + N₁)` whenever `N₁` bounds `|u|`, `‖Du‖` and `‖D²u‖` there, then
it is `α`-Hölder with constant `C (K + N)`, and `‖Du‖` and `‖D²u‖` are bounded by `C (K + N)` on
`closure Ω`. -/
private theorem exists_holderOnWith_and_norm_le_of_forall_holderOnWith {α : ℝ≥0} (hα : 0 < α)
    {Ω : Set E} (hΩ : Bornology.IsBounded Ω) (hbdry : Ω.HasC2HolderBoundary α) (C₁ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
      ContDiffOn ℝ 2 u U → (∀ z ∈ closure Ω, |u z| ≤ N) →
      HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
      (∀ N₁ : ℝ≥0, (∀ z ∈ closure Ω, |u z| ≤ N₁) → (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ N₁) →
        (∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ N₁) →
        HolderOnWith (C₁ * (K + N₁)) α (iteratedFDeriv ℝ 2 u) (closure Ω)) →
      HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closure Ω) ∧
        (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ C * (K + N)) ∧
        ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (K + N) := by
  -- The boundary patches are Lipschitz graphs, so the interpolation inequalities hold.
  obtain ⟨C₂, ε₀, hε₀, hint⟩ := exists_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded
    (F := ℝ) (Set.hasLipschitzGraphBoundary_iff.1 hbdry.hasLipschitzGraphBoundary) hΩ α
  -- The interpolation scale `ε ≤ min ε₀ 1`, with `C₁ C₂ ε^α ≤ 1 / 2`.
  obtain ⟨ε₁, hε₁, hε₁1, hε₁C⟩ := Real.exists_pos_le_one_mul_rpow_le (C₁ * C₂)
    (NNReal.coe_pos.2 hα) (by norm_num : (0 : ℝ) < 1 / 2)
  set ε := min ε₁ ε₀
  have hε : 0 < ε := lt_min hε₁ hε₀
  have hεα : ε ^ (α : ℝ) ≤ 1 :=
    Real.rpow_le_one hε.le ((min_le_left _ _).trans hε₁1) α.coe_nonneg
  have hεC : C₁ * C₂ * ε ^ (α : ℝ) ≤ 1 / 2 := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hε.le (min_le_left _ _) α.coe_nonneg) (by positivity)).trans hε₁C
  set c : ℝ := C₂ / ε ^ 2
  have hc : 0 ≤ c := by positivity
  set A : ℝ := 2 * C₁ * (2 + c)
  refine ⟨(1 + A + c + C₂ * A).toNNReal, fun {U u N K V} hU hΩU hu hN hV hest => ?_⟩
  -- The Hölder constant `H` of `D²u` on `closure Ω`, the smallest one.
  set H := nnHolderNorm α ((closure Ω).domRestrict (iteratedFDeriv ℝ 2 u))
  have hH : HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closure Ω) :=
    HolderWith.restrict_iff.1 hV.holderWith.memHolder.holderWith
  -- The common bound `N₁ = (1 + c) N + C₂ H ε^α` of `|u|`, `‖Du‖` and `‖D²u‖`.
  have hb := forall_norm_le_of_interpolation hint hε (min_le_right _ _)
    ((min_le_left _ _).trans hε₁1) hU hΩU hu hN hH
  set N₁ : ℝ := N + c * N + C₂ * H * ε ^ (α : ℝ)
  have hN₁ : 0 ≤ N₁ := by positivity
  have hHN : H ≤ C₁ * (K + N₁.toNNReal) :=
    (hest N₁.toNNReal (fun z hz => (hb z hz).1.trans (Real.le_coe_toNNReal _))
      (fun z hz => (hb z hz).2.1.trans (Real.le_coe_toNNReal _))
      (fun z hz => (hb z hz).2.2.trans (Real.le_coe_toNNReal _))).holderWith.nnholderNorm_le
  have h : (H : ℝ) ≤ C₁ * (K + N₁) := by
    have : (H : ℝ) ≤ ((C₁ * (K + N₁.toNNReal) : ℝ≥0) : ℝ) := by exact_mod_cast hHN
    rwa [NNReal.coe_mul, NNReal.coe_add, Real.coe_toNNReal _ hN₁] at this
  obtain ⟨hHA, hN₁le⟩ := le_mul_add_and_le_mul_add_of_le_mul_add hc hεα hεC h
  have hC : (1 + A + c + C₂ * A) * (K + N) ≤ ((1 + A + c + C₂ * A).toNNReal : ℝ) * (K + N) :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity)
  refine ⟨hH.mono_const ?_, fun z hz => (hb z hz).2.1.trans (hN₁le.trans hC),
    fun z hz => (hb z hz).2.2.trans (hN₁le.trans hC)⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_add]
  have hCA : 0 ≤ C₂ * A := by positivity
  exact hHA.trans ((mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans hC)

/-! ### Lower-order terms -/

/-- On a bounded domain `Ω` with Lipschitz graph boundary, a function `φ` that is `C²` near
`closure Ω` with `|φ|`, `‖Dφ‖` and `‖D²φ‖` bounded by `N` there has `φ` and `Dφ` `α`-Hölder on `Ω`
with constant `C (N + N)`, for `α ≤ 1` and a constant `C` depending only on `Ω` and `α`, since `Ω`
is a Lipschitz domain (`Set.IsLipschitzDomain.exists_holderOnWith_of_norm_fderiv_le`). -/
theorem exists_holderOnWith_and_holderOnWith_fderiv_of_norm_le {α : ℝ≥0} (hα1 : α ≤ 1)
    {Ω : Set E} (hΩ : Bornology.IsBounded Ω) (hbdry : Ω.HasLipschitzGraphBoundary) :
    ∃ C : ℝ≥0, ∀ {U : Set E} {φ : E → ℝ} {N : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
      ContDiffOn ℝ 2 φ U → (∀ z ∈ closure Ω, |φ z| ≤ N) →
      (∀ z ∈ closure Ω, ‖fderiv ℝ φ z‖ ≤ N) → (∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 φ z‖ ≤ N) →
      HolderOnWith (C * (N + N)) α φ Ω ∧ HolderOnWith (C * (N + N)) α (fderiv ℝ φ) Ω := by
  obtain ⟨C, hC⟩ := (hbdry.isLipschitzDomain
    finrank_euclideanSpace_fin).exists_holderOnWith_of_norm_fderiv_le hΩ hα1
  refine ⟨C, fun {U φ N} hU hΩU hφ h0 h1 h2 => ?_⟩
  have hcd : ∀ z ∈ Ω, ContDiffAt ℝ 2 φ z := fun z hz =>
    hφ.contDiffAt (hU.mem_nhds (hΩU (subset_closure hz)))
  constructor
  · exact hC (fun z hz => (hcd z hz).differentiableAt (by norm_num))
      (fun z hz => by rw [Real.norm_eq_abs]; exact h0 z (subset_closure hz))
      fun z hz => h1 z (subset_closure hz)
  · refine hC (fun z hz => ((hcd z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) (fun z hz => h1 z (subset_closure hz)) fun z hz => ?_
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact h2 z (subset_closure hz)

/-- **The global Schauder estimate with lower-order terms on a bounded domain with `C^{2,α}`
boundary.** Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary`), as in
`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`. Let
`0 < λ`, `Λ`, `L`, `M` and `B` be given. Then there is a constant `C` with the following property.
Let `a` have ellipticity bounds `λ, Λ` at every point of `closure Ω`, and entries `α`-Hölder with
constant `L` and bounded by `M` on `closure Ω`; let the drift `b` and the potential `c` be
`α`-Hölder with constant `B` and bounded by `B` on `Ω`. Put
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu + b · ∇u + c u`. Let `u` be `C²` on an open set containing `closure Ω`,
vanishing on the frontier of `Ω`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `closure Ω` and
with `D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `Ω` with constant `K`,
then `D²u` is `α`-Hölder on `closure Ω` with constant `C (K + N)`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L`, `M` and `B`: not on the coefficients beyond
these bounds, nor on `u`. No sign condition on `c` is needed. This is Gilbarg–Trudinger,
Theorem 6.6, for zero boundary values, with the norms of `Du` and `D²u` on the right. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω)
    (hbdry : Ω.HasC2HolderBoundary α) {lam : ℝ} (Lam : ℝ) (L M B : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      HolderOnWith B α b Ω → (∀ z ∈ Ω, ‖b z‖ ≤ B) →
      HolderOnWith B α c Ω → (∀ z ∈ Ω, |c z| ≤ B) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) →
        (∀ z ∈ closure Ω, |u z| ≤ N) → (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ N) →
        (∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u z (b z) +
            c z * u z) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closure Ω) := by
  obtain ⟨C₀, hC₀⟩ := exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv
    hα hα1 hΩ hbdry Lam L M hlam
  -- `Ω` is a bounded Lipschitz domain, so bounds on a function and its derivatives make it and
  -- its derivative `α`-Hölder on `Ω`.
  obtain ⟨C₁, hC₁⟩ :=
    exists_holderOnWith_and_holderOnWith_fderiv_of_norm_le hα1.le hΩ hbdry.hasLipschitzGraphBoundary
  set P : ℝ≥0 := 2 * B + 4 * B * C₁
  refine ⟨C₀ * (1 + P), fun {a b c} hEll hEll' hL hM hHb hb hHc hc {U u N K V} hU hΩU hu hu0
    hN0 hN1 hN2 hV hK => ?_⟩
  have hΩcl : Ω ⊆ closure Ω := subset_closure
  -- `u` and `Du` are `α`-Hölder on `Ω` with constant `2 C₁ N`.
  obtain ⟨hHu, hHDu⟩ := hC₁ hU hΩU hu hN0 hN1 hN2
  -- The principal part `L u - (b · ∇u + c u)` is `α`-Hölder on `Ω` with constant `K + N P`.
  have hlow := holderOnWith_fderiv_apply_add_mul hHu hHDu (fun z hz => hN0 z (hΩcl hz))
    (fun z hz => hN1 z (hΩcl hz)) hHb hb hHc hc
  have hprin : HolderOnWith (K + N * P) α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω := by
    have h := hK.sub hlow
    simp only [Pi.sub_def, add_sub_add_right_eq_sub, add_sub_cancel_right] at h
    exact h.mono_const (le_of_eq (by ring))
  refine (hC₀ hEll hEll' hL hM hU hΩU hu hu0 hN0 hN1 hN2 hV hprin).mono_const ?_
  calc C₀ * (K + N * P + N) ≤ C₀ * ((1 + P) * (K + N)) := by
        gcongr
        calc K + N * P + N ≤ K + N * P + N + K * P := le_self_add
          _ = (1 + P) * (K + N) := by ring
    _ = C₀ * (1 + P) * (K + N) := by ring

/-- **The global Schauder estimate with lower-order terms on a bounded domain with `C^{2,α}`
boundary, in terms of `sup |u|`.** Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded set with
`C^{2,α}` boundary (`Set.HasC2HolderBoundary`). Let `0 < λ`, `Λ`, `L`, `M` and `B` be given. Then
there is a constant `C` with the following property. Let `a` have ellipticity bounds `λ, Λ` at every
point of `closure Ω`, and entries `α`-Hölder with constant `L` and bounded by `M` on `closure Ω`;
let the drift `b` and the potential `c` be `α`-Hölder with constant `B` and bounded by `B` on `Ω`.
Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu + b · ∇u + c u`. Let `u` be `C²` on an open set containing `closure Ω`,
vanishing on the frontier of `Ω`, with `|u| ≤ N` on `closure Ω` and with `D²u` `α`-Hölder there
(with any constant). If `L u` is `α`-Hölder on `Ω` with constant `K`, then `D²u` is `α`-Hölder on
`closure Ω` with constant `C (K + N)`, and `‖Du‖` and `‖D²u‖` are bounded by `C (K + N)` on
`closure Ω`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L`, `M` and `B`, and no sign condition on `c` is
needed (Gilbarg–Trudinger, Theorem 6.6, for zero boundary values). -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_add_fderiv_add_mul
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω)
    (hbdry : Ω.HasC2HolderBoundary α) {lam : ℝ} (Lam : ℝ) (L M B : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      HolderOnWith B α b Ω → (∀ z ∈ Ω, ‖b z‖ ≤ B) →
      HolderOnWith B α c Ω → (∀ z ∈ Ω, |c z| ≤ B) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) →
        (∀ z ∈ closure Ω, |u z| ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u z (b z) +
            c z * u z) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closure Ω) ∧
          (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ C * (K + N)) ∧
          ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (K + N) := by
  obtain ⟨C₁, hC₁⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul
      hα hα1 hΩ hbdry Lam L M B hlam
  obtain ⟨C, hC⟩ := exists_holderOnWith_and_norm_le_of_forall_holderOnWith hα hΩ hbdry C₁
  exact ⟨C, fun {a b c} hEll hEll' hL hM hHb hb hHc hc {U u N K V} hU hΩU hu hu0 hN hV hK =>
    hC hU hΩU hu hN hV fun _ h0 h1 h2 =>
      hC₁ hEll hEll' hL hM hHb hb hHc hc hU hΩU hu hu0 h0 h1 h2 hV hK⟩

/-! ### Nonpositive potential -/

/-- **The global Schauder estimate for a nonpositive potential.** Let `0 < α < 1` and let
`Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary (`Set.HasC2HolderBoundary`). Let `0 < λ`,
`Λ`, `L`, `M` and `B` be given. Then there is a constant `C` with the following property. Let `a`
have ellipticity bounds `λ, Λ` at every point of `closure Ω`, and entries `α`-Hölder with constant
`L` and bounded by `M` on `closure Ω`; let the drift `b` and the potential `c` be `α`-Hölder with
constant `B` and bounded by `B` on `Ω`, and let `c ≤ 0` on `Ω`. Put
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu + b · ∇u + c u`. Let `u` be `C²` on an open set containing `closure Ω`,
vanishing on the frontier of `Ω`, with `D²u` `α`-Hölder on `closure Ω` (with any constant). If
`L u` is `α`-Hölder on `Ω` with constant `K` and bounded there by `F`, then on `closure Ω`

* `|u| ≤ C F`,
* `D²u` is `α`-Hölder with constant `C (K + F)`,
* `‖Du‖` and `‖D²u‖` are bounded by `C (K + F)`.

So the `C^{2,α}(closure Ω)` norm of `u` is bounded by `C` times the `C^{0,α}(Ω)` norm of `L u`, with
`C` depending only on `Ω`, `α`, `λ`, `Λ`, `L`, `M` and `B`, not on the coefficients beyond these
bounds. This is the a priori estimate of the method of continuity for the Dirichlet problem
(Gilbarg–Trudinger, Theorem 6.6 for zero boundary values, with `sup |u|` bounded by the maximum
principle, Theorem 3.7). The sign condition `c ≤ 0` cannot be dropped: `u = sin x` on `(0, π)`
vanishes on the boundary and solves `u'' + u = 0`. -/
theorem
    exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω)
    (hbdry : Ω.HasC2HolderBoundary α) {lam : ℝ} (Lam : ℝ) (L M B : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      HolderOnWith B α b Ω → (∀ z ∈ Ω, ‖b z‖ ≤ B) →
      HolderOnWith B α c Ω → (∀ z ∈ Ω, |c z| ≤ B) → (∀ z ∈ Ω, c z ≤ 0) →
      ∀ {U : Set E} {u : E → ℝ} {K F V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u z (b z) +
            c z * u z) Ω →
        (∀ z ∈ Ω, |∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ u z (b z) + c z * u z| ≤ F) →
        (∀ z ∈ closure Ω, |u z| ≤ C * F) ∧
          HolderOnWith (C * (K + F)) α (iteratedFDeriv ℝ 2 u) (closure Ω) ∧
          (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ C * (K + F)) ∧
          ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (K + F) := by
  obtain ⟨C₁, hC₁⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_add_fderiv_add_mul hα hα1 hΩ
      hbdry Lam L M B hlam
  -- A Lipschitz domain is the interior of its closure.
  have hint : interior (closure Ω) = Ω :=
    (hbdry.hasLipschitzGraphBoundary.isLipschitzDomain finrank_euclideanSpace_fin).interior_closure
  -- The constant `D` of the maximum principle, `|u| ≤ D F`.
  set D : ℝ≥0 := ((Real.exp ((B / lam + 1) * Metric.diam (closure Ω)) - 1) / lam).toNNReal
  refine ⟨D + C₁ * (1 + D), fun {a b c} hEll hEll' hL hM hHb hb hHc hc hc0 {U u K F V} hU hΩU hu
    hu0 hV hK hF => ?_⟩
  have hD : ∀ z ∈ closure Ω, |u z| ≤ D * F := fun z hz =>
    (abs_le_mul_of_abs_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_eq_zero_frontier hΩ hint
      hlam (fun _ hx => hEll _ (subset_closure hx)) (fun _ hx => hb _ hx) (fun _ hx => hc0 _ hx)
      B.coe_nonneg F.coe_nonneg (hu.continuousOn.mono hΩU)
      (fun _ hx => hu.contDiffAt (hU.mem_nhds (hΩU (subset_closure hx))))
      (fun _ hx => by simpa only [smul_eq_mul] using hF _ hx) (fun _ hx => hu0 _ hx) hz).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) F.coe_nonneg)
  obtain ⟨h2, h1, h2'⟩ := hC₁ hEll hEll' hL hM hHb hb hHc hc hU hΩU hu hu0 (N := D * F)
    (fun z hz => by exact_mod_cast hD z hz) hV hK
  -- `C₁ (K + D F) ≤ (D + C₁ (1 + D)) (K + F)`.
  have hle : C₁ * (K + D * F) ≤ (D + C₁ * (1 + D)) * (K + F) := by
    calc C₁ * (K + D * F) ≤ C₁ * ((1 + D) * (K + F)) := by
          gcongr
          calc K + D * F ≤ K + D * F + (D * K + F) := le_self_add
            _ = (1 + D) * (K + F) := by ring
      _ ≤ (D + C₁ * (1 + D)) * (K + F) := by
          rw [← mul_assoc]
          gcongr
          exact le_add_self
  have hle' : (C₁ : ℝ) * (K + D * F) ≤ (D + C₁ * (1 + D)) * (K + F) := by exact_mod_cast hle
  refine ⟨fun z hz => (hD z hz).trans ?_, h2.mono_const hle, fun z hz => (h1 z hz).trans hle',
    fun z hz => (h2' z hz).trans hle'⟩
  gcongr
  exact le_self_add

/-! ### The principal part in terms of `sup |u|` and of the data -/

/-- **The global Schauder estimate on a bounded domain with `C^{2,α}` boundary, in terms of
`sup |u|`.** Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary`), as in
`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`. Let
`0 < λ`, `Λ`, `L` and `M` be given. Then there is a constant `C` with the following property. Let
`a` have ellipticity bounds `λ, Λ` at every point of `closure Ω`, and entries `α`-Hölder with
constant `L` and bounded by `M` on `closure Ω`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an
open set containing `closure Ω`, vanishing on the frontier of `Ω`, with `|u| ≤ N` on `closure Ω`
and with `D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `Ω` with constant
`K`, then `D²u` is `α`-Hölder on `closure Ω` with constant `C (K + N)`, and `‖Du‖` and `‖D²u‖` are
bounded by `C (K + N)` on `closure Ω`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L` and `M` (Gilbarg–Trudinger, Theorem 6.6, for
zero boundary values and without lower-order terms). This is the case `b = c = 0` of
`exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_add_fderiv_add_mul`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω)
    (hbdry : Ω.HasC2HolderBoundary α) {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) →
        (∀ z ∈ closure Ω, |u z| ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closure Ω) ∧
          (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ C * (K + N)) ∧
          ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (K + N) := by
  obtain ⟨C, hC⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_add_fderiv_add_mul hα hα1 hΩ
      hbdry Lam L M 0 hlam
  exact ⟨C, fun {a} hEll hEll' hL hM {U u N K V} hU hΩU hu hu0 hN hV hK =>
    hC (b := 0) (c := 0) hEll hEll' hL hM (HolderWith.zero.holderOnWith Ω) (by simp)
      (HolderWith.zero.holderOnWith Ω) (by simp) hU hΩU hu hu0 hN hV (by simpa using hK)⟩

/-- **The global Schauder a priori estimate on a bounded domain with `C^{2,α}` boundary.** Let
`0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary`), as in
`exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`. Let `0 < λ`, `Λ`, `L`
and `M` be given. Then there is a constant `C` with the following property. Let `a` have
ellipticity bounds `λ, Λ` at every point of `closure Ω`, and entries `α`-Hölder with constant `L`
and bounded by `M` on `closure Ω`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an open set
containing `closure Ω`, vanishing on the frontier of `Ω`, with `D²u` `α`-Hölder on `closure Ω`
(with any constant). If `|L u| ≤ F` on `Ω` and `L u` is `α`-Hölder on `Ω` with constant `K`, then
`|u|`, `‖Du‖` and `‖D²u‖` are bounded by `C (K + F)` on `closure Ω`, and `D²u` is `α`-Hölder there
with constant `C (K + F)`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L` and `M`. This is Gilbarg–Trudinger's
Theorem 6.6 for zero boundary values and without lower-order terms, with `|u|` bounded by the
maximum principle (Theorem 3.7): the case `b = c = 0` of
`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos`. -/
theorem exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : Bornology.IsBounded Ω)
    (hbdry : Ω.HasC2HolderBoundary α) {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      (∀ z ∈ closure Ω, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) →
      (∀ z ∈ closure Ω, ∀ ξ : E, (a z).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun z => a z i j) (closure Ω)) →
      (∀ z ∈ closure Ω, ∀ i j, |a z i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {F K V : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        (∀ z ∈ Ω, |∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ F) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        (∀ z ∈ closure Ω, |u z| ≤ C * (K + F)) ∧
          HolderOnWith (C * (K + F)) α (iteratedFDeriv ℝ 2 u) (closure Ω) ∧
          (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ C * (K + F)) ∧
          ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (K + F) := by
  obtain ⟨C, hC⟩ :=
    exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos hα
      hα1 hΩ hbdry Lam L M 0 hlam
  refine ⟨C, fun {a} hEll hEll' hL hM {U u F K V} hU hΩU hu hu0 hV hF hK => ?_⟩
  obtain ⟨h0, h2⟩ := hC (b := 0) (c := 0) hEll hEll' hL hM (HolderWith.zero.holderOnWith Ω)
    (by simp) (HolderWith.zero.holderOnWith Ω) (by simp) (by simp) hU hΩU hu hu0 hV
    (by simpa using hK) (by simpa using hF)
  exact ⟨fun z hz => (h0 z hz).trans (by gcongr; exact le_add_of_nonneg_left K.coe_nonneg), h2⟩

end TauCeti.PDE
