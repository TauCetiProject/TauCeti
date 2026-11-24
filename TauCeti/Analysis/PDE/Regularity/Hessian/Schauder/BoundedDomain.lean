/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.CurvedBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.LowerOrder
import TauCeti.Analysis.Holder.LipschitzDomain
import TauCeti.Analysis.InnerProductSpace.GraphPatch
import TauCeti.Analysis.Sobolev.LipschitzDomain.GraphPatch
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Schauder estimate on a bounded domain with `C^{2,α}` boundary

Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary: near each
point `x` of its frontier, `Ω` is the region `{z | γ z < ⟪z, ν⟫}` above the graph of a `C^{2,α}`
function over a hyperplane `ν^⊥`, that is

`ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}`

for a unit vector `ν`, a radius `r > 0` and a `C²` function `γ` invariant under translation along
`ν`, with `Dγ` and `D²γ` bounded and `D²γ` `α`-Hölder. This file proves the global `C^{2,α}`
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

The same estimate holds for the general operator `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + b · ∇u + c u`, with a drift
`b` and a potential `c` that are `α`-Hölder and bounded on `Ω`, the constant now depending also on
their bounds (in the `TauCeti.PDE` namespace,
`exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul`).
No sign condition on `c` is needed. This is Gilbarg–Trudinger's global estimate, Theorem 6.6, for
zero boundary values, with the norms of `Du` and `D²u` still on the right; an interpolation
inequality on `Ω` would reduce `N` to the supremum of `|u|`.

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
* **Lower-order terms.** A domain with a graph patch at every frontier point is a Lipschitz domain
  (`TauCeti.isLipschitzDomain_of_forall_ball_inter_eq`), so on the bounded domain `Ω` the bounds
  `N` on `u`, `Du` and `D²u` make `u` and `Du` `α`-Hölder with constant a multiple of `N`
  (`Set.IsLipschitzDomain.exists_holderOnWith_of_norm_fderiv_le`). The Hölder constant of
  `b · ∇u + c u` on `Ω` is then a multiple of `N`
  (`TauCeti.PDE.holderOnWith_fderiv_apply_add_mul`), and the estimate for the principal part
  applies to `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = L u - b · ∇u - c u`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`: the
  global Schauder estimate on a bounded domain with `C^{2,α}` boundary.
* `exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul`,
  in the `TauCeti.PDE` namespace: the same estimate with lower-order terms.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2: Lemma 6.5 (the boundary estimate) and Theorem 6.6 (the global estimate, obtained
  from the interior and boundary estimates by a finite covering).
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
`0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary: near each point
`x` of its frontier, `ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` for a unit vector `ν`, a radius
`r > 0` and a `C²` function `γ` invariant under translation along `ν`, with `‖Dγ‖ ≤ G`,
`‖D²γ‖ ≤ G` and `D²γ` `α`-Hölder with constant `G`. Let `0 < λ`, `Λ`, `L` and `M` be given. Then
there is a constant `C` with the following property. Let `a` have ellipticity bounds `λ, Λ` at
every point of `closure Ω`, and entries `α`-Hölder with constant `L` and bounded by `M` on
`closure Ω`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an open set containing `closure Ω`,
vanishing on the frontier of `Ω`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `closure Ω` and
with `D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `Ω` with constant `K`,
then `D²u` is `α`-Hölder on `closure Ω` with constant `C (K + N)`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L` and `M`: not on `a` beyond the stated bounds,
nor on `u` (Gilbarg–Trudinger, Theorem 6.6, with the norms of `Du` and `D²u` on the right). -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      ContDiff ℝ 2 γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ (∀ z, ‖fderiv ℝ γ z‖ ≤ G) ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ γ) z‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ})
    {lam : ℝ} (Lam : ℝ) (L M : ℝ≥0) (hlam : 0 < lam) :
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
  obtain ⟨δ, hδ, A, hA⟩ :=
    exists_dist_iteratedFDeriv_two_le_of_dist_lt hα hα1 hΩo hΩ hbdry Lam L M hlam
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

/-! ### Lower-order terms -/

/-- **The global Schauder estimate with lower-order terms on a bounded domain with `C^{2,α}`
boundary.** Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary,
described at each frontier point as in
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
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      ContDiff ℝ 2 γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ (∀ z, ‖fderiv ℝ γ z‖ ≤ G) ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ γ) z‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ})
    {lam : ℝ} (Lam : ℝ) (L M B : ℝ≥0) (hlam : 0 < lam) :
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
    hα hα1 hΩo hΩ hbdry Lam L M hlam
  -- `Ω` is a bounded Lipschitz domain, so bounds on a function and its derivative make it
  -- `α`-Hölder on `Ω`.
  have hLip : Ω.IsLipschitzDomain (EuclideanSpace ℝ (Fin n)) :=
    TauCeti.isLipschitzDomain_of_forall_ball_inter_eq finrank_euclideanSpace_fin fun x hx => by
      obtain ⟨ν, γ, G, r, hν, hγ, hγν, hG, -, -, hr, hΩx⟩ := hbdry x hx
      refine ⟨ν, γ, G, r, norm_ne_zero_iff.1 (by rw [hν]; exact one_ne_zero),
        lipschitzWith_of_nnNorm_fderiv_le (hγ.differentiable (by norm_num)) fun z => ?_,
        hγν, hr, hΩx⟩
      rw [← NNReal.coe_le_coe, coe_nnNorm]
      exact hG z
  obtain ⟨C₁, hC₁⟩ := hLip.exists_holderOnWith_of_norm_fderiv_le hΩ hα1.le
  set P : ℝ≥0 := 2 * B + 4 * B * C₁
  refine ⟨C₀ * (1 + P), fun {a b c} hEll hEll' hL hM hHb hb hHc hc {U u N K V} hU hΩU hu hu0
    hN0 hN1 hN2 hV hK => ?_⟩
  have hΩcl : Ω ⊆ closure Ω := subset_closure
  have hcd : ∀ z ∈ Ω, ContDiffAt ℝ 2 u z := fun z hz => hu.contDiffAt (hU.mem_nhds (hΩU (hΩcl hz)))
  -- `u` and `Du` are `α`-Hölder on `Ω` with constant `2 C₁ N`.
  have hHu : HolderOnWith (C₁ * (N + N)) α u Ω :=
    hC₁ (fun z hz => (hcd z hz).differentiableAt (by norm_num))
      (fun z hz => by rw [Real.norm_eq_abs]; exact hN0 z (hΩcl hz)) fun z hz => hN1 z (hΩcl hz)
  have hHDu : HolderOnWith (C₁ * (N + N)) α (fderiv ℝ u) Ω := by
    refine hC₁ (fun z hz => ((hcd z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) (fun z hz => hN1 z (hΩcl hz)) fun z hz => ?_
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hN2 z (hΩcl hz)
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

end TauCeti.PDE
