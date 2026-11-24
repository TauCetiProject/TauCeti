/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.CurvedBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
import TauCeti.Analysis.Holder.Interpolation
import TauCeti.Analysis.InnerProductSpace.GraphPatch
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
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

Interpolation up to the boundary removes `‖Du‖` and `‖D²u‖` from the right side
(`exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_sum_smul_fderiv_fderiv`):
if only `|u| ≤ N` on `closure Ω`, then `[D²u]_{α; closure Ω}`, `‖Du‖` and `‖D²u‖` are at most
`C ([L u]_{α; Ω} + N)`. The maximum principle then bounds `|u|` by `sup_Ω |L u|`, which gives the a
priori estimate
(`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`)

`|u|_{0; Ω} + |Du|_{0; Ω} + |D²u|_{0; Ω} + [D²u]_{α; Ω} ≤ C (sup_Ω |L u| + [L u]_{α; Ω})`.

This is Gilbarg–Trudinger's global estimate, Theorem 6.6, for zero boundary values and without
lower-order terms.

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
* **Interpolation.** The closure of `Ω` satisfies a uniform interior cone condition
  (`TauCeti.exists_forall_closedBall_add_smul_subset`), so at a small scale `ε` the interpolation
  inequalities up to the boundary,
  `HolderOnWith.norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_forall_closedBall_add_smul_subset`,
  bound `‖Du‖` and `‖D²u‖` by `C_ε N + 5 ε^α [D²u]_α`. Inserted into the estimate above, the
  multiple of `[D²u]_α` is absorbed into the left side for `ε` small.
* **The maximum principle.** `L u` is continuous on `closure Ω`, so `|L u| ≤ F` on `Ω` holds on
  `closure Ω`, and the maximum principle for non-divergence operators
  (`TauCeti.PDE.abs_le_add_of_abs_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_abs_le_frontier`)
  bounds `|u|` by a multiple of `F` depending only on `λ` and the diameter of `Ω`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`: the
  global Schauder estimate on a bounded domain with `C^{2,α}` boundary.
* `exists_forall_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded`: the interpolation
  inequalities up to the boundary of `Ω`, at every small scale `ε`.
* `exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_sum_smul_fderiv_fderiv`:
  the same with only `sup |u|` on the right, bounding also `‖Du‖` and `‖D²u‖`.
* `exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`:
  the a priori estimate of `u` in `C^{2,α}(closure Ω)` by `L u` in `C^{0,α}(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.1, Theorem 3.7 (the bound on `sup |u|`); Section 6.2: Lemma 6.5 (the boundary
  estimate) and Theorem 6.6 (the global estimate, obtained
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

/-- **Interpolation up to the boundary of a bounded domain with `C^{2,α}` boundary.** Let `Ω` be
a bounded set described at each frontier point by a patch as in
`exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`. There are a scale
`ε₀ > 0` and a constant `0 < c ≤ 1`, depending only on `Ω`, such that at every scale
`0 < ε ≤ ε₀`, every `u` that is `C²` on an open set containing `closure Ω`, with `|u| ≤ N` and
`D²u` `α`-Hölder with constant `H` on `closure Ω`, has `‖Du‖` and `‖D²u‖` at most
`9 (c ε)⁻² N + 5 H ε^α` on `closure Ω` (Gilbarg–Trudinger, Section 6.8). -/
theorem exists_forall_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded {α : ℝ≥0}
    {Ω : Set E}
    (hΩ : Bornology.IsBounded Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      ContDiff ℝ 2 γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ (∀ z, ‖fderiv ℝ γ z‖ ≤ G) ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ γ) z‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    ∃ ε₀ > 0, ∃ c > 0, c ≤ 1 ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ {U : Set E} {u : E → ℝ} {N H : ℝ≥0},
      IsOpen U → closure Ω ⊆ U → ContDiffOn ℝ 2 u U → (∀ z ∈ closure Ω, |u z| ≤ N) →
      HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closure Ω) → ∀ z ∈ closure Ω,
        ‖fderiv ℝ u z‖ ≤ 9 / (c * ε) ^ 2 * N + 5 * H * ε ^ (α : ℝ) ∧
        ‖iteratedFDeriv ℝ 2 u z‖ ≤ 9 / (c * ε) ^ 2 * N + 5 * H * ε ^ (α : ℝ) := by
  -- The closure of `Ω` satisfies a uniform interior cone condition.
  obtain ⟨h₀, hh₀, c, hc, hc1, hcone⟩ :=
    TauCeti.exists_forall_closedBall_add_smul_subset hΩ.isCompact_closure fun x hx => by
      obtain ⟨ν, γ, G, r, hν, hγ, hγν, hG1, -, -, hr, hΩr⟩ := hbdry x hx
      refine ⟨ν, γ, G, r, hν, (lipschitzWith_of_nnNorm_fderiv_le
        (hγ.differentiable two_ne_zero) fun z => ?_).lipschitzOnWith, hγν, hr, hΩr⟩
      rw [← NNReal.coe_le_coe, coe_nnNorm]
      exact hG1 z
  have hcone' : ∀ z ∈ closure Ω, ∃ v : E, ‖v‖ = 1 ∧
      ∀ t, 0 < t → t ≤ h₀ → closedBall (z + t • v) (c * t) ⊆ closure Ω := fun z hz => by
    obtain ⟨v, hv, hb⟩ := hcone z hz
    exact ⟨v, hv, fun t ht hth => (hb t ht hth).trans subset_closure⟩
  refine ⟨min h₀ 1, lt_min hh₀ one_pos, c, hc, hc1,
    fun ε hε hεε₀ {U u N H} hU hΩU hu hN hH z hz => ?_⟩
  have hε1 : ε ≤ 1 := hεε₀.trans (min_le_right _ _)
  obtain ⟨h1, h2⟩ :=
    hH.norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_forall_closedBall_add_smul_subset hU hu
      hΩU (M := N) (fun y hy => by simpa only [Real.norm_eq_abs] using hN y hy) hc hc1 hcone' hε
      (hεε₀.trans (min_le_left _ _))
  have hHε : 0 ≤ (H : ℝ) * ε ^ (α : ℝ) := by positivity
  refine ⟨(h1 z hz).trans ?_, (h2 z hz).trans ?_⟩
  · have hpow : ε ^ (1 + (α : ℝ)) ≤ ε ^ (α : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
    have h9 : 9 * (N : ℝ) / (c ^ 2 * ε) ≤ 9 / (c * ε) ^ 2 * N := by
      rw [div_mul_eq_mul_div, mul_comm 9]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    nlinarith [H.coe_nonneg]
  · have h8 : 8 * (N : ℝ) / (c * ε) ^ 2 ≤ 9 / (c * ε) ^ 2 * N := by
      rw [div_mul_eq_mul_div, mul_comm 9]
      exact div_le_div_of_nonneg_right (by nlinarith [N.coe_nonneg]) (by positivity)
    nlinarith

/-- **The global Schauder estimate on a bounded domain with `C^{2,α}` boundary, with `sup |u|` on
the right.** Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary,
described at each frontier point `x` by a patch `ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` as
in `exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv`. Let `0 < λ`, `Λ`,
`L` and `M` be given. Then there is a constant `C` with the following property. Let `a` have
ellipticity bounds `λ, Λ` at every point of `closure Ω`, and entries `α`-Hölder with constant `L`
and bounded by `M` on `closure Ω`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an open set
containing `closure Ω`, vanishing on the frontier of `Ω`, with `|u| ≤ N` on `closure Ω` and with
`D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `Ω` with constant `K`, then
`D²u` is `α`-Hölder on `closure Ω` with constant `C (K + N)`, and `‖Du‖` and `‖D²u‖` are bounded
by `C (K + N)` on `closure Ω`.

The constant depends only on `Ω`, `α`, `λ`, `Λ`, `L` and `M` (Gilbarg–Trudinger, Theorem 6.6, for
zero boundary values and without lower-order terms). -/
theorem exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω)
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
        ContDiffOn ℝ 2 u U → (∀ z ∈ frontier Ω, u z = 0) → (∀ z ∈ closure Ω, |u z| ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        HolderOnWith K α (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closure Ω) ∧
          (∀ z ∈ closure Ω, ‖fderiv ℝ u z‖ ≤ C * (K + N)) ∧
          ∀ z ∈ closure Ω, ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (K + N) := by
  obtain ⟨C₀, hC₀⟩ := exists_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv
    hα hα1 hΩo hΩ hbdry Lam L M hlam
  obtain ⟨ε₀, hε₀, c, hc, hc1, hint⟩ :=
    exists_forall_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded hΩ hbdry
  -- The interpolation scale `ε`, small enough to absorb the Hölder constant of `D²u`.
  obtain ⟨ρ, hρ, hρ1, hρC⟩ := Real.exists_pos_le_one_mul_rpow_le (5 * C₀)
    (NNReal.coe_pos.2 hα) (by norm_num : (0 : ℝ) < 1 / 2)
  set ε := min ρ ε₀
  have hε : 0 < ε := lt_min hρ hε₀
  have hεC : 5 * C₀ * ε ^ (α : ℝ) ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
    hε.le (min_le_left _ _) α.coe_nonneg) (by positivity)).trans hρC
  have hεα : ε ^ (α : ℝ) ≤ 1 := Real.rpow_le_one hε.le ((min_le_left _ _).trans hρ1) α.coe_nonneg
  set κ : ℝ := 9 / (c * ε) ^ 2
  have hκ : 1 ≤ κ := (one_le_div (by positivity)).2 <| (pow_le_one₀ (by positivity) <|
    (mul_le_of_le_one_left hε.le hc1).trans ((min_le_left _ _).trans hρ1)).trans (by norm_num)
  set A : ℝ := 2 * C₀ * (1 + κ)
  refine ⟨(5 * A + κ).toNNReal, fun {a} hEll hEll' hL hM {U u N K V} hU hΩU hu hu0 hN hV hK => ?_⟩
  -- The best Hölder constant `H` of `D²u` on `closure Ω`; then `|u|`, `‖Du‖` and `‖D²u‖` are at
  -- most `N₁ = κ N + 5 H ε^α` on `closure Ω`.
  set H := nnHolderNorm α ((closure Ω).domRestrict (iteratedFDeriv ℝ 2 u))
  have hH : HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closure Ω) :=
    HolderWith.restrict_iff.1 hV.holderWith.memHolder.holderWith
  have hb := hint ε hε (min_le_right _ _) hU hΩU hu hN hH
  set N₁ : ℝ := κ * N + 5 * H * ε ^ (α : ℝ)
  have hN₁ : 0 ≤ N₁ := by positivity
  have hNN₁ : (N : ℝ) ≤ N₁ :=
    le_add_of_le_of_nonneg (le_mul_of_one_le_left N.coe_nonneg hκ) (by positivity)
  -- The estimate with `N₁` in place of `N`, and absorption of `5 C₀ ε^α H ≤ H / 2`.
  have hHA : (H : ℝ) ≤ A * (K + N) := by
    have h := (hC₀ hEll hEll' hL hM hU hΩU hu hu0
      (fun z hz => (hN z hz).trans (hNN₁.trans (Real.le_coe_toNNReal _)))
      (fun z hz => (hb z hz).1.trans (Real.le_coe_toNNReal _))
      (fun z hz => (hb z hz).2.trans (Real.le_coe_toNNReal _)) hV hK).holderWith.nnholderNorm_le
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_add, Real.coe_toNNReal _ hN₁] at h
    have habs : 5 * C₀ * ε ^ (α : ℝ) * H ≤ 1 / 2 * H :=
      mul_le_mul_of_nonneg_right hεC H.coe_nonneg
    simp only [A, N₁] at h ⊢
    nlinarith [(by positivity : (0 : ℝ) ≤ C₀ * N), (by positivity : (0 : ℝ) ≤ C₀ * κ * K)]
  -- Collect the bounds: `H` and `N₁` are at most `(5 A + κ) (K + N)`.
  have hC : (5 * A + κ) * (K + N) ≤ ((5 * A + κ).toNNReal : ℝ) * (K + N) :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity)
  have hκK : 0 ≤ κ * K := by positivity
  have hN₁A : N₁ ≤ (5 * A + κ) * (K + N) := by
    have hHε : (H : ℝ) * ε ^ (α : ℝ) ≤ H := mul_le_of_le_one_right H.coe_nonneg hεα
    simp only [N₁]
    nlinarith
  refine ⟨hH.mono_const ?_, fun z hz => (hb z hz).1.trans (hN₁A.trans hC),
    fun z hz => (hb z hz).2.trans (hN₁A.trans hC)⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_mul]
  exact le_trans (by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ κ) N.coe_nonneg]) hC

/-- **The global Schauder a priori estimate on a bounded domain with `C^{2,α}` boundary.** Let
`0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary, described at each
frontier point by a patch as in
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
maximum principle (Theorem 3.7). -/
theorem exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩo : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω)
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
  obtain ⟨C₁, hC₁⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closure_and_norm_le_of_sum_smul_fderiv_fderiv hα hα1
      hΩo hΩ hbdry Lam L M hlam
  -- The constant of the maximum principle on `closure Ω`.
  set D : ℝ := (Real.exp ((0 / lam + 1) * Metric.diam (closure Ω)) - 1) / lam
  have hD : 0 ≤ D :=
    div_nonneg (sub_nonneg.2 (Real.one_le_exp (by positivity))) hlam.le
  refine ⟨(C₁ * (1 + D) + D).toNNReal,
    fun {a} hEll hEll' hL hM {U u F K V} hU hΩU hu hu0 hV hF hK => ?_⟩
  -- `L u` is continuous on `closure Ω`, so the bound `|L u| ≤ F` extends to `closure Ω`.
  have hd2 : ContinuousOn (fderiv ℝ (fderiv ℝ u)) (closure Ω) :=
    ((hu.fderiv_of_isOpen (m := 1) hU le_rfl).continuousOn_fderiv_of_isOpen hU le_rfl).mono hΩU
  have hLc : ContinuousOn (fun z => ∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (closure Ω) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((hL i j).continuousOn hα).smul ((hd2.clm_apply continuousOn_const).clm_apply
        continuousOn_const)
  have hFcl : ∀ z ∈ closure Ω, |∑ i, ∑ j, a z i j • fderiv ℝ (fderiv ℝ u) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ F := fun z hz => by
    refine (closure_minimal ?_ (hLc.abs.preimage_isClosed_of_isClosed isClosed_closure
      (isClosed_Iic (a := (F : ℝ)))) hz).2
    exact fun y hy => ⟨subset_closure hy, hF y hy⟩
  -- The maximum principle bounds `|u|` by `D F`.
  have hu0' : ∀ z ∈ closure Ω, |u z| ≤ D * F := fun z hz => by
    have h := abs_le_add_of_abs_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_abs_le_frontier
      (b := 0) (c := 0) (β := 0) (M := 0) hΩ.isCompact_closure hlam
      (fun x hx ξ => hEll x (interior_subset hx) ξ) (by simp) (by simp) le_rfl F.coe_nonneg
      (hu.continuousOn.mono hΩU)
      (fun x hx => hu.contDiffAt (hU.mem_nhds (hΩU (interior_subset hx))))
      (fun x hx => by simpa [smul_eq_mul] using hFcl x (interior_subset hx))
      (fun x hx => by rw [hu0 x (frontier_closure_subset hx), abs_zero]) hz
    rwa [zero_add, mul_div_right_comm] at h
  have hDF : 0 ≤ D * F := by positivity
  obtain ⟨hH, h1, h2⟩ := hC₁ hEll hEll' hL hM hU hΩU hu hu0
    (fun z hz => (hu0' z hz).trans (Real.le_coe_toNNReal _)) hV hK
  -- Collect the bounds: `D F` and `C₁ (K + D F)` are at most `(C₁ (1 + D) + D) (K + F)`.
  have hC : (C₁ * (1 + D) + D) * (K + F) ≤ ((C₁ * (1 + D) + D).toNNReal : ℝ) * (K + F) :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity)
  have hDK : 0 ≤ D * K := by positivity
  have hC₁ : (C₁ : ℝ) * (K + (D * F).toNNReal) ≤ (C₁ * (1 + D) + D) * (K + F) := by
    rw [Real.coe_toNNReal _ hDF]
    nlinarith [mul_nonneg C₁.coe_nonneg hDK, mul_nonneg C₁.coe_nonneg F.coe_nonneg,
      mul_nonneg hD (add_nonneg K.coe_nonneg F.coe_nonneg), mul_nonneg C₁.coe_nonneg K.coe_nonneg]
  refine ⟨fun z hz => (hu0' z hz).trans (le_trans ?_ hC), hH.mono_const ?_,
    fun z hz => (h1 z hz).trans (hC₁.trans hC), fun z hz => (h2 z hz).trans (hC₁.trans hC)⟩
  · nlinarith [mul_nonneg C₁.coe_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + D)
      (add_nonneg K.coe_nonneg F.coe_nonneg))]
  · rw [← NNReal.coe_le_coe, NNReal.coe_mul]
    exact hC₁.trans hC

end TauCeti.PDE
