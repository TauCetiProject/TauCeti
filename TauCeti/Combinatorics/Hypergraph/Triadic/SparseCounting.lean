/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.Placement
import TauCeti.Combinatorics.Hypergraph.PairColor.Counting
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-!
# Sparse routes in induced counting

A lower route specifies vertex cells and pair colors, but imposes no top-color constraints.
Its actual count counts injective maps realizing these data. Its prediction is the product of
the cell sizes times all the required pair-color densities; unlike the induced prediction,
this is an upper envelope using independent choices of vertices, not falling factorials.

If any required pair color has density below `ρ`, both the actual lower-route count and its
prediction are at most `ρ` times the cell-size product. Top-color constraints can only decrease
the actual count, and the intrinsic induced prediction is bounded by the lower prediction.
Consequently the placed induced count and its prediction differ by at most that same bound,
without any regularity assumption. This handles the sparse branch of local induced counting;
only routes with all pair densities bounded below need a regularity-based counting argument.
Repeated cells, empty hosts, and patterns with fewer than two vertices are allowed.

The actual bound uses `PairColorSystem.card_le_pairColorDensity_mul_prod`; no pair-counting
argument is repeated here.

For a regular lower skeleton, `abs_lowerRouteCountAt_sub_expectedLowerRouteCountAt_le` compares
the actual lower-route count at a transversal placement with its prediction, for every route: it
is the counting lemma for prescribed pair colors
(`PairSkeleton3.IsPairColorRegular.abs_card_filter_colorOfPair_sub_prod_le`) applied to the box of
assigned cells.

## References

* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Function

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V]
  {C : TriadicComplex3 V} {F : FiniteColored3Pattern κ}

/-- The injective maps realizing a placement and its pair-color route, without top-color
constraints. -/
noncomputable def lowerRouteMaps (φ : PatternPlacement3 C F) (ψ : PairColorPlacement3 φ) :
    Finset (Fin F.k → V) := by
  classical
  exact univ.filter fun g ↦ Injective g ∧ (∀ i, g i ∈ φ.vertexCell i) ∧
    ∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
      C.skeleton.pairColors.colorOfPair (g p.1.1) (g p.1.2) = some (ψ.pairColor p)

/-- Membership in the maps realizing a lower route. -/
@[simp]
theorem mem_lowerRouteMaps {φ : PatternPlacement3 C F} {ψ : PairColorPlacement3 φ}
    {g : Fin F.k → V} :
    g ∈ lowerRouteMaps φ ψ ↔ Injective g ∧ (∀ i, g i ∈ φ.vertexCell i) ∧
      ∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
        C.skeleton.pairColors.colorOfPair (g p.1.1) (g p.1.2) = some (ψ.pairColor p) := by
  classical
  simp [lowerRouteMaps]

/-- The number of injective maps realizing the cells and pair colors of a route. -/
noncomputable def lowerRouteCountAt (φ : PatternPlacement3 C F) (ψ : PairColorPlacement3 φ) : ℕ :=
  #(lowerRouteMaps φ ψ)

theorem lowerRouteCountAt_def (φ : PatternPlacement3 C F) (ψ : PairColorPlacement3 φ) :
    lowerRouteCountAt φ ψ = #(lowerRouteMaps φ ψ) :=
  (rfl)

/-- The cell-size product times the product of the pair-color densities of a route.
This is an upper envelope for the intrinsic induced prediction, also for repeated cells. -/
noncomputable def expectedLowerRouteCountAt (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) : ℝ :=
  (∏ i, (#(φ.vertexCell i) : ℝ)) *
    ∏ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
      (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
        (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ)

theorem expectedLowerRouteCountAt_def (φ : PatternPlacement3 C F) (ψ : PairColorPlacement3 φ) :
    expectedLowerRouteCountAt φ ψ = (∏ i, (#(φ.vertexCell i) : ℝ)) *
      ∏ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
        (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
          (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ) :=
  (rfl)

/-- The lower-route prediction is nonnegative. -/
theorem expectedLowerRouteCountAt_nonneg (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) : 0 ≤ expectedLowerRouteCountAt φ ψ := by
  rw [expectedLowerRouteCountAt_def]
  exact mul_nonneg (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    (prod_nonneg fun _ _ ↦ by exact_mod_cast pairColorDensity_nonneg _ _ _ _)

/-- The maps realizing a lower route are the maps into the box of assigned cells realizing its
pair colors: realizing a pair color forces distinct values, so these maps are injective. -/
private theorem lowerRouteMaps_eq_filter_piFinset (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) :
    lowerRouteMaps φ ψ = {g ∈ Fintype.piFinset φ.vertexCell |
      ∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
        C.skeleton.pairColors.colorOfPair (g p.1.1) (g p.1.2) = some (ψ.pairColor p)} := by
  ext g
  simp only [mem_lowerRouteMaps, mem_filter, Fintype.mem_piFinset]
  refine ⟨fun ⟨_, hcell, hcolor⟩ ↦ ⟨hcell, hcolor⟩, fun ⟨hcell, hcolor⟩ ↦ ⟨?_, hcell, hcolor⟩⟩
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · simpa [hij] using hcolor ⟨(i, j), h⟩
  · simpa [hij] using hcolor ⟨(j, i), h⟩

/-- **Lower-route counting.** At a transversal placement of a pattern on `k` vertices into an
`ε`-regular lower skeleton, the number of injective maps realizing a route differs from its
prediction, the cell-size product times the pair-color densities of the route, by at most
`(k choose 2) * ε` times the cell-size product. No lower bound on the densities is needed. -/
theorem abs_lowerRouteCountAt_sub_expectedLowerRouteCountAt_le {φ : PatternPlacement3 C F}
    (hφ : φ.Transversal) (ψ : PairColorPlacement3 φ) {ε : ℝ}
    (h : C.skeleton.IsPairColorRegular ε) :
    |(lowerRouteCountAt φ ψ : ℝ) - expectedLowerRouteCountAt φ ψ| ≤
      F.k.choose 2 * ε * ∏ i, (#(φ.vertexCell i) : ℝ) := by
  simpa [lowerRouteCountAt_def, lowerRouteMaps_eq_filter_piFinset,
    expectedLowerRouteCountAt_def] using
    h.abs_card_filter_colorOfPair_sub_prod_le φ.vertexCell φ.vertexCell_mem
      (φ.transversal_iff.1 hφ) ψ.pairColor

namespace PairColorPlacement3

variable {φ : PatternPlacement3 C F} (ψ : PairColorPlacement3 φ) {ρ ρ' : ℝ}

/-- A route is sparse at floor `ρ` if one of its required pair-color densities is below `ρ`. -/
def IsSparseRoute (ρ : ℝ) : Prop :=
  ∃ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
    (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
      (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ) < ρ

/-- A sparse route has a pair-color density below the floor. -/
theorem isSparseRoute_iff : ψ.IsSparseRoute ρ ↔
    ∃ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
      (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
        (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ) < ρ :=
  Iff.rfl

/-- A route is not sparse exactly when every required pair-color density is at least the floor. -/
theorem not_isSparseRoute_iff : ¬ψ.IsSparseRoute ρ ↔
    ∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
      ρ ≤ (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
        (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ) := by
  simp [isSparseRoute_iff]

/-- A sparse route stays sparse when the floor increases. -/
theorem IsSparseRoute.mono (h : ψ.IsSparseRoute ρ) (hρ : ρ ≤ ρ') : ψ.IsSparseRoute ρ' := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans_le hρ⟩

end PairColorPlacement3

/-- Any prescribed pair color caps the actual lower-route count at its density times the
cell-size product. No regularity or transversality assumption is needed. -/
theorem lowerRouteCountAt_le_pairColorDensity_mul_prod (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) (p : {p : Fin F.k × Fin F.k // p.1 < p.2}) :
    (lowerRouteCountAt φ ψ : ℝ) ≤
      (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
        (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ) * ∏ i, (#(φ.vertexCell i) : ℝ) := by
  rw [lowerRouteCountAt_def]
  exact C.skeleton.pairColors.card_le_pairColorDensity_mul_prod _ _ p.2.ne _
    (fun _ hg ↦ (mem_lowerRouteMaps.1 hg).2.1)
    (fun _ hg ↦ (mem_lowerRouteMaps.1 hg).2.2 p)

/-- A sparse route self-bounds on the actual side, without regularity assumptions. -/
theorem lowerRouteCountAt_le_of_sparseRoute (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) {ρ : ℝ} (h : ψ.IsSparseRoute ρ) :
    (lowerRouteCountAt φ ψ : ℝ) ≤ ρ * ∏ i, (#(φ.vertexCell i) : ℝ) := by
  obtain ⟨p, hp⟩ := h
  exact (lowerRouteCountAt_le_pairColorDensity_mul_prod φ ψ p).trans
    (mul_le_mul_of_nonneg_right hp.le (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _))

/-- A sparse route self-bounds on the predicted side, because all the other density factors
lie in `[0, 1]`. -/
theorem expectedLowerRouteCountAt_le_of_sparseRoute (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) {ρ : ℝ} (h : ψ.IsSparseRoute ρ) :
    expectedLowerRouteCountAt φ ψ ≤ ρ * ∏ i, (#(φ.vertexCell i) : ℝ) := by
  classical
  obtain ⟨p, hp⟩ := h
  rw [expectedLowerRouteCountAt_def, mul_comm ρ]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ hp.le)
    (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  simpa using prod_le_prod_of_subset_of_le_one₀ (s := {p}) (t := univ)
    (f := fun q ↦ (pairColorDensity C.skeleton.pairColors (ψ.pairColor q)
      (φ.vertexCell q.1.1) (φ.vertexCell q.1.2) : ℝ)) (subset_univ _)
    (fun _ _ ↦ by exact_mod_cast pairColorDensity_nonneg _ _ _ _)
    (fun _ _ _ ↦ by exact_mod_cast pairColorDensity_le_one _ _ _ _)

namespace Colored3Graph

variable (H : Colored3Graph κ V)

/-- Forgetting the top-color constraints embeds the placed induced copies into the lower route. -/
theorem placedInducedCopyCount_le_lowerRouteCountAt (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) : H.placedInducedCopyCount φ ψ ≤ lowerRouteCountAt φ ψ := by
  classical
  rw [placedInducedCopyCount_def, lowerRouteCountAt_def]
  refine card_le_card_of_injOn (fun f : Fin F.k ↪ V ↦ (f : Fin F.k → V)) ?_ ?_
  · intro f hf
    obtain ⟨-, hcell, hcolor⟩ := mem_placedInducedCopies.1 hf
    exact mem_lowerRouteMaps.2 ⟨f.injective, hcell, hcolor⟩
  · exact fun _ _ _ _ h ↦ DFunLike.coe_injective h

variable [DecidableEq κ]

/-- The intrinsic induced prediction is bounded by the lower-route prediction: its injection
factor is at most the cell-size product, and its top-density factors are at most one. -/
theorem expectedInducedCountAt_le_expectedLowerRouteCountAt (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) : H.expectedInducedCountAt φ ψ ≤ expectedLowerRouteCountAt φ ψ := by
  rw [expectedInducedCountAt_def, expectedLowerRouteCountAt_def]
  have hpair : 0 ≤ ∏ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
      (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
        (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ) :=
    prod_nonneg fun _ _ ↦ by exact_mod_cast pairColorDensity_nonneg _ _ _ _
  refine (mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) hpair)
    (prod_le_one₀ (fun _ _ ↦ ?_) fun _ _ ↦ ?_)).trans ?_
  · exact_mod_cast H.relativeDensity_nonneg _ _
  · exact_mod_cast H.relativeDensity_le_one _ _
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast placementInjectionCount_le_prod φ) hpair

/-- **Sparse-route induced counting.** The placed actual and predicted induced counts differ by
at most `ρ` times the cell-size product whenever one pair-color density is below `ρ`.
Neither regularity nor transversality is required. -/
theorem placed_induced_counting3_of_sparseRoute (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) {ρ : ℝ} (h : ψ.IsSparseRoute ρ) :
    |(H.placedInducedCopyCount φ ψ : ℝ) - H.expectedInducedCountAt φ ψ| ≤
      ρ * ∏ i, (#(φ.vertexCell i) : ℝ) := by
  have hcount : (H.placedInducedCopyCount φ ψ : ℝ) ≤ lowerRouteCountAt φ ψ := by
    exact_mod_cast H.placedInducedCopyCount_le_lowerRouteCountAt φ ψ
  have ha := hcount.trans (lowerRouteCountAt_le_of_sparseRoute φ ψ h)
  have hb := (H.expectedInducedCountAt_le_expectedLowerRouteCountAt φ ψ).trans
    (expectedLowerRouteCountAt_le_of_sparseRoute φ ψ h)
  have h₀ := H.expectedInducedCountAt_nonneg φ ψ
  have h₁ : (0 : ℝ) ≤ H.placedInducedCopyCount φ ψ := Nat.cast_nonneg _
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

end Colored3Graph

end TauCeti
