/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.SparseCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The predicted mass of exceptional routes

Fix a triadic complex `C` on `V`, a colored three-uniform pattern `F` on `k = F.k` vertices, and
a coloring `H` of the triples of `V`. A route `ψ` over a placement `φ` of `F` is *top-regular*
for `H` at `(η, r)` when `H` is `(η, r)`-top-regular over the polyad of every canonically ordered
pattern triple. An induced counting lemma counts the copies of `F` along top-regular routes; the
remaining routes pass through an exceptional polyad and are discarded. On the actual side, the
copies along such routes are embeddings meeting an exceptional polyad, which
`Colored3Graph.exceptional_route_mass_le` bounds by the exceptional polyad mass. This file bounds
the discarded prediction, the sum `H.exceptionalPredictedMass3 C F η r` of the local predictions
over the transversal placements and their routes that are not top-regular.

The bound passes through the lower route, which forgets the top colors. Its prediction, the
cell-size product times the pair-color densities, dominates the induced prediction. At a
transversal placement in an `ε`-regular lower skeleton, lower-route counting
(`abs_lowerRouteCountAt_sub_expectedLowerRouteCountAt_le`) shows that the lower-route prediction
is within `(k choose 2) ε` times the cell-size product of the number of injective maps realizing
the route. These maps, for the routes that are not top-regular, are again embeddings meeting an
exceptional polyad, as distinct routes are realized by disjoint sets of maps. The counting error
is paid once for each of the at most `m ^ (k choose 2)` routes of a placement, where `m` is the
number of pair colors, and the cell-size products of the placements add up to `|V| ^ k`.
No density floor on the routes is needed.

## Main definitions

* `TauCeti.PairColorPlacement3.IsTopRegularRoute`: every polyad of the route is top-regular.
* `TauCeti.Colored3Graph.exceptionalPredictedMass3`: the prediction of the transversal
  placements along routes that are not top-regular.

## Main results

* `TauCeti.Colored3Graph.sum_lowerRouteCountAt_not_isTopRegularRoute_le`: the maps realizing
  routes that are not top-regular are controlled by the exceptional polyad mass.
* `TauCeti.Colored3Graph.exceptional_route_prediction_mass_le`: the bound
  `(k.choose 3 * μ + m ^ (k.choose 2) * k.choose 2 * ε) * |V| ^ k` on the exceptional predicted
  mass, where `μ` is the exceptional polyad mass.

## References

* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Function

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V] {C : TriadicComplex3 V}
  {F : FiniteColored3Pattern κ}

/-! ### Top-regular routes -/

namespace PairColorPlacement3

variable {κ' : Type*} [DecidableEq κ'] {φ : PatternPlacement3 C F}

/-- A route is top-regular for a coloring `H` at `(η, r)` when `H` is `(η, r)`-top-regular over
the polyad of every canonically ordered pattern triple. -/
def IsTopRegularRoute (ψ : PairColorPlacement3 φ) (H : Colored3Graph κ' V) (η : ℝ) (r : ℕ) :
    Prop :=
  ∀ (i j l : Fin F.k) (hij : i < j) (hjl : j < l),
    H.IsTopRegularOverPolyad (ψ.polyad i j l hij hjl) η r

/-- Unfolded form of `PairColorPlacement3.IsTopRegularRoute`. -/
theorem isTopRegularRoute_iff (ψ : PairColorPlacement3 φ) (H : Colored3Graph κ' V) (η : ℝ)
    (r : ℕ) : ψ.IsTopRegularRoute H η r ↔ ∀ (i j l : Fin F.k) (hij : i < j) (hjl : j < l),
      H.IsTopRegularOverPolyad (ψ.polyad i j l hij hjl) η r :=
  Iff.rfl

end PairColorPlacement3

/-! ### The exceptional predicted mass -/

namespace Colored3Graph

variable [DecidableEq κ] (H : Colored3Graph κ V)

variable (C F) in
open Classical in
/-- The predicted mass of the exceptional routes: the sum of the local predictions over the
transversal placements of `F` and their routes that are not `(η, r)`-top-regular for `H`. -/
noncomputable def exceptionalPredictedMass3 (η : ℝ) (r : ℕ) : ℝ :=
  ∑ φ : PatternPlacement3 C F with φ.Transversal,
    ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r, H.expectedInducedCountAt φ ψ

variable (C F) in
open Classical in
theorem exceptionalPredictedMass3_def (η : ℝ) (r : ℕ) :
    H.exceptionalPredictedMass3 C F η r =
      ∑ φ : PatternPlacement3 C F with φ.Transversal,
        ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r,
          H.expectedInducedCountAt φ ψ :=
  (rfl)

variable (C F) in
/-- The exceptional predicted mass is nonnegative. -/
theorem exceptionalPredictedMass3_nonneg (η : ℝ) (r : ℕ) :
    0 ≤ H.exceptionalPredictedMass3 C F η r :=
  sum_nonneg fun φ _ ↦ sum_nonneg fun ψ _ ↦ H.expectedInducedCountAt_nonneg φ ψ

variable (C F) in
open Classical in
/-- **Maps along exceptional routes.** The injective maps realizing the cells and pair colors of
routes that are not `(η, r)`-top-regular for `H`, over all placements of a pattern on `k`
vertices, number at most `k.choose 3 * H.exceptionalPolyadMass C η r * |V| ^ k`. Each of them
sends some increasing pattern triple into an irregular selected polyad, and distinct routes are
realized by disjoint sets of maps. -/
theorem sum_lowerRouteCountAt_not_isTopRegularRoute_le (η : ℝ) (r : ℕ) :
    ∑ φ : PatternPlacement3 C F, ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r,
        (lowerRouteCountAt φ ψ : ℝ) ≤
      F.k.choose 3 * H.exceptionalPolyadMass C η r * (Fintype.card V : ℝ) ^ F.k := by
  refine le_trans ?_ (H.exceptional_route_mass_le C F.k η r)
  set s := (univ : Finset (Σ φ : PatternPlacement3 C F, PairColorPlacement3 φ)).filter
    fun σ ↦ ¬σ.2.IsTopRegularRoute H η r
  have hdisj : (s : Set (Σ φ : PatternPlacement3 C F, PairColorPlacement3 φ)).PairwiseDisjoint
      fun σ ↦ lowerRouteMaps σ.1 σ.2 := by
    rintro ⟨φ, ψ⟩ - ⟨φ', ψ'⟩ - hne
    refine disjoint_left.2 fun g hg hg' ↦ hne ?_
    obtain ⟨-, hφ, hψ⟩ := mem_lowerRouteMaps.1 hg
    obtain ⟨-, hφ', hψ'⟩ := mem_lowerRouteMaps.1 hg'
    obtain rfl := PatternPlacement3.eq_of_forall_mem hφ hφ'
    obtain rfl := PairColorPlacement3.eq_of_forall_colorOfPair_eq_some hψ hψ'
    rfl
  -- Every map along an exceptional route is an embedding meeting an irregular polyad.
  have hsub : s.biUnion (fun σ ↦ lowerRouteMaps σ.1 σ.2) ⊆
      ({f : Fin F.k ↪ V | ∃ P ∈ C.polyads, ¬H.IsTopRegularOverPolyad P η r ∧
        ∃ i j l : Fin F.k, i < j ∧ j < l ∧ ∃ x ∈ P.support, x.1 = ![f i, f j, f l]} :
          Finset (Fin F.k ↪ V)).map ⟨fun f : Fin F.k ↪ V ↦ ⇑f, DFunLike.coe_injective⟩ := by
    intro g hg
    obtain ⟨⟨φ, ψ⟩, hσ, hg⟩ := mem_biUnion.1 hg
    obtain ⟨hinj, hcell, hcolor⟩ := mem_lowerRouteMaps.1 hg
    obtain ⟨i, j, l, hij, hjl, hirr⟩ : ∃ (i j l : Fin F.k) (hij : i < j) (hjl : j < l),
        ¬H.IsTopRegularOverPolyad (ψ.polyad i j l hij hjl) η r := by
      simpa [s, PairColorPlacement3.isTopRegularRoute_iff] using hσ
    have hmono : StrictMono ![i, j, l] :=
      Fin.strictMono_iff_lt_succ.2 fun m ↦ by fin_cases m; exacts [hij, hjl]
    refine mem_map.2 ⟨⟨g, hinj⟩, mem_filter.2 ⟨mem_univ _, ψ.polyad i j l hij hjl,
      ψ.polyad_mem i j l hij hjl, hirr, i, j, l, hij, hjl,
      ⟨g ∘ ![i, j, l], hinj.comp hmono.injective⟩, ?_, ?_⟩, rfl⟩
    · simp [hcell, hcolor ⟨(i, j), hij⟩, hcolor ⟨(i, l), hij.trans hjl⟩, hcolor ⟨(j, l), hjl⟩]
    · ext m
      fin_cases m <;> simp
  have hsum : ∑ φ : PatternPlacement3 C F, ∑ ψ : PairColorPlacement3 φ with
      ¬ψ.IsTopRegularRoute H η r, lowerRouteCountAt φ ψ =
        #(s.biUnion fun σ ↦ lowerRouteMaps σ.1 σ.2) := by
    rw [card_biUnion hdisj, sum_filter]
    simp only [sum_filter, lowerRouteCountAt_def]
    exact (Fintype.sum_sigma fun σ : Σ φ : PatternPlacement3 C F, PairColorPlacement3 φ ↦
      if ¬σ.2.IsTopRegularRoute H η r then #(lowerRouteMaps σ.1 σ.2) else 0).symm
  exact_mod_cast hsum.le.trans ((card_le_card hsub).trans_eq (card_map _))

variable {H} in
/-- **The exceptional predicted mass.** For a pattern on `k` vertices and an `ε`-regular lower
skeleton with `m` pair colors, the prediction of the transversal placements along routes that are
not `(η, r)`-top-regular for `H` is at most
`(k.choose 3 * H.exceptionalPolyadMass C η r + m ^ (k.choose 2) * k.choose 2 * ε) * |V| ^ k`.
The first term is the mass of the maps realizing these routes; the second pays the lower-route
counting error once for each route of every placement. -/
theorem exceptional_route_prediction_mass_le {ε : ℝ} (hε : 0 ≤ ε)
    (hreg : C.skeleton.IsPairColorRegular ε) (η : ℝ) (r : ℕ) :
    H.exceptionalPredictedMass3 C F η r ≤
      (F.k.choose 3 * H.exceptionalPolyadMass C η r +
        C.pairColorCount ^ F.k.choose 2 * F.k.choose 2 * ε) * (Fintype.card V : ℝ) ^ F.k := by
  classical
  set B : PatternPlacement3 C F → ℝ := fun φ ↦ ∏ i, (#(φ.vertexCell i) : ℝ)
  have hB (φ) : 0 ≤ B φ := prod_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hε' : 0 ≤ (F.k.choose 2 : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε
  -- Along each route of a transversal placement, the prediction is at most the number of maps
  -- realizing the lower route plus the lower-route counting error.
  have hroute {φ : PatternPlacement3 C F} (hφ : φ.Transversal) (ψ : PairColorPlacement3 φ) :
      H.expectedInducedCountAt φ ψ ≤ lowerRouteCountAt φ ψ + F.k.choose 2 * ε * B φ := by
    have := abs_sub_le_iff.1 (abs_lowerRouteCountAt_sub_expectedLowerRouteCountAt_le hφ ψ hreg)
    linarith [H.expectedInducedCountAt_le_expectedLowerRouteCountAt φ ψ]
  -- Each placement has at most `m ^ (k choose 2)` routes.
  have hcard (φ : PatternPlacement3 C F) :
      (#{ψ : PairColorPlacement3 φ | ¬ψ.IsTopRegularRoute H η r} : ℝ) ≤
        C.pairColorCount ^ F.k.choose 2 := by
    exact_mod_cast (card_filter_le _ _).trans PairColorPlacement3.card_le_pairColorCount_pow
  have hlower := H.sum_lowerRouteCountAt_not_isTopRegularRoute_le C F η r
  have hsumB : ∑ φ, B φ = (Fintype.card V : ℝ) ^ F.k := by
    simp only [B]
    exact_mod_cast PatternPlacement3.sum_prod_card_vertexCell (C := C) (F := F)
  calc H.exceptionalPredictedMass3 C F η r
      ≤ ∑ φ : PatternPlacement3 C F with φ.Transversal,
          ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r,
            ((lowerRouteCountAt φ ψ : ℝ) + F.k.choose 2 * ε * B φ) :=
        sum_le_sum fun φ hφ ↦ sum_le_sum fun ψ _ ↦ hroute (mem_filter.1 hφ).2 ψ
    _ = ∑ φ : PatternPlacement3 C F with φ.Transversal,
          ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r,
            (lowerRouteCountAt φ ψ : ℝ) +
        ∑ φ : PatternPlacement3 C F with φ.Transversal,
          (#{ψ : PairColorPlacement3 φ | ¬ψ.IsTopRegularRoute H η r} : ℝ) *
            (F.k.choose 2 * ε * B φ) := by
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ∑ φ : PatternPlacement3 C F,
          ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r,
            (lowerRouteCountAt φ ψ : ℝ) +
        ∑ φ : PatternPlacement3 C F,
          (C.pairColorCount ^ F.k.choose 2 : ℝ) * (F.k.choose 2 * ε * B φ) := by
        gcongr ?_ + ?_
        · exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun φ _ _ ↦
            sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
        · refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun φ _ _ ↦
            mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hε' (hB φ))).trans
            (sum_le_sum fun φ _ ↦ ?_)
          exact mul_le_mul_of_nonneg_right (hcard φ) (mul_nonneg hε' (hB φ))
    _ ≤ F.k.choose 3 * H.exceptionalPolyadMass C η r * (Fintype.card V : ℝ) ^ F.k +
        C.pairColorCount ^ F.k.choose 2 * (F.k.choose 2 * ε * (Fintype.card V : ℝ) ^ F.k) := by
        rw [← mul_sum, ← mul_sum, hsumB]
        linarith
    _ = (F.k.choose 3 * H.exceptionalPolyadMass C η r +
          C.pairColorCount ^ F.k.choose 2 * F.k.choose 2 * ε) * (Fintype.card V : ℝ) ^ F.k := by
        ring

end Colored3Graph

end TauCeti
