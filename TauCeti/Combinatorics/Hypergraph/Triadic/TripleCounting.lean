/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.InducedCounting

/-!
# Counting a single colored triple over a triadic complex

The smallest pattern with a triple constraint is a single triple of a color `c`, the pattern
`FiniteColored3Pattern.const 3 c` on three vertices. This file works out the induced counting
lemma `Colored3Graph.abs_inducedCopyCount_sub_expectedInducedCount_le_of_topRegular` for it.

Its labeled induced copies in a coloring `H` are the injective triples of vertices whose
underlying triple has color `c` (`Colored3Graph.inducedCopyCount_const_three`). A placement of
the pattern into a triadic complex `C` together with a route over it is the same datum as a
selected polyad `P` of `C`: three vertex cells and the colors of the three canonical pairs.
Hence the prediction is a sum over the selected polyads. Each polyad `P` contributes the number
of injective triples with coordinates in its cells, times the densities of its three pair colors
over the corresponding pairs of cells, times the relative density of `c` over `P`.

Over a polyad decomposition, the exact number of injective triples of color `c` is the sum over
the selected polyads of the support size times the relative density of `c`
(`Colored3Graph.card_filter_color_eq_sum_card_support_mul_relativeDensity`). For this pattern the
prediction therefore replaces the support of each polyad by its lower-skeleton estimate (the
injective triples of its cells times its three pair densities) and keeps the relative densities.
The counting lemma bounds the total error by `ε |V| ^ 3`.

## Main results

* `TauCeti.Colored3Graph.expectedInducedCount_const_three`: the prediction for a single colored
  triple as a sum over the selected polyads.
* `TauCeti.Colored3Graph.abs_card_filter_color_sub_sum_le_of_topRegular`: the counting lemma
  for a single colored triple.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Function

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V] {C : TriadicComplex3 V}

section ThreeVertices

/-! ### Placements and routes of a pattern on three vertices -/

variable {G : Colored3Graph κ (Fin 3)}

/-- A product over the three canonical pairs of three pattern vertices. -/
private theorem prod_pair_fin_three {M : Type*} [CommMonoid M]
    (f : {p : Fin 3 × Fin 3 // p.1 < p.2} → M) :
    ∏ p, f p = f ⟨(0, 1), by decide⟩ * f ⟨(0, 2), by decide⟩ * f ⟨(1, 2), by decide⟩ := by
  rw [show (univ : Finset {p : Fin 3 × Fin 3 // p.1 < p.2}) =
      {⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩} by decide,
    prod_insert (by decide), prod_insert (by decide), prod_singleton, mul_assoc]

/-- A product over the single increasing triple of three pattern vertices. -/
private theorem prod_triple_fin_three {M : Type*} [CommMonoid M]
    (f : {t : Fin 3 × Fin 3 × Fin 3 // t.1 < t.2.1 ∧ t.2.1 < t.2.2} → M) :
    ∏ t, f t = f ⟨(0, 1, 2), by decide⟩ := by
  rw [show (univ : Finset {t : Fin 3 × Fin 3 × Fin 3 // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) =
      {⟨(0, 1, 2), by decide⟩} by decide, prod_singleton]

/-- The only increasing triple of three pattern vertices is `0 < 1 < 2`. -/
private theorem eq_zero_one_two {i j l : Fin 3} (hij : i < j) (hjl : j < l) :
    i = 0 ∧ j = 1 ∧ l = 2 := by
  omega

private theorem fin_three_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  omega

/-- The canonical pairs of three pattern vertices are `(0, 1)`, `(0, 2)` and `(1, 2)`. -/
private theorem pair_fin_three_cases (p : {p : Fin 3 × Fin 3 // p.1 < p.2}) :
    p = ⟨(0, 1), by decide⟩ ∨ p = ⟨(0, 2), by decide⟩ ∨ p = ⟨(1, 2), by decide⟩ := by
  revert p
  decide

private theorem zero_lt_one_fin_three : (0 : Fin 3) < 1 := by decide

private theorem one_lt_two_fin_three : (1 : Fin 3) < 2 := by decide

/-- The placement and route of a pattern on three vertices given by a selected polyad. -/
private def placementOfPolyad (P : Polyad3 C.skeleton) (hP : P ∈ C.polyads) :
    Σ φ : PatternPlacement3 C (⟨3, G⟩ : FiniteColored3Pattern κ), PairColorPlacement3 φ :=
  ⟨⟨![P.c₀, P.c₁, P.c₂], fun i ↦ by
      rcases fin_three_cases i with rfl | rfl | rfl <;> simp [P.hc₀, P.hc₁, P.hc₂]⟩,
    ⟨fun p ↦ if p.val.1 = 0 then (if p.val.2 = 1 then P.color₀₁ else P.color₀₂) else P.color₁₂,
      fun i j l hij hjl ↦ by
        obtain ⟨rfl, rfl, rfl⟩ := eq_zero_one_two hij hjl
        convert hP
        ext <;> simp⟩⟩

/-- The selected polyad of the route of a pattern on three vertices. -/
private def polyadOfRoute
    (σ : Σ φ : PatternPlacement3 C (⟨3, G⟩ : FiniteColored3Pattern κ), PairColorPlacement3 φ) :
    Polyad3 C.skeleton :=
  σ.2.polyad 0 1 2 zero_lt_one_fin_three one_lt_two_fin_three

private theorem polyadOfRoute_mem
    (σ : Σ φ : PatternPlacement3 C (⟨3, G⟩ : FiniteColored3Pattern κ), PairColorPlacement3 φ) :
    polyadOfRoute σ ∈ C.polyads :=
  σ.2.polyad_mem ..

private theorem polyadOfRoute_placementOfPolyad (P : Polyad3 C.skeleton) (hP : P ∈ C.polyads) :
    polyadOfRoute (placementOfPolyad (G := G) P hP) = P := by
  ext <;> simp [polyadOfRoute, placementOfPolyad]

private theorem placementOfPolyad_polyadOfRoute
    (σ : Σ φ : PatternPlacement3 C (⟨3, G⟩ : FiniteColored3Pattern κ), PairColorPlacement3 φ) :
    placementOfPolyad (polyadOfRoute σ) (polyadOfRoute_mem σ) = σ := by
  -- Both the cells and the pair colors are determined by their values at `0, 1, 2`.
  refine PairColorPlacement3.sigma_ext (funext fun i ↦ ?_) (funext fun p ↦ ?_)
  · rcases fin_three_cases i with rfl | rfl | rfl <;> simp [placementOfPolyad, polyadOfRoute]
  · rcases pair_fin_three_cases p with rfl | rfl | rfl <;> simp [placementOfPolyad, polyadOfRoute]

/-- The cell-respecting injections of a placement of three pattern vertices are the injective
triples with coordinates in the assigned cells. -/
private theorem placementInjectionCount_eq_card_filter
    (φ : PatternPlacement3 C (⟨3, G⟩ : FiniteColored3Pattern κ)) :
    placementInjectionCount φ = #{x : {x : Fin 3 → V // Injective x} |
      x.val 0 ∈ φ.vertexCell 0 ∧ x.val 1 ∈ φ.vertexCell 1 ∧ x.val 2 ∈ φ.vertexCell 2} := by
  rw [placementInjectionCount_def, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun f := ⟨f, f.injective⟩, invFun x := ⟨x.val, x.property⟩ } fun f ↦ ?_)
  simp [Fin.forall_fin_succ]

end ThreeVertices

namespace Colored3Graph

variable [DecidableEq κ] {H H' : Colored3Graph κ V}

/-- **The prediction for a single colored triple.** The predicted number of induced copies of the
single triple of color `c` is the sum, over the selected polyads `P` of `C`, of the number of
injective triples with coordinates in the cells of `P`, times the densities of the three pair
colors of `P` over the corresponding pairs of cells, times the relative density of `c` over `P`. -/
theorem expectedInducedCount_const_three (H : Colored3Graph κ V) (C : TriadicComplex3 V) (c : κ) :
    H.expectedInducedCount C (FiniteColored3Pattern.const 3 c) =
      ∑ P ∈ C.polyads,
        (#{x : {x : Fin 3 → V // Injective x} |
            x.val 0 ∈ P.c₀ ∧ x.val 1 ∈ P.c₁ ∧ x.val 2 ∈ P.c₂} : ℝ) *
          (pairColorDensity C.skeleton.pairColors P.color₀₁ P.c₀ P.c₁ : ℝ) *
          (pairColorDensity C.skeleton.pairColors P.color₀₂ P.c₀ P.c₂ : ℝ) *
          (pairColorDensity C.skeleton.pairColors P.color₁₂ P.c₁ P.c₂ : ℝ) *
          (H.relativeDensity c P : ℝ) := by
  rw [FiniteColored3Pattern.const_def, expectedInducedCount_def]
  refine (Fintype.sum_sigma fun σ : Σ φ : PatternPlacement3 C ⟨3, Colored3Graph.const c⟩,
    PairColorPlacement3 φ ↦ H.expectedInducedCountAt σ.1 σ.2).symm.trans ?_
  refine sum_bij' (fun σ _ ↦ polyadOfRoute σ) (fun P hP ↦ placementOfPolyad P hP)
    (fun σ _ ↦ polyadOfRoute_mem σ) (fun _ _ ↦ mem_univ _)
    (fun σ _ ↦ placementOfPolyad_polyadOfRoute σ)
    (fun P hP ↦ polyadOfRoute_placementOfPolyad P hP) fun ⟨φ, ψ⟩ _ ↦ ?_
  rw [expectedInducedCountAt_def, prod_pair_fin_three, prod_triple_fin_three,
    placementInjectionCount_eq_card_filter]
  -- The polyad of the route has the cells and pair colors of `φ` and `ψ`, and the pattern color
  -- of its triple is `c`.
  simp [polyadOfRoute, FiniteColored3Pattern.tripleColor_def, mul_assoc]

/-- **Counting a single colored triple.** Let `C` be a polyad decomposition and `0 < ε`, and
suppose that `H` approximates `H'`, that the lower skeleton of `C` is regular, and that `H'` is
top-regular over most polyads of `C` at a positive rank, all at the parameters of the induced
counting lemma for patterns on three vertices, and that the vertex cells of `C` form an
equipartition into at least `diagonalControl3 3 ε` cells. Then the number of injective triples
of `H` of color `c` differs by at most `ε |V| ^ 3` from the sum over the selected polyads `P` of
the injective triples in the cells of `P`, times the three pair densities of `P`, times the
relative density of `c` in `H'` over `P`. -/
theorem abs_card_filter_color_sub_sum_le_of_topRegular (hC : C.IsPolyadDecomposition) {ε : ℝ}
    (hε : 0 < ε) (c : κ) (hedit : H.Approximates3 H' (inducedCountingParameter3 3 ε))
    (hlower : C.skeleton.LowerSkeletonRegular (inducedCountingSchedule3 3 ε))
    {r : ℕ} (hr : 1 ≤ r)
    (htop : H'.TopRegularOverMostPolyads C (inducedCountingSchedule3 3 ε C.complexity)
      (inducedCountingParameter3 3 ε) r)
    (hcells : C.VertexCellsControlled (diagonalControl3 3 ε)) :
    |(#{x : {x : Fin 3 → V // Injective x} |
        H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) -
      ∑ P ∈ C.polyads,
        (#{x : {x : Fin 3 → V // Injective x} |
            x.val 0 ∈ P.c₀ ∧ x.val 1 ∈ P.c₁ ∧ x.val 2 ∈ P.c₂} : ℝ) *
          (pairColorDensity C.skeleton.pairColors P.color₀₁ P.c₀ P.c₁ : ℝ) *
          (pairColorDensity C.skeleton.pairColors P.color₀₂ P.c₀ P.c₂ : ℝ) *
          (pairColorDensity C.skeleton.pairColors P.color₁₂ P.c₁ P.c₂ : ℝ) *
          (H'.relativeDensity c P : ℝ)| ≤
      ε * (Fintype.card V : ℝ) ^ 3 := by
  have h := abs_inducedCopyCount_sub_expectedInducedCount_le_of_topRegular
    (F := FiniteColored3Pattern.const 3 c) hC hε (by simpa using hedit) (by simpa using hlower)
    hr (by simpa using htop) (by simpa using hcells)
  rwa [inducedCopyCount_const_three, expectedInducedCount_const_three,
    FiniteColored3Pattern.k_const] at h

end Colored3Graph

end TauCeti
