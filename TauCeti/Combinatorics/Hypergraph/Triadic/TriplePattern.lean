/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.InducedCounting
import TauCeti.Data.Fintype.EmbeddingFiber

/-!
# Counting the triples of one color over a regular triadic complex

This file works out the induced counting lemma for the simplest colored three-uniform pattern,
`FiniteColored3Pattern.const 3 c`: three vertices whose triple has color `c`. Its labelled
induced copies in a coloring `H` of the triples of `V` are the orderings of the triples of
color `c`, so `H.inducedCopyCount (const 3 c) = 6 * #{s | H.color s = c}`
(`Colored3Graph.inducedCopyCount_const_three`).

For a pattern on three vertices, a placement together with a route is the same as a selected
polyad `P` of the triadic complex `C`: the three cells and the three pair colors of `P`. The
prediction is therefore a sum over the selected polyads. Each polyad contributes the number of
injective triples with one vertex in each of its cells, times the densities of its three pair
colors between its cells, times the relative density of `c` over its support.

When the polyads of `C` decompose the injective triples, the actual count is the same sum with
the predicted volume of each polyad replaced by the size of its support. The counting lemma
`Colored3Graph.abs_inducedCopyCount_sub_expectedInducedCount_le_of_topRegular` at `k = 3`
bounds the difference between the two by `ε |V| ^ 3` under its regularity hypotheses.

## Main results

* `TauCeti.Colored3Graph.expectedInducedCount_const_three`: the prediction for a single triple of
  color `c` as a sum over the selected polyads.
* `TauCeti.Colored3Graph.sum_relativeDensity_mul_card_support`: over a polyad decomposition, the
  relative densities of `c` weighted by the support sizes add up to six times the number of
  triples of color `c`.
* `TauCeti.Colored3Graph.abs_six_mul_card_sub_sum_polyads_le_of_topRegular`: the counting lemma
  for the triples of color `c`, with the prediction written out over the polyads.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V] {C : TriadicComplex3 V}

/-- The placement of the three pattern vertices into the cells of a selected polyad, with the
route recording the pair colors of the polyad. -/
private def polyadSigma (c : κ) (P : Polyad3 C.skeleton) (hP : P ∈ C.polyads) :
    Σ φ : PatternPlacement3 C (⟨3, Colored3Graph.const c⟩ : FiniteColored3Pattern κ),
      PairColorPlacement3 φ :=
  ⟨⟨![P.c₀, P.c₁, P.c₂], fun i ↦ by fin_cases i; exacts [P.hc₀, P.hc₁, P.hc₂]⟩,
    ⟨fun p ↦
      if p.1.2 = 1 then P.color₀₁ else if p.1.1 = 0 then P.color₀₂ else P.color₁₂,
      fun i j l hij hjl ↦ by
        convert hP using 1
        fin_cases i <;> fin_cases j <;> fin_cases l <;> simp at hij hjl
        refine Polyad3.ext_data ?_ ?_ ?_ ?_ ?_ ?_ <;> simp⟩⟩

/-- **The prediction for a single colored triple.** Over a triadic complex `C`, the predicted
number of labelled induced copies of a triple of color `c` is the sum over the selected polyads
`P` of the number of injective triples with one vertex in each cell of `P`, times the densities
of the three pair colors of `P` between its cells, times the relative density of `c` over `P`. -/
theorem expectedInducedCount_const_three (H : Colored3Graph κ V) (C : TriadicComplex3 V)
    (c : κ) :
    H.expectedInducedCount C (FiniteColored3Pattern.const 3 c) = ∑ P ∈ C.polyads,
      (Nat.card {f : Fin 3 ↪ V // f 0 ∈ P.c₀ ∧ f 1 ∈ P.c₁ ∧ f 2 ∈ P.c₂} : ℝ) *
        ((pairColorDensity C.skeleton.pairColors P.color₀₁ P.c₀ P.c₁ : ℝ) *
          pairColorDensity C.skeleton.pairColors P.color₀₂ P.c₀ P.c₂ *
          pairColorDensity C.skeleton.pairColors P.color₁₂ P.c₁ P.c₂) *
        H.relativeDensity c P := by
  rw [FiniteColored3Pattern.const_def, expectedInducedCount_def]
  refine (Fintype.sum_sigma fun σ ↦ H.expectedInducedCountAt σ.1 σ.2).symm.trans ?_
  -- A placement with a route is determined by the polyad it induces on the triple `0 < 1 < 2`.
  refine sum_bij (fun σ _ ↦ σ.2.polyad 0 1 2 (by simp) (by simp))
    (fun σ _ ↦ σ.2.polyad_mem _ _ _ _ _) (fun σ _ τ _ h ↦ ?_)
    (fun P hP ↦ ⟨polyadSigma c P hP, mem_univ _, ?_⟩) (fun σ _ ↦ ?_)
  · obtain ⟨φ, ψ⟩ := σ
    obtain ⟨φ', ψ'⟩ := τ
    have hc (i) : φ.vertexCell i = φ'.vertexCell i := by
      fin_cases i
      · simpa using congrArg Polyad3.c₀ h
      · simpa using congrArg Polyad3.c₁ h
      · simpa using congrArg Polyad3.c₂ h
    obtain rfl : φ = φ' := PatternPlacement3.ext (funext hc)
    have hk (p) : ψ.pairColor p = ψ'.pairColor p := by
      obtain ⟨⟨i, j⟩, hij⟩ := p
      fin_cases i <;> fin_cases j <;> simp at hij
      · simpa using congrArg Polyad3.color₀₁ h
      · simpa using congrArg Polyad3.color₀₂ h
      · simpa using congrArg Polyad3.color₁₂ h
    obtain rfl : ψ = ψ' := PairColorPlacement3.ext (funext hk)
    rfl
  · refine Polyad3.ext_data ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [polyadSigma]
  · -- The three pattern pairs and the single pattern triple, written out.
    obtain ⟨φ, ψ⟩ := σ
    have huniv₂ : (univ : Finset {p : Fin 3 × Fin 3 // p.1 < p.2}) =
        {⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩} := by decide
    have huniv₃ : (univ : Finset {t : Fin 3 × Fin 3 × Fin 3 // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) =
        {⟨(0, 1, 2), by decide⟩} := by decide
    have hcard : Nat.card {f : Fin 3 ↪ V // ∀ i, f i ∈ φ.vertexCell i} =
        Nat.card {f : Fin 3 ↪ V //
          f 0 ∈ φ.vertexCell 0 ∧ f 1 ∈ φ.vertexCell 1 ∧ f 2 ∈ φ.vertexCell 2} :=
      Nat.card_congr <| Equiv.subtypeEquivRight fun f ↦ ⟨fun h ↦ ⟨h 0, h 1, h 2⟩,
        fun h i ↦ by fin_cases i; exacts [h.1, h.2.1, h.2.2]⟩
    rw [expectedInducedCountAt_def, huniv₂, huniv₃, prod_insert (by simp),
      prod_insert (by simp), prod_singleton, prod_singleton, placementInjectionCount_def]
    simp only [PairColorPlacement3.polyad_c₀, PairColorPlacement3.polyad_c₁,
      PairColorPlacement3.polyad_c₂, PairColorPlacement3.polyad_color₀₁,
      PairColorPlacement3.polyad_color₀₂, PairColorPlacement3.polyad_color₁₂,
      FiniteColored3Pattern.tripleColor_def, color_const]
    rw [hcard]
    ring

/-- **The actual count of a single colored triple.** Over a polyad decomposition, summing the
relative density of `c` over each selected polyad, weighted by the size of its support, gives six
times the number of triples of color `c`. Compare `expectedInducedCount_const_three`, where the
support size of each polyad is replaced by its predicted volume. -/
theorem sum_relativeDensity_mul_card_support (H : Colored3Graph κ V)
    (hC : C.IsPolyadDecomposition) (c : κ) :
    ∑ P ∈ C.polyads, (H.relativeDensity c P : ℝ) * #P.support = 6 * #{s | H.color s = c} := by
  let q (x : {x : Fin 3 → V // Function.Injective x}) : Prop :=
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
  have hP (P : Polyad3 C.skeleton) :
      (H.relativeDensity c P : ℝ) * #P.support = #{x ∈ P.support | q x} := by
    rw [relativeDensity_def]
    exact_mod_cast H.relDensityOn_mul_card c P.support
  -- The supports of the selected polyads partition the injective triples.
  have hU : C.polyads.biUnion (fun P ↦ {x ∈ P.support | q x}) = ({x | q x} : Finset _) := by
    ext x
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨_, _, _, hx⟩ ↦ hx, fun hx ↦
      (C.isPolyadDecomposition_iff.1 hC x).imp fun P h ↦ ⟨h.1, h.2, hx⟩⟩
  -- An injective triple is the same as an embedding of `Fin 3`, and each triple of color `c` is
  -- the image of `3! = 6` embeddings.
  have hcard : #{x | q x} = Nat.factorial 3 * #{s | H.color s = c} :=
    (card_equiv (Equiv.subtypeInjectiveEquivEmbedding _ _) fun x ↦ by
      rw [mem_filter_univ, mem_filter_univ]
      rfl).trans (Set.powersetCard.card_filter_ofFinEmb fun s ↦ H.color s = c)
  simp_rw [hP]
  rw [← Nat.cast_sum, ← card_biUnion fun P _ Q _ hPQ ↦ disjoint_filter_filter
    (Polyad3.pairwise_disjoint_support hPQ), hU, hcard]
  norm_num [Nat.factorial]

/-- **Counting the triples of one color over a regular triadic complex.** Under the hypotheses of
`abs_inducedCopyCount_sub_expectedInducedCount_le_of_topRegular` for a pattern on three vertices,
six times the number of triples of color `c` in `H` differs by at most `ε |V| ^ 3` from the sum
over the selected polyads `P` of the number of injective triples with one vertex in each cell of
`P`, times the three pair-color densities of `P`, times the relative density of `c` over `P` in
`H'`. -/
theorem abs_six_mul_card_sub_sum_polyads_le_of_topRegular {H H' : Colored3Graph κ V}
    (hC : C.IsPolyadDecomposition) {ε : ℝ} (hε : 0 < ε)
    (hedit : H.Approximates3 H' (inducedCountingParameter3 3 ε))
    (hlower : C.skeleton.LowerSkeletonRegular (inducedCountingSchedule3 3 ε))
    {r : ℕ} (hr : 1 ≤ r)
    (htop : H'.TopRegularOverMostPolyads C (inducedCountingSchedule3 3 ε C.complexity)
      (inducedCountingParameter3 3 ε) r)
    (hcells : C.VertexCellsControlled (diagonalControl3 3 ε)) (c : κ) :
    |6 * (#{s | H.color s = c} : ℝ) - ∑ P ∈ C.polyads,
      (Nat.card {f : Fin 3 ↪ V // f 0 ∈ P.c₀ ∧ f 1 ∈ P.c₁ ∧ f 2 ∈ P.c₂} : ℝ) *
        ((pairColorDensity C.skeleton.pairColors P.color₀₁ P.c₀ P.c₁ : ℝ) *
          pairColorDensity C.skeleton.pairColors P.color₀₂ P.c₀ P.c₂ *
          pairColorDensity C.skeleton.pairColors P.color₁₂ P.c₁ P.c₂) *
        H'.relativeDensity c P| ≤ ε * (Fintype.card V : ℝ) ^ 3 := by
  have h := abs_inducedCopyCount_sub_expectedInducedCount_le_of_topRegular
    (F := ⟨3, Colored3Graph.const c⟩) hC hε hedit hlower hr htop hcells
  rwa [← FiniteColored3Pattern.const_def, inducedCopyCount_const_three,
    expectedInducedCount_const_three, FiniteColored3Pattern.k_const, Nat.cast_mul,
    Nat.cast_ofNat] at h

end Colored3Graph

end TauCeti
