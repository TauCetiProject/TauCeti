/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.MapCells
public import TauCeti.Combinatorics.Hypergraph.Polyad.SupportStability
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

/-!
# Top regularity after moving vertices between matched cells

Rebalancing a vertex partition keeps the pair coloring but changes the cells. Match the old
cells injectively to the new cells, and suppose only vertices in `B` leave their matched cell.
A triple whose polyad is not preserved must meet `B`, so at most `3 |B| |V|²` triples move.
Combining this count with support stability bounds the new irregular support by the old
irregular support plus `(1 + 2 / η) 3 |B| |V|²`, independently of the palette size.

The final theorem expresses this bound as top regularity over most polyads of the new
partition. No equitability is assumed: the estimate can be applied to the output of any
rebalancing construction with a bound on the moved vertex set. It includes repeated cells,
empty hosts, and arbitrary ranks, and does not change the triple coloring.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the padding-and-rebalancing setting.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {S T : PairSkeleton3 κ₂ V} {H : Colored3Graph κ V} {δ ε η : ℝ} {r : ℕ}

open Classical in
/-- Moving vertices in `B` between injectively matched cells increases irregular support
mass by at most `(1 + 2 / η) 3 |B| |V|²`. Pair colors and the top coloring stay unchanged.
The regularity parameters must satisfy `δ + 2η + η / ε ≤ ε`. -/
theorem sum_card_support_not_isTopRegularOverPolyad_le_of_vertexRepartition
    [Fintype κ₂]
    (f : S.vertexPart.parts ↪ T.vertexPart.parts)
    (hcolors : ∀ p, S.pairColors.color p = T.pairColors.color p) (B : Finset V)
    (hcells : ∀ v ∉ B, (f ⟨S.vertexPart.part v,
      S.vertexPart.part_mem.2 (mem_univ _)⟩ : Finset V) = T.vertexPart.part v)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    (∑ Q : Polyad3 T with ¬H.IsTopRegularOverPolyad Q ε r, (#Q.support : ℝ)) ≤
      (∑ P : Polyad3 S with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
        (1 + 2 / η) * (3 * #B * (Fintype.card V : ℝ) ^ 2) := by
  have h := sum_card_support_not_isTopRegularOverPolyad_le_of_injective (H := H) (r := r)
    (Polyad3.mapCells_injective f.injective) hε hη hbudget
  refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_
    (add_nonneg zero_le_one (div_nonneg (by norm_num) hη.le))))
  exact_mod_cast Polyad3.card_ofTriple_ne_mapCells_le f hcolors B hcells

/-- Top regularity over most polyads survives moving only the vertices of `B` between matched
cells. The new complex selects all polyads and keeps the pair coloring. The error charge is
normalized by the original number of ordered injective triples; when that number is zero,
both exceptional masses and the charge are zero. -/
theorem TopRegularOverMostPolyads.of_vertexRepartition {C : TriadicComplex3 V} {ε₀ : ℝ}
    (h : H.TopRegularOverMostPolyads C δ ε₀ r) (hC : C.IsPolyadDecomposition)
    (P : Finpartition (univ : Finset V)) (f : C.skeleton.vertexPart.parts ↪ P.parts)
    (B : Finset V)
    (hcells : ∀ v ∉ B, (f ⟨C.skeleton.vertexPart.part v,
      C.skeleton.vertexPart.part_mem.2 (mem_univ _)⟩ : Finset V) = P.part v)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    H.TopRegularOverMostPolyads
      ⟨C.pairColorCount, ⟨P, C.skeleton.pairColors⟩, univ⟩ ε
      (ε₀ + (1 + 2 / η) * (3 * #B * (Fintype.card V : ℝ) ^ 2) /
        (Fintype.card V).descFactorial 3) r := by
  classical
  let D : TriadicComplex3 V := ⟨C.pairColorCount, ⟨P, C.skeleton.pairColors⟩, univ⟩
  have hD : D.IsPolyadDecomposition :=
    D.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ mem_univ _
  have hmass := sum_card_support_not_isTopRegularOverPolyad_le_of_vertexRepartition
    (H := H) (r := r) (T := D.skeleton) f (fun _ ↦ rfl) B hcells hε hη hbudget
  have hnorm := div_le_div_of_nonneg_right hmass
    (Nat.cast_nonneg (α := ℝ) ((Fintype.card V).descFactorial 3))
  rw [add_div, ← exceptionalPolyadMass_eq_sum_div hC,
    ← exceptionalPolyadMass_eq_sum_div hD] at hnorm
  exact topRegularOverMostPolyads_iff.2
    (hnorm.trans (add_le_add (topRegularOverMostPolyads_iff.1 h) le_rfl))

end TauCeti.Colored3Graph
