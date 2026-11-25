/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.InducedCounting
public import TauCeti.Combinatorics.Hypergraph.Triadic.Recoloring
public import TauCeti.Combinatorics.Hypergraph.Triadic.RegularityLemma
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-!
# Strong regular approximation of colorings of triples

A strong regular approximation of a coloring `H` of the triples of `V` is a second coloring `H'`
together with a triadic complex `C` such that

* `H'` is within edit discrepancy `ε` of `H`,
* the selected polyads of `C` decompose the injective triples,
* the lower skeleton of `C` is regular for a schedule `F`, evaluated at the number of vertex cells
  plus the number of pair colors,
* `H'` is `(F C.complexity, R C.complexity)`-top-regular over all polyads of `C` outside an
  `ε`-proportion of the injective triples, and
* the complexity of `C` is at most a bound `b`.

The approximation weakens as `ε`, `F` and `b` grow and as `R` drops
(`Colored3Graph.IsStrongRegularApproximation3.mono`), and a strong regular approximation of `H` is
one of every coloring close to `H`, with the edit discrepancy added to `ε`
(`Colored3Graph.IsStrongRegularApproximation3.of_approximates3`).

Both schedules are chosen before the complexity bound. The regularity conditions of the predicate
evaluate them only at the complex `C`: `F` at its number of vertex cells plus pair colors for
skeleton regularity and at `C.complexity` for top regularity, and `R` only at `C.complexity`. The
bound `regularityBound3`, by contrast, depends on the whole schedules. The regular approximation
lemma for three-uniform hypergraphs (`Colored3Graph.exists_strong_regular_approximation3`) gives
every coloring of the triples of a large enough host a strong regular approximation at the bound
`regularityBound3 q ε F R t₀`, which depends only on the number `q` of top colors, `ε`, `F`, `R`
and the requested number `t₀` of vertex cells. It combines the regularity lemma with a
regular lower skeleton
(`Colored3Graph.exists_strong_topRegularOverMostPolyads_lowerSkeletonRegular`), which produces a
coarse complex and a fine palette refinement with a small polyad energy gap, with the coupled
recoloring of the triples toward the coarse densities
(`Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_recoloringHostBound_le`).

At the parameters of the induced counting lemma, a strong regular approximation with controlled
vertex cells and positive rank `1 ≤ R C.complexity` predicts the induced copies of a fixed colored
pattern on `k` vertices within `ε |V| ^ k`
(`Colored3Graph.IsStrongRegularApproximation3.abs_inducedCopyCount_sub_expectedInducedCount_le`),
so, for a pointwise positive rank schedule `R`, every coloring on a large enough host has such a
prediction (`Colored3Graph.exists_strong_regular_approximation3_counting`).

## Main definitions

* `TauCeti.regularityBound3`: the host-independent bound on the complexity, which is also the
  size of host required.
* `TauCeti.Colored3Graph.IsStrongRegularApproximation3`: strong regular approximation.

## Main results

* `TauCeti.Colored3Graph.IsStrongRegularApproximation3.mono`: monotonicity in the parameters.
* `TauCeti.Colored3Graph.IsStrongRegularApproximation3.of_approximates3`: edit transfer.
* `TauCeti.Colored3Graph.exists_strong_regular_approximation3`: every coloring of the triples of a
  large enough host has a strong regular approximation with at least `t₀` equitable vertex cells.
* `Colored3Graph.IsStrongRegularApproximation3.abs_inducedCopyCount_sub_expectedInducedCount_le`:
  induced counting from a strong regular approximation at the counting parameters.
* `TauCeti.Colored3Graph.exists_strong_regular_approximation3_counting`: a strong regular
  approximation together with its induced counting estimate.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorems 2.2 and 2.3 and Lemma 4.2.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti

/-- The complexity bound in the strong regular approximation of a coloring of the triples with `q`
top colors, at edit discrepancy and exceptional proportion `ε`, regularity schedule `F`, rank
schedule `R` and requested number `t₀` of vertex cells. It is independent of the host, bounds the
complexity of the complex, and is the size of host required. -/
noncomputable def regularityBound3 (q : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) : ℕ :=
  let B := strongTriadicRegularityBound F ((ε / (2 * ((q : ℝ) + 1))) ^ 2)
    (recoloringTolerance q F R) (recoloringMass F (fun _ ↦ ε) R) (fun _ ↦ 1) (max t₀ 1)
  let M := (range (B + 1)).sup fun t ↦
    strongTopRegularityStep t (recoloringTolerance q F R) (recoloringMass F (fun _ ↦ ε) R)
      (fun _ ↦ 1) B
  max t₀ (max (B + B + B ^ 3 * B ^ 3)
    (recoloringHostBound q ε F (fun _ ↦ ε) R (B + B + B ^ 3 * B ^ 3) (B ^ 3 * M ^ 3)))

/-- Unfolding lemma for `regularityBound3`. -/
theorem regularityBound3_def (q : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    regularityBound3 q ε F R t₀ =
      let B := strongTriadicRegularityBound F ((ε / (2 * ((q : ℝ) + 1))) ^ 2)
        (recoloringTolerance q F R) (recoloringMass F (fun _ ↦ ε) R) (fun _ ↦ 1) (max t₀ 1)
      let M := (range (B + 1)).sup fun t ↦
        strongTopRegularityStep t (recoloringTolerance q F R) (recoloringMass F (fun _ ↦ ε) R)
          (fun _ ↦ 1) B
      max t₀ (max (B + B + B ^ 3 * B ^ 3)
        (recoloringHostBound q ε F (fun _ ↦ ε) R (B + B + B ^ 3 * B ^ 3) (B ^ 3 * M ^ 3))) :=
  (rfl)

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V]

/-- `(H', C)` is a strong regular approximation of `H` at edit discrepancy and exceptional
proportion `ε`, regularity schedule `F`, rank schedule `R` and complexity bound `b`: `H'` is
`ε`-close to `H`, the polyads of `C` decompose the injective triples, the lower skeleton of `C` is
`F`-regular, `H'` is `(F C.complexity, R C.complexity)`-top-regular over `C` outside an
`ε`-proportion of the injective triples, and the complexity of `C` is at most `b`. -/
structure IsStrongRegularApproximation3 (H H' : Colored3Graph κ V) (C : TriadicComplex3 V)
    (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (b : ℕ) : Prop where
  /-- The approximant is within edit discrepancy `ε` of the coloring. -/
  approximates3 : H.Approximates3 H' ε
  /-- The selected polyads decompose the injective triples. -/
  isPolyadDecomposition : C.IsPolyadDecomposition
  /-- The lower skeleton is regular for the schedule `F`. -/
  lowerSkeletonRegular : C.skeleton.LowerSkeletonRegular F
  /-- The approximant is top-regular at the schedules evaluated at the complexity, outside an
  `ε`-proportion of the injective triples. -/
  topRegularOverMostPolyads :
    H'.TopRegularOverMostPolyads C (F C.complexity) ε (R C.complexity)
  /-- The complexity is at most `b`. -/
  complexity_le : C.complexity ≤ b

namespace IsStrongRegularApproximation3

variable {H H' H₀ : Colored3Graph κ V} {C : TriadicComplex3 V} {ε ε' δ : ℝ} {F F' : ℕ → ℝ}
  {R R' : ℕ → ℕ} {b b' : ℕ}

/-- A strong regular approximation weakens as the error, the regularity schedule and the
complexity bound grow and as the rank schedule drops. -/
theorem mono (h : H.IsStrongRegularApproximation3 H' C ε F R b) (hε : ε ≤ ε') (hF : F ≤ F')
    (hR : R' ≤ R) (hb : b ≤ b') : H.IsStrongRegularApproximation3 H' C ε' F' R' b' where
  approximates3 := h.approximates3.mono hε
  isPolyadDecomposition := h.isPolyadDecomposition
  lowerSkeletonRegular := h.lowerSkeletonRegular.mono hF
  topRegularOverMostPolyads := h.topRegularOverMostPolyads.mono (hF _) hε (hR _)
  complexity_le := h.complexity_le.trans hb

/-- **Edit transfer.** A strong regular approximation of `H` is one of every coloring `H₀`
within edit discrepancy `δ` of `H`, at the error `ε + δ`. -/
theorem of_approximates3 (h : H.IsStrongRegularApproximation3 H' C ε F R b)
    (h₀ : H₀.Approximates3 H δ) : H₀.IsStrongRegularApproximation3 H' C (ε + δ) F R b where
  approximates3 := add_comm δ ε ▸ h₀.trans h.approximates3
  isPolyadDecomposition := h.isPolyadDecomposition
  lowerSkeletonRegular := h.lowerSkeletonRegular
  topRegularOverMostPolyads :=
    h.topRegularOverMostPolyads.mono le_rfl (le_add_of_nonneg_right h₀.nonneg) le_rfl
  complexity_le := h.complexity_le

/-- The complex of a strong regular approximation has at most `b` vertex cells. -/
theorem card_parts_le (h : H.IsStrongRegularApproximation3 H' C ε F R b) :
    #C.skeleton.vertexPart.parts ≤ b :=
  C.card_parts_le_complexity.trans h.complexity_le

/-- The complex of a strong regular approximation has at most `b` pair colors. -/
theorem pairColorCount_le (h : H.IsStrongRegularApproximation3 H' C ε F R b) :
    C.pairColorCount ≤ b :=
  C.pairColorCount_le_complexity.trans h.complexity_le

/-- The complex of a strong regular approximation has at most `b` selected polyads. -/
theorem card_polyads_le (h : H.IsStrongRegularApproximation3 H' C ε F R b) :
    #C.polyads ≤ b :=
  C.card_polyads_le_complexity.trans h.complexity_le

/-- **Induced counting from a strong regular approximation.** Let `F` be a pattern on `k`
vertices and let `0 < ε`. If `(H', C)` is a strong regular approximation of `H` at the counting
parameter `inducedCountingParameter3 k ε` and the counting schedule `inducedCountingSchedule3 k ε`,
at a rank schedule positive at `C.complexity` and any complexity bound, and the vertex cells of `C`
form an equipartition into at least `diagonalControl3 k ε` cells, then the induced count of `F`
in `H` differs from the prediction `H'.expectedInducedCount C F` by at most `ε |V| ^ k`. -/
theorem abs_inducedCopyCount_sub_expectedInducedCount_le {F : FiniteColored3Pattern κ}
    (hε : 0 < ε)
    (h : H.IsStrongRegularApproximation3 H' C (inducedCountingParameter3 F.k ε)
      (inducedCountingSchedule3 F.k ε) R b)
    (hR : 1 ≤ R C.complexity) (hcells : C.VertexCellsControlled (diagonalControl3 F.k ε)) :
    |(H.inducedCopyCount F : ℝ) - H'.expectedInducedCount C F| ≤
      ε * (Fintype.card V : ℝ) ^ F.k :=
  abs_inducedCopyCount_sub_expectedInducedCount_le_of_topRegular h.isPolyadDecomposition hε
    h.approximates3 h.lowerSkeletonRegular hR h.topRegularOverMostPolyads hcells

end IsStrongRegularApproximation3

variable [Fintype κ]

/-- **Strong regular approximation of colorings of triples.** Let `ε > 0`, let `F` be a positive
regularity schedule, let `R` be a rank schedule and let `t₀` be a requested number of vertex
cells. Every coloring `H` of the triples of a host with at least `regularityBound3 q ε F R t₀`
vertices, for `q` top colors, has a strong regular approximation `(H', C)` at the complexity bound
`regularityBound3 q ε F R t₀`, so the complexity of `C` is bounded independently of the host, and
the vertex cells of `C` form an equipartition into at least `t₀` cells. -/
theorem exists_strong_regular_approximation3 (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (t₀ : ℕ)
    (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V) :
    ∃ (H' : Colored3Graph κ V) (C : TriadicComplex3 V),
      C.VertexCellsControlled t₀ ∧
        H.IsStrongRegularApproximation3 H' C ε F R
          (regularityBound3 (Fintype.card κ) ε F R t₀) := by
  set q := Fintype.card κ
  set η := recoloringTolerance q F R
  set μ := recoloringMass F (fun _ ↦ ε) R
  set g : ℝ := (ε / (2 * ((q : ℝ) + 1))) ^ 2
  set B := strongTriadicRegularityBound F g η μ (fun _ ↦ 1) (max t₀ 1)
  set M := (range (B + 1)).sup fun t ↦ strongTopRegularityStep t η μ (fun _ ↦ 1) B
  set K := B + B + B ^ 3 * B ^ 3
  set N := recoloringHostBound q ε F (fun _ ↦ ε) R K (B ^ 3 * M ^ 3)
  have hbound : regularityBound3 q ε F R t₀ = max t₀ (max K N) := by
    rw [regularityBound3_def]
  have hKN : max K N ≤ Fintype.card V := (le_max_right _ _).trans (hbound ▸ hV)
  have hN4 : 4 ≤ N := by simp only [N, recoloringHostBound_def]; exact le_max_left _ _
  have hV₀ : max t₀ 1 ≤ #(univ : Finset V) := by
    rw [card_univ]
    have := (le_max_left _ _).trans (hbound ▸ hV)
    have := (le_max_right _ _).trans hKN
    omega
  -- An equipartition into `max t₀ 1` cells seeds the regularity lemma.
  obtain ⟨P₀, hP₀, hP₀card⟩ := Finpartition.exists_equipartition_card_eq _ (by omega) hV₀
  obtain ⟨C, D, f, hCt, hCm, hDm, hCP₀, hCeq, hDV, hCreg, hf, -, hCpol, hDpol, hDreg, hgap⟩ :=
    H.exists_strong_topRegularOverMostPolyads_lowerSkeletonRegular P₀ hP₀ (g := g) (η := η)
      (μ := μ) (by positivity) hF (fun n ↦ recoloringTolerance_pos q R (hF n))
      (fun n ↦ recoloringMass_pos R (hF n) hε) (fun _ ↦ 1)
      (by rw [hP₀card]; exact (by omega : B ≤ K).trans ((le_max_left _ _).trans hKN))
  rw [hP₀card] at hCt hCm
  -- The coarse complexity is at most `K`, and the fine complex has at most `B³ M³` polyads.
  have hCK : C.complexity ≤ K := C.complexity_le.trans (by dsimp only [K]; gcongr)
  have hDM : D.pairColorCount ≤ M :=
    hDm.trans ((topRegularRefinementBound_le_strongTopRegularityStep η μ (fun _ ↦ 1) hCm
      (C.complexity_le.trans (by gcongr))).trans
      (le_sup (f := fun t ↦ strongTopRegularityStep t η μ (fun _ ↦ 1) B)
        (mem_range.2 (Nat.lt_succ_of_le hCt))))
  have hDP : Fintype.card (Polyad3 D.skeleton) ≤ B ^ 3 * M ^ 3 :=
    (card_polyad3_le D.skeleton).trans (by rw [hDV, Fintype.card_fin]; gcongr)
  -- Recolor the triples toward the coarse densities.
  obtain ⟨H', happrox, htop⟩ := hDreg.exists_approximates3_of_recoloringHostBound_le
    (C.isPolyadDecomposition_of_polyads_eq_univ hCpol)
    (D.isPolyadDecomposition_of_polyads_eq_univ hDpol) hDV.le f (fun p ↦ (hf p).symm) hgap hε
    (hF _) hε hCK hDP ((le_max_right _ _).trans hKN)
  refine ⟨H', C, TriadicComplex3.vertexCellsControlled_iff.2 ⟨hCeq, ?_⟩,
    ⟨happrox, C.isPolyadDecomposition_of_polyads_eq_univ hCpol, hCreg, htop,
      hCK.trans (hbound ▸ (le_max_left _ _).trans (le_max_right _ _))⟩⟩
  exact (le_max_left t₀ 1).trans (hP₀card ▸ Finpartition.card_mono hCP₀)

/-- **Strong regular approximation with induced counting.** Let `F` be a pattern on `k` vertices,
let `0 < ε`, and let `R` be a positive rank schedule. Every coloring `H` of the triples of a large
enough host has a strong regular approximation `(H', C)` at the counting parameters and at the
complexity bound `regularityBound3 q (inducedCountingParameter3 k ε) (inducedCountingSchedule3 k ε)
R (diagonalControl3 k ε)`, for `q` top colors, which is also the required host size. Its vertex
cells are at least `diagonalControl3 k ε` equitable cells, and the induced count of `F` in `H`
differs from the prediction `H'.expectedInducedCount C F` by at most `ε |V| ^ k`. -/
theorem exists_strong_regular_approximation3_counting (H : Colored3Graph κ V)
    (F : FiniteColored3Pattern κ) {ε : ℝ} (hε : 0 < ε) {R : ℕ → ℕ} (hR : ∀ n, 1 ≤ R n)
    (hV : regularityBound3 (Fintype.card κ) (inducedCountingParameter3 F.k ε)
      (inducedCountingSchedule3 F.k ε) R (diagonalControl3 F.k ε) ≤ Fintype.card V) :
    ∃ (H' : Colored3Graph κ V) (C : TriadicComplex3 V),
      C.VertexCellsControlled (diagonalControl3 F.k ε) ∧
      H.IsStrongRegularApproximation3 H' C (inducedCountingParameter3 F.k ε)
        (inducedCountingSchedule3 F.k ε) R (regularityBound3 (Fintype.card κ)
          (inducedCountingParameter3 F.k ε) (inducedCountingSchedule3 F.k ε) R
          (diagonalControl3 F.k ε)) ∧
      |(H.inducedCopyCount F : ℝ) - H'.expectedInducedCount C F| ≤
        ε * (Fintype.card V : ℝ) ^ F.k := by
  obtain ⟨H', C, hcells, h⟩ := H.exists_strong_regular_approximation3
    (inducedCountingParameter3_pos F.k hε) (inducedCountingSchedule3_pos F.k hε) R _ hV
  exact ⟨H', C, hcells, h, h.abs_inducedCopyCount_sub_expectedInducedCount_le hε (hR _) hcells⟩

end Colored3Graph

end TauCeti
