/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.WeightedCauchySchwarz
public import TauCeti.Combinatorics.SimpleGraph.Density
public import TauCeti.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Field

/-!
# Size-weighted energy of a vertex partition

For a finite simple graph `G` on `V` with `n = |V|` and a partition `P` of the vertex set, the
size-weighted energy is
`G.weightedEnergy P = ∑ A ∈ P, ∑ B ∈ P, (|A||B| / n²) · d_G(A, B)²`,
where `d_G = SimpleGraph.edgeDensity`. It is the mean square of the block-average step function
`(x, y) ↦ d_G(P.part x, P.part y)` (`SimpleGraph.weightedEnergy_eq_sum_part`).

Two conventions are deliberate. All ordered pairs of parts are summed, **including** the diagonal
blocks `A = B`, and `d_G(A, A)` uses the denominator `|A|²` (ordered pairs, loops counted as
non-edges), not `|A|(|A| - 1)`. Consequently the energy is *not* Mathlib's
`Finpartition.energy`, which averages over off-diagonal pairs of parts without size weights and
is not monotone under arbitrary refinement.

The weighted energy is monotone under arbitrary refinement, with an exact defect: for `Q ≤ P`, the
weighted mean square deviation between the densities of fine blocks and of their coarse parent
blocks is the energy gap (`SimpleGraph.weightedDensityDeviation_sq`). By weighted Cauchy–Schwarz,
an energy gap of at most `ε` bounds the weighted mean absolute deviation by `√ε`
(`SimpleGraph.weightedDensityDeviation_abs_le`). Neither statement needs equitability or
regularity; these are the energy-increment inputs of weak and strong regularity arguments.

## Main results

* `SimpleGraph.weightedEnergy`: the size-weighted energy, with `weightedEnergy_nonneg` and
  `weightedEnergy_le_one`.
* `SimpleGraph.weightedEnergy_eq_sum_part`: the energy is the mean square of the block-average
  step function.
* `SimpleGraph.weightedDensityDeviation_sq`: the refinement defect identity.
* `SimpleGraph.weightedEnergy_mono_of_refines`: refining a partition does not decrease energy.
* `SimpleGraph.weightedDensityDeviation_abs_le`: the absolute-deviation bound from an energy gap.
* `SimpleGraph.sum_sum_abs_edgeDensity_part_sub_le`: the same bound summed over pairs of vertices.

## References

* L. Lovász, B. Szegedy, *Szemerédi's Lemma for the Analyst*, GAFA 17 (2007).
* Y. Zhao, *Graph Theory and Additive Combinatorics* (2023), ch. 2.
* The size-weighted energy and its refinement monotonicity also appear, for directed relations,
  as `energy` and `energy_mono` in the Lean library `cameronfreer/regularity-lemmata`
  (`Partition/Energy.lean`).
-/

public section

open Finset Finpartition

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **size-weighted energy** of a partition `P` of the vertices of `G`:
`∑ A ∈ P, ∑ B ∈ P, (|A||B| / |V|²) · d_G(A, B)²`. It sums over all ordered pairs of parts,
including the diagonal blocks `A = B`, where `d_G(A, A)` has denominator `|A|²`. Unlike Mathlib's
`Finpartition.energy`, it is monotone under arbitrary refinement
(`SimpleGraph.weightedEnergy_mono_of_refines`). -/
noncomputable def weightedEnergy (P : Finpartition (univ : Finset V)) : ℝ :=
  ∑ A ∈ P.parts, ∑ B ∈ P.parts,
    (#A * #B / (Fintype.card V : ℝ) ^ 2) * (G.edgeDensity A B : ℝ) ^ 2

/-- Unfolding lemma for `SimpleGraph.weightedEnergy`. -/
theorem weightedEnergy_def (P : Finpartition (univ : Finset V)) :
    G.weightedEnergy P = ∑ A ∈ P.parts, ∑ B ∈ P.parts,
      (#A * #B / (Fintype.card V : ℝ) ^ 2) * (G.edgeDensity A B : ℝ) ^ 2 :=
  (rfl)

/-- The weighted energy, summed over the subtype of parts. -/
private theorem weightedEnergy_eq_sum_subtype (P : Finpartition (univ : Finset V)) :
    G.weightedEnergy P = ∑ A : P.parts, ∑ C : P.parts,
      (#A.1 * #C.1 / (Fintype.card V : ℝ) ^ 2) * (G.edgeDensity A.1 C.1 : ℝ) ^ 2 := by
  rw [weightedEnergy, ← sum_coe_sort]
  exact sum_congr rfl fun A _ => (sum_coe_sort _ _).symm

/-- The weighted energy is nonnegative. -/
theorem weightedEnergy_nonneg (P : Finpartition (univ : Finset V)) : 0 ≤ G.weightedEnergy P :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

/-- The weighted energy is at most one, since edge densities lie in `[0, 1]` and the block
weights sum to at most one. -/
theorem weightedEnergy_le_one (P : Finpartition (univ : Finset V)) : G.weightedEnergy P ≤ 1 := by
  rw [weightedEnergy_eq_sum_subtype]
  refine le_trans (sum_le_sum fun A _ => sum_le_sum fun C _ => ?_) (by
    simpa using P.sum_sum_weight_le_one)
  have h0 : (0 : ℝ) ≤ G.edgeDensity A.1 C.1 := mod_cast G.edgeDensity_nonneg _ _
  have h1 : (G.edgeDensity A.1 C.1 : ℝ) ≤ 1 := mod_cast G.edgeDensity_le_one _ _
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ h0 h1)

/-- The weighted energy is the mean square of the block-average step function
`(x, y) ↦ d_G(P.part x, P.part y)` over all ordered pairs of vertices, diagonal included. -/
theorem weightedEnergy_eq_sum_part (P : Finpartition (univ : Finset V)) :
    G.weightedEnergy P = (∑ x, ∑ y, (G.edgeDensity (P.part x) (P.part y) : ℝ) ^ 2) /
      (Fintype.card V : ℝ) ^ 2 := by
  rw [sum_congr rfl fun x _ => P.sum_apply_part fun C => (G.edgeDensity (P.part x) C : ℝ) ^ 2,
    P.sum_apply_part fun A => ∑ C ∈ P.parts, #C • (G.edgeDensity A C : ℝ) ^ 2,
    weightedEnergy, sum_div]
  refine sum_congr rfl fun A _ => ?_
  rw [nsmul_eq_mul, mul_sum, sum_div]
  refine sum_congr rfl fun C _ => ?_
  rw [nsmul_eq_mul]
  ring

section Refinement

variable {P Q : Finpartition (univ : Finset V)}

/-- The size-weighted correlation between fine densities and their parent densities is the coarse
energy, since each coarse density is the size-weighted average of its fine densities. -/
private theorem sum_sum_weight_mul_edgeDensity_mul_parent (h : Q ≤ P) :
    ∑ B : Q.parts, ∑ D : Q.parts,
      (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) * (G.edgeDensity B.1 D.1 : ℝ) *
        G.edgeDensity (refinementParent h B).1 (refinementParent h D).1 =
      G.weightedEnergy P := by
  rw [weightedEnergy_eq_sum_subtype, sum_sum_eq_sum_sum_fiber h]
  refine sum_congr rfl fun A _ => sum_congr rfl fun C _ => ?_
  calc _ = ∑ B : Q.parts with refinementParent h B = A,
      ∑ D : Q.parts with refinementParent h D = C,
        (#(G.interedges B.1 D.1) : ℝ) *
          ((G.edgeDensity A.1 C.1 : ℝ) / (Fintype.card V : ℝ) ^ 2) := by
        refine sum_congr rfl fun B hB => sum_congr rfl fun D hD => ?_
        rw [(mem_filter.1 hB).2, (mem_filter.1 hD).2,
          ← G.card_mul_card_mul_edgeDensity_real]
        ring
    _ = _ := by
        simp_rw [← sum_mul]
        rw [G.sum_sum_card_interedges_fiber_real, ← G.card_mul_card_mul_edgeDensity_real]
        ring

/-- The size-weighted mean square of the parent densities is the coarse energy, since the fine
parts with a given parent partition it. -/
private theorem sum_sum_weight_mul_parent_sq (h : Q ≤ P) :
    ∑ B : Q.parts, ∑ D : Q.parts,
      (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) *
        (G.edgeDensity (refinementParent h B).1 (refinementParent h D).1 : ℝ) ^ 2 =
      G.weightedEnergy P := by
  rw [weightedEnergy_eq_sum_subtype, sum_sum_eq_sum_sum_fiber h]
  refine sum_congr rfl fun A _ => sum_congr rfl fun C _ => ?_
  calc _ = ∑ B : Q.parts with refinementParent h B = A,
      ∑ D : Q.parts with refinementParent h D = C,
        (#B.1 : ℝ) * #D.1 *
          ((G.edgeDensity A.1 C.1 : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2) := by
        refine sum_congr rfl fun B hB => sum_congr rfl fun D hD => ?_
        rw [(mem_filter.1 hB).2, (mem_filter.1 hD).2]
        ring
    _ = _ := by
        simp_rw [← sum_mul, ← sum_mul_sum]
        have hA := sum_card_filter_refinementParent_eq h A
        have hC := sum_card_filter_refinementParent_eq h C
        rw [← Nat.cast_sum, ← Nat.cast_sum, hA, hC]
        ring

/-- **Refinement defect identity.** For a refinement `Q ≤ P`, the size-weighted mean square
deviation of the fine block densities from the densities of their coarse parent blocks equals
the energy gap. All ordered pairs of fine parts are summed, diagonal blocks included; no
equitability or regularity is assumed, and on the empty host both sides vanish. -/
theorem weightedDensityDeviation_sq (h : Q ≤ P) :
    ∑ B : Q.parts, ∑ D : Q.parts,
      (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) *
        ((G.edgeDensity B.1 D.1 : ℝ) -
          G.edgeDensity (refinementParent h B).1 (refinementParent h D).1) ^ 2 =
      G.weightedEnergy Q - G.weightedEnergy P := by
  calc _ = ∑ B : Q.parts, ∑ D : Q.parts,
        ((#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) * (G.edgeDensity B.1 D.1 : ℝ) ^ 2 -
          2 * ((#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) * (G.edgeDensity B.1 D.1 : ℝ) *
            G.edgeDensity (refinementParent h B).1 (refinementParent h D).1) +
          (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) *
            (G.edgeDensity (refinementParent h B).1 (refinementParent h D).1 : ℝ) ^ 2) :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    _ = G.weightedEnergy Q - 2 * G.weightedEnergy P + G.weightedEnergy P := by
        -- The first occurrence of the coarse energy is the cross term, the second the parent term.
        nth_rw 1 [← G.sum_sum_weight_mul_edgeDensity_mul_parent h]
        rw [← G.sum_sum_weight_mul_parent_sq h, weightedEnergy_eq_sum_subtype G Q]
        simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    _ = _ := by ring

/-- **Monotonicity under refinement.** If `P` refines `Q` (`P ≤ Q`), then the energy of `P` is at
least that of `Q`. -/
theorem weightedEnergy_mono_of_refines {P Q : Finpartition (univ : Finset V)} (h : P ≤ Q) :
    G.weightedEnergy Q ≤ G.weightedEnergy P := by
  rw [← sub_nonneg, ← G.weightedDensityDeviation_sq h]
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

/-- **Energy gap controls absolute deviation.** For a refinement `Q ≤ P` whose energy gap is at
most `ε`, the size-weighted mean absolute deviation of the fine block densities from their
parent densities is at most `√ε`. This is weighted Cauchy–Schwarz applied to
`SimpleGraph.weightedDensityDeviation_sq`, using that the block weights sum to at most one. -/
theorem weightedDensityDeviation_abs_le (h : Q ≤ P) {ε : ℝ}
    (hgap : G.weightedEnergy Q - G.weightedEnergy P ≤ ε) :
    ∑ B : Q.parts, ∑ D : Q.parts,
      (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) *
        |(G.edgeDensity B.1 D.1 : ℝ) -
          G.edgeDensity (refinementParent h B).1 (refinementParent h D).1| ≤ √ε := by
  rw [← G.weightedDensityDeviation_sq (P := P) (Q := Q) h] at hgap
  have hw : ∑ B : Q.parts, ∑ D : Q.parts,
      (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) ≤ 1 := by
    simpa using Q.sum_sum_weight_le_one
  rw [← Fintype.sum_prod_type'] at hgap hw ⊢
  exact Finset.weighted_sum_abs_le_sqrt (ι := Q.parts × Q.parts) univ
    (fun p => #p.1.1 * #p.2.1 / (Fintype.card V : ℝ) ^ 2)
    (fun p => (G.edgeDensity p.1.1 p.2.1 : ℝ) -
      G.edgeDensity (refinementParent h p.1).1 (refinementParent h p.2).1)
    (fun _ _ => by positivity) hw hgap

/-- Summed over all ordered pairs of vertices, the edge densities between the parts through them
change by at most `√ε * (card V) ^ 2` from a refinement `Q ≤ P` to `P` whose energy gap is at
most `ε`. This is `SimpleGraph.weightedDensityDeviation_abs_le` with each pair of fine parts
counted once for each pair of vertices in it. -/
theorem sum_sum_abs_edgeDensity_part_sub_le (h : Q ≤ P) {ε : ℝ}
    (hgap : G.weightedEnergy Q - G.weightedEnergy P ≤ ε) :
    ∑ x, ∑ y, |(G.edgeDensity (Q.part x) (Q.part y) : ℝ) -
      G.edgeDensity (P.part x) (P.part y)| ≤ √ε * Fintype.card V ^ 2 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- Group both vertices by their fine parts, each paired with its coarse parent.
  calc ∑ x, ∑ y, |(G.edgeDensity (Q.part x) (Q.part y) : ℝ) -
        G.edgeDensity (P.part x) (P.part y)|
      = ∑ x, ∑ D : Q.parts, #D.1 • |(G.edgeDensity (Q.part x) D.1 : ℝ) -
          G.edgeDensity (P.part x) (refinementParent h D).1| :=
        sum_congr rfl fun x _ ↦ Finpartition.sum_apply_part_part h fun B A ↦
          |(G.edgeDensity (Q.part x) B : ℝ) - G.edgeDensity (P.part x) A|
    _ = ∑ D : Q.parts, ∑ B : Q.parts, #B.1 • (#D.1 • |(G.edgeDensity B.1 D.1 : ℝ) -
          G.edgeDensity (refinementParent h B).1 (refinementParent h D).1|) := by
        rw [sum_comm]
        exact sum_congr rfl fun D _ ↦ Finpartition.sum_apply_part_part h fun B A ↦
          #D.1 • |(G.edgeDensity B D.1 : ℝ) - G.edgeDensity A (refinementParent h D).1|
    _ = (Fintype.card V : ℝ) ^ 2 * ∑ B : Q.parts, ∑ D : Q.parts,
          (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) * |(G.edgeDensity B.1 D.1 : ℝ) -
            G.edgeDensity (refinementParent h B).1 (refinementParent h D).1| := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun B _ ↦ ?_
        rw [mul_sum]
        refine sum_congr rfl fun D _ ↦ ?_
        rw [nsmul_eq_mul, nsmul_eq_mul]
        field_simp
    _ ≤ (Fintype.card V : ℝ) ^ 2 * √ε := by grw [G.weightedDensityDeviation_abs_le h hgap]
    _ = √ε * Fintype.card V ^ 2 := mul_comm _ _


end Refinement

end SimpleGraph
