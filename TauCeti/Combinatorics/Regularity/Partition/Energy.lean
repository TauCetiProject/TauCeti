/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
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

/-- The part sizes of a partition of the vertices add up to `|V|`. -/
private theorem sum_card_subtype (P : Finpartition (univ : Finset V)) :
    ∑ A : P.parts, (#A.1 : ℝ) = Fintype.card V := by
  rw [sum_coe_sort P.parts fun A => (#A : ℝ)]
  exact_mod_cast P.sum_card_parts

/-- The block weights `|A||B| / |V|²` of a partition sum to at most one (to one on a nonempty
host). -/
private theorem sum_sum_weight_le_one (P : Finpartition (univ : Finset V)) :
    ∑ A : P.parts, ∑ C : P.parts, (#A.1 * #C.1 / (Fintype.card V : ℝ) ^ 2) ≤ 1 := by
  simp_rw [← sum_div, ← sum_mul_sum, sum_card_subtype, ← sq]
  exact div_self_le_one _

/-- The weighted energy is nonnegative. -/
theorem weightedEnergy_nonneg (P : Finpartition (univ : Finset V)) : 0 ≤ G.weightedEnergy P :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

/-- The weighted energy is at most one, since edge densities lie in `[0, 1]` and the block
weights sum to at most one. -/
theorem weightedEnergy_le_one (P : Finpartition (univ : Finset V)) : G.weightedEnergy P ≤ 1 := by
  rw [weightedEnergy_eq_sum_subtype]
  refine le_trans (sum_le_sum fun A _ => sum_le_sum fun C _ => ?_) (sum_sum_weight_le_one P)
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

/-- A double sum over the fine parts, grouped by the coarse parents of both parts. -/
private theorem sum_sum_eq_sum_sum_fiber (h : Q ≤ P) (F : Q.parts → Q.parts → ℝ) :
    ∑ B : Q.parts, ∑ D : Q.parts, F B D = ∑ A : P.parts, ∑ C : P.parts,
      ∑ B with refinementParent h B = A, ∑ D with refinementParent h D = C, F B D := by
  rw [← sum_fiberwise univ (refinementParent h) fun B => ∑ D, F B D]
  refine sum_congr rfl fun A _ => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun B _ => ?_
  exact (sum_fiberwise univ (refinementParent h) (F B)).symm

/-- The edge count between two coarse parts is the sum of the edge counts between their fine
parts. -/
private theorem sum_sum_card_interedges_fiber (h : Q ≤ P) (A C : P.parts) :
    ∑ B with refinementParent h B = A, ∑ D with refinementParent h D = C,
      (#(G.interedges B.1 D.1) : ℝ) = #(G.interedges A.1 C.1) := by
  conv_rhs => rw [← biUnion_filter_refinementParent_eq h A,
    ← biUnion_filter_refinementParent_eq h C,
    G.card_interedges_biUnion_left _ _ _ (Q.pairwiseDisjoint_subtype_val _)]
  push_cast
  refine sum_congr rfl fun B _ => ?_
  rw [G.card_interedges_biUnion_right _ _ _ (Q.pairwiseDisjoint_subtype_val _), Nat.cast_sum]

omit [Fintype V] [DecidableEq V] in
/-- The real form of `SimpleGraph.card_mul_card_mul_edgeDensity`. -/
private theorem card_mul_card_mul_edgeDensity_real (s t : Finset V) :
    (#s * #t : ℝ) * (G.edgeDensity s t : ℝ) = #(G.interedges s t) := by
  exact_mod_cast G.card_mul_card_mul_edgeDensity s t

/-- The size-weighted correlation between fine densities and their parent densities is the coarse
energy, since each coarse density is the size-weighted average of its fine densities. -/
private theorem sum_sum_weight_mul_edgeDensity_mul_parent (h : Q ≤ P) :
    ∑ B : Q.parts, ∑ D : Q.parts,
      (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) * (G.edgeDensity B.1 D.1 : ℝ) *
        G.edgeDensity (refinementParent h B).1 (refinementParent h D).1 =
      G.weightedEnergy P := by
  rw [weightedEnergy_eq_sum_subtype, sum_sum_eq_sum_sum_fiber h]
  refine sum_congr rfl fun A _ => sum_congr rfl fun C _ => ?_
  calc _ = ∑ B with refinementParent h B = A, ∑ D with refinementParent h D = C,
        (#(G.interedges B.1 D.1) : ℝ) *
          ((G.edgeDensity A.1 C.1 : ℝ) / (Fintype.card V : ℝ) ^ 2) := by
        refine sum_congr rfl fun B hB => sum_congr rfl fun D hD => ?_
        rw [(mem_filter.1 hB).2, (mem_filter.1 hD).2,
          ← card_mul_card_mul_edgeDensity_real]
        ring
    _ = _ := by
        simp_rw [← sum_mul]
        rw [sum_sum_card_interedges_fiber, ← card_mul_card_mul_edgeDensity_real]
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
  calc _ = ∑ B with refinementParent h B = A, ∑ D with refinementParent h D = C,
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
  rw [← G.weightedDensityDeviation_sq h] at hgap
  have hw := sum_sum_weight_le_one Q
  rw [← Fintype.sum_prod_type'] at hgap hw ⊢
  -- Weighted Cauchy–Schwarz: `(∑ w |δ|)² ≤ (∑ w) (∑ w δ²) ≤ ε` when the weights sum to at most one.
  have key (w δ : Q.parts × Q.parts → ℝ) (hw0 : ∀ p ∈ univ, 0 ≤ w p) (hw1 : ∑ p, w p ≤ 1)
      (hε : ∑ p, w p * δ p ^ 2 ≤ ε) : ∑ p, w p * |δ p| ≤ √ε := by
    have hg : ∀ p ∈ univ, 0 ≤ w p * δ p ^ 2 := fun p hp => mul_nonneg (hw0 p hp) (sq_nonneg _)
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    refine (sum_sq_le_sum_mul_sum_of_sq_le_mul univ hw0 hg
      fun p _ => (by rw [mul_pow, sq_abs]; ring : _ = _).le).trans ?_
    exact (mul_le_mul hw1 hε (sum_nonneg hg) zero_le_one).trans_eq (one_mul ε)
  exact key (fun p => #p.1.1 * #p.2.1 / (Fintype.card V : ℝ) ^ 2)
    (fun p => (G.edgeDensity p.1.1 p.2.1 : ℝ) -
      G.edgeDensity (refinementParent h p.1).1 (refinementParent h p.2).1)
    (fun _ _ => by positivity) hw hgap

end Refinement

end SimpleGraph
