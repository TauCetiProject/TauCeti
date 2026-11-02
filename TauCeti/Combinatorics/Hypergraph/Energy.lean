/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Basic
public import TauCeti.Combinatorics.Regularity.Partition.Energy
public import Mathlib.Data.Fintype.Pi
import TauCeti.Order.Partition.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.BigOperators

/-!
# Size-weighted energy of a uniform hypergraph

For an `r`-uniform hypergraph `H` on `V` and an `r`-tuple of vertex sets `A : Fin r → Finset V`,
the box density `H.boxDensity A` is the proportion of the ordered tuples `x` with `x i ∈ A i` for
every `i` whose entries form an edge of `H`. Tuples with a repeated entry never form an edge, so
the box of a repeated set `A i = A j` keeps all its ordered tuples in the denominator; for graphs
this is the convention of `SimpleGraph.edgeDensity`.

For a partition `P` of the vertex set and `n = |V|`, the size-weighted energy is
`H.weightedEnergy P = ∑ A, (∏ i, |A i| / nʳ) · d_H(A)²`,
summed over all `r`-tuples `A` of parts of `P`, repeated parts included. It is the mean square of
the box-average step function `x ↦ d_H(P.part ∘ x)` over all `nʳ` ordered tuples
(`UniformHypergraph.weightedEnergy_eq_sum_part`). This is the `r`-uniform analogue of the
size-weighted graph energy `SimpleGraph.weightedEnergy`, and for `r = 2` the two agree
(`SimpleGraph.weightedEnergy_toUniformHypergraph`).

Box densities are conditional expectations of the edge indicator of ordered tuples. Consequently,
for a refinement `Q ≤ P`, the mean square deviation of the fine box densities from the coarse ones
is the energy gap (`UniformHypergraph.weightedDensityDeviation_sq`), so the energy is monotone
under refinement. By Cauchy–Schwarz, an energy gap of at most `ε` bounds the mean absolute
deviation by `√ε` (`UniformHypergraph.sum_abs_boxDensity_part_sub_le`). Neither statement needs
equitability or regularity.

The conditional-expectation argument adapts `TauCeti.Colored3Graph.sum_relativeDensity_ofTriple_mul`
and the defect identity follows the tuple form of `TauCeti.Colored3Graph.polyadDensityDeviation_sq`,
both in `TauCeti.Combinatorics.Hypergraph.Polyad.Energy`, from polyads of a colored `3`-graph to
boxes of parts of a uniform hypergraph.

## Main definitions

* `TauCeti.UniformHypergraph.boxEdges`: the ordered tuples of a box forming an edge.
* `TauCeti.UniformHypergraph.boxDensity`: the rational density of the edges in a box.
* `TauCeti.UniformHypergraph.weightedEnergy`: the size-weighted energy of a vertex partition.

## Main results

* `TauCeti.UniformHypergraph.weightedEnergy_eq_sum_part`: the energy is the mean square of the
  box-average step function.
* `TauCeti.UniformHypergraph.weightedEnergy_nonneg` and
  `TauCeti.UniformHypergraph.weightedEnergy_le_one`.
* `TauCeti.UniformHypergraph.weightedDensityDeviation_sq`: the refinement defect identity.
* `TauCeti.UniformHypergraph.weightedEnergy_mono_of_refines`: refining a partition does not
  decrease the energy.
* `TauCeti.UniformHypergraph.sum_abs_boxDensity_part_sub_le`: the absolute-deviation bound from
  an energy gap.
* `SimpleGraph.weightedEnergy_toUniformHypergraph`: for the `2`-uniform hypergraph of
  a simple graph, the energy is the graph's size-weighted energy.

## References

* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
* Y. Zhao, *Graph Theory and Additive Combinatorics* (2023), ch. 2.
* The size-weighted energy of a relation on ordered tuples and its refinement monotonicity also
  appear as `energy` and `energy_mono` in the Lean library `cameronfreer/regularity-lemmata`
  (`Partition/Energy.lean`).
-/

public section

open Finset

namespace TauCeti

namespace UniformHypergraph

variable {r : ℕ} {V : Type*} [DecidableEq V] (H : UniformHypergraph r V)

/-! ### Box densities -/

/-- The ordered tuples `x` with `x i ∈ A i` for every `i` whose entries form an edge of `H`. -/
def boxEdges (A : Fin r → Finset V) : Finset (Fin r → V) :=
  (Fintype.piFinset A).filter fun x ↦ univ.image x ∈ H.edges

variable {H} in
/-- Membership in `UniformHypergraph.boxEdges`. -/
@[simp]
theorem mem_boxEdges {A : Fin r → Finset V} {x : Fin r → V} :
    x ∈ H.boxEdges A ↔ (∀ i, x i ∈ A i) ∧ univ.image x ∈ H.edges := by
  simp [boxEdges]

/-- The **box density** of `H` in the box `A 0 × ⋯ × A (r - 1)`: the proportion of its ordered
tuples whose entries form an edge of `H`. It is `0` when some `A i` is empty. -/
def boxDensity (A : Fin r → Finset V) : ℚ :=
  #(H.boxEdges A) / ∏ i, #(A i)

/-- The box density is the number of edge-forming tuples over the number of tuples in the box. -/
theorem boxDensity_def (A : Fin r → Finset V) :
    H.boxDensity A = #(H.boxEdges A) / ∏ i, #(A i) :=
  (rfl)

/-- The edge-forming tuples of a box lie in the box. -/
theorem boxEdges_subset (A : Fin r → Finset V) : H.boxEdges A ⊆ Fintype.piFinset A :=
  filter_subset _ _

/-- The box density is nonnegative. -/
theorem boxDensity_nonneg (A : Fin r → Finset V) : 0 ≤ H.boxDensity A := by
  rw [boxDensity_def]
  positivity

/-- The box density is at most `1`. -/
theorem boxDensity_le_one (A : Fin r → Finset V) : H.boxDensity A ≤ 1 := by
  rw [boxDensity_def]
  refine div_le_one_of_le₀ ?_ (by positivity)
  exact_mod_cast (card_le_card (H.boxEdges_subset A)).trans_eq (Fintype.card_piFinset A)

/-! ### Energy -/

variable [Fintype V]

/-- The **size-weighted energy** of a partition `P` of the vertices of `H`:
`∑ A, (∏ i, |A i| / |V|ʳ) · d_H(A)²`, summed over all `r`-tuples `A` of parts of `P`, repeated
parts included. It is the mean square of the box-average step function
(`UniformHypergraph.weightedEnergy_eq_sum_part`) and is monotone under refinement
(`UniformHypergraph.weightedEnergy_mono_of_refines`). -/
noncomputable def weightedEnergy (P : Finpartition (univ : Finset V)) : ℝ :=
  ∑ A : Fin r → P.parts,
    (∏ i, (#(A i : Finset V) : ℝ)) / (Fintype.card V : ℝ) ^ r * (H.boxDensity (A ·) : ℝ) ^ 2

/-- Unfolding lemma for `UniformHypergraph.weightedEnergy`. -/
theorem weightedEnergy_def (P : Finpartition (univ : Finset V)) :
    H.weightedEnergy P = ∑ A : Fin r → P.parts,
      (∏ i, (#(A i : Finset V) : ℝ)) / (Fintype.card V : ℝ) ^ r * (H.boxDensity (A ·) : ℝ) ^ 2 :=
  (rfl)

/-- The energy is the mean square of the box-average step function `x ↦ d_H(P.part ∘ x)` over
all ordered `r`-tuples of vertices, repeated entries included. -/
theorem weightedEnergy_eq_sum_part (P : Finpartition (univ : Finset V)) :
    H.weightedEnergy P = (∑ x : Fin r → V, (H.boxDensity (P.part ∘ x) : ℝ) ^ 2) /
      (Fintype.card V : ℝ) ^ r := by
  have h := P.sum_piFinset_apply_part (ι := Fin r) fun A ↦ (H.boxDensity A : ℝ) ^ 2
  simp only [Fintype.piFinset_univ] at h
  simp only [Function.comp_def]
  rw [h, sum_div]
  refine sum_congr rfl fun A _ ↦ ?_
  rw [nsmul_eq_mul]
  push_cast
  ring

/-- The energy is nonnegative. -/
theorem weightedEnergy_nonneg (P : Finpartition (univ : Finset V)) : 0 ≤ H.weightedEnergy P :=
  sum_nonneg fun _ _ ↦ by positivity

/-- The energy is at most one, since box densities lie in `[0, 1]`. -/
theorem weightedEnergy_le_one (P : Finpartition (univ : Finset V)) : H.weightedEnergy P ≤ 1 := by
  rw [weightedEnergy_eq_sum_part]
  refine div_le_one_of_le₀ ?_ (by positivity)
  calc ∑ x : Fin r → V, (H.boxDensity (P.part ∘ x) : ℝ) ^ 2
      ≤ ∑ _x : Fin r → V, (1 : ℝ) := sum_le_sum fun x _ ↦
        pow_le_one₀ (mod_cast H.boxDensity_nonneg _) (mod_cast H.boxDensity_le_one _)
    _ = (Fintype.card V : ℝ) ^ r := by simp

/-- **Box densities are conditional expectations.** If `φ` is constant on each box of parts of
`P`, then weighting `φ` at each tuple by the box density of its box of parts gives the sum of `φ`
over the edge-forming tuples. -/
private theorem sum_boxDensity_part_mul (P : Finpartition (univ : Finset V))
    (φ : (Fin r → V) → ℝ) (hφ : ∀ x y, P.part ∘ x = P.part ∘ y → φ x = φ y) :
    ∑ x, (H.boxDensity (P.part ∘ x) : ℝ) * φ x = ∑ x with univ.image x ∈ H.edges, φ x := by
  -- The tuples sharing the box of parts of `y` contribute `φ y` in total.
  have key : ∀ y : Fin r → V, ∑ x ∈ Fintype.piFinset (P.part ∘ y),
      φ x / #(Fintype.piFinset (P.part ∘ x)) = φ y := by
    intro y
    have hpos : (#(Fintype.piFinset (P.part ∘ y)) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (card_pos.2 ⟨y, (P.mem_piFinset_part_iff fun _ ↦ mem_univ _).2 rfl⟩).ne'
    have heq : ∀ x ∈ Fintype.piFinset (P.part ∘ y), φ x / #(Fintype.piFinset (P.part ∘ x)) =
        φ y / #(Fintype.piFinset (P.part ∘ y)) := fun x hx ↦ by
      have hxy : P.part ∘ x = P.part ∘ y := (P.mem_piFinset_part_iff fun _ ↦ mem_univ _).1 hx
      rw [hxy, hφ x y hxy]
    rw [sum_congr rfl heq, sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos]
  -- Expand each density as a count over the box, then exchange the two sums.
  calc ∑ x, (H.boxDensity (P.part ∘ x) : ℝ) * φ x
      = ∑ x, ∑ y with univ.image y ∈ H.edges,
          if y ∈ Fintype.piFinset (P.part ∘ x) then
            φ x / #(Fintype.piFinset (P.part ∘ x)) else 0 := by
        refine sum_congr rfl fun x _ ↦ ?_
        have hbox : {y ∈ (univ : Finset (Fin r → V)) | univ.image y ∈ H.edges} ∩
            Fintype.piFinset (P.part ∘ x) = H.boxEdges (P.part ∘ x) := by
          ext y
          simp [and_comm]
        rw [sum_ite_mem, hbox, sum_const, nsmul_eq_mul, boxDensity_def, Fintype.card_piFinset]
        push_cast
        ring
    _ = ∑ y with univ.image y ∈ H.edges,
          ∑ x ∈ Fintype.piFinset (P.part ∘ y), φ x / #(Fintype.piFinset (P.part ∘ x)) := by
        rw [sum_comm]
        refine sum_congr rfl fun y _ ↦ ?_
        rw [← sum_filter]
        refine sum_congr (Finset.ext fun x ↦ ?_) fun _ _ ↦ rfl
        simp only [mem_filter, mem_univ, true_and, Function.comp_def,
          P.mem_piFinset_part_iff fun _ ↦ mem_univ _, eq_comm]
    _ = _ := sum_congr rfl fun y _ ↦ key y

/-! ### Refinement -/

section Refinement

variable {P Q : Finpartition (univ : Finset V)}

/-- The correlation between the fine and the coarse box densities is the mean square of the coarse
box density, since the coarse box density is constant on the fine boxes. -/
private theorem sum_boxDensity_mul_boxDensity (h : Q ≤ P) :
    ∑ x : Fin r → V, (H.boxDensity (Q.part ∘ x) : ℝ) * H.boxDensity (P.part ∘ x) =
      ∑ x : Fin r → V, (H.boxDensity (P.part ∘ x) : ℝ) ^ 2 := by
  -- A fine box of parts determines the coarse one.
  have hQP : ∀ x y : Fin r → V, Q.part ∘ x = Q.part ∘ y → P.part ∘ x = P.part ∘ y := by
    intro x y hxy
    have hx : x ∈ Fintype.piFinset (Q.part ∘ y) :=
      (Q.mem_piFinset_part_iff fun _ ↦ mem_univ _).2 hxy
    refine (P.mem_piFinset_part_iff fun _ ↦ mem_univ _).1 (Fintype.mem_piFinset.2 fun i ↦ ?_)
    exact Finpartition.part_mono h (y i) (Fintype.mem_piFinset.1 hx i)
  simp_rw [sq]
  rw [H.sum_boxDensity_part_mul Q _ fun x y hxy ↦ by rw [hQP x y hxy],
    H.sum_boxDensity_part_mul P _ fun x y hxy ↦ by rw [hxy]]

/-- **Refinement defect identity.** For a refinement `Q ≤ P`, the mean square deviation of the
fine box densities from the coarse box densities, over all ordered `r`-tuples of vertices, equals
the energy gap. No equitability or regularity is assumed. -/
theorem weightedDensityDeviation_sq (h : Q ≤ P) :
    (∑ x : Fin r → V,
        ((H.boxDensity (Q.part ∘ x) : ℝ) - H.boxDensity (P.part ∘ x)) ^ 2) /
        (Fintype.card V : ℝ) ^ r =
      H.weightedEnergy Q - H.weightedEnergy P := by
  rw [weightedEnergy_eq_sum_part, weightedEnergy_eq_sum_part, ← sub_div]
  congr 1
  have hc := H.sum_boxDensity_mul_boxDensity h
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum] at hc ⊢
  rw [hc]
  ring

/-- **Monotonicity under refinement.** If `P` refines `Q` (`P ≤ Q`), then the energy of `P` is at
least that of `Q`. -/
theorem weightedEnergy_mono_of_refines (h : P ≤ Q) :
    H.weightedEnergy Q ≤ H.weightedEnergy P := by
  rw [← sub_nonneg, ← H.weightedDensityDeviation_sq h]
  positivity

/-- **Energy gap controls absolute deviation.** For a refinement `Q ≤ P` whose energy gap is at
most `ε`, the box densities of the fine and the coarse boxes of parts through an ordered
`r`-tuple differ by at most `√ε` on average over all `|V|ʳ` tuples. -/
theorem sum_abs_boxDensity_part_sub_le (h : Q ≤ P) {ε : ℝ}
    (hgap : H.weightedEnergy Q - H.weightedEnergy P ≤ ε) :
    ∑ x : Fin r → V, |(H.boxDensity (Q.part ∘ x) : ℝ) - H.boxDensity (P.part ∘ x)| ≤
      √ε * (Fintype.card V : ℝ) ^ r := by
  set N : ℝ := (Fintype.card V : ℝ) ^ r
  have hcard : (Fintype.card (Fin r → V) : ℝ) = N := by simp [N]
  obtain hN | hN := eq_or_ne N 0
  · -- Without tuples both sides vanish.
    have : IsEmpty (Fin r → V) := by
      rw [← Fintype.card_eq_zero_iff]
      exact_mod_cast hcard.trans hN
    rw [univ_eq_empty, sum_empty, hN, mul_zero]
  have hN₀ : 0 < N := lt_of_le_of_ne (by positivity) hN.symm
  rw [← H.weightedDensityDeviation_sq h] at hgap
  have hw : ∑ _x : Fin r → V, N⁻¹ ≤ 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul, hcard, mul_inv_cancel₀ hN]
  have hε : ∑ x : Fin r → V, N⁻¹ *
      ((H.boxDensity (Q.part ∘ x) : ℝ) - H.boxDensity (P.part ∘ x)) ^ 2 ≤ ε := by
    rwa [← mul_sum, inv_mul_eq_div]
  have := weighted_sum_abs_le_sqrt univ (fun _ ↦ N⁻¹) _ (fun _ _ ↦ inv_nonneg.2 hN₀.le) hw hε
  rw [← mul_sum, inv_mul_le_iff₀ hN₀] at this
  linarith

end Refinement

/-! ### Graphs -/

section SimpleGraph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The box density of a simple graph's `2`-uniform hypergraph in a box `A 0 × A 1` is the edge
density of `G` between `A 0` and `A 1`. -/
@[simp]
theorem _root_.SimpleGraph.boxDensity_toUniformHypergraph (A : Fin 2 → Finset V) :
    G.toUniformHypergraph.boxDensity A = G.edgeDensity (A 0) (A 1) := by
  have hcard : #(G.toUniformHypergraph.boxEdges A) = #(G.interedges (A 0) (A 1)) := by
    refine card_equiv (piFinTwoEquiv fun _ ↦ V) fun x ↦ ?_
    have himage : univ.image x = {x 0, x 1} := by
      ext v
      simp [Fin.exists_fin_two, eq_comm]
    simp [himage, Fin.forall_fin_two, SimpleGraph.mem_interedges_iff, and_assoc]
  rw [boxDensity_def, hcard, Fin.prod_univ_two, SimpleGraph.edgeDensity_def]
  push_cast
  rfl

/-- **Comparison with graphs.** The energy of a simple graph's `2`-uniform hypergraph is the
size-weighted energy `SimpleGraph.weightedEnergy` of the graph. -/
@[simp]
theorem _root_.SimpleGraph.weightedEnergy_toUniformHypergraph (P : Finpartition (univ : Finset V)) :
    G.toUniformHypergraph.weightedEnergy P = G.weightedEnergy P := by
  rw [weightedEnergy_eq_sum_part, SimpleGraph.weightedEnergy_eq_sum_part,
    ← (piFinTwoEquiv fun _ ↦ V).symm.sum_comp, Fintype.sum_prod_type]
  simp [Function.comp_def]

end SimpleGraph

end UniformHypergraph

end TauCeti
