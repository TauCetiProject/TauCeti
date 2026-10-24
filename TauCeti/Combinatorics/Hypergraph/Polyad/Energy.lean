/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.WeightedCauchySchwarz
public import TauCeti.Combinatorics.Hypergraph.Polyad.Density
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Rat.BigOperators

/-!
# The polyad energy of a coloring of triples

For a coloring `H` of the unordered triples of a finite vertex type `V` with a finite palette, and
a lower skeleton `S` (vertex cells and pair colors), every injective triple `x` lies in the
support of exactly one polyad `P_x = Polyad3.ofTriple S x`. The polyad energy is the mean, over
the `|V| (|V| - 1) (|V| - 2)` injective triples, of the squared relative color densities at their
polyads:
`H.polyadEnergy S = (∑ x, ∑ c, d_H(c | P_x)²) / |V|.descFactorial 3`.
Grouping the triples by their polyads, it is the support-weighted sum
`∑ P, ∑ c, (|P.support| / |V|.descFactorial 3) · d_H(c | P)²`
(`Colored3Graph.polyadEnergy_eq_sum_polyad`). This is the index of Rödl and Schacht, with one
term for each top color; it is the arity-three analogue of the size-weighted graph energy
`SimpleGraph.weightedEnergy`, with polyads in place of pairs of vertex cells.

The energy is the mean square of a conditional expectation. The relative density of `c` at the
polyad of `x` is the average, over the support of that polyad, of the indicator that a triple has
color `c`; hence weighting any function constant on polyad supports by these densities is the
same as summing it over the triples of color `c`
(`Colored3Graph.sum_relativeDensity_ofTriple_mul`). Consequently, if every polyad over a skeleton
`T` lies inside a polyad over `S` (for instance when the cells and pair colors of `T` refine those
of `S`, `Polyad3.ofTriple_eq_ofTriple_of_le`), the mean square deviation of the fine densities
from the coarse ones is exactly the energy gap (`Colored3Graph.polyadDensityDeviation_sq`). So the
energy does not decrease under refinement, it lies in `[0, 1]`, and an energy gap of at most `ε`
bounds the mean absolute deviation of each color density by `√ε`. These are the inputs of an
energy-increment argument that regularizes a coloring over a refined lower skeleton.

## Main definitions

* `TauCeti.Colored3Graph.polyadEnergy`: the polyad energy of a coloring over a lower skeleton.

## Main results

* `TauCeti.Colored3Graph.sum_relativeDensity_ofTriple_mul`: relative densities at polyads act as
  conditional expectations of the color indicators.
* `TauCeti.Colored3Graph.polyadEnergy_nonneg` and `TauCeti.Colored3Graph.polyadEnergy_le_one`.
* `TauCeti.Colored3Graph.polyadEnergy_eq_sum_polyad`: the support-weighted sum over polyads.
* `TauCeti.Colored3Graph.polyadDensityDeviation_sq`: the refinement defect identity.
* `TauCeti.Colored3Graph.polyadEnergy_mono_of_refines`: refining the skeleton does not decrease
  the energy.
* `TauCeti.Colored3Graph.polyadDensityDeviation_abs_le`: the absolute-deviation bound from an
  energy gap.
* `TauCeti.Colored3Graph.polyadEnergy_const`: a constant coloring has energy one.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the index of a partition.
* The mass-weighted polyad energy and its monotonicity under merging cells appear as
  `polyadEnergy` and `polyadEnergy_comp_le` in the Lean library `cameronfreer/regularity-lemmata`
  (`Hypergraph/PolyadEnergy.lean`), for observables on ordered tuples and colorings of lower
  faces by `Fin K`.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ] (H : Colored3Graph κ V)

/-- There are `|V| (|V| - 1) (|V| - 2)` injective triples. -/
private theorem card_injective_triple :
    Fintype.card {x : Fin 3 → V // Function.Injective x} = (Fintype.card V).descFactorial 3 := by
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _), Fintype.card_embedding_eq,
    Fintype.card_fin]

/-- **Relative densities are conditional expectations.** If `φ` is constant on the support of
each polyad over `S`, then weighting `φ` at each injective triple by the relative density of `c`
at the polyad of that triple gives the sum of `φ` over the triples of color `c`. -/
theorem sum_relativeDensity_ofTriple_mul {S : PairSkeleton3 κ₂ V} (c : κ)
    (φ : {x : Fin 3 → V // Function.Injective x} → ℝ)
    (hφ : ∀ x y, Polyad3.ofTriple S x = Polyad3.ofTriple S y → φ x = φ y) :
    ∑ x, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) * φ x =
      ∑ x with H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c, φ x := by
  -- The triples sharing the polyad of `y` contribute `φ y` in total.
  have key : ∀ y, ∑ x ∈ (Polyad3.ofTriple S y).support,
      φ x / #(Polyad3.ofTriple S x).support = φ y := by
    intro y
    have hpos : (#(Polyad3.ofTriple S y).support : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (card_pos.2 ⟨y, Polyad3.mem_support_ofTriple y⟩).ne'
    have heq : ∀ x ∈ (Polyad3.ofTriple S y).support, φ x / #(Polyad3.ofTriple S x).support =
        φ y / #(Polyad3.ofTriple S y).support := fun x hx ↦ by
      have hxy := Polyad3.mem_support_iff_eq_ofTriple.1 hx
      rw [← hxy, hφ x y hxy.symm]
    rw [sum_congr rfl heq, sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos]
  -- Expand each density as a count over the support, then exchange the two sums.
  calc ∑ x, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) * φ x
      = ∑ x, ∑ y with H.color (Set.powersetCard.ofFinEmb 3 V ⟨y.1, y.2⟩) = c,
          if y ∈ (Polyad3.ofTriple S x).support then
            φ x / #(Polyad3.ofTriple S x).support else 0 := by
        refine sum_congr rfl fun x _ ↦ ?_
        rw [sum_ite_mem, sum_const, filter_inter, univ_inter, nsmul_eq_mul, relativeDensity_def,
          relDensityOn_def]
        push_cast
        ring
    _ = ∑ y with H.color (Set.powersetCard.ofFinEmb 3 V ⟨y.1, y.2⟩) = c,
          ∑ x ∈ (Polyad3.ofTriple S y).support, φ x / #(Polyad3.ofTriple S x).support := by
        rw [sum_comm]
        refine sum_congr rfl fun y _ ↦ ?_
        rw [← sum_filter]
        refine sum_congr (ext fun x ↦ ?_) fun _ _ ↦ rfl
        simp only [mem_filter, mem_univ, true_and, Polyad3.mem_support_iff_eq_ofTriple, eq_comm]
    _ = _ := sum_congr rfl fun y _ ↦ key y

variable [Fintype κ]

/-- At each injective triple, the squared relative densities of all colors sum to at most one. -/
private theorem sum_sq_relativeDensity_ofTriple_le_one {S : PairSkeleton3 κ₂ V}
    (x : {x : Fin 3 → V // Function.Injective x}) :
    ∑ c, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2 ≤ 1 := by
  calc ∑ c, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2
      ≤ ∑ c, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) :=
        sum_le_sum fun c _ ↦ pow_le_of_le_one (mod_cast H.relativeDensity_nonneg c _)
          (mod_cast H.relativeDensity_le_one c _) two_ne_zero
    _ = 1 := mod_cast H.sum_relativeDensity (P := Polyad3.ofTriple S x)
        ⟨x, Polyad3.mem_support_ofTriple x⟩

variable (S : PairSkeleton3 κ₂ V)

/-- The **polyad energy** of a coloring `H` over a lower skeleton `S`: the mean, over the injective
triples `x`, of `∑ c, d_H(c | P_x)²`, where `P_x` is the polyad of `x` over `S` and
`d_H(c | P) = H.relativeDensity c P`. It is the support-weighted sum of the squared relative
densities over all polyads (`Colored3Graph.polyadEnergy_eq_sum_polyad`), and it is `0` when
`V` has fewer than three vertices. -/
noncomputable def polyadEnergy : ℝ :=
  (∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
      (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2) / (Fintype.card V).descFactorial 3

/-- Unfolding lemma for `Colored3Graph.polyadEnergy`. -/
theorem polyadEnergy_def :
    H.polyadEnergy S = (∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
      (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2) / (Fintype.card V).descFactorial 3 :=
  (rfl)

/-- The polyad energy is nonnegative. -/
theorem polyadEnergy_nonneg : 0 ≤ H.polyadEnergy S :=
  div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)

/-- The polyad energy is at most one, since at each triple the relative densities of all colors
lie in `[0, 1]` and sum to one. -/
theorem polyadEnergy_le_one : H.polyadEnergy S ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  calc _ ≤ ∑ _x : {x : Fin 3 → V // Function.Injective x}, (1 : ℝ) :=
        sum_le_sum fun x _ ↦ H.sum_sq_relativeDensity_ofTriple_le_one x
    _ = (Fintype.card V).descFactorial 3 := by
        rw [sum_const, card_univ, card_injective_triple, nsmul_one]

/-- The polyad energy is the sum over all polyads `P` and colors `c` of
`(|P.support| / |V|.descFactorial 3) · d_H(c | P)²`. -/
theorem polyadEnergy_eq_sum_polyad [Fintype κ₂] :
    H.polyadEnergy S = ∑ P : Polyad3 S, ∑ c,
      (#P.support / ((Fintype.card V).descFactorial 3 : ℝ)) * (H.relativeDensity c P : ℝ) ^ 2 := by
  classical
  rw [polyadEnergy_def, ← sum_fiberwise univ (Polyad3.ofTriple S), sum_div]
  refine sum_congr rfl fun P _ ↦ ?_
  -- The triples whose polyad is `P` form the support of `P`.
  have hP : {x ∈ (univ : Finset {x : Fin 3 → V // Function.Injective x}) |
      Polyad3.ofTriple S x = P} = P.support := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Polyad3.mem_support_iff_eq_ofTriple, eq_comm]
  rw [hP, sum_congr rfl fun x hx ↦ by rw [← Polyad3.mem_support_iff_eq_ofTriple.1 hx],
    sum_const, nsmul_eq_mul, mul_sum, sum_div]
  refine sum_congr rfl fun c _ ↦ ?_
  ring

/-! ### Refinement -/

section Refinement

variable {S} {T : PairSkeleton3 κ₂' V}
  (h : ∀ x y, Polyad3.ofTriple T x = Polyad3.ofTriple T y →
    Polyad3.ofTriple S x = Polyad3.ofTriple S y)
include h

omit [Fintype κ] in
/-- The correlation between the fine and the coarse densities of a color is the mean square of the
coarse density, since the coarse density is constant on the fine polyads. -/
private theorem sum_relativeDensity_mul_relativeDensity (c : κ) :
    ∑ x, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) *
        H.relativeDensity c (Polyad3.ofTriple S x) =
      ∑ x, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2 := by
  simp_rw [sq]
  rw [H.sum_relativeDensity_ofTriple_mul c _ fun x y hxy ↦ by rw [h x y hxy],
    H.sum_relativeDensity_ofTriple_mul c _ fun x y hxy ↦ by rw [hxy]]

/-- **Refinement defect identity.** If every polyad over `T` lies in a polyad over `S`, the mean
over the injective triples of the squared deviations of the relative densities at the fine polyads
from those at the coarse polyads, summed over colors, equals the energy gap. -/
theorem polyadDensityDeviation_sq :
    (∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
        ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
          H.relativeDensity c (Polyad3.ofTriple S x)) ^ 2) /
        (Fintype.card V).descFactorial 3 =
      H.polyadEnergy T - H.polyadEnergy S := by
  rw [polyadEnergy_def, polyadEnergy_def, ← sub_div, sum_comm, sum_comm (s := univ) (t := univ)
    (f := fun x c ↦ (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) ^ 2),
    sum_comm (s := univ) (t := univ)
    (f := fun x c ↦ (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2), ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun c _ ↦ ?_
  have hc := H.sum_relativeDensity_mul_relativeDensity h c
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum] at hc ⊢
  rw [hc]
  ring

/-- **Monotonicity under refinement.** If every polyad over `T` lies in a polyad over `S`, the
energy over `T` is at least the energy over `S`. -/
theorem polyadEnergy_mono_of_refines : H.polyadEnergy S ≤ H.polyadEnergy T := by
  rw [← sub_nonneg, ← H.polyadDensityDeviation_sq h]
  exact div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)

/-- **Energy gap controls absolute deviation.** If every polyad over `T` lies in a polyad over `S`
and the energy gap is at most `ε`, then for each color `c` the relative densities of `c` at the
fine and at the coarse polyads differ by at most `√ε` on average over the injective triples. -/
theorem polyadDensityDeviation_abs_le {ε : ℝ} (hgap : H.polyadEnergy T - H.polyadEnergy S ≤ ε)
    (c : κ) :
    ∑ x : {x : Fin 3 → V // Function.Injective x},
        |(H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
          H.relativeDensity c (Polyad3.ofTriple S x)| ≤
      √ε * (Fintype.card V).descFactorial 3 := by
  obtain hD | hD := eq_or_ne ((Fintype.card V).descFactorial 3) 0
  · -- Without injective triples both sides vanish.
    have : IsEmpty {x : Fin 3 → V // Function.Injective x} := by
      rw [← Fintype.card_eq_zero_iff, card_injective_triple, hD]
    rw [univ_eq_empty, sum_empty, hD, Nat.cast_zero, mul_zero]
  set D : ℝ := ((Fintype.card V).descFactorial 3 : ℝ)
  have hD₀ : 0 < D := Nat.cast_pos.2 (Nat.pos_of_ne_zero hD)
  rw [← H.polyadDensityDeviation_sq h] at hgap
  have hw : ∑ _x : {x : Fin 3 → V // Function.Injective x}, D⁻¹ ≤ 1 := by
    rw [sum_const, card_univ, card_injective_triple, nsmul_eq_mul, mul_inv_cancel₀ hD₀.ne']
  have hε : ∑ x : {x : Fin 3 → V // Function.Injective x}, D⁻¹ *
      ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
        H.relativeDensity c (Polyad3.ofTriple S x)) ^ 2 ≤ ε := by
    refine le_trans ?_ hgap
    rw [← mul_sum, inv_mul_eq_div]
    gcongr with x
    exact single_le_sum (f := fun c ↦ ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) -
      H.relativeDensity c (Polyad3.ofTriple S x)) ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ c)
  have := weighted_sum_abs_le_sqrt univ (fun _ ↦ D⁻¹) _ (fun _ _ ↦ inv_nonneg.2 hD₀.le) hw hε
  rw [← mul_sum, inv_mul_le_iff₀ hD₀] at this
  linarith

end Refinement

/-- A constant coloring has polyad energy one over every lower skeleton, once there are injective
triples: each triple sees density one for the constant color and zero for the others. -/
theorem polyadEnergy_const (c₀ : κ) (hV : 3 ≤ Fintype.card V) :
    (const c₀ : Colored3Graph κ V).polyadEnergy S = 1 := by
  have hx : ∀ x : {x : Fin 3 → V // Function.Injective x},
      ∑ c, ((const c₀ : Colored3Graph κ V).relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2 =
        1 := fun x ↦ by
    rw [Fintype.sum_eq_single c₀ fun c hc ↦ by
      rw [relativeDensity_def, relDensityOn_const_of_ne (Ne.symm hc)]; simp]
    rw [relativeDensity_def, relDensityOn_const_self ⟨x, Polyad3.mem_support_ofTriple x⟩]
    simp
  rw [polyadEnergy_def, sum_congr rfl fun x _ ↦ hx x, sum_const, card_univ, card_injective_triple,
    nsmul_one]
  exact div_self (Nat.cast_ne_zero.2 (Nat.descFactorial_pos.2 hV).ne')

end Colored3Graph

end TauCeti
