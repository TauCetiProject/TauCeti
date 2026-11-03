/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy

/-!
# Energy gain from resolved polyad witnesses

Suppose a lower skeleton `T` refines `S`, and for each polyad in a finite family we have a
large set of triples on which a color density differs substantially from its density on the
whole polyad. If membership in every such witness set is constant on the polyads of `T`, then
these witnesses force a quantitative polyad energy gain. Witnesses of relative size at least `δ` and
density deviation at least `δ` force an energy gain of at least `δ³` times the support mass
of the family, normalized by the number of injective triples.

Witnesses may be unions of subpolyad supports, so this estimate applies to the tests in top
regularity at any rank. Only their supports matter here; the construction of a bounded pair
refinement resolving them is separate. The family may select a different top color for each
polyad. No equitability, distinct-cell condition, or nonempty-host assumption is needed.

The argument is the conditional-expectation energy increment: on a resolved witness, the
average fine density equals the actual density, and Cauchy–Schwarz turns its deviation into
a lower bound for the fine variance. Disjoint coarse polyad supports allow these bounds to
be summed without loss.

## Main results

* `TauCeti.Colored3Graph.sum_relativeDensity_ofTriple_on`: conditional expectation on a
  resolved set of triples.
* `TauCeti.Colored3Graph.card_mul_sq_relDensityOn_sub_le_sum`: a resolved set's density
  deviation controls the sum of squared fine-density deviations.
* `TauCeti.Colored3Graph.polyadEnergy_increment_of_witnesses`: the quantitative energy gain
  for a finite family of resolved witnesses.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the index-increment argument.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  (H : Colored3Graph κ V) {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}

/-- On a set that is a union of fine polyad supports, the sum of the fine relative densities
is the actual color count, expressed as the density times the size of the set. -/
theorem sum_relativeDensity_ofTriple_on (c : κ)
    (U : Finset {x : Fin 3 → V // Function.Injective x})
    (hU : ∀ x y, Polyad3.ofTriple T x = Polyad3.ofTriple T y → (x ∈ U ↔ y ∈ U)) :
    ∑ x ∈ U, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) =
      #U * (H.relDensityOn c U : ℝ) := by
  classical
  have h := H.sum_relativeDensity_ofTriple_mul (S := T) c
    (fun x ↦ if x ∈ U then 1 else 0) (fun x y hxy ↦ by simp only [hU x y hxy])
  have hcount : ∑ x ∈ U, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) =
      #{x ∈ U | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
    simpa [mul_ite, sum_ite_mem, inter_comm, inter_filter] using h
  rw [hcount, relDensityOn_def]
  push_cast
  obtain rfl | hne := U.eq_empty_or_nonempty
  · simp
  · exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hne.card_pos.ne')).symm

/-- **Cauchy–Schwarz on a resolved witness.** The squared deviation of its density from any
real number `a`, multiplied by its size, is bounded by the sum of the squared deviations of
the fine densities from `a`. The empty witness is allowed. -/
theorem card_mul_sq_relDensityOn_sub_le_sum (c : κ)
    (U : Finset {x : Fin 3 → V // Function.Injective x})
    (hU : ∀ x y, Polyad3.ofTriple T x = Polyad3.ofTriple T y → (x ∈ U ↔ y ∈ U)) (a : ℝ) :
    #U * ((H.relDensityOn c U : ℝ) - a) ^ 2 ≤
      ∑ x ∈ U, ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) - a) ^ 2 := by
  classical
  obtain rfl | hne := U.eq_empty_or_nonempty
  · simp
  have hpos : (0 : ℝ) < #U := Nat.cast_pos.2 hne.card_pos
  have hsum : ∑ x ∈ U, ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) - a) =
      #U * ((H.relDensityOn c U : ℝ) - a) := by
    rw [sum_sub_distrib, H.sum_relativeDensity_ofTriple_on c U hU, sum_const,
      nsmul_eq_mul]
    ring
  have hcs := sum_mul_sq_le_sq_mul_sq U (fun _ ↦ (1 : ℝ))
    (fun x ↦ (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) - a)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hsum] at hcs
  nlinarith

variable [Fintype κ]

/-- **Resolved irregularity witnesses force an energy gain.** For each coarse polyad in `B`,
choose a color and a witness contained in its support. If every witness is a union of fine
polyad supports, has at least a `δ`-fraction of its parent's size, and has density deviation at
least `δ`, then the energy gain is at least `δ³` times the normalized support mass of `B`.
The refinement hypothesis concerns all polyads, while resolution is needed only for the
chosen witnesses. In particular, they may be unions of rank-`r` subpolyad tests. -/
theorem polyadEnergy_increment_of_witnesses
    (h : ∀ x y, Polyad3.ofTriple T x = Polyad3.ofTriple T y →
      Polyad3.ofTriple S x = Polyad3.ofTriple S y)
    (B : Finset (Polyad3 S)) (c : Polyad3 S → κ)
    (U : Polyad3 S → Finset {x : Fin 3 → V // Function.Injective x})
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsub : ∀ P ∈ B, U P ⊆ P.support)
    (hresolve : ∀ P ∈ B, ∀ x y, Polyad3.ofTriple T x = Polyad3.ofTriple T y →
      (x ∈ U P ↔ y ∈ U P))
    (hsize : ∀ P ∈ B, δ * #P.support ≤ #(U P))
    (hdev : ∀ P ∈ B, δ ≤ |(H.relDensityOn (c P) (U P) : ℝ) - H.relativeDensity (c P) P|) :
    δ ^ 3 * ((∑ P ∈ B, (#P.support : ℝ)) / (Fintype.card V).descFactorial 3) ≤
      H.polyadEnergy T - H.polyadEnergy S := by
  classical
  let d := fun x k ↦ ((H.relativeDensity k (Polyad3.ofTriple T x) : ℝ) -
    H.relativeDensity k (Polyad3.ofTriple S x)) ^ 2
  have hlocal (P : Polyad3 S) (hP : P ∈ B) :
      δ ^ 3 * #P.support ≤ ∑ x ∈ P.support, ∑ k, d x k := by
    have hsq : δ ^ 2 ≤
        ((H.relDensityOn (c P) (U P) : ℝ) - H.relativeDensity (c P) P) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hδ (hdev P hP) 2
    calc δ ^ 3 * #P.support = δ ^ 2 * (δ * #P.support) := by ring
      _ ≤ δ ^ 2 * #(U P) := mul_le_mul_of_nonneg_left (hsize P hP) (sq_nonneg _)
      _ ≤ #(U P) * ((H.relDensityOn (c P) (U P) : ℝ) -
          H.relativeDensity (c P) P) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) #(U P)]
      _ ≤ ∑ x ∈ U P, ((H.relativeDensity (c P) (Polyad3.ofTriple T x) : ℝ) -
          H.relativeDensity (c P) P) ^ 2 :=
        H.card_mul_sq_relDensityOn_sub_le_sum (c P) (U P) (hresolve P hP) _
      _ = ∑ x ∈ U P, d x (c P) := by
        refine sum_congr rfl fun x hx ↦ ?_
        simp only [d, ← Polyad3.mem_support_iff_eq_ofTriple.1 (hsub P hP hx)]
      _ ≤ ∑ x ∈ P.support, ∑ k, d x k := by
        refine (sum_le_sum fun x _ ↦ single_le_sum (f := d x)
          (fun k _ ↦ sq_nonneg _) (mem_univ (c P))).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (hsub P hP) (fun x _ _ ↦
          sum_nonneg fun k _ ↦ sq_nonneg _)
  have hdisj : (B : Set (Polyad3 S)).PairwiseDisjoint Polyad3.support :=
    fun _ _ _ _ hne ↦ Polyad3.pairwise_disjoint_support hne
  have hsum : δ ^ 3 * (∑ P ∈ B, (#P.support : ℝ)) ≤
      ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ k, d x k := by
    calc _ = ∑ P ∈ B, δ ^ 3 * #P.support := mul_sum ..
      _ ≤ ∑ P ∈ B, ∑ x ∈ P.support, ∑ k, d x k := sum_le_sum hlocal
      _ = ∑ x ∈ B.biUnion Polyad3.support, ∑ k, d x k := (sum_biUnion hdisj).symm
      _ ≤ ∑ x, ∑ k, d x k := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun x _ _ ↦ sum_nonneg fun k _ ↦ sq_nonneg _)
  rw [← H.polyadDensityDeviation_sq h, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end TauCeti.Colored3Graph
