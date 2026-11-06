/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Exceptional

/-!
# Affine E₇ numerical types

Eight distinct components of self-intersection `-2w` containing the edges of affine E₇
exhaust a numerical type. Their weights agree, their intersection matrix is the negative
affine Cartan matrix times the common weight, and their multiplicities are a positive
integer multiple of the affine marks. For a minimal numerical type of genus one, every
component genus is zero. The equivalence with the component set preserves the given labels.

The numbering is that of `TauCeti.AffineDynkinType.E7`: node `0` is trivalent, node `1`
is its short leaf, and the other arms are `2 - 3 - 4` and `5 - 6 - 7`.
The marks are `(4, 2, 3, 2, 1, 3, 2, 1)`.

## References

* [Stacks Project, Lemma 55.6.2, case (33), Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T).
* The finite E₇ classification and affine exclusion in
  `TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Exceptional` determine
  the weights and intersections. The intersection-form kernel criterion and the affine
  Cartan marks then determine the multiplicities.
-/

public section

namespace TauCeti.NumericalType

open Finset _root_.Matrix

universe u

variable (T : NumericalType.{u})

/-- The numerical data of a genus-one affine E₇ diagram: constant weights, multiplicities
proportional to its marks, and intersection matrix given by its affine Cartan matrix.
Component genera are imposed separately in the minimal classification. -/
def IsGenusOneAffineE7Shape (T : NumericalType.{u}) : Prop :=
  ∃ e : Fin 8 ≃ T.Component,
  (∀ i, T.weight (e i) = T.weight (e 0)) ∧
  (∀ i, (T.multiplicity (e i) : ℤ) =
    AffineDynkinType.E7.marks i * T.multiplicity (e 4)) ∧
  (∀ i j, T.intersection (e i) (e j) =
    -(T.weight (e 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j)

/-- The complete numerical data recorded by `IsGenusOneAffineE7Shape`. -/
theorem isGenusOneAffineE7Shape_iff : T.IsGenusOneAffineE7Shape ↔
  ∃ e : Fin 8 ≃ T.Component,
  (∀ i, T.weight (e i) = T.weight (e 0)) ∧
  (∀ i, (T.multiplicity (e i) : ℤ) =
    AffineDynkinType.E7.marks i * T.multiplicity (e 4)) ∧
  (∀ i j, T.intersection (e i) (e j) =
    -(T.weight (e 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j) := Iff.rfl

/-- The relabelling step of `affineE7_weights_intersections`: once the weights and intersections
of the chain `c` and of the branch `l 1` are known, those of `l` follow in the canonical
numbering. -/
private lemma affineE7_weights_intersections_of_chain (l : Fin 8 → T.Component)
    (c : ℕ → T.Component) (hc0 : l 4 = c 0) (hc1 : l 3 = c 1) (hc2 : l 2 = c 2)
    (hc3 : l 0 = c 3) (hc4 : l 5 = c 4) (hc5 : l 6 = c 5) (hc6 : l 7 = c 6)
    (hself1 : T.intersection (l 1) (l 1) = -(2 * (T.weight (l 1) : ℤ))) {w : ℕ+}
    (hwb : (T.weight (l 1) : ℤ) = w) (hweight : ∀ i < 7, (T.weight (c i) : ℤ) = w)
    (hentry : ∀ {i j : ℕ}, i < 7 → j < 7 → T.intersection (c i) (c j) =
      if i = j then -(2 * (w : ℤ)) else if i + 1 = j ∨ j + 1 = i then (w : ℤ) else 0)
    (hbentry : ∀ {i : ℕ}, i < 7 → T.intersection (c i) (l 1) = if i = 3 then (w : ℤ) else 0) :
    (∀ i, T.weight (l i) = T.weight (l 0)) ∧
      (∀ i j, T.intersection (l i) (l j) =
        -(T.weight (l 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j) := by
  classical
  -- Return to the canonical affine numbering. These identities name the relabelling,
  -- so subsequent uses of the chain formulas need no unfolding of the component map.
  have hw0 : (T.weight (l 0) : ℤ) = w := hc3 ▸ hweight 3 (by omega)
  have hweights : ∀ i, T.weight (l i) = T.weight (l 0) := by
    intro i
    apply PNat.coe_injective
    apply Int.natCast_inj.mp
    rw [hw0]
    fin_cases i <;> simp [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hwb, hweight]
  have hmatrix : ∀ i j, T.intersection (l i) (l j) =
      -(T.weight (l 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j := by
    intro i j
    -- The affine API is indexed by Fin E7.nodes; elaboration identifies it with Fin 8.
    erw [AffineDynkinType.cartanMatrix_apply AffineDynkinType.isGraphical_E7 i j]
    rw [hw0]
    fin_cases i <;> fin_cases j <;>
      simp! only [Fin.zero_eta, Fin.isValue, hc3, Nat.reduceLT, hentry, ↓reduceIte,
        AffineDynkinType.nodes_E7, neg_mul, neg_inj, Fin.mk_one, hbentry, zero_ne_one,
        Int.reduceNeg, mul_ite, mul_neg, mul_one, neg_neg, mul_zero, left_eq_ite_iff,
        Int.natCast_eq_zero, PNat.ne_zero, imp_false, Decidable.not_not, Fin.reduceFinMk, hc2,
        Nat.succ_ne_self, Nat.reduceAdd, Nat.reduceEqDiff, or_true, Fin.reduceEq, hc1,
        Nat.one_lt_ofNat, OfNat.ofNat_ne_one, or_self, right_eq_ite_iff, hc0, Nat.ofNat_pos,
        OfNat.ofNat_ne_zero, zero_add, OfNat.one_ne_ofNat, hc4, or_false, hc5, hc6,
        Nat.lt_add_one, T.intersection_comm (l 1), one_ne_zero, hself1, hwb,
        OfNat.zero_ne_ofNat]
    all_goals first
      | (erw [AffineDynkinType.graph_E7_adj]; norm_num)
      | ring
  exact ⟨hweights, hmatrix⟩

/-- The finite E₇ subdiagrams fix the whole affine E₇ intersection matrix. -/
private lemma affineE7_weights_intersections (l : Fin 8 → T.Component)
    (hl : Function.Injective l)
    (hself : ∀ i, T.intersection (l i) (l i) = -(2 * (T.weight (l i) : ℤ)))
    (hadj : ∀ i j : Fin 8, AffineDynkinType.E7.graph.Adj i j →
      0 < T.intersection (l i) (l j)) :
    Fintype.card T.Component = 8 ∧
      (∀ i, T.weight (l i) = T.weight (l 0)) ∧
      (∀ i j, T.intersection (l i) (l j) =
        -(T.weight (l 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j) := by
  classical
  -- Read the two long arms as a chain, with the short arm as its extra branch.
  let c : ℕ → T.Component := fun i ↦
    l (if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else
      if i = 3 then 0 else if i = 4 then 5 else if i = 5 then 6 else 7)
  have hc : T.IsSelfIntersectionMinusTwoChain 7 c := {
    injOn := by
      intro i hi j hj hij
      have hij' : _ := hl hij
      interval_cases i <;> interval_cases j <;> simp_all [c]
    intersection_self := fun i _ ↦ hself _
    intersection_succ_pos := by
      intro i hi
      have hi' : i < 6 := by omega
      interval_cases i <;> simp only [c] <;> apply hadj <;>
        erw [AffineDynkinType.graph_E7_adj] <;> norm_num }
  have hbne : ∀ i < 7, l 1 ≠ c i := by
    intro i hi
    interval_cases i <;> simp [c, hl.eq_iff]
  have hbpos : 0 < T.intersection (c 3) (l 1) :=
    hadj 0 1 (by erw [AffineDynkinType.graph_E7_adj]; norm_num)
  have hge : 8 ≤ Fintype.card T.Component := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective l hl
  have hcard : Fintype.card T.Component = 8 := by
    by_contra h
    have hz := hc.intersection_branch_eq_zero T (by omega) hbne (hself 1)
    exact hbpos.ne' hz
  obtain ⟨w, hwb, hweight, hentry, hbentry⟩ :=
    T.exists_weight_intersection_branch_eight_eq hc (by omega) hbne (hself 1) hbpos
  exact ⟨hcard, T.affineE7_weights_intersections_of_chain l c rfl rfl rfl rfl rfl rfl rfl (hself 1)
    hwb hweight hentry hbentry⟩

/-- Eight distinct components of self-intersection `-2w` containing the affine E₇ edges
are the entire numerical type. All weights agree, all intersections are determined, and
the multiplicities are the affine marks times the multiplicity at node `4`.
Only the displayed edges are assumed; absence of other edges and exhaustion are conclusions.
No minimality or genus assumption is needed. -/
theorem exists_equiv_affineE7 (l : Fin 8 → T.Component)
    (hl : Function.Injective l)
    (hself : ∀ i, T.intersection (l i) (l i) = -(2 * (T.weight (l i) : ℤ)))
    (hadj : ∀ i j : Fin 8, AffineDynkinType.E7.graph.Adj i j →
      0 < T.intersection (l i) (l j)) :
    ∃ e : Fin 8 ≃ T.Component, (∀ i, e i = l i) ∧
      (∀ i, T.weight (e i) = T.weight (l 0)) ∧
      (∀ i, (T.multiplicity (e i) : ℤ) =
        AffineDynkinType.E7.marks i * T.multiplicity (l 4)) ∧
      (∀ i j, T.intersection (e i) (e j) =
        -(T.weight (l 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j) := by
  classical
  obtain ⟨hcard, hweights, hmatrix⟩ := T.affineE7_weights_intersections l hl hself hadj
  have hbij : Function.Bijective l :=
    (Fintype.bijective_iff_injective_and_card l).mpr
      ⟨hl, by simpa only [Fintype.card_fin] using hcard.symm⟩
  let e := Equiv.ofBijective l hbij
  have he : ∀ i, e i = l i := fun _ ↦ rfl
  refine ⟨e, he, fun i ↦ he i ▸ hweights i, ?_, fun i j ↦ by simp only [he, hmatrix]⟩
  intro i
  have hnode : AffineDynkinType.E7.marks 4 = 1 := by
    simpa only [AffineDynkinType.affineNode_E7] using
      AffineDynkinType.marks_affineNode AffineDynkinType.E7
  exact T.multiplicity_eq_mul_of_equiv_intersection e AffineDynkinType.E7.cartanMatrix
    (-(T.weight (l 0) : ℤ)) hmatrix AffineDynkinType.E7.marks
    (AffineDynkinType.cartanMatrix_mulVec_marks_eq_zero AffineDynkinType.valid_E7) 4 hnode i

variable {T}

/-- **The affine E₇ case of the minimal genus-one classification.** Eight distinct components
containing the affine E₇ edges exhaust the type, have genus zero and constant weight, and
have the affine Cartan intersection matrix and the affine marks as multiplicity ratios.
The equivalence preserves all supplied labels. This is case (33) of Stacks, Tag 0C8T. -/
theorem IsMinimal.exists_equiv_affineE7 (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    (l : Fin 8 → T.Component) (hl : Function.Injective l)
    (hadj : ∀ i j : Fin 8, AffineDynkinType.E7.graph.Adj i j →
      0 < T.intersection (l i) (l j)) :
    ∃ e : Fin 8 ≃ T.Component, (∀ i, e i = l i) ∧
      (∀ i, T.genus (e i) = 0) ∧
      (∀ i, T.weight (e i) = T.weight (l 0)) ∧
      (∀ i, (T.multiplicity (e i) : ℤ) =
        AffineDynkinType.E7.marks i * T.multiplicity (l 4)) ∧
      (∀ i j, T.intersection (e i) (e j) =
        -(T.weight (l 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j) := by
  have hcard : 1 < Fintype.card T.Component := by
    have hge := Fintype.card_le_of_injective l hl
    simp only [Fintype.card_fin] at hge
    omega
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff hcard).mp ⟨hT, hg⟩
  obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE7 l hl
    (fun i ↦ (T.isMinusTwoIndex_iff.mp (h₂ (l i))).2) hadj
  exact ⟨e, he, fun i ↦ (T.isMinusTwoIndex_iff.mp (h₂ (e i))).1, hw, hm, ha⟩

/-- In the affine E₇ shape, a component weight divides all weights with quotient at most four,
and a component multiplicity divides all multiplicities with quotient at most six. -/
lemma IsGenusOneAffineE7Shape.exists_weight_and_multiplicity_dvd_and_le
    (hshape : T.IsGenusOneAffineE7Shape) :
    (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
      (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
        (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) := by
  classical
  obtain ⟨e, hw, hm, -⟩ := (isGenusOneAffineE7Shape_iff T).mp hshape
  refine T.exists_weight_and_multiplicity_dvd_and_le_of_int_of_equiv (nw := 4) (nm := 6)
    e 0 4 (fun i ↦ ?_) (fun i ↦ ?_)
  all_goals simp only [← Nat.lt_succ_iff, Nat.exists_lt_succ_right]
  · rw [hw i]; omega
  · rw [hm i]
    fin_cases i <;> simp

end TauCeti.NumericalType
