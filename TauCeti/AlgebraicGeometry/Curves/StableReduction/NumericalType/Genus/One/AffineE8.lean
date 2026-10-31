/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.E8

/-!
# Affine E₈ numerical types

Nine distinct components of self-intersection `-2w` containing the edges of affine E₈
exhaust a numerical type. All weights agree, the intersection matrix is the negative affine
Cartan matrix times the common weight, and the multiplicities are a positive integer multiple
of the affine marks. In a minimal numerical type of genus one all component genera are zero.
The resulting equivalence preserves the supplied component labels.

The numbering is that of `TauCeti.AffineDynkinType.E8`: node `0` is trivalent, node `1` is its
short leaf, and the other arms are `2 - 3` and `4 - 5 - 6 - 7 - 8`.
The marks are `(6, 3, 4, 2, 5, 4, 3, 2, 1)`.

## References

* [Stacks Project, Lemma 55.6.2, case (34), Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T).
* The simply-laced calculation and affine exclusion in
  `TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.E8` determine the weights,
  intersections, and exhaustion. The multiplicity argument follows the E₇ construction in
  `TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineE7`, using
  `NumericalType.dotProduct_intersection_mulVec_eq_zero_iff` and the affine Cartan marks.
-/

public section

namespace TauCeti.NumericalType

open Finset _root_.Matrix

universe u

variable (T : NumericalType.{u})

/-- The numerical data of a genus-one affine E₈ diagram: constant weights, multiplicities
proportional to its marks, and intersection matrix given by its affine Cartan matrix.
Component genera are imposed separately in the minimal classification. -/
def IsGenusOneAffineE8Shape (T : NumericalType.{u}) : Prop :=
  ∃ e : Fin 9 ≃ T.Component,
  (∀ i, T.weight (e i) = T.weight (e 0)) ∧
  (∀ i, (T.multiplicity (e i) : ℤ) =
    AffineDynkinType.E8.marks i * T.multiplicity (e 8)) ∧
  (∀ i j, T.intersection (e i) (e j) =
    -(T.weight (e 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j)

/-- The complete numerical data recorded by `IsGenusOneAffineE8Shape`. -/
theorem isGenusOneAffineE8Shape_iff : T.IsGenusOneAffineE8Shape ↔
  ∃ e : Fin 9 ≃ T.Component,
  (∀ i, T.weight (e i) = T.weight (e 0)) ∧
  (∀ i, (T.multiplicity (e i) : ℤ) =
    AffineDynkinType.E8.marks i * T.multiplicity (e 8)) ∧
  (∀ i j, T.intersection (e i) (e j) =
    -(T.weight (e 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j) := Iff.rfl

/-- The finite E₈ calculation and affine exclusion determine the full intersection data. -/
private lemma affineE8_weights_intersections (l : Fin 9 → T.Component)
    (hl : Function.Injective l)
    (hself : ∀ i, T.intersection (l i) (l i) = -(2 * (T.weight (l i) : ℤ)))
    (hadj : ∀ i j : Fin 9, AffineDynkinType.E8.graph.Adj i j →
      0 < T.intersection (l i) (l j)) :
    Fintype.card T.Component = 9 ∧
      (∀ i, T.weight (l i) = T.weight (l 0)) ∧
      (∀ i j, T.intersection (l i) (l j) =
        -(T.weight (l 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j) := by
  classical
  -- Read both longer arms as a chain, with node 1 as its extra leaf.
  let c : ℕ → T.Component := fun i ↦
    l (if i = 0 then 8 else if i = 1 then 7 else if i = 2 then 6 else
      if i = 3 then 5 else if i = 4 then 4 else if i = 5 then 0 else
      if i = 6 then 2 else 3)
  have hc : T.IsSelfIntersectionMinusTwoChain 8 c := {
    injOn := by
      intro i hi j hj hij
      have hij' := hl hij
      interval_cases i <;> interval_cases j <;> simp_all [c]
    intersection_self := fun i _ ↦ hself _
    intersection_succ_pos := by
      intro i hi
      have hi' : i < 7 := by omega
      interval_cases i <;> simp only [c] <;> apply hadj <;>
        erw [AffineDynkinType.graph_E8_adj] <;> norm_num }
  have hbne : ∀ i < 8, l 1 ≠ c i := by
    intro i hi
    interval_cases i <;> simp [c, hl.eq_iff]
  have hbpos : 0 < T.intersection (c 5) (l 1) :=
    hadj 0 1 (by erw [AffineDynkinType.graph_E8_adj]; norm_num)
  have hge : 9 ≤ Fintype.card T.Component := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective l hl
  have hcard : Fintype.card T.Component = 9 := by
    by_contra h
    exact hc.not_affineE8 (by omega) hbne (hself 1) hbpos
  obtain ⟨w, hw, hwb, hedge, hab, hbzero⟩ :=
    hc.exists_weight_intersection_affineE8_eq hbne (hself 1) hbpos
  have hentry {i j : ℕ} (hi : i < 8) (hj : j < 8) :=
    hc.intersection_eq_ite (by omega) hw hedge hi hj
  have hbentry {i : ℕ} (hi : i < 8) :
      T.intersection (c i) (l 1) = if i = 5 then (w : ℤ) else 0 := by
    split_ifs with h5
    · subst h5
      exact hab
    · exact hbzero i hi h5
  -- Name the inverse relabelling to apply the chain formulas in affine node order.
  have hc0 : l 8 = c 0 := rfl
  have hc1 : l 7 = c 1 := rfl
  have hc2 : l 6 = c 2 := rfl
  have hc3 : l 5 = c 3 := rfl
  have hc4 : l 4 = c 4 := rfl
  have hc5 : l 0 = c 5 := rfl
  have hc6 : l 2 = c 6 := rfl
  have hc7 : l 3 = c 7 := rfl
  have hw0 : (T.weight (l 0) : ℤ) = w := hw 5 (by omega)
  have hweights : ∀ i, T.weight (l i) = T.weight (l 0) := by
    intro i
    apply PNat.coe_injective
    apply Int.natCast_inj.mp
    rw [hw0]
    fin_cases i <;> first
      | exact hwb
      | exact hw 0 (by omega)
      | exact hw 1 (by omega)
      | exact hw 2 (by omega)
      | exact hw 3 (by omega)
      | exact hw 4 (by omega)
      | exact hw 5 (by omega)
      | exact hw 6 (by omega)
      | exact hw 7 (by omega)
  have hmatrix : ∀ i j, T.intersection (l i) (l j) =
      -(T.weight (l 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j := by
    intro i j
    -- The affine API is indexed by Fin E8.nodes, which elaborates as Fin 9.
    erw [AffineDynkinType.cartanMatrix_apply AffineDynkinType.isGraphical_E8 i j]
    rw [hw0]
    fin_cases i <;> fin_cases j <;>
      simp! [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
        hentry, hbentry, T.intersection_comm (l 1), hself 1, hwb]
    all_goals first
      | (erw [AffineDynkinType.graph_E8_adj]; norm_num)
      | ring
  exact ⟨hcard, hweights, hmatrix⟩

/-- Nine distinct components of self-intersection `-2w` containing the affine E₈ edges
are the entire numerical type. All weights agree, all intersections are determined, and
the multiplicities are the affine marks times the multiplicity at node `8`.
Only the displayed edges are assumed; absence of other edges and exhaustion are conclusions.
No minimality or genus assumption is needed. -/
theorem exists_equiv_affineE8 (l : Fin 9 → T.Component)
    (hl : Function.Injective l)
    (hself : ∀ i, T.intersection (l i) (l i) = -(2 * (T.weight (l i) : ℤ)))
    (hadj : ∀ i j : Fin 9, AffineDynkinType.E8.graph.Adj i j →
      0 < T.intersection (l i) (l j)) :
    ∃ e : Fin 9 ≃ T.Component, (∀ i, e i = l i) ∧
      (∀ i, T.weight (e i) = T.weight (l 0)) ∧
      (∀ i, (T.multiplicity (e i) : ℤ) =
        AffineDynkinType.E8.marks i * T.multiplicity (l 8)) ∧
      (∀ i j, T.intersection (e i) (e j) =
        -(T.weight (l 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j) := by
  classical
  obtain ⟨hcard, hweights, hmatrix⟩ := T.affineE8_weights_intersections l hl hself hadj
  have hbij : Function.Bijective l :=
    (Fintype.bijective_iff_injective_and_card l).mpr
      ⟨hl, by simpa only [Fintype.card_fin] using hcard.symm⟩
  let e := Equiv.ofBijective l hbij
  have he : ∀ i, e i = l i := fun _ ↦ rfl
  refine ⟨e, he, fun i ↦ he i ▸ hweights i, ?_, fun i j ↦ by simp only [he, hmatrix]⟩
  intro i
  have hnode : AffineDynkinType.E8.marks 8 = 1 := by
    simpa only [AffineDynkinType.affineNode_E8] using
      AffineDynkinType.marks_affineNode AffineDynkinType.E8
  exact T.multiplicity_eq_mul_of_equiv_intersection e AffineDynkinType.E8.cartanMatrix
    (-(T.weight (l 0) : ℤ)) hmatrix AffineDynkinType.E8.marks
    (AffineDynkinType.cartanMatrix_mulVec_marks_eq_zero AffineDynkinType.valid_E8) 8 hnode i

variable {T}

/-- **The affine E₈ case of the minimal genus-one classification.** Nine distinct components
containing the affine E₈ edges exhaust the type, have genus zero and constant weight, and
have the affine Cartan intersection matrix and the affine marks as multiplicity ratios.
The equivalence preserves all supplied labels. This is case (34) of Stacks, Tag 0C8T. -/
theorem IsMinimal.exists_equiv_affineE8 (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    (l : Fin 9 → T.Component) (hl : Function.Injective l)
    (hadj : ∀ i j : Fin 9, AffineDynkinType.E8.graph.Adj i j →
      0 < T.intersection (l i) (l j)) :
    ∃ e : Fin 9 ≃ T.Component, (∀ i, e i = l i) ∧
      (∀ i, T.genus (e i) = 0) ∧
      (∀ i, T.weight (e i) = T.weight (l 0)) ∧
      (∀ i, (T.multiplicity (e i) : ℤ) =
        AffineDynkinType.E8.marks i * T.multiplicity (l 8)) ∧
      (∀ i j, T.intersection (e i) (e j) =
        -(T.weight (l 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j) := by
  have hcard : 1 < Fintype.card T.Component := by
    have hge := Fintype.card_le_of_injective l hl
    simp only [Fintype.card_fin] at hge
    omega
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff hcard).mp ⟨hT, hg⟩
  obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE8 l hl
    (fun i ↦ (T.isMinusTwoIndex_iff.mp (h₂ (l i))).2) hadj
  exact ⟨e, he, fun i ↦ (T.isMinusTwoIndex_iff.mp (h₂ (e i))).1, hw, hm, ha⟩

/-- In the affine E₈ shape, a component weight divides all weights with quotient at most four,
and a component multiplicity divides all multiplicities with quotient at most six. -/
lemma IsGenusOneAffineE8Shape.exists_weight_and_multiplicity_dvd_and_le
    (hshape : T.IsGenusOneAffineE8Shape) :
    (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
      (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
        (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) := by
  classical
  obtain ⟨e, hw, hm, -⟩ := (isGenusOneAffineE8Shape_iff T).mp hshape
  refine T.exists_weight_and_multiplicity_dvd_and_le_of_int_of_equiv (nw := 4) (nm := 6)
    e 0 8 (fun i ↦ ?_) (fun i ↦ ?_)
  all_goals simp only [← Nat.lt_succ_iff, Nat.exists_lt_succ_right]
  · rw [hw i]; omega
  · rw [hm i]
    fin_cases i <;> simp

end TauCeti.NumericalType
