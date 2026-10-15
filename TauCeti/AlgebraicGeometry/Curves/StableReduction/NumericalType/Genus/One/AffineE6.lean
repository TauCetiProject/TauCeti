/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Branch
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.IntersectionForm

/-!
# The affine E₆ configuration in a numerical type

Seven components of self-intersection `-2w` containing the affine E₆ diagram exhaust a
numerical type. Their weights agree, their intersection matrix is minus that common weight
times the affine Cartan matrix, and their multiplicities are proportional to the affine marks.
The trivalent component is labelled `0`, with the three arms `1 - 2`, `3 - 4`, and `5 - 6`.
Thus the marks are `(3, 2, 1, 2, 1, 2, 1)`.

The result does not assume that unspecified intersections vanish, that the seven components
exhaust the type, or that the type has genus one. Its genus-one specialization also identifies
all component genera. These numerical data describe the exceptional tree configuration in the
classification of minimal genus-one fibres.

## References

* [Stacks Project, Lemma 55.6.2, case (32), Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T).
* The proper E₆ classification `NumericalType.exists_weight_intersection_branch_six_eq` and
  its affine exclusion `NumericalType.intersection_eq_zero_of_branch_six` supply the
  intersection data and exhaustion argument. The Cartan matrix and marks are those of
  `TauCeti.AffineDynkinType.E6`.
-/

public section

namespace TauCeti.NumericalType

open Finset _root_.Matrix

universe u

variable {T : NumericalType.{u}}

/-- Overlapping proper E₆ subdiagrams determine every weight and matrix entry. -/
private lemma affineE6_weights_intersections (c : Fin 7 → T.Component)
    (hc : Function.Injective c)
    (hself : ∀ i, T.intersection (c i) (c i) = -(2 * (T.weight (c i) : ℤ)))
    (hadj : ∀ i j, AffineDynkinType.E6.graph.Adj i j → 0 < T.intersection (c i) (c j)) :
    (∀ i, T.weight (c i) = T.weight (c 0)) ∧
      ∀ i j, T.intersection (c i) (c j) =
        -(T.weight (c 0) : ℤ) * AffineDynkinType.E6.cartanMatrix i j := by
  classical
  have hcard : 6 < Fintype.card T.Component := by
    have := Fintype.card_le_of_injective c hc
    have hdim : Fintype.card (Fin 7) = 7 := Fintype.card_fin _
    rw [hdim] at this
    omega
  have hne {i j : Fin 7} (h : i ≠ j) : c i ≠ c j := hc.ne h
  -- Each subdiagram omits the end of a different arm. Together they cover every pair.
  obtain ⟨w, hw2, hw1, hwcenter, hw3, hw4, hw5,
      ha21, ha10, ha03, ha34, ha05, hz20, hz23, hz24, hz25, hz13, hz14, hz15, hz04, hz35, hz45⟩ :=
    T.exists_weight_intersection_branch_six_eq hcard
      (hself 2) (hself 1) (hself 0) (hself 3) (hself 4) (hself 5)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hadj 2 1 (by simp)) (hadj 1 0 (by simp)) (hadj 0 3 (by simp)) (hadj 3 4 (by simp))
      (hadj 0 5 (by simp))
  have hbase : (w : ℤ) = T.weight (c 0) := hwcenter.symm
  rw [hbase] at hw2 hw1 hw3 hw4 hw5 ha21 ha10 ha03 ha34 ha05
  obtain ⟨w', -, -, hwcenter', -, hw6, -,
      -, -, -, ha56, -, -, -, hz26, -, -, hz16, -, hz06, -, hz63⟩ :=
    T.exists_weight_intersection_branch_six_eq hcard
      (hself 2) (hself 1) (hself 0) (hself 5) (hself 6) (hself 3)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hadj 2 1 (by simp)) (hadj 1 0 (by simp)) (hadj 0 5 (by simp)) (hadj 5 6 (by simp))
      (hadj 0 3 (by simp))
  have hbase' : (w' : ℤ) = T.weight (c 0) := hwcenter'.symm
  rw [hbase'] at hw6 ha56
  obtain ⟨-, -, -, -, -, -, -,
      -, -, -, -, -, -, -, hz46, -, -, -, -, -, -, -⟩ :=
    T.exists_weight_intersection_branch_six_eq hcard
      (hself 4) (hself 3) (hself 0) (hself 5) (hself 6) (hself 1)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hadj 4 3 (by simp)) (hadj 3 0 (by simp)) (hadj 0 5 (by simp)) (hadj 5 6 (by simp))
      (hadj 0 1 (by simp))
  have hw : ∀ i, T.weight (c i) = T.weight (c 0) := by
    intro i
    fin_cases i
    · rfl
    · exact_mod_cast hw1
    · exact_mod_cast hw2
    · exact_mod_cast hw3
    · exact_mod_cast hw4
    · exact_mod_cast hw5
    · exact_mod_cast hw6
  refine ⟨hw, ?_⟩
  intro i j
  -- Use `Fin 7` for the conditional as well as for `c`; the Cartan API is indexed by
  -- `Fin E6.nodes`, whose implicit decidability instance is opaque outside its module.
  have hC (i j : Fin 7) : AffineDynkinType.E6.cartanMatrix i j =
      if i = j then 2 else if AffineDynkinType.E6.graph.Adj i j then -1 else 0 := by
    convert AffineDynkinType.cartanMatrix_apply AffineDynkinType.isGraphical_E6 i j using 1
    split_ifs <;> first | rfl | contradiction
  have hG (i j : Fin 7) : AffineDynkinType.E6.graph.Adj i j ↔
      (min (i : ℕ) (j : ℕ), max (i : ℕ) (j : ℕ)) ∈
        [((0 : ℕ), (1 : ℕ)), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)] :=
    AffineDynkinType.graph_E6_adj i j
  rw [hC]
  simp only [Fin.ext_iff, hG]
  clear hadj hc hne
  fin_cases i <;> fin_cases j <;> norm_num
  all_goals grind [T.intersection_comm]

/-- Seven distinct components containing the affine E₆ diagram and of self-intersection `-2w`
exhaust the numerical type. -/
private lemma card_eq_seven_of_affineE6 (c : Fin 7 → T.Component)
    (hc : Function.Injective c)
    (hself : ∀ i, T.intersection (c i) (c i) = -(2 * (T.weight (c i) : ℤ)))
    (hadj : ∀ i j, AffineDynkinType.E6.graph.Adj i j → 0 < T.intersection (c i) (c j)) :
    Fintype.card T.Component = 7 := by
  have hge := Fintype.card_le_of_injective c hc
  have hdim : Fintype.card (Fin 7) = 7 := Fintype.card_fin _
  rw [hdim] at hge
  by_contra hcard
  have hne {i j : Fin 7} (h : i ≠ j) : c i ≠ c j := hc.ne h
  have hz := T.intersection_eq_zero_of_branch_six (by omega)
    (hself 2) (hself 1) (hself 0) (hself 3) (hself 4) (hself 5) (hself 6)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide))
    (hadj 2 1 (by simp)) (hadj 1 0 (by simp)) (hadj 0 3 (by simp))
    (hadj 3 4 (by simp)) (hadj 0 5 (by simp))
  exact (hadj 5 6 (by simp)).ne' hz

/-- The affine E₆ configuration exhausts the component set and determines its weights,
multiplicities, and intersections, preserving the supplied labels. All weights agree;
the multiplicities are `(3m, 2m, m, 2m, m, 2m, m)` and the
intersection matrix is minus the common weight times the affine E₆ Cartan matrix. -/
theorem exists_equiv_affineE6 (c : Fin 7 → T.Component) (hc : Function.Injective c)
    (hself : ∀ i, T.intersection (c i) (c i) = -(2 * (T.weight (c i) : ℤ)))
    (hadj : ∀ i j, AffineDynkinType.E6.graph.Adj i j → T.Adj (c i) (c j)) :
    ∃ e : Fin 7 ≃ T.Component, (∀ i, e i = c i) ∧
      (∀ i, T.weight (e i) = T.weight (c 0)) ∧
      (∀ i, (T.multiplicity (e i) : ℤ) =
        (T.multiplicity (c 2) : ℤ) * AffineDynkinType.E6.marks i) ∧
      (∀ i j, T.intersection (e i) (e j) =
        -(T.weight (c 0) : ℤ) * AffineDynkinType.E6.cartanMatrix i j) := by
  classical
  have hpos := fun i j h ↦ (T.adj_iff.mp (hadj i j h)).2
  have hcard := card_eq_seven_of_affineE6 c hc hself hpos
  have hdim : Fintype.card (Fin 7) = 7 := Fintype.card_fin _
  have hbij : Function.Bijective c :=
    (Fintype.bijective_iff_injective_and_card c).mpr ⟨hc, by rw [hdim]; exact hcard.symm⟩
  let e := Equiv.ofBijective c hbij
  have he : ∀ i, e i = c i := congrFun (Equiv.coe_ofBijective c hbij)
  obtain ⟨hw, ha⟩ := affineE6_weights_intersections c hc hself hpos
  -- Transport the affine marks to the components. The intersection-form kernel criterion
  -- identifies them with the multiplicity vector, without solving the seven rows again.
  let x : T.Component → ℤ := fun i ↦ AffineDynkinType.E6.marks (e.symm i)
  have hx : T.intersection *ᵥ x = 0 := by
    ext v
    obtain ⟨i, rfl⟩ := e.surjective v
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← e.sum_comp]
    simp only [x, Equiv.symm_apply_apply]
    simp only [he, ha]
    simp_rw [mul_assoc]
    rw [← mul_sum]
    have hzero : ∑ j : Fin 7, AffineDynkinType.E6.cartanMatrix i j *
        AffineDynkinType.E6.marks j = 0 :=
      congrFun (AffineDynkinType.cartanMatrix_mulVec_marks_eq_zero AffineDynkinType.valid_E6) i
    rw [hzero, mul_zero]
  have hratio := (T.dotProduct_intersection_mulVec_eq_zero_iff x).mp (by rw [hx]; simp)
  refine ⟨e, he, by simpa only [he] using hw, ?_, by simpa only [he] using ha⟩
  intro i
  have h := hratio (e i) (e 2)
  have hm2 : AffineDynkinType.E6.marks (2 : Fin 7) = 1 := by
    rw [AffineDynkinType.marks_E6]
    rfl
  simp only [x, Equiv.symm_apply_apply] at h
  simpa only [hm2, mul_one, he] using h.symm

/-- A minimal genus-one numerical type containing the affine E₆ diagram has zero component
genera and the complete affine E₆ weight, multiplicity, and intersection data. -/
theorem IsMinimal.exists_equiv_affineE6 (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    (c : Fin 7 → T.Component) (hc : Function.Injective c)
    (hadj : ∀ i j, AffineDynkinType.E6.graph.Adj i j → T.Adj (c i) (c j)) :
    ∃ e : Fin 7 ≃ T.Component, (∀ i, e i = c i) ∧ (∀ i, T.genus (e i) = 0) ∧
      (∀ i, T.weight (e i) = T.weight (c 0)) ∧
      (∀ i, (T.multiplicity (e i) : ℤ) =
        (T.multiplicity (c 2) : ℤ) * AffineDynkinType.E6.marks i) ∧
      (∀ i j, T.intersection (e i) (e j) =
        -(T.weight (c 0) : ℤ) * AffineDynkinType.E6.cartanMatrix i j) := by
  have hcard : 1 < Fintype.card T.Component := by
    have := Fintype.card_le_of_injective c hc
    have hdim : Fintype.card (Fin 7) = 7 := Fintype.card_fin _
    rw [hdim] at this
    omega
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff hcard).mp ⟨hT, hg⟩
  obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE6 c hc
    (fun i ↦ (T.isMinusTwoIndex_iff.mp (h₂ (c i))).2) hadj
  exact ⟨e, he, fun i ↦ (T.isMinusTwoIndex_iff.mp (h₂ (e i))).1, hw, hm, ha⟩

end TauCeti.NumericalType
