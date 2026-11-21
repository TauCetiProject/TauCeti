/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Equipartition
public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.CoupledRecoloring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Gap
import TauCeti.Combinatorics.Hypergraph.Polyad.Nontransversal
import TauCeti.Combinatorics.Hypergraph.Polyad.Perm
import TauCeti.Combinatorics.Hypergraph.Polyad.Rank
import TauCeti.Combinatorics.Hypergraph.Triadic.Recoloring.OrbitCoupling
import TauCeti.Data.Finset.Piecewise
import TauCeti.Data.Nat.Factorial.Basic
import TauCeti.Order.Partition.Equipartition

/-!
# Coupled triple recoloring over fine polyads

Given a coarse triadic complex `C` and a fine palette refinement `D` with small polyad energy gap
from `C` to `D`, suppose a coloring `H : Colored3Graph κ V` is `(η, 1)`-top-regular over most
polyads of `D`. This file provides two coupled triple-recoloring theorems producing an `ε`-close
coloring `H'` that is rank-one top-regular over most polyads of `C`:

1. `TauCeti.Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le`:
   a general version for any pair-color refinement `D` of `C`, building on the orbit-glued coupled
   recoloring `TauCeti.Colored3Graph.exists_coupled_recoloring_of_polyadEnergy_sub_le`.
2. `TauCeti.Colored3Graph.exists_recoloring_topRegularOverMostPolyads`: a streamlined version when
   `C` and `D` share an equitable vertex partition with at least `48 / ε` cells, coupling directly
   on unordered supports over canonical representatives of distinct-cell `S₃`-orbits via
   `TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`,
   `TauCeti.two_mul_add_one_mul_exp_lt_of_le_two_pow`, and
   `Finset.exists_piecewise_of_pairwiseDisjoint`.

Both constructions share the passage from good-child subpolyad discrepancies to coarse subpolyad
discrepancies, rank-one top regularity over coarse polyads, and fiberwise Markov charging of
irregular coarse polyads.

## Main results

* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le`:
  coupled recoloring from fine rank-one top regularity across a small polyad energy gap.
* `TauCeti.Colored3Graph.exists_recoloring_topRegularOverMostPolyads`: coupled recoloring from a
  same-cell fine rank-one top-regular refinement with equitable vertex cells.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V]

section SharedCoarsePassage

variable [DecidableEq κ]

open Classical in
/-- Aggregating subpolyad discrepancy of `H'` against `H.relativeDensity c P` across good fine
children of `P`, charging bad fine children trivially by `#Q.support`. -/
private theorem abs_relDensityOn_sub_coarse_mul_card_le_of_good_children
    (H H' : Colored3Graph κ V) {C D : TriadicComplex3 V}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    {P : Polyad3 C.skeleton} {Good : Polyad3 D.skeleton → Prop} {τ θ : ℝ} (hτ0 : 0 ≤ τ)
    (hgood : ∀ Q : Polyad3 D.skeleton, Q.coarsen hV f = P → Good Q →
      ∀ (c : κ) (S' : Subpolyad3 Q),
        |((H'.relDensityOn c S'.support : ℝ) - H.relativeDensity c P) * #S'.support| ≤
          τ * #Q.support)
    (hbad : ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P ∧ ¬Good Q,
        (#Q.support : ℝ) ≤ θ * #P.support)
    (c : κ) (U : Subpolyad3 P) :
    |((H'.relDensityOn c U.support : ℝ) - H.relativeDensity c P) * #U.support| ≤
      (τ + θ) * #P.support := by
  have hmiss (Q : Polyad3 D.skeleton) (hQ : Q.coarsen hV f ≠ P) :
      U.support ∩ Q.support = ∅ :=
    disjoint_iff_inter_eq_empty.1 ((Polyad3.pairwise_disjoint_support hQ.symm).mono
      U.support_subset (Polyad3.support_subset_coarsen hV f hf Q))
  have hsumP : ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P, (#Q.support : ℝ) =
      #P.support := by
    have h := Polyad3.sum_card_support_coarsen hV f hf P
    rw [← Finset.filter_congr_decidable] at h
    exact_mod_cast h
  rw [H'.relDensityOn_sub_mul_card_eq_sum_inter_support D.skeleton c U.support]
  calc |∑ Q : Polyad3 D.skeleton,
          ((H'.relDensityOn c (U.support ∩ Q.support) : ℝ) - H.relativeDensity c P) *
            #(U.support ∩ Q.support)|
      ≤ ∑ Q : Polyad3 D.skeleton,
          |((H'.relDensityOn c (U.support ∩ Q.support) : ℝ) - H.relativeDensity c P) *
            #(U.support ∩ Q.support)| := abs_sum_le_sum_abs _ _
    _ = ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P,
          |((H'.relDensityOn c (U.support ∩ Q.support) : ℝ) - H.relativeDensity c P) *
            #(U.support ∩ Q.support)| := by
        rw [sum_filter]
        refine sum_congr rfl fun Q _ ↦ ?_
        split_ifs with hQ <;> [rfl; simp [hmiss Q hQ]]
    _ ≤ ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P,
          (τ * #Q.support + if ¬Good Q then (#Q.support : ℝ) else 0) := by
        refine sum_le_sum fun Q hQ ↦ ?_
        by_cases hG : Good Q
        · simp only [hG, not_true_eq_false, ↓reduceIte, add_zero]
          simpa only [Subpolyad3.support_restrict] using
            hgood Q (mem_filter.1 hQ).2 hG c (U.restrict Q)
        · simp only [hG, not_false_eq_true, ↓reduceIte]
          have habs : |(H'.relDensityOn c (U.support ∩ Q.support) : ℝ) -
              H.relativeDensity c P| ≤ 1 :=
            abs_sub_le_of_nonneg_of_le (mod_cast H'.relDensityOn_nonneg c _)
              (mod_cast H'.relDensityOn_le_one c _) (mod_cast H.relativeDensity_nonneg c P)
              (mod_cast H.relativeDensity_le_one c P)
          have hcard : (#(U.support ∩ Q.support) : ℝ) ≤ #Q.support := by
            exact_mod_cast card_le_card inter_subset_right
          rw [abs_mul, Nat.abs_cast]
          have h1 := mul_le_mul habs hcard (Nat.cast_nonneg _) zero_le_one
          linarith [mul_nonneg hτ0 (Nat.cast_nonneg (α := ℝ) #Q.support)]
    _ = τ * #P.support +
          ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P ∧ ¬Good Q, (#Q.support : ℝ) := by
        rw [sum_add_distrib, ← mul_sum, hsumP, ← sum_filter, filter_filter]
    _ ≤ (τ + θ) * #P.support := by linarith

open Classical in
/-- Rank-one coarse top regularity over `P` from good fine children with subpolyad discrepancy at
most `τ * #Q.support` and bad-child mass at most `θ * #P.support`, when `2 * (τ + θ) ≤ δ²`. -/
private theorem isTopRegularOverPolyad_of_good_children
    (H H' : Colored3Graph κ V) {C D : TriadicComplex3 V}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    {P : Polyad3 C.skeleton} {Good : Polyad3 D.skeleton → Prop} {τ θ δ : ℝ}
    (hδ : 0 < δ) (hτ0 : 0 ≤ τ) (htol : 2 * (τ + θ) ≤ δ ^ 2)
    (hgood : ∀ Q : Polyad3 D.skeleton, Q.coarsen hV f = P → Good Q →
      ∀ (c : κ) (S' : Subpolyad3 Q),
        |((H'.relDensityOn c S'.support : ℝ) - H.relativeDensity c P) * #S'.support| ≤
          τ * #Q.support)
    (hbad : ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P ∧ ¬Good Q,
        (#Q.support : ℝ) ≤ θ * #P.support) :
    H'.IsTopRegularOverPolyad P δ 1 := by
  have hsub := abs_relDensityOn_sub_coarse_mul_card_le_of_good_children H H' hV f hf hτ0 hgood hbad
  rw [isTopRegularOverPolyad_one_iff]
  intro c U hU
  obtain hP0 | hPpos := P.support.eq_empty_or_nonempty
  · have hU0 : U.support = ∅ := subset_empty.1 (hP0 ▸ U.support_subset)
    simpa [hU0, H'.relativeDensity_of_support_eq_empty c hP0] using hδ.le
  · have hUpos : (0 : ℝ) < #U.support := (mul_pos hδ (Nat.cast_pos.2 hPpos.card_pos)).trans_le hU
    have hUP : (#U.support : ℝ) ≤ #P.support := by exact_mod_cast card_le_card U.support_subset
    have hU_dev := hsub c U
    have hP_dev := hsub c (Subpolyad3.ofSubcells P P.c₀ P.c₁ P.c₂)
    rw [Subpolyad3.support_ofSubcells_cells, ← H'.relativeDensity_def] at hP_dev
    rw [abs_mul, Nat.abs_cast] at hU_dev hP_dev
    have hbase : |(H'.relativeDensity c P : ℝ) - H.relativeDensity c P| * #U.support ≤
        (τ + θ) * #P.support :=
      (mul_le_mul_of_nonneg_left hUP (abs_nonneg _)).trans hP_dev
    have hsplit : |(H'.relDensityOn c U.support : ℝ) - H'.relativeDensity c P| ≤
        |(H'.relDensityOn c U.support : ℝ) - H.relativeDensity c P| +
          |(H'.relativeDensity c P : ℝ) - H.relativeDensity c P| := by
      rw [abs_sub_comm (H'.relativeDensity c P : ℝ)]; exact abs_sub_le _ _ _
    have hmul := mul_le_mul_of_nonneg_right hsplit hUpos.le
    rw [add_mul] at hmul
    refine le_of_mul_le_mul_right ?_ hUpos
    calc |(H'.relDensityOn c U.support : ℝ) - H'.relativeDensity c P| * #U.support
        ≤ 2 * (τ + θ) * #P.support := by linarith
      _ ≤ δ ^ 2 * #P.support := by gcongr
      _ ≤ δ * #U.support := by nlinarith

open Classical in
/-- Markov charging of irregular coarse polyads over a configurable filter `Keep` of coarse
polyads: irregular polyads outside `Keep` contribute to `repMass`, while irregular polyads in
`Keep` are charged to `¬Good` fine children via `θ⁻¹`. -/
private theorem topRegularOverMostPolyads_of_good_children
    {H H' : Colored3Graph κ V} {C D : TriadicComplex3 V}
    (hC : C.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (Keep : Polyad3 C.skeleton → Prop) (Good : Polyad3 D.skeleton → Prop)
    {τ θ δ ε' : ℝ} (hδ : 0 < δ) (hτ0 : 0 ≤ τ) (hθ : 0 < θ) (hε' : 0 ≤ ε')
    (htol : 2 * (τ + θ) ≤ δ ^ 2)
    (hgood : ∀ (P : Polyad3 C.skeleton) (Q : Polyad3 D.skeleton),
      Keep P → Q.coarsen hV f = P → Good Q →
      ∀ (c : κ) (S' : Subpolyad3 Q),
        |((H'.relDensityOn c S'.support : ℝ) - H.relativeDensity c P) * #S'.support| ≤
          τ * #Q.support)
    {repMass badMass : ℝ}
    (hrep : ∑ P : Polyad3 C.skeleton with ¬Keep P, (#P.support : ℝ) ≤ repMass)
    (hbad : ∑ Q : Polyad3 D.skeleton with Keep (Q.coarsen hV f) ∧ ¬Good Q,
        (#Q.support : ℝ) ≤ badMass)
    (hbudget : 0 < (Fintype.card V).descFactorial 3 →
      repMass + badMass / θ ≤ ε' * (Fintype.card V).descFactorial 3) :
    H'.TopRegularOverMostPolyads C δ ε' 1 := by
  let badChild (P : Polyad3 C.skeleton) : ℝ :=
    ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P ∧ ¬Good Q, (#Q.support : ℝ)
  have hcharge (P : Polyad3 C.skeleton) :
      (if ¬H'.IsTopRegularOverPolyad P δ 1 then (#P.support : ℝ) else 0) ≤
        (if ¬Keep P then (#P.support : ℝ) else 0) +
          (if Keep P then badChild P / θ else 0) := by
    have hbc0 : 0 ≤ badChild P / θ :=
      div_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) hθ.le
    by_cases hP : H'.IsTopRegularOverPolyad P δ 1
    · simp only [hP, not_true_eq_false, ↓reduceIte]
      split_ifs <;> positivity
    · simp only [hP, not_false_eq_true, ↓reduceIte]
      by_cases hK : Keep P
      · simp only [hK, not_true_eq_false, ↓reduceIte, zero_add]
        rw [le_div_iff₀ hθ, mul_comm]
        by_contra! hlt
        exact hP (isTopRegularOverPolyad_of_good_children H H' hV f hf hδ hτ0 htol
          (fun Q hQP hGQ ↦ hgood P Q hK hQP hGQ) hlt.le)
      · simp only [hK, not_false_eq_true, ↓reduceIte, add_zero, le_refl]
  have hfib : ∑ P : Polyad3 C.skeleton with Keep P, badChild P =
      ∑ Q : Polyad3 D.skeleton with Keep (Q.coarsen hV f) ∧ ¬Good Q, (#Q.support : ℝ) := by
    rw [← sum_fiberwise_of_maps_to (g := fun Q : Polyad3 D.skeleton ↦ Q.coarsen hV f)
      (fun Q hQ ↦ mem_filter.2 ⟨mem_univ _, (mem_filter.1 hQ).2.1⟩)]
    refine sum_congr rfl fun P hP ↦ sum_congr ?_ fun _ _ ↦ rfl
    ext Q
    simp only [mem_filter, mem_univ, true_and]
    have hKP : Keep P := (mem_filter.1 hP).2
    exact ⟨by rintro ⟨rfl, hng⟩; exact ⟨⟨hKP, hng⟩, rfl⟩,
      by rintro ⟨⟨_, hng⟩, rfl⟩; exact ⟨rfl, hng⟩⟩
  have hsum_irr : ∑ P : Polyad3 C.skeleton with ¬H'.IsTopRegularOverPolyad P δ 1,
      (#P.support : ℝ) ≤ repMass + badMass / θ := by
    calc ∑ P : Polyad3 C.skeleton with ¬H'.IsTopRegularOverPolyad P δ 1, (#P.support : ℝ)
        = ∑ P : Polyad3 C.skeleton,
            if ¬H'.IsTopRegularOverPolyad P δ 1 then (#P.support : ℝ) else 0 := sum_filter _ _
      _ ≤ ∑ P : Polyad3 C.skeleton,
            ((if ¬Keep P then (#P.support : ℝ) else 0) +
              (if Keep P then badChild P / θ else 0)) := sum_le_sum fun P _ ↦ hcharge P
      _ = (∑ P : Polyad3 C.skeleton with ¬Keep P, (#P.support : ℝ)) +
            (∑ P : Polyad3 C.skeleton with Keep P, badChild P) / θ := by
          rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_div]
      _ = (∑ P : Polyad3 C.skeleton with ¬Keep P, (#P.support : ℝ)) +
            (∑ Q : Polyad3 D.skeleton with Keep (Q.coarsen hV f) ∧ ¬Good Q,
              (#Q.support : ℝ)) / θ := by rw [hfib]
      _ ≤ repMass + badMass / θ := add_le_add hrep (div_le_div_of_nonneg_right hbad hθ.le)
  rw [topRegularOverMostPolyads_iff, exceptionalPolyadMass_eq_sum_div hC]
  rcases Nat.eq_zero_or_pos ((Fintype.card V).descFactorial 3) with hdesc0 | hdesc
  · rw [hdesc0, Nat.cast_zero, div_zero]
    exact hε'
  · rw [div_le_iff₀ (Nat.cast_pos.2 hdesc)]
    exact hsum_irr.trans (hbudget hdesc)

end SharedCoarsePassage

section EnergyGapRecoloring

variable [Fintype κ] [DecidableEq κ]

/-- **Coupled triple recoloring across a small polyad energy gap.** Let `D` refine `C` along a
pair-color projection `f` recovering `C.skeleton.pairColors.color`, with both complexes selecting
polyad decompositions, and suppose `H` is `(η, 1)`-top-regular over all polyads of `D` outside a
`μ`-proportion of the injective triples, with polyad energy gap from `C` to `D` at most `g`. For
`0 ≤ η` and `0 < δ, β, θ`, when `N₀` satisfies the Hoeffding support bound
`221 (3 |V|² + |κ| + 7) ≤ β² N₀` and `2 (|κ| (η + β) + θ) ≤ δ²`, there is a coloring `H'` within
edit discrepancy `|κ| (√g + β)` of `H` that is `(δ, 1)`-top-regular over all polyads of `C` outside
a proportion of the injective triples bounded by
`(μ + card (Polyad3 D.skeleton) * N₀ / |V|.descFactorial 3) / θ`. -/
theorem TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le
    {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {η μ δ β θ N₀ g : ℝ}
    (h : H.TopRegularOverMostPolyads D η μ 1)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hβ : 0 < β) (hθ : 0 < θ)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀)
    (htol : 2 * (Fintype.card κ * (η + β) + θ) ≤ δ ^ 2) :
    ∃ H' : Colored3Graph κ V,
      H.Approximates3 H' (Fintype.card κ * (√g + β)) ∧
      H'.TopRegularOverMostPolyads C δ
        ((μ + Fintype.card (Polyad3 D.skeleton) * N₀ /
          (Fintype.card V).descFactorial 3) / θ) 1 := by
  classical
  have hN₀_pos : 0 < N₀ := pos_of_support_lower_bound hN₀
  obtain ⟨H', happrox, hchild⟩ :=
    exists_coupled_recoloring_of_polyadEnergy_sub_le (H := H) (C := C) (D := D) hV f hf hgap hβ hN₀
  refine ⟨H', happrox, ?_⟩
  let Good : Polyad3 D.skeleton → Prop := fun Q ↦
    N₀ ≤ (#Q.support : ℝ) ∧ H.IsTopRegularOverPolyad Q η 1
  have hbad : ∑ Q : Polyad3 D.skeleton with True ∧ ¬Good Q, (#Q.support : ℝ) ≤
      μ * (Fintype.card V).descFactorial 3 + Fintype.card (Polyad3 D.skeleton) * N₀ := by
    let s₁ := univ.filter fun Q : Polyad3 D.skeleton ↦ ¬N₀ ≤ (#Q.support : ℝ)
    let s₂ := univ.filter fun Q : Polyad3 D.skeleton ↦ ¬H.IsTopRegularOverPolyad Q η 1
    have hunion : (univ.filter fun Q : Polyad3 D.skeleton ↦ True ∧ ¬Good Q) = s₁ ∪ s₂ := by
      ext Q; simp only [Good, s₁, s₂, mem_union, mem_filter, mem_univ, true_and, not_and]
      tauto
    have hsmall_sum : ∑ Q ∈ s₁, (#Q.support : ℝ) ≤ Fintype.card (Polyad3 D.skeleton) * N₀ := by
      calc ∑ Q ∈ s₁, (#Q.support : ℝ)
          ≤ ∑ _Q ∈ s₁, N₀ := sum_le_sum fun Q hQ ↦ (not_le.1 (mem_filter.1 hQ).2).le
        _ ≤ ∑ _Q : Polyad3 D.skeleton, N₀ :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ hN₀_pos.le
        _ = Fintype.card (Polyad3 D.skeleton) * N₀ := by rw [sum_const, card_univ, nsmul_eq_mul]
    have hirr_D : ∑ Q ∈ s₂, (#Q.support : ℝ) ≤ μ * (Fintype.card V).descFactorial 3 := by
      simpa only [s₂] using h.sum_card_support_univ_le hD
    have hinter : 0 ≤ ∑ Q ∈ s₁ ∩ s₂, (#Q.support : ℝ) := sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    rw [hunion]
    linarith [sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := fun Q ↦ (#Q.support : ℝ))]
  have hε' : 0 ≤ (μ + Fintype.card (Polyad3 D.skeleton) * N₀ /
      (Fintype.card V).descFactorial 3) / θ := by
    have := h.nonneg; positivity
  refine topRegularOverMostPolyads_of_good_children (H := H) hC hV f hf (fun _ ↦ True) Good
    (τ := Fintype.card κ * (η + β)) (repMass := 0)
    (badMass := μ * (Fintype.card V).descFactorial 3 + Fintype.card (Polyad3 D.skeleton) * N₀)
    hδ (by positivity) hθ hε' htol (fun P Q _ hQP hGQ c S' ↦ hchild hQP hGQ.1 hGQ.2 c S')
    (by simp) (by convert hbad) (fun hdesc ↦ ?_)
  have hdescR : (0 : ℝ) < (Fintype.card V).descFactorial 3 := Nat.cast_pos.2 hdesc
  rw [zero_add, div_le_iff₀ hθ]
  exact le_of_eq (by field_simp [hθ.ne', hdescR.ne'])

end EnergyGapRecoloring

section EquipartitionRecoloring

variable [Fintype κ] [DecidableEq κ]

/-- Large, distinct-cell, rank-one top-regular fine polyads recolored in the gluing step. -/
private def IsGoodFinePolyad (H : Colored3Graph κ V) {D : TriadicComplex3 V} (η γ : ℝ) (s : ℕ)
    (Q : Polyad3 D.skeleton) : Prop :=
  Q.HasDistinctCells ∧ γ * (s : ℝ) ^ 3 ≤ #Q.support ∧ H.IsTopRegularOverPolyad Q η 1

omit [Fintype κ] in
private theorem isGoodFinePolyad_perm_iff (H : Colored3Graph κ V) {D : TriadicComplex3 V}
    (η γ : ℝ) (s : ℕ) (Q : Polyad3 D.skeleton) (σ : Equiv.Perm (Fin 3)) :
    IsGoodFinePolyad H η γ s (Q.perm σ) ↔ IsGoodFinePolyad H η γ s Q := by
  simp [IsGoodFinePolyad]

/-- Local coupled recoloring on the unordered support of a single good fine polyad `Q`. -/
private theorem exists_local_coupled_recoloring (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η γ : ℝ} {s : ℕ} (hs : 1 ≤ s) (hη : 0 < η) (hγ : 0 < γ)
    (hcells : ∀ A ∈ D.skeleton.vertexPart.parts, #A ≤ 2 * s)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤ s)
    (Q : Polyad3 D.skeleton) (hQ : IsGoodFinePolyad H η γ s Q) :
    ∃ x : Set.powersetCard V 3 → κ,
      (∀ e ∉ Q.unorderedSupport, x e = H.color e) ∧
      (#{e ∈ Q.unorderedSupport | x e ≠ H.color e} : ℝ) ≤
        (∑ c : κ, #Q.support *
          |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
          Fintype.card κ * η * #Q.support ∧
      ∀ (S : Subpolyad3 Q) (d : κ),
        |(#{e ∈ S.unorderedSupport | x e = d} : ℝ) -
            H.relativeDensity d (Q.coarsen hVeq.le π) * #S.unorderedSupport| ≤
          2 * Fintype.card κ * η * #Q.support := by
  classical
  obtain ⟨hdist, hsize, hreg⟩ := hQ
  have hQpos : (0 : ℝ) < #Q.support := lt_of_lt_of_le (by positivity) hsize
  have hPne : (Q.coarsen hVeq.le π).support.Nonempty :=
    (card_pos.1 (Nat.cast_pos.1 hQpos)).mono
      (Polyad3.support_subset_coarsen hVeq.le π (fun p ↦ (hπ p).symm) Q)
  have hcardΩ : #Q.unorderedSupport = #Q.support := hdist.card_unorderedSupport
  have hIcard : Fintype.card (Subpolyad3 Q) ≤ 2 ^ (12 * s ^ 2) := by
    refine (card_subpolyad3_le_mul_card Q).trans (Nat.pow_le_pow_right two_pos ?_)
    have h0 := hcells Q.c₀ Q.hc₀; have h1 := hcells Q.c₁ Q.hc₁; have h2 := hcells Q.c₂ Q.hc₂
    calc #Q.c₀ * #Q.c₁ + #Q.c₀ * #Q.c₂ + #Q.c₁ * #Q.c₂
        ≤ (2 * s) * (2 * s) + (2 * s) * (2 * s) + (2 * s) * (2 * s) := by gcongr
      _ = 12 * s ^ 2 := by ring
  have hN_bound :
      ((12 * s ^ 2 : ℕ) : ℝ) + Fintype.card κ + 2 ≤ 2 * η ^ 2 * #Q.unorderedSupport := by
    rw [hcardΩ]
    have hs2 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ s := Nat.one_le_cast.2 hs
      nlinarith
    have hreq' : (Fintype.card κ : ℝ) + 14 ≤ 2 * η ^ 2 * γ * s := by
      rwa [div_le_iff₀' (by positivity)] at hs_req
    have h1 : ((12 * s ^ 2 : ℕ) : ℝ) + Fintype.card κ + 2 ≤
        ((Fintype.card κ : ℝ) + 14) * (s : ℝ) ^ 2 := by
      push_cast
      have : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
      nlinarith
    have h2 : ((Fintype.card κ : ℝ) + 14) * (s : ℝ) ^ 2 ≤ 2 * η ^ 2 * (γ * (s : ℝ) ^ 3) := by
      calc _ ≤ (2 * η ^ 2 * γ * s) * (s : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hreq' (sq_nonneg _)
        _ = 2 * η ^ 2 * (γ * (s : ℝ) ^ 3) := by ring
    linarith [mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ 2 * η ^ 2)]
  have hub : 2 * (Fintype.card (Subpolyad3 Q) + 1 : ℝ) * Fintype.card κ *
      Real.exp (-2 * (η * #Q.support) ^ 2 / #Q.unorderedSupport) < 1 := by
    rw [← hcardΩ]
    exact two_mul_add_one_mul_exp_lt_of_le_two_pow hIcard hN_bound
  have hQcount (c : κ) : (#{e ∈ Q.unorderedSupport | H.color e = c} : ℝ) =
      (H.relativeDensity c Q : ℝ) * #Q.support := by
    rw [hdist.card_filter_unorderedSupport H c, H.relativeDensity_def]
    exact_mod_cast (H.relDensityOn_mul_card c Q.support).symm
  have hx₀ (S : Subpolyad3 Q) (c : κ) :
      |(#{e ∈ S.unorderedSupport | H.color e = c} : ℝ) -
        (#{e ∈ Q.unorderedSupport | H.color e = c} : ℝ) / #Q.unorderedSupport *
          #S.unorderedSupport| ≤ η * #Q.support := by
    have hScount : (#{e ∈ S.unorderedSupport | H.color e = c} : ℝ) =
        (H.relDensityOn c S.support : ℝ) * #S.support := by
      rw [S.card_filter_unorderedSupport hdist H c]
      exact_mod_cast (H.relDensityOn_mul_card c S.support).symm
    rw [hScount, hQcount, hcardΩ, S.card_unorderedSupport hdist,
      mul_div_cancel_right₀ _ hQpos.ne', ← sub_mul, abs_mul, Nat.abs_cast]
    exact hreg.abs_relDensityOn_sub_mul_card_le c S
  have hp0 (c : κ) : 0 ≤ (H.relativeDensity c (Q.coarsen hVeq.le π) : ℝ) :=
    mod_cast H.relativeDensity_nonneg c _
  have hp1 : ∑ c : κ, (H.relativeDensity c (Q.coarsen hVeq.le π) : ℝ) = 1 :=
    mod_cast H.sum_relativeDensity hPne
  obtain ⟨x, hxout, hxedit, hxdisc⟩ := exists_recoloring_abs_card_filter_sub_mul_card_le
    Q.unorderedSupport H.color hp0 hp1 (fun S : Subpolyad3 Q ↦ S.unorderedSupport)
    (fun S ↦ S.unorderedSupport_subset) (mul_pos hη hQpos) hx₀ hub
  refine ⟨x, hxout, hxedit.trans_eq ?_, fun S d ↦ (hxdisc S d).trans_eq (by ring)⟩
  congr 1
  · congr 1
    refine sum_congr rfl fun c _ ↦ ?_
    rw [hQcount, hcardΩ, ← sub_mul, abs_mul, Nat.abs_cast, mul_comm]
  · ring

omit [Fintype κ] in
/-- Transfer a local subpolyad discrepancy bound on a permuted representative `Q.perm σ` back to
`Q` when `H'` agrees with the local coloring `x` on `(Q.perm σ).unorderedSupport`. -/
private theorem abs_relDensityOn_sub_of_perm_recoloring (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {Q : Polyad3 D.skeleton} (hdist : Q.HasDistinctCells) (hQne : Q.support.Nonempty)
    (σ : Equiv.Perm (Fin 3)) (x : Set.powersetCard V 3 → κ) (S : Subpolyad3 Q) (d : κ) {B : ℝ}
    (hH'_eq : ∀ {e}, e ∈ (Q.perm σ).unorderedSupport → H'.color e = x e)
    (hdisc : |(#{e ∈ (S.perm σ).unorderedSupport | x e = d} : ℝ) -
        H.relativeDensity d ((Q.perm σ).coarsen hVeq.le π) *
          #(S.perm σ).unorderedSupport| ≤ B) :
    |((H'.relDensityOn d S.support : ℝ) -
        H.relativeDensity d (Q.coarsen hVeq.le π)) * #S.support| ≤ B := by
  have hcount : (#{e ∈ (S.perm σ).unorderedSupport | x e = d} : ℝ) =
      (H'.relDensityOn d S.support : ℝ) * #S.support := by
    have hfilt : {e ∈ (S.perm σ).unorderedSupport | x e = d} =
        {e ∈ S.unorderedSupport | H'.color e = d} := by
      rw [Subpolyad3.unorderedSupport_perm]
      refine filter_congr fun e he ↦ ?_
      have heQ : e ∈ (Q.perm σ).unorderedSupport := by
        rw [Polyad3.unorderedSupport_perm]; exact S.unorderedSupport_subset he
      rw [hH'_eq heQ]
    rw [hfilt, S.card_filter_unorderedSupport hdist H' d]
    exact_mod_cast (H'.relDensityOn_mul_card d S.support).symm
  rw [hcount, Subpolyad3.unorderedSupport_perm, S.card_unorderedSupport hdist,
    Polyad3.coarsen_perm_of_support_nonempty Q hQne σ hVeq.le π (fun p ↦ (hπ p).symm),
    relativeDensity_perm] at hdisc
  rwa [sub_mul]

/-- Summing the local coupled-recoloring edit budget over canonical `S₃`-representatives is at most
one-sixth of the total polyad-density deviation plus `|κ| η |V| (|V| - 1) (|V| - 2)`. -/
private theorem six_mul_sum_local_budget_le (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η : ℝ} (hη : 0 < η) (G : Finset (Polyad3 D.skeleton))
    (horbit : ∀ Q₁ ∈ G, ∀ Q₂ ∈ G, ∀ σ : Equiv.Perm (Fin 3),
      Q₂ = Q₁.perm σ → Q₁ = Q₂ ∧ σ = 1) :
    6 * ∑ Q ∈ G,
        ((∑ c : κ, #Q.support *
            |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
          Fintype.card κ * η * #Q.support) ≤
      (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
          #Q.support * |(H.relativeDensity c Q : ℝ) -
            H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3 := by
  let Φ : Polyad3 D.skeleton → ℝ := fun Q ↦
    (∑ c : κ, #Q.support *
      |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
      Fintype.card κ * η * #Q.support
  have htotalD : ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) =
      (Fintype.card V).descFactorial 3 := by
    have hdec :
        (⟨D.pairColorCount, D.skeleton, univ⟩ : TriadicComplex3 V).IsPolyadDecomposition :=
      (TriadicComplex3.isPolyadDecomposition_iff_ofTriple_mem _).2 fun _ ↦ mem_univ _
    exact_mod_cast hdec.sum_card_support
  have hΦperm (Q : Polyad3 D.skeleton) (σ : Equiv.Perm (Fin 3)) : Φ (Q.perm σ) = Φ Q := by
    obtain hQ0 | hQne := Q.support.eq_empty_or_nonempty
    · simp [Φ, hQ0]
    · simp only [Φ, Polyad3.card_support_perm, relativeDensity_perm,
        Polyad3.coarsen_perm_of_support_nonempty Q hQne σ hVeq.le π (fun p ↦ (hπ p).symm)]
  have hΦ0 (Q : Polyad3 D.skeleton) : 0 ≤ Φ Q :=
    add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (abs_nonneg _)) (by norm_num)) (by positivity)
  calc 6 * ∑ Q ∈ G, Φ Q
      ≤ ∑ Q : Polyad3 D.skeleton, Φ Q :=
        Polyad3.six_mul_sum_le_of_perm_invariant G Φ hΦ0 hΦperm horbit
    _ = (∑ c : κ, ∑ Q : Polyad3 D.skeleton, #Q.support *
          |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3 := by
        dsimp only [Φ]; rw [sum_add_distrib, ← sum_div, sum_comm, ← mul_sum, htotalD]

/-- Coupled recoloring on each canonical `S₃`-representative of a good fine polyad, glued across
their pairwise disjoint unordered supports into a global coloring `H'`. -/
private theorem exists_glued_coupled_recoloring (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η γ : ℝ} {s : ℕ} (hs : 1 ≤ s) (hη : 0 < η) (hγ : 0 < γ)
    (hcells : ∀ A ∈ D.skeleton.vertexPart.parts, #A ≤ 2 * s)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤ s) :
    ∃ H' : Colored3Graph κ V,
      (6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
        (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
          #Q.support * |(H.relativeDensity c Q : ℝ) -
            H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3) ∧
      (∀ Q : Polyad3 D.skeleton, IsGoodFinePolyad H η γ s Q →
        ∀ (S : Subpolyad3 Q) (d : κ),
          |((H'.relDensityOn d S.support : ℝ) -
              H.relativeDensity d (Q.coarsen hVeq.le π)) * #S.support| ≤
            2 * Fintype.card κ * η * #Q.support) := by
  classical
  let eP : D.skeleton.vertexPart.parts ≃ Fin (Fintype.card D.skeleton.vertexPart.parts) :=
    Fintype.equivFin _
  let GoodCanon : Finset (Polyad3 D.skeleton) := univ.filter fun Q ↦
    IsGoodFinePolyad H η γ s Q ∧ StrictMono fun i : Fin 3 ↦ eP ⟨Q.cell i, Q.cell_mem_parts i⟩
  have hcanon_orbit : ∀ Q₁ ∈ GoodCanon, ∀ Q₂ ∈ GoodCanon, ∀ σ : Equiv.Perm (Fin 3),
      Q₂ = Q₁.perm σ → Q₁ = Q₂ ∧ σ = 1 := by
    intro Q₁ hQ₁ Q₂ hQ₂ σ h
    obtain ⟨τ, -, huniq⟩ := (mem_filter.1 hQ₁).2.1.1.existsUnique_perm_strictMono eP eP.injective
    have hσ1 : σ = 1 := (huniq σ (by simpa [← h] using (mem_filter.1 hQ₂).2.2)).trans
      (huniq 1 (by simpa using (mem_filter.1 hQ₁).2.2)).symm
    exact ⟨by simpa [hσ1] using h.symm, hσ1⟩
  have hdisj : (GoodCanon : Set (Polyad3 D.skeleton)).PairwiseDisjoint Polyad3.unorderedSupport :=
    fun Q₁ hQ₁ Q₂ hQ₂ hne ↦ Polyad3.disjoint_unorderedSupport_of_forall_ne_perm fun σ h ↦
      hne (hcanon_orbit Q₁ hQ₁ Q₂ hQ₂ σ h).1
  let xQ (Q : Polyad3 D.skeleton) : Set.powersetCard V 3 → κ :=
    if h : IsGoodFinePolyad H η γ s Q then
      (exists_local_coupled_recoloring H π hVeq hπ hs hη hγ hcells hs_req Q h).choose
    else H.color
  have hxQ_spec {Q : Polyad3 D.skeleton} (hQ : IsGoodFinePolyad H η γ s Q) :=
    (exists_local_coupled_recoloring H π hVeq hπ hs hη hγ hcells hs_req Q hQ).choose_spec
  obtain ⟨h, h_eq, h_out, h_count⟩ :=
    Finset.exists_piecewise_of_pairwiseDisjoint GoodCanon Polyad3.unorderedSupport hdisj H.color xQ
  let H' : Colored3Graph κ V := ⟨h⟩
  have hncard : ({e | H.color e ≠ H'.color e}.ncard : ℝ) =
      ∑ Q ∈ GoodCanon, (#{e ∈ Q.unorderedSupport | xQ Q e ≠ H.color e} : ℝ) := by
    have hedit_set : {e | H.color e ≠ H'.color e} =
        (({e ∈ GoodCanon.biUnion Polyad3.unorderedSupport | h e ≠ H.color e} :
          Finset (Set.powersetCard V 3)) : Set _) := by
      ext e
      simp only [Set.mem_ofPred_eq, mem_coe, mem_filter]
      refine ⟨fun hne ↦ ⟨?_, hne.symm⟩, fun ⟨_, hne⟩ ↦ hne.symm⟩
      by_contra hnot
      exact hne (h_out e hnot).symm
    rw [hedit_set, Set.ncard_coe_finset, h_count, Nat.cast_sum]
  refine ⟨H', ?_, ?_⟩
  · refine (le_trans ?_ (six_mul_sum_local_budget_le H π hVeq hπ hη GoodCanon hcanon_orbit))
    rw [hncard]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun Q hQ ↦ ?_) (by norm_num)
    have hQg := (mem_filter.1 hQ).2.1
    simpa only [xQ, dite_eq_left hQg] using (hxQ_spec hQg).2.1
  · intro Q hQ S d
    have hQne : Q.support.Nonempty := card_pos.1 (Nat.cast_pos.1
      (lt_of_lt_of_le (by positivity : (0 : ℝ) < γ * (s : ℝ) ^ 3) hQ.2.1))
    obtain ⟨σ, hσ, -⟩ := hQ.1.existsUnique_perm_strictMono eP eP.injective
    have hQ'good : IsGoodFinePolyad H η γ s (Q.perm σ) :=
      (isGoodFinePolyad_perm_iff H η γ s Q σ).2 hQ
    have hQ'mem : Q.perm σ ∈ GoodCanon := mem_filter.2 ⟨mem_univ _, hQ'good, hσ⟩
    have hdisc := (hxQ_spec hQ'good).2.2 (S.perm σ) d
    exact (abs_relDensityOn_sub_of_perm_recoloring H H' π hVeq hπ hQ.1 hQne σ
      (xQ (Q.perm σ)) S d (fun he ↦ h_eq (Q.perm σ) hQ'mem _ he)
      (by simpa only [xQ, dite_eq_left hQ'good] using hdisc)).trans_eq
      (by rw [Polyad3.card_support_perm])

/-- Derive `H.Approximates3 H' ε` from the glued global edit bound and the polyad energy gap. -/
private theorem approximates3_of_glued_edit_bound (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    {ε η g : ℝ} (hε : 0 < ε) (hV6 : 6 ≤ Fintype.card V)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη_eps : (Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η ≤ ε)
    (hedit : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
      (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
        #Q.support * |(H.relativeDensity c Q : ℝ) -
          H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
      Fintype.card κ * η * (Fintype.card V).descFactorial 3) :
    H.Approximates3 H' ε := by
  have hdev : ∑ c : κ, ∑ Q : Polyad3 D.skeleton,
        #Q.support * |(H.relativeDensity c Q : ℝ) -
          H.relativeDensity c (Q.coarsen hVeq.le π)| ≤
      (Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3 := by
    calc _ ≤ ∑ _c : κ, (√g * (Fintype.card V).descFactorial 3) :=
          sum_le_sum fun c _ ↦ H.sum_card_support_mul_abs_relativeDensity_coarsen_le_of_color_eq
            hVeq.le π (fun p ↦ (hπ p).symm) hgap c
      _ = (Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3 := by
          rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]
  have hdesc_le : ((Fintype.card V).descFactorial 3 : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card V) 3
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) ^ 3 := by
    have hV_pos_nat : 0 < Fintype.card V := by omega
    have : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV_pos_nat
    positivity
  have h6 : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (Fintype.card V).descFactorial 3 := Nat.cast_nonneg _
    have h1 : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
        ε * (Fintype.card V).descFactorial 3 := by
      calc 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ)
          ≤ ((Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3) / 2 +
              (Fintype.card κ : ℝ) * η * (Fintype.card V).descFactorial 3 := by linarith
        _ = ((Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η) *
              (Fintype.card V).descFactorial 3 := by ring
        _ ≤ ε * (Fintype.card V).descFactorial 3 := by gcongr
    nlinarith
  rw [approximates3_iff, editDiscrepancy3_def]
  push_cast
  rw [Nat.card_eq_fintype_card, div_le_iff₀ hVpos]
  exact h6

omit [Fintype κ] in
open Classical in
/-- Total bad fine polyad mass over distinct-cell coarse polyads is bounded by the irregular fine
mass plus the tiny fine polyad mass. -/
private theorem sum_card_support_bad_fine_le (H : Colored3Graph κ V) {C D : TriadicComplex3 V}
    (π : Fin D.pairColorCount → Fin C.pairColorCount) {η μ γ : ℝ} (hγ : 0 < γ)
    (hV6 : 6 ≤ Fintype.card V) (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hD : D.IsPolyadDecomposition) (htopD : H.TopRegularOverMostPolyads D η μ 1) :
    ∑ Q : Polyad3 D.skeleton with
        (Q.coarsen hVeq.le π).HasDistinctCells ∧
          ¬IsGoodFinePolyad H η γ (Fintype.card V / #C.skeleton.vertexPart.parts) Q,
        (#Q.support : ℝ) ≤
      (μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ) * (Fintype.card V).descFactorial 3 := by
  set t := #C.skeleton.vertexPart.parts
  set s := Fintype.card V / t
  have hsplit : ∑ Q : Polyad3 D.skeleton with
        (Q.coarsen hVeq.le π).HasDistinctCells ∧ ¬IsGoodFinePolyad H η γ s Q, (#Q.support : ℝ) ≤
      (∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η 1, (#Q.support : ℝ)) +
      (∑ Q : Polyad3 D.skeleton with (#Q.support : ℝ) < γ * (s : ℝ) ^ 3, (#Q.support : ℝ)) := by
    rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun Q _ ↦ ?_
    have : (0 : ℝ) ≤ #Q.support := Nat.cast_nonneg _
    split_ifs with hQ hirr htiny <;> try linarith
    exact absurd ⟨(Polyad3.hasDistinctCells_coarsen_iff Q hVeq π).1 hQ.1,
      not_lt.1 htiny, hirr⟩ hQ.2
  have hirrD := htopD.sum_card_support_univ_le hD
  have htinyD : ∑ Q : Polyad3 D.skeleton with (#Q.support : ℝ) < γ * (s : ℝ) ^ 3,
        (#Q.support : ℝ) ≤
      2 * (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V).descFactorial 3 := by
    have hcardD : (Fintype.card (Polyad3 D.skeleton) : ℝ) ≤
        (t : ℝ) ^ 3 * (D.pairColorCount : ℝ) ^ 3 := by
      have h1 := card_polyad3_le D.skeleton; rw [hVeq, Fintype.card_fin] at h1; exact_mod_cast h1
    have hts : (t : ℝ) * s ≤ Fintype.card V := by exact_mod_cast Nat.mul_div_le (Fintype.card V) t
    have hpow : (Fintype.card V : ℝ) ^ 3 ≤ 2 * (Fintype.card V).descFactorial 3 := by
      exact_mod_cast Nat.pow_le_two_mul_descFactorial (k := 3) hV6
    calc _ ≤ ∑ _Q : Polyad3 D.skeleton, (γ * (s : ℝ) ^ 3) := by
          rw [sum_filter]
          refine sum_le_sum fun Q _ ↦ ?_
          split_ifs with hlt <;> [exact hlt.le; positivity]
      _ = (Fintype.card (Polyad3 D.skeleton) : ℝ) * (γ * (s : ℝ) ^ 3) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ ((t : ℝ) ^ 3 * (D.pairColorCount : ℝ) ^ 3) * (γ * (s : ℝ) ^ 3) := by gcongr
      _ = (D.pairColorCount : ℝ) ^ 3 * γ * ((t : ℝ) * s) ^ 3 := by ring
      _ ≤ (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V : ℝ) ^ 3 := by gcongr
      _ ≤ (D.pairColorCount : ℝ) ^ 3 * γ * (2 * (Fintype.card V).descFactorial 3) := by gcongr
      _ = 2 * (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V).descFactorial 3 := by ring
  linarith

/-- **Coupled recoloring from a fine rank-one top-regular refinement.** Given a coarse triadic
complex `C` with at least `48 / ε` equitable vertex cells and a same-cell palette refinement `D`
over which `H` is `(η, 1)`-top-regular outside a `μ`-proportion and has polyad energy gap at most
`g`, if the cell size `s = |V| / #C.skeleton.vertexPart.parts` and parameters satisfy the coupled
recoloring budgets, then there exists a recoloring `H'` with `H.Approximates3 H' ε` and
`H'.TopRegularOverMostPolyads C δ₁ ε 1`. -/
theorem exists_recoloring_topRegularOverMostPolyads
    (H : Colored3Graph κ V) {C D : TriadicComplex3 V}
    (π : Fin D.pairColorCount → Fin C.pairColorCount) {ε δ₁ η μ γ g : ℝ}
    (hε : 0 < ε) (hδ₁ : 0 < δ₁) (hη : 0 < η) (hγ : 0 < γ)
    (hV6 : 6 ≤ Fintype.card V)
    (hCeq : C.skeleton.vertexPart.IsEquipartition)
    (ht : 48 / ε ≤ #C.skeleton.vertexPart.parts)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    (htopD : H.TopRegularOverMostPolyads D η μ 1)
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη_eps : (Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η ≤ ε)
    (hη_reg : 2 * (Fintype.card κ : ℝ) * η ≤ δ₁ ^ 2 / 4)
    (hμ_γ : μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ ≤ 3 * ε * δ₁ ^ 2 / 16)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤
      ((Fintype.card V / #C.skeleton.vertexPart.parts : ℕ) : ℝ)) :
    ∃ H' : Colored3Graph κ V,
      H.Approximates3 H' ε ∧ H'.TopRegularOverMostPolyads C δ₁ ε 1 := by
  classical
  have ht_pos : 0 < #C.skeleton.vertexPart.parts :=
    Nat.cast_pos.1 (lt_of_lt_of_le (by positivity) ht)
  have hs1 : 1 ≤ Fintype.card V / #C.skeleton.vertexPart.parts :=
    Nat.div_pos (C.skeleton.vertexPart.card_parts_le_card.trans_eq card_univ) ht_pos
  have hcell_ub : ∀ A ∈ D.skeleton.vertexPart.parts,
      #A ≤ 2 * (Fintype.card V / #C.skeleton.vertexPart.parts) := fun A hA ↦ by
    simpa only [card_univ, hVeq] using hCeq.card_part_le_two_mul_div (hVeq ▸ hA)
  obtain ⟨H', hedit, hdisc⟩ := exists_glued_coupled_recoloring H π hVeq hπ hs1 hη hγ
    hcell_ub hs_req
  refine ⟨H', approximates3_of_glued_edit_bound H H' π hε hV6 hVeq hπ hgap hη_eps hedit, ?_⟩
  have hrep : ∑ P : Polyad3 C.skeleton with ¬P.HasDistinctCells, (#P.support : ℝ) ≤
      (ε / 4) * (Fintype.card V).descFactorial 3 := by
    have hpow : (Fintype.card V : ℝ) ^ 3 ≤ 2 * (Fintype.card V).descFactorial 3 := by
      exact_mod_cast Nat.pow_le_two_mul_descFactorial (k := 3) hV6
    have hdiv : 6 / (#C.skeleton.vertexPart.parts : ℝ) ≤ ε / 8 := by
      rw [div_le_iff₀ (Nat.cast_pos.2 ht_pos)]; rw [div_le_iff₀ hε] at ht; linarith
    calc _ ≤ 6 * (Fintype.card V : ℝ) ^ 3 / #C.skeleton.vertexPart.parts :=
          Polyad3.sum_card_support_not_hasDistinctCells_le C.skeleton hCeq ht_pos
      _ = (6 / #C.skeleton.vertexPart.parts) * (Fintype.card V : ℝ) ^ 3 := by ring
      _ ≤ (ε / 8) * (2 * (Fintype.card V).descFactorial 3) := by gcongr
      _ = (ε / 4) * (Fintype.card V).descFactorial 3 := by ring
  have hbad := sum_card_support_bad_fine_le H π hγ hV6 hVeq hD htopD
  have htol : 2 * (2 * (Fintype.card κ : ℝ) * η + δ₁ ^ 2 / 4) ≤ δ₁ ^ 2 := by linarith
  refine topRegularOverMostPolyads_of_good_children
    hC hVeq.le π (fun p ↦ (hπ p).symm) Polyad3.HasDistinctCells
    (IsGoodFinePolyad H η γ (Fintype.card V / #C.skeleton.vertexPart.parts))
    hδ₁ (by positivity) (by positivity) hε.le htol
    (fun P Q _ hQP hGQ d S' ↦ hQP ▸ hdisc Q hGQ S' d) hrep hbad fun _ ↦ ?_
  have hdesc0 : (0 : ℝ) ≤ (Fintype.card V).descFactorial 3 := Nat.cast_nonneg _
  have hbad_div :
      (μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ) * (Fintype.card V).descFactorial 3 /
          (δ₁ ^ 2 / 4) ≤
        (3 * ε / 4) * (Fintype.card V).descFactorial 3 := by
    have h1 := (mul_le_mul_of_nonneg_right hμ_γ hdesc0)
    calc _ ≤ (3 * ε * δ₁ ^ 2 / 16) * (Fintype.card V).descFactorial 3 / (δ₁ ^ 2 / 4) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = (3 * ε / 4) * (Fintype.card V).descFactorial 3 := by field_simp [hδ₁.ne']; ring
  linarith

end EquipartitionRecoloring

end Colored3Graph

end TauCeti
