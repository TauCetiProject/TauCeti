/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Combinatorics.Hypergraph.Polyad.Density

/-!
# Coarse top-regularity from good fine children

Given a fine refinement `D` of a coarse triadic complex `C` with coarse parent projection
`Q.coarsen hV f`, suppose `2 * (τ + θ) ≤ δ ^ 2`, a coloring `H'` tracks `H.relativeDensity c P`
within `τ * #Q.support` across subpolyads of every good fine child `Q` of a coarse polyad `P` in
`Keep`, and the remaining fine children of `P` carry at most a `θ`-fraction of `#P.support`. Then
`H'` is `(δ, 1)`-top-regular over `P`. Averaging via Markov charging yields
`H'.TopRegularOverMostPolyads C δ ε' 1` from global mass bounds `repMass` on `¬Keep` coarse
polyads and `badMass` on `¬Good` fine children under `Keep` when
`repMass + badMass / θ ≤ ε' * (|V|)₃`
(`TauCeti.Colored3Graph.topRegularOverMostPolyads_of_good_children`).

## Main results

* `TauCeti.Colored3Graph.topRegularOverMostPolyads_of_good_children`: `(δ, 1)`-top-regularity
  over most polyads of `C` from good fine children and coarse/bad-child mass budgets.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

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
  have hsumP : ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P, (#Q.support : ℝ) =
      #P.support := by
    have h := Polyad3.sum_card_support_coarsen hV f hf P
    rw [← Finset.filter_congr_decidable] at h
    exact_mod_cast h
  have hagg := H'.abs_relDensityOn_sub_mul_card_le_sum_polyadMap
    (fun Q : Polyad3 D.skeleton ↦ Q.coarsen hV f) U.support_subset c
    (a := H.relativeDensity c P) (mod_cast H.relativeDensity_nonneg c P)
    (mod_cast H.relativeDensity_le_one c P)
  simp only [Polyad3.coarsen_ofTriple hV f hf, ne_eq, not_true_eq_false, filter_false,
    empty_inter, card_empty, Nat.cast_zero, add_zero] at hagg
  calc |((H'.relDensityOn c U.support : ℝ) - H.relativeDensity c P) * #U.support|
      ≤ ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P,
          |((H'.relDensityOn c (U.support ∩ Q.support) : ℝ) - H.relativeDensity c P) *
            #(U.support ∩ Q.support)| := by convert hagg
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

/-- If `H'` tracks `H.relativeDensity c P` within `τ * #Q.support` on subpolyads of `Good`
fine children `Q` of `Keep` coarse polyads `P`, non-kept coarse mass is at most `repMass`,
`Keep`-parent `¬Good` child mass is at most `badMass`, `2 * (τ + θ) ≤ δ ^ 2`, and
`repMass + badMass / θ ≤ ε' * (|V|)₃`, then `H'.TopRegularOverMostPolyads C δ ε' 1`. -/
theorem topRegularOverMostPolyads_of_good_children
    {H H' : Colored3Graph κ V} {C D : TriadicComplex3 V}
    (hC : C.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (Keep : Polyad3 C.skeleton → Prop) (Good : Polyad3 D.skeleton → Prop)
    [DecidablePred Keep] [DecidablePred Good]
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
  classical
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
          (fun Q hQP hGQ ↦ hgood P Q hK hQP hGQ) (by convert hlt.le))
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
  have hrep' : ∑ P ∈ univ.filter (fun P : Polyad3 C.skeleton ↦ ¬Keep P), (#P.support : ℝ) ≤
      repMass := by
    convert hrep using 2
  have hbad' : ∑ Q ∈ univ.filter (fun Q : Polyad3 D.skeleton ↦ Keep (Q.coarsen hV f) ∧ ¬Good Q),
      (#Q.support : ℝ) ≤ badMass := by
    convert hbad using 2
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
      _ ≤ repMass + badMass / θ := add_le_add hrep' (div_le_div_of_nonneg_right hbad' hθ.le)
  rw [topRegularOverMostPolyads_iff, exceptionalPolyadMass_eq_sum_div hC]
  rcases Nat.eq_zero_or_pos ((Fintype.card V).descFactorial 3) with hdesc0 | hdesc
  · rw [hdesc0, Nat.cast_zero, div_zero]
    exact hε'
  · rw [div_le_iff₀ (Nat.cast_pos.2 hdesc)]
    exact hsum_irr.trans (hbudget hdesc)

end Colored3Graph

end TauCeti
