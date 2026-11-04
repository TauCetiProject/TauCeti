/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Amplifying top regularity from rank one

Rank-one top regularity controls signed color discrepancy on every subpolyad, including those
below the density-test threshold. Intersections of subpolyads are subpolyads, so inclusion-exclusion
then controls the discrepancy on unions of `r` subpolyads with loss at most `2 ^ r`. Choosing the
rank-one parameter `δ` with `2 ^ r * δ ≤ ε ^ 2` gives rank-`r` top regularity at parameter `ε`.
This supplies the quantitative conversion between single-subpolyad and union-subpolyad tests.

The argument follows the subpolyad tests of Rödl–Schacht and uses Mathlib's
`Finset.inclusion_exclusion_sum_biUnion` for the central inclusion-exclusion identity.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

open Subpolyad3

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} {H : Colored3Graph κ V} {δ ε : ℝ}

private theorem sum_color_discrepancy (c : κ)
    (A : Finset {x : Fin 3 → V // Function.Injective x}) :
    (∑ x ∈ A, ((if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c then 1 else 0) -
      (H.relativeDensity c P : ℝ))) =
      ((H.relDensityOn c A : ℝ) - H.relativeDensity c P) * #A := by
  classical
  have hc : (H.relDensityOn c A : ℝ) * #A =
      (#{x ∈ A | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) := by
    exact_mod_cast H.relDensityOn_mul_card c A
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
  rw [sum_boole]
  rw [← hc]
  ring

/-- Rank-one top regularity bounds signed discrepancy on every subpolyad, including those
whose support is below the regularity threshold. -/
theorem IsTopRegularOverPolyad.abs_relDensityOn_sub_mul_card_le
    (h : H.IsTopRegularOverPolyad P δ 1) (c : κ) (Q : Subpolyad3 P) :
    |(H.relDensityOn c Q.support : ℝ) - H.relativeDensity c P| * #Q.support ≤
      δ * #P.support := by
  have : Nonempty κ := ⟨c⟩
  have hδ := h.nonneg
  by_cases hQ : δ * #P.support ≤ (#Q.support : ℝ)
  · calc
      _ ≤ δ * #Q.support := by
        gcongr
        exact isTopRegularOverPolyad_one_iff.1 h c Q hQ
      _ ≤ _ := by gcongr; exact Q.support_subset
  · have h₀ : (0 : ℝ) ≤ H.relDensityOn c Q.support := by
      exact_mod_cast H.relDensityOn_nonneg c Q.support
    have h₁ : (H.relDensityOn c Q.support : ℝ) ≤ 1 := by
      exact_mod_cast H.relDensityOn_le_one c Q.support
    have h₀' : (0 : ℝ) ≤ H.relativeDensity c P := by
      exact_mod_cast H.relativeDensity_nonneg c P
    have h₁' : (H.relativeDensity c P : ℝ) ≤ 1 := by
      exact_mod_cast H.relativeDensity_le_one c P
    have hd : |(H.relDensityOn c Q.support : ℝ) - H.relativeDensity c P| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    calc _ ≤ 1 * (#Q.support : ℝ) := by gcongr
      _ ≤ _ := by simpa using (lt_of_not_ge hQ).le

/-- Rank-one top regularity bounds the signed discrepancy on a finite union of subpolyads,
with a loss bounded by the number of subsets of the indexing type. -/
theorem IsTopRegularOverPolyad.abs_relDensityOn_unionSupport_sub_mul_card_le
    (h : H.IsTopRegularOverPolyad P δ 1) (c : κ) {ι : Type*} [Fintype ι]
    (Q : ι → Subpolyad3 P) :
    |(H.relDensityOn c (unionSupport Q) : ℝ) - H.relativeDensity c P| * #(unionSupport Q) ≤
      (2 : ℝ) ^ Fintype.card ι * δ * #P.support := by
  classical
  have : Nonempty κ := ⟨c⟩
  have hδ := h.nonneg
  let f := fun x : {x : Fin 3 → V // Function.Injective x} ↦
    (if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c then 1 else 0) -
      (H.relativeDensity c P : ℝ)
  have hi (t : (univ : Finset ι).powerset.filter (·.Nonempty)) :
      |∑ x ∈ t.1.inf' (mem_filter.1 t.2).2 (fun i ↦ (Q i).support), f x| ≤
        δ * #P.support := by
    have ht := h.abs_relDensityOn_sub_mul_card_le c
      (finsetInter t.1 (mem_filter.1 t.2).2 Q)
    rw [support_finsetInter] at ht
    rw [sum_color_discrepancy, abs_mul]
    simpa only [Nat.abs_cast] using ht
  have hsum : |∑ x ∈ unionSupport Q, f x| ≤
      (2 : ℝ) ^ Fintype.card ι * δ * #P.support := by
    rw [unionSupport_def, inclusion_exclusion_sum_biUnion]
    calc
      _ ≤ ∑ t : (univ : Finset ι).powerset.filter (·.Nonempty),
          |(-1 : ℤ) ^ (#t.1 + 1) • ∑ x ∈ t.1.inf' (mem_filter.1 t.2).2
            (fun i ↦ (Q i).support), f x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : (univ : Finset ι).powerset.filter (·.Nonempty), δ * #P.support := by
        apply sum_le_sum
        intro t _
        simpa [zsmul_eq_mul, abs_mul, abs_neg_one_pow] using hi t
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe]
        have hc : #((univ : Finset ι).powerset.filter (·.Nonempty)) ≤ 2 ^ Fintype.card ι := by
          simpa using card_filter_le (univ : Finset ι).powerset (·.Nonempty)
        have hc' : (#((univ : Finset ι).powerset.filter (·.Nonempty)) : ℝ) ≤
            (2 : ℝ) ^ Fintype.card ι := by exact_mod_cast hc
        calc _ ≤ (2 : ℝ) ^ Fintype.card ι * (δ * #P.support) := by gcongr
          _ = _ := by ring
  dsimp only [f] at hsum
  simpa only [sum_color_discrepancy, abs_mul, Nat.abs_cast] using hsum

/-- Rank-one regularity at parameter `δ` implies rank-`r` regularity at parameter `ε` whenever
`2 ^ r * δ ≤ ε ^ 2` and `ε` is positive. The rank may be zero. -/
theorem IsTopRegularOverPolyad.of_rank_one (h : H.IsTopRegularOverPolyad P δ 1)
    {r : ℕ} (hε : 0 < ε) (hδε : (2 : ℝ) ^ r * δ ≤ ε ^ 2) :
    H.IsTopRegularOverPolyad P ε r := by
  rw [isTopRegularOverPolyad_iff]
  intro c Q hQ
  obtain hP | hP := P.support.eq_empty_or_nonempty
  · have hU : unionSupport Q = ∅ := subset_empty.1 (hP ▸ unionSupport_subset Q)
    simpa [hU, H.relativeDensity_of_support_eq_empty c hP] using hε.le
  · have hU : (0 : ℝ) < #(unionSupport Q) :=
      (mul_pos hε (Nat.cast_pos.2 hP.card_pos)).trans_le hQ
    have hd := h.abs_relDensityOn_unionSupport_sub_mul_card_le c Q
    simp only [Fintype.card_fin] at hd
    have hb : |(H.relDensityOn c (unionSupport Q) : ℝ) - H.relativeDensity c P| *
        #(unionSupport Q) ≤ ε * #(unionSupport Q) := by
      calc _ ≤ (2 : ℝ) ^ r * δ * #P.support := hd
        _ ≤ ε ^ 2 * #P.support := by gcongr
        _ ≤ ε * #(unionSupport Q) := by nlinarith
    exact (mul_le_mul_iff_left₀ hU).1 (by simpa [mul_comm] using hb)

/-- The explicit calibration `ε ^ 2 / 2 ^ r` of rank-one regularity suffices for rank-`r`
regularity at every positive parameter `ε`. -/
theorem IsTopRegularOverPolyad.of_rank_one_div_pow {r : ℕ}
    (h : H.IsTopRegularOverPolyad P (ε ^ 2 / (2 : ℝ) ^ r) 1) (hε : 0 < ε) :
    H.IsTopRegularOverPolyad P ε r := by
  apply h.of_rank_one hε
  rw [mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]

end TauCeti.Colored3Graph
