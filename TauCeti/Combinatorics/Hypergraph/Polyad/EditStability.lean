/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Stability of top regularity under recoloring

If at most an `η`-fraction of a polyad's supported triples are recolored, the density on a
test carrying an `ε`-fraction of its support changes by at most `η / ε`; the density on the
whole polyad changes by at most `η`. Consequently `(δ, r)`-top regularity survives with
positive parameter `ε` whenever `δ + η + η / ε ≤ ε`. For positive `δ` and `0 ≤ η ≤ 1`, the parameter
`δ + 2 * √η` suffices, independently of the rank and the number of top colors.

These estimates control the regularity error incurred by editing a coloring, including the
cleanup and rebalancing steps in regular approximation arguments. All edit counts here count
role-ordered injective triples, just as the relative densities do; no factor of six is lost.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} {H H' : Colored3Graph κ V}
  {δ ε η : ℝ} {r : ℕ}

/-- Top regularity survives recoloring at most an `η`-fraction of the polyad's support.
The new threshold `ε` must absorb the old error, the change on the whole support, and the
change on a test of relative size at least `ε`. The rank is unchanged. -/
theorem IsTopRegularOverPolyad.edit_of_card_filter_ne_le
    (h : H.IsTopRegularOverPolyad P δ r) (hε : 0 < ε) (hη : 0 ≤ η) (hbudget : δ + η + η / ε ≤ ε)
    (hedit : (#{x ∈ P.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
      H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) ≤ η * #P.support) :
    H'.IsTopRegularOverPolyad P ε r := by
  rw [isTopRegularOverPolyad_iff]
  intro c Q hQ
  obtain hP | hP := P.support.eq_empty_or_nonempty
  · have hU : Subpolyad3.unionSupport Q = ∅ :=
      subset_empty.1 (hP ▸ Subpolyad3.unionSupport_subset Q)
    simp [hU, H'.relativeDensity_of_support_eq_empty c hP, hε.le]
  have hPpos : (0 : ℝ) < #P.support := Nat.cast_pos.2 hP.card_pos
  have hUpos : (0 : ℝ) < #(Subpolyad3.unionSupport Q) :=
    (mul_pos hε hPpos).trans_le hQ
  -- Edits on every test are bounded by the edits on the whole polyad.
  have hd (A : Finset {x : Fin 3 → V // Function.Injective x}) (hA : A ⊆ P.support) :
      |(H.relDensityOn c A : ℝ) - H'.relDensityOn c A| * #A ≤ η * #P.support := by
    have hc : |(H.relDensityOn c A : ℝ) - H'.relDensityOn c A| * #A ≤
        (#{x ∈ A | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
          H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) := by
      exact_mod_cast H.abs_relDensityOn_sub_mul_card_le_card_filter_ne H' c A
    apply hc.trans (le_trans ?_ hedit)
    exact_mod_cast card_le_card (filter_subset_filter _ hA)
  have hwhole : |(H.relativeDensity c P : ℝ) - H'.relativeDensity c P| ≤ η := by
    rw [relativeDensity_def, relativeDensity_def]
    exact (mul_le_mul_iff_left₀ hPpos).1 (by simpa [mul_comm] using hd P.support Subset.rfl)
  have htest : |(H.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ) -
      H'.relDensityOn c (Subpolyad3.unionSupport Q)| ≤ η / ε := by
    apply (mul_le_mul_iff_left₀ hUpos).1
    calc
      _ ≤ η * #P.support := by
        simpa [mul_comm] using hd _ (Subpolyad3.unionSupport_subset Q)
      _ = η / ε * (ε * #P.support) := by field_simp
      _ ≤ η / ε * #(Subpolyad3.unionSupport Q) := by gcongr
      _ = _ := by ring
  -- Compare the old and new densities on the test and on the parent support.
  have hδε : δ ≤ ε := by
    have := div_nonneg hη hε.le
    linarith
  have hreg := isTopRegularOverPolyad_iff.1 h c Q
    ((mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg _)).trans hQ)
  calc
    _ ≤ |(H'.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ) -
          H.relDensityOn c (Subpolyad3.unionSupport Q)| +
        |(H.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ) - H.relativeDensity c P| +
        |(H.relativeDensity c P : ℝ) - H'.relativeDensity c P| := by
      have h₁ := abs_sub_le (H'.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ)
        (H.relativeDensity c P) (H'.relativeDensity c P)
      have h₂ := abs_sub_le (H'.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ)
        (H.relDensityOn c (Subpolyad3.unionSupport Q)) (H.relativeDensity c P)
      linarith
    _ ≤ ε := by rw [abs_sub_comm] at htest; linarith

/-- An edit fraction `η ≤ 1` worsens the regularity parameter by at most `2 * √η`, at any
rank. The old parameter is positive; empty polyad supports are allowed. -/
theorem IsTopRegularOverPolyad.edit_sqrt (h : H.IsTopRegularOverPolyad P δ r)
    (hδ : 0 < δ) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hedit : (#{x ∈ P.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
      H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) ≤ η * #P.support) :
    H'.IsTopRegularOverPolyad P (δ + 2 * Real.sqrt η) r := by
  have hs := Real.sqrt_nonneg η
  have hs₂ := Real.sq_sqrt hη
  have hs₁ : Real.sqrt η ≤ 1 := (Real.sqrt_le_one).2 hη₁
  have hε : 0 < δ + 2 * Real.sqrt η := by positivity
  apply h.edit_of_card_filter_ne_le hε hη ?_ hedit
  have hdiv : η / (δ + 2 * Real.sqrt η) ≤ Real.sqrt η := by
    apply (div_le_iff₀ hε).2
    nlinarith
  nlinarith

end TauCeti.Colored3Graph
