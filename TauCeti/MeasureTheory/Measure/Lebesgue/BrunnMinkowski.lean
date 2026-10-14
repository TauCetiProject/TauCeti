/-
Copyright (c) 2026 Weiyi Wang, Jonathan Ho, The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Jonathan Ho, The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# One-dimensional Brunn–Minkowski inequality

For two nonempty Lebesgue-measurable subsets of the real line, the outer volume of their
Minkowski sum is at least the sum of their volumes. No measurability of the Minkowski sum
is required, and the inequality includes zero and infinite volumes. Nonemptiness is essential:
adding the empty set to a positive-volume set gives the empty set.

The compact-set and Borel-set arguments are adapted from Weiyi Wang and Jonathan Ho's
[Mathlib PR #44802](https://github.com/leanprover-community/mathlib4/pull/44802), originating
in [Jonathan Ho's isoperimetric formalization](https://github.com/hojonathanho/isoperimetric).
The proof translates the compact sets so that their extreme points meet at zero; the two
translates have null intersection and their union lies in their Minkowski sum. Inner
regularity then gives the Borel-set inequality. Measurable subsets with the same volume
extend it to Lebesgue-measurable sets. The weighted form uses Mathlib's `Measure.addHaar_smul`.

This is the one-dimensional set inequality used in the Prékopa–Leindler argument.

## References

* Terence Tao, [The Brunn–Minkowski inequality for nilpotent groups]
  (https://terrytao.wordpress.com/2011/09/16/the-brunn-minkowski-inequality-for-nilpotent-groups/),
  for the one-dimensional set argument and its role in the functional inequality.
-/

public section

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Real

/-- One-dimensional **Brunn–Minkowski theorem** for compact sets. -/
theorem volume_add_volume_le_of_isCompact {A B : Set ℝ} (hAn : A.Nonempty) (hAc : IsCompact A)
    (hBn : B.Nonempty) (hBc : IsCompact B) : volume A + volume B ≤ volume (A + B) :=
  calc
    _ = volume (A + {-sSup A}) + volume (B + {-sInf B}) := by simp
    _ = volume ((A + {-sSup A}) ∪ (B + {-sInf B})) +
        volume ((A + {-sSup A}) ∩ (B + {-sInf B})) := by
      rw [measure_union_add_inter _ (hBc.add isCompact_singleton).measurableSet]
    _ ≤ volume ((A + {-sSup A}) ∪ (B + {-sInf B})) := by
      suffices (A + {-sSup A}) ∩ (B + {-sInf B}) ⊆ {0} by
        grw [this]
        simp
      refine fun x ⟨hA, hB⟩ ↦ le_antisymm ?_ ?_
      · exact nonpos_of_add_le_left <| le_csSup hAc.bddAbove <| by simpa using hA
      · exact nonneg_of_le_add_left <| csInf_le hBc.bddBelow <| by simpa using hB
    _ ≤ volume ((A + {-sSup A}) + (B + {-sInf B})) := by
      refine measure_mono <| Set.union_subset_iff.mpr ⟨?_, ?_⟩
      · exact Set.subset_add_left _ (by simpa using hBc.sInf_mem hBn)
      · exact Set.subset_add_right _ (by simpa using hAc.sSup_mem hAn)
    _ = _ := by
      rw [add_add_add_comm]
      simp

/-- One-dimensional **Brunn–Minkowski theorem** for Borel sets, with outer volume on the
right. The sum need not be Borel, and the input sets may have infinite volume. -/
theorem volume_add_volume_le {A B : Set ℝ} (hAn : A.Nonempty) (hAm : MeasurableSet A)
    (hBn : B.Nonempty) (hBm : MeasurableSet B) : volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a, ha⟩ := hAn
  obtain ⟨b, hb⟩ := hBn
  by_cases hA : volume A = ∞
  · trans volume (A + {b})
    · simp [hA]
    · gcongr
      simpa using hb
  by_cases hB : volume B = ∞
  · trans volume ({a} + B)
    · simp [hB]
    · gcongr
      simpa using ha
  calc
    _ = (⨆ (K) (_ : K ⊆ A) (_ : IsCompact K), volume K) +
        (⨆ (K) (_ : K ⊆ B) (_ : IsCompact K), volume K) := by
      rw [hAm.measure_eq_iSup_isCompact_of_ne_top hA, hBm.measure_eq_iSup_isCompact_of_ne_top hB]
    _ ≤ ⨆ (K) (_ : K ⊆ A) (_ : IsCompact K) (L) (_ : L ⊆ B) (_ : IsCompact L),
        volume K + volume L := by
      simp_rw [iSup_and']
      refine ENNReal.biSup_add_biSup_le' ⟨∅, by simp⟩ ⟨∅, by simp⟩ fun K hK L hL ↦ ?_
      aesop (add safe [le_iSup_of_le])
    _ ≤ _ := by
      refine iSup₂_le fun K hKA ↦ iSup₂_le fun hK L ↦ iSup₂_le fun hLB hL ↦ ?_
      trans volume (K ∪ {a}) + volume (L ∪ {b})
      · gcongr <;> simp
      grw [volume_add_volume_le_of_isCompact (by simp) (hK.union isCompact_singleton)
        (by simp) (hL.union isCompact_singleton), Set.union_subset hKA (by simpa using ha),
        Set.union_subset hLB (by simpa using hb)]

/-- One-dimensional **Brunn–Minkowski theorem** for Lebesgue-measurable sets, with outer
volume on the right. No finiteness or measurability of the sum is assumed. -/
theorem volume_add_volume_le_of_nullMeasurableSet {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) : volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a, ha⟩ := hAn
  obtain ⟨b, hb⟩ := hBn
  obtain ⟨K, hKA, hKm, hK⟩ := hAm.exists_measurable_subset_ae_eq
  obtain ⟨L, hLB, hLm, hL⟩ := hBm.exists_measurable_subset_ae_eq
  -- Adjoin points to retain nonemptiness even when a measurable representative is empty.
  have hKvol : volume (K ∪ {a}) = volume A := by
    simpa using measure_congr (hK.union (ae_eq_empty.2 (measure_singleton a)))
  have hLvol : volume (L ∪ {b}) = volume B := by
    simpa using measure_congr (hL.union (ae_eq_empty.2 (measure_singleton b)))
  rw [← hKvol, ← hLvol]
  exact (volume_add_volume_le (by simp) (hKm.union (measurableSet_singleton a))
    (by simp) (hLm.union (measurableSet_singleton b))).trans
    (measure_mono (add_subset_add (union_subset hKA (by simpa using ha))
      (union_subset hLB (by simpa using hb))))

/-- Weighted one-dimensional **Brunn–Minkowski theorem** for Lebesgue-measurable sets.
The coefficients may vanish; extended multiplication uses `0 * ∞ = 0`. Taking
`c = 1 - θ` and `d = θ` gives the convex-combination form for every `θ ∈ [0,1]`. -/
theorem mul_volume_add_mul_volume_le {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ENNReal.ofReal c * volume A + ENNReal.ofReal d * volume B ≤
      volume (c • A + d • B) := by
  have h := volume_add_volume_le_of_nullMeasurableSet hAn.smul_set
    (Measure.NullMeasurableSet.const_smul hAm c) hBn.smul_set
    (Measure.NullMeasurableSet.const_smul hBm d)
  simpa [Measure.addHaar_smul, abs_of_nonneg hc, abs_of_nonneg hd] using h

/-- Real-valued one-dimensional Brunn–Minkowski inequality. Finiteness of the outer
volume of the sum implies finiteness of both input volumes. -/
theorem volume_real_add_volume_real_le {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) (hfin : volume (A + B) ≠ ∞) :
    volume.real A + volume.real B ≤ volume.real (A + B) := by
  have h := volume_add_volume_le_of_nullMeasurableSet hAn hAm hBn hBm
  have hA : volume A ≠ ∞ := ne_top_of_le_ne_top hfin ((le_self_add).trans h)
  have hB : volume B ≠ ∞ := ne_top_of_le_ne_top hfin ((le_add_self).trans h)
  simpa [measureReal_def, ENNReal.toReal_add hA hB] using ENNReal.toReal_mono hfin h

/-- Real-valued weighted one-dimensional Brunn–Minkowski inequality. The outer volume
of the weighted sum must be finite; a zero coefficient still permits an infinite input volume. -/
theorem mul_volume_real_add_mul_volume_real_le {A B : Set ℝ} (hAn : A.Nonempty)
    (hAm : NullMeasurableSet A volume) (hBn : B.Nonempty)
    (hBm : NullMeasurableSet B volume) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfin : volume (c • A + d • B) ≠ ∞) :
    c * volume.real A + d * volume.real B ≤ volume.real (c • A + d • B) := by
  have h := mul_volume_add_mul_volume_le hAn hAm hBn hBm hc hd
  have hA : ENNReal.ofReal c * volume A ≠ ∞ :=
    ne_top_of_le_ne_top hfin (le_self_add.trans h)
  have hB : ENNReal.ofReal d * volume B ≠ ∞ :=
    ne_top_of_le_ne_top hfin (le_add_self.trans h)
  simpa [measureReal_def, ENNReal.toReal_add hA hB, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd] using ENNReal.toReal_mono hfin h

end Real
