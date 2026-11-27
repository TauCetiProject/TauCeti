/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart

/-!
# The end charts of a sphere with moving input ends

A sphere with moving input ends is the plane minus the centers `c i` of its input ends, with
nonzero scales `a i`, and an output end at `∞`. In real coordinates its ends are charted by
`realChart (z ↦ c i + a i φ₀(z))` for the input end `i` and by the positive end chart `φ'_∞` of the
output end. This file records how these charts sit relative to the centers and to the truncation
`Σ_T` (`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation`).

## Main results

In the namespace `TauCeti.Floer`:

* `subset_preimage_puncturedSphereTruncation_union`: the sphere is covered by `Σ_T` and the images
  of the bands `(T, ∞) × [0, 1)` of its ends.
-/

public section

open Set Function Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_apply)

namespace TauCeti.Floer

variable {ι : Type*} {c a : ι → ℂ}

/-- Every point of the sphere with moving input ends, in real coordinates, lies in the truncation
`Σ_T`, or in the image of the band `(T, ∞) × [0, 1)` under the chart
`realChart (z ↦ c i + a i φ₀(z))` of an input end `i`, or under the positive end chart `φ'_∞` of
the output end. -/
theorem subset_preimage_puncturedSphereTruncation_union (ha : ∀ i, a i ≠ 0) (T : ℝ) :
    {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} ⊆
      Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T ∪
        ((⋃ i, realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) '' (Ioi T ×ˢ Ico 0 1)) ∪
          positiveEndChart inf '' (Ioi T ×ˢ Ico 0 1)) := by
  intro z hz
  set w := Complex.equivRealProdCLM.symm z
  by_cases hzT : w ∈ puncturedSphereTruncation c a T
  · exact Or.inl hzT
  refine Or.inr ?_
  simp only [mem_puncturedSphereTruncation, not_and_or, not_forall, not_le] at hzT
  rcases hzT with ⟨i, hi⟩ | hout
  · refine Or.inl (mem_iUnion.2 ⟨i, ?_⟩)
    set ζ := Complex.equivRealProdCLM (zero.endCoord ((w - c i) / a i))
    -- The longitudinal coordinate of `ζ` exceeds `T`, since `w` lies in the disc about `c i`.
    have hgt : T < ζ.1 := by
      refine lt_of_not_ge fun hle ↦ hi.not_ge ?_
      have hv : (w - c i) / a i ≠ zero.endCenter := by
        rw [endCenter_zero]
        exact div_ne_zero (sub_ne_zero.2 (hz i)) (ha i)
      have h := (re_endCoord_le_iff (by decide) hv).1 hle
      rw [endCenter_zero, sub_zero, norm_div, le_div_iff₀ (norm_pos_iff.2 (ha i))] at h
      linarith
    -- Move the angular coordinate into `[0, 1)` by an integer shift.
    have hper : Periodic (fun t ↦ realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z)
        (ζ.1, t)) 1 := realChart_add_mul_cylindricalEndLift_add_one (c i) (a i) ζ.1
    have h := hper.sub_int_mul_eq (x := ζ.2) ⌊ζ.2⌋
    rw [mul_one, ← Int.fract] at h
    exact ⟨(ζ.1, Int.fract ζ.2), ⟨hgt, Int.fract_nonneg _, Int.fract_lt_one _⟩,
      h.trans (realChart_add_mul_cylindricalEndLift_endCoord (ha i) (hz i))⟩
  · refine Or.inr ⟨endBandCoord inf z, ⟨?_, (endBandCoord_mem inf z).2⟩,
      positiveEndChart_endBandCoord inf ?_⟩
    · have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (by positivity) hout)
      rw [endBandCoord_apply, mem_Ioi]
      exact (lt_fst_positiveEndCoord_inf_iff hw0).2 hout
    · rw [endCenter_inf]
      exact norm_pos_iff.1 (lt_of_le_of_lt (by positivity) hout)

end TauCeti.Floer
