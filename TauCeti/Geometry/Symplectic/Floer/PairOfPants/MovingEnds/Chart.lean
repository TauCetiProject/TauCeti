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

* `equivRealProdCLM_symm_positiveEndChart_inf_ne`: if the centers lie in the disc
  `‖w‖ ≤ 2 exp (2π)`, then beyond `s = 1` the output end misses every center.
* `subset_preimage_puncturedSphereTruncation_union`: the sphere is covered by `Σ_T` and the images
  of the bands `(T, ∞) × [0, 1)` of its ends.
-/

public section

open Set Function Filter Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology
open TauCeti.Complex (realChart realChart_apply)

namespace TauCeti.Floer

variable {ι : Type*} {c a : ι → ℂ}

/-- If the centers lie in the disc `‖w‖ ≤ 2 exp (2π)`, then beyond `s = 1` the output end, in the
positive end chart `φ'_∞`, misses every center. -/
theorem equivRealProdCLM_symm_positiveEndChart_inf_ne
    (hc : ∀ i, ‖c i‖ ≤ 2 * Real.exp (2 * π)) {ζ : ℝ × ℝ} (hζ : 1 < ζ.1) (j : ι) :
    Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) ≠ c j := by
  intro h
  have h₁ := norm_equivRealProdCLM_symm_positiveEndChart_inf ζ.1 ζ.2
  rw [Prod.mk.eta, h] at h₁
  have : Real.exp (2 * π) < Real.exp (2 * π * ζ.1) :=
    Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  linarith [hc j]

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
    have hd : 0 < ‖w - c i‖ := norm_pos_iff.2 (sub_ne_zero.2 (hz i))
    have hlim : Tendsto (fun s : ℝ ↦ ‖a i‖ * Real.exp (-(2 * π * s)) / 2) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop Real.two_pi_pos)).const_mul ‖a i‖).div_const 2
    obtain ⟨R, hR⟩ := (hlim.eventually (gt_mem_nhds hd)).exists
    obtain ⟨z₀, -, -, hz₀⟩ := exists_add_mul_cylindricalEndLift_eq (r := T) (ha i) hR.le hi.le
    -- The longitudinal coordinate of `z₀` exceeds `T`, since its distance to `c i` is smaller.
    have hgt : T < z₀.re := by
      by_contra hle
      have hdist := norm_add_mul_cylindricalEndLift_sub (c i) (a i) z₀
      rw [hz₀] at hdist
      have : Real.exp (-(2 * π * T)) ≤ Real.exp (-(2 * π * z₀.re)) :=
        Real.exp_le_exp.2 (by nlinarith [pi_pos])
      nlinarith [norm_nonneg (a i)]
    -- Move the angular coordinate into `[0, 1)` by an integer shift.
    have hper : Periodic (fun t ↦ realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z)
        (z₀.re, t)) 1 := realChart_add_mul_cylindricalEndLift_add_one (c i) (a i) z₀.re
    have h := hper.sub_int_mul_eq (x := z₀.im) ⌊z₀.im⌋
    rw [mul_one, ← Int.fract] at h
    refine ⟨(z₀.re, Int.fract z₀.im), ⟨hgt, Int.fract_nonneg _, Int.fract_lt_one _⟩, h.trans ?_⟩
    rw [realChart_apply, show Complex.equivRealProdCLM.symm (z₀.re, z₀.im) = z₀ from
      Complex.ext (by simp) (by simp), hz₀]
    simp [w]
  · refine Or.inr ⟨endBandCoord inf z, ⟨?_, (endBandCoord_mem inf z).2⟩,
      positiveEndChart_endBandCoord inf ?_⟩
    · have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (by positivity) hout)
      rw [endBandCoord_apply, mem_Ioi]
      exact (lt_fst_positiveEndCoord_inf_iff hw0).2 hout
    · rw [endCenter_inf]
      exact norm_pos_iff.1 (lt_of_le_of_lt (by positivity) hout)

end TauCeti.Floer
