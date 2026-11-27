/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
import TauCeti.Analysis.Normed.Module.CoveringNumber

/-!
# Polynomial volume bounds for norm balls in groups of units

For a homomorphism `j : S →* Eˣ` into a finite-dimensional real normed algebra, the set
where `‖y * j s‖ ≤ R` and `‖(y * j s)⁻¹‖ ≤ R'` is covered by at most
`(1 + 2 R R' / ε) ^ dim E` left translates of `{s | ‖j s - 1‖ ≤ ε}`.
The theorem `MeasureTheory.measure_setOf_norm_le_and_norm_inv_le_le` gives the resulting
bound for any left-invariant measure, without a measurability assumption on `j`.

## Provenance

`MeasureTheory.measure_setOf_norm_le_and_norm_inv_le_le` is adapted from
`New.DiscreteSeries.measure_ball_le_covering` (file `src/Lib/DiscreteSeries/Haar/TotalMass.lean`)
in grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
The source treats unitary groups and right-invariant measures; here the algebra is arbitrary,
the measure is left-invariant, and the net is supplied by
`TauCeti.exists_finset_isCover_of_subset_closedBall`.

## References

* R. Vershynin, *High-Dimensional Probability*, Cambridge University Press (2018), §4.2
  (the volumetric bound on nets).
-/

public section

open Module

namespace MeasureTheory

variable {S E : Type*} [Group S] [MeasurableSpace S] [MeasurableMul S]
  [NormedRing E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Polynomial covering bound for norm balls.** Let `ν` be a left-invariant measure on a group
`S`, `j : S →* Eˣ` a homomorphism to the units of a finite-dimensional real normed algebra and
`y ∈ Eˣ`. For `ε > 0`, the set where `‖y * j s‖ ≤ R` and `‖(y * j s)⁻¹‖ ≤ R'` has measure at most
`(1 + 2 R R' / ε) ^ dim E` times the measure of the ball where `‖j s - 1‖ ≤ ε`. -/
theorem measure_setOf_norm_le_and_norm_inv_le_le (ν : Measure S) [ν.IsMulLeftInvariant]
    (j : S →* Eˣ) (y : Eˣ) {ε R R' : ℝ} (hε : 0 < ε) :
    ν {s | ‖((y * j s : Eˣ) : E)‖ ≤ R ∧ ‖(((y * j s)⁻¹ : Eˣ) : E)‖ ≤ R'} ≤
      ENNReal.ofReal ((1 + 2 * R * R' / ε) ^ finrank ℝ E) * ν {s | ‖(j s : E) - 1‖ ≤ ε} := by
  set T := {s | ‖((y * j s : Eˣ) : E)‖ ≤ R ∧ ‖(((y * j s)⁻¹ : Eˣ) : E)‖ ≤ R'}
  set B := {s | ‖(j s : E) - 1‖ ≤ ε}
  rcases T.eq_empty_or_nonempty with hT | ⟨s₀, hs₀⟩
  · simp [hT]
  have hR : 0 ≤ R := (norm_nonneg _).trans hs₀.1
  rcases ((norm_nonneg _).trans hs₀.2).eq_or_lt with rfl | hR'
  · -- `R' = 0` forces `E` to be the zero ring, where every point lies in `B`.
    have : Subsingleton E := subsingleton_of_zero_eq_one <| by
      rw [← Units.mul_inv (y * j s₀), norm_le_zero_iff.1 hs₀.2, mul_zero]
    have hTB : T ⊆ B := fun s _ ↦ by simp [B, Subsingleton.elim ((j s : E) - 1) 0, hε.le]
    simpa [finrank_zero_of_subsingleton] using measure_mono hTB
  -- An `ε / R'`-net of the image of `T`, by points `y * j (k c)` with `k c ∈ T`.
  have hδ : ((ε / R').toNNReal : ℝ) = ε / R' := Real.coe_toNNReal _ (by positivity)
  have hA : (fun s ↦ ((y * j s : Eˣ) : E)) '' T ⊆ Metric.closedBall 0 R.toNNReal := by
    rintro _ ⟨s, hs, rfl⟩
    simpa [Real.coe_toNNReal _ hR] using hs.1
  obtain ⟨N, hNA, hcover, hcard⟩ := TauCeti.exists_finset_isCover_of_subset_closedBall
    (ε := (ε / R').toNNReal) (by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity) hA
  choose! k hkT hkf using fun c (hc : c ∈ N) ↦ hNA hc
  -- The left translates `k c • B` cover `T`.
  have hcov : T ⊆ ⋃ c ∈ N, (fun s ↦ (k c)⁻¹ * s) ⁻¹' B := by
    intro g hg
    obtain ⟨c, hc, hgc⟩ := Set.mem_iUnion₂.1 <| Metric.isCover_iff_subset_iUnion_closedBall.1
      hcover (Set.mem_image_of_mem _ hg)
    refine Set.mem_iUnion₂.2 ⟨c, hc, ?_⟩
    have hdist : ‖((y * j g : Eˣ) : E) - ((y * j (k c) : Eˣ) : E)‖ ≤ ε / R' := by
      simpa [hkf c hc, dist_eq_norm, hδ] using hgc
    have key : (j ((k c)⁻¹ * g) : E) - 1 = (((y * j (k c))⁻¹ : Eˣ) : E) *
        (((y * j g : Eˣ) : E) - ((y * j (k c) : Eˣ) : E)) := by
      simp [mul_sub, ← Units.val_mul, map_mul, map_inv, mul_assoc]
    simp only [Set.mem_preimage, B, Set.mem_ofPred_eq, key]
    calc _ ≤ ‖(((y * j (k c))⁻¹ : Eˣ) : E)‖ *
          ‖((y * j g : Eˣ) : E) - ((y * j (k c) : Eˣ) : E)‖ := norm_mul_le _ _
      _ ≤ R' * (ε / R') := by gcongr; exact (hkT c hc).2
      _ = ε := by field_simp
  calc ν T ≤ ∑ c ∈ N, ν ((fun s ↦ (k c)⁻¹ * s) ⁻¹' B) :=
        (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
    _ = N.card * ν B := by simp [measure_preimage_mul]
    _ ≤ ENNReal.ofReal ((1 + 2 * R * R' / ε) ^ finrank ℝ E) * ν B := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        refine ENNReal.ofReal_le_ofReal (hcard.trans_eq ?_)
        rw [hδ, Real.coe_toNNReal _ hR]
        field_simp

end MeasureTheory
