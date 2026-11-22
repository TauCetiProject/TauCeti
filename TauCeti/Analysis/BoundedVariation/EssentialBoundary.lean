/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.OneDimensional.ReducedBoundary
import TauCeti.Analysis.BoundedVariation.RelativeIsoperimetric
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Covering.HausdorffDensity

/-!
# The essential boundary and the reduced boundary

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure `μ`, and let `s` be a set of locally finite perimeter in an open set `Ω ⊆ E`. The reduced
boundary `∂*s` (`TauCeti.reducedBoundary`) lies in the essential boundary `∂ᵉs`
(`TauCeti.essentialBoundary`, see `TauCeti.reducedBoundary_subset_essentialBoundary`). This file
proves **Federer's theorem**: in `Ω` the two differ by an `Hⁿ⁻¹`-null set,

`Hⁿ⁻¹((∂ᵉs ∩ Ω) \ ∂*s) = 0`

(`TauCeti.euclideanHausdorffMeasure_essentialBoundary_inter_sdiff_reducedBoundary_eq_zero`),
where `Hⁿ⁻¹ = μHE[n - 1]` is the normalized Euclidean Hausdorff measure. Equivalently,
`∂ᵉs ∩ Ω` and `∂*s` agree `Hⁿ⁻¹`-almost everywhere
(`TauCeti.essentialBoundary_inter_ae_eq_reducedBoundary`).

In dimension `n ≤ 1`, `∂ᵉs ∩ Ω = ∂*s` literally as sets
(`TauCeti.reducedBoundary_eq_inter_essentialBoundary_of_finrank_le_one`).

## Proof

In dimension `n ≥ 2`, at a point `x` of the essential boundary, the proportion of `s` in
`closedBall x r` tends neither to `0` nor to `1` as `r → 0⁺`. It depends continuously on `r`, so for
some `a > 0` both `s` and its complement fill a proportion at least `a` of arbitrarily small balls
around `x`
(`TauCeti.exists_pos_frequently_ofReal_mul_measure_closedBall_le`). The relative isoperimetric
inequality in those balls (`TauCeti.min_measure_inter_measure_sdiff_rpow_le_perimeter`) then gives
`c r ^ (n - 1) ≤ P(s; ball x r)` for arbitrarily small `r`, with `c > 0` depending on `x`
(`TauCeti.exists_pos_frequently_ofReal_mul_pow_le_perimeter_ball`). This needs no assumption on
the perimeter of `s` beyond null-measurability near `x`.

So the perimeter measure `|Dχ_s|` has positive upper `(n - 1)`-dimensional density at every point
of `∂ᵉs ∩ Ω` (`TauCeti.exists_pos_frequently_ofReal_mul_pow_le_variationMeasure_closedBall`).
Sorting these points by the size of that density, the density comparison
`MeasureTheory.Measure.mul_hausdorffMeasure_le_measure` bounds the Hausdorff measure of each part
lying off `∂*s` by a multiple of its perimeter measure. That vanishes, since the perimeter measure
is carried by the reduced boundary (`TauCeti.ae_mem_reducedBoundary`).

## Main results

* `TauCeti.exists_pos_frequently_ofReal_mul_pow_le_perimeter_ball`: at a point of the essential
  boundary, `c r ^ (n - 1) ≤ P(s; ball x r)` for some `c > 0` and arbitrarily small `r > 0`.
* `TauCeti.exists_pos_frequently_ofReal_mul_pow_le_variationMeasure_closedBall`: the perimeter
  measure has positive upper `(n - 1)`-dimensional density at every point of `∂ᵉs ∩ Ω`.
* `TauCeti.euclideanHausdorffMeasure_essentialBoundary_inter_sdiff_reducedBoundary_eq_zero`:
  **Federer's theorem**, `Hⁿ⁻¹((∂ᵉs ∩ Ω) \ ∂*s) = 0`.
* `TauCeti.essentialBoundary_inter_ae_eq_reducedBoundary`: `∂ᵉs ∩ Ω = ∂*s` up to an `Hⁿ⁻¹`-null
  set.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Theorem 16.2.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §5.8, Lemma 5.5.
* L. Ambrosio, N. Fusco and D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.61.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E} {x : E}

/-- **Perimeter lower bound at the essential boundary.** In dimension `n ≥ 2`, let `s` be
null-measurable near a point `x` of its essential boundary. Then for some `c > 0` and arbitrarily
small radii `r > 0`, the perimeter of `s` in `ball x r` is at least `c r ^ (n - 1)`. This follows
from the relative isoperimetric inequality, since both `s` and its complement fill a fixed
proportion of arbitrarily small balls around `x`. -/
theorem exists_pos_frequently_ofReal_mul_pow_le_perimeter_ball (hn : 2 ≤ finrank ℝ E)
    {U : Set E} (hU : U ∈ 𝓝 x) (hs : NullMeasurableSet s (μ.restrict U))
    (hx : x ∈ essentialBoundary μ s) :
    ∃ c > 0, ∃ᶠ r in 𝓝[>] 0,
      ENNReal.ofReal (c * r ^ (finrank ℝ E - 1)) ≤ perimeter μ ⟨ball x r, isOpen_ball⟩ s := by
  set n := finrank ℝ E
  obtain ⟨a, ha, hfreq⟩ := exists_pos_frequently_ofReal_mul_measure_closedBall_le hx
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  set m := μ.real (ball (0 : E) 1)
  have hm : 0 < m := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  set K : ℝ := 2 ^ (n + 1) / m ^ (n : ℝ)⁻¹
  have hK : 0 < K := by positivity
  set p : ℝ := 1 - (n : ℝ)⁻¹
  have hp : 0 ≤ p := sub_nonneg.2 (inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ n)))
  have hnp : (n : ℝ) * p = ((n - 1 : ℕ) : ℝ) := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    simp only [p, mul_sub, mul_one, mul_inv_cancel₀ this]
  refine ⟨(a * m) ^ p / K, by positivity,
    (hfreq.and_eventually (Ioo_mem_nhdsGT hε)).mono fun r ⟨⟨h₁, h₂⟩, hr0, hrε⟩ => ?_⟩
  -- Closed and open balls agree up to a null set, so the proportions transfer to `ball x r`.
  have hcb := μ.addHaar_closedBall_ae_eq_ball_of_ne_zero x r hr0.ne'
  have hlow : ENNReal.ofReal (a * m * r ^ n) ≤ min (μ (s ∩ ball x r)) (μ (ball x r \ s)) := by
    have e : ENNReal.ofReal (a * m * r ^ n) = ENNReal.ofReal a * μ (closedBall x r) := by
      rw [Measure.addHaar_closedBall μ x hr0.le, ← ofReal_measureReal measure_ball_lt_top.ne,
        ← ENNReal.ofReal_mul (pow_nonneg hr0.le n), ← ENNReal.ofReal_mul ha.le]
      congr 1
      ring
    rw [e]
    exact le_min (h₁.trans_eq (measure_congr (EventuallyEqSet.rfl.inter hcb)))
      (h₂.trans_eq (measure_congr (hcb.diff EventuallyEqSet.rfl)))
  -- The relative isoperimetric inequality in `ball x r`.
  have hiso := min_measure_inter_measure_sdiff_rpow_le_perimeter (μ := μ)
    (Ω := ⟨ball x r, isOpen_ball⟩) hn (c := x) (r := r)
    (hs.mono (Measure.restrict_mono ((ball_subset_ball hrε.le).trans hεU) le_rfl)) subset_rfl
  have hpow : ENNReal.ofReal (a * m * r ^ n) ^ p =
      ENNReal.ofReal ((a * m) ^ p * r ^ (n - 1)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp, Real.mul_rpow (by positivity)
      (by positivity), ← Real.rpow_natCast r n, ← Real.rpow_mul hr0.le, hnp, Real.rpow_natCast]
  have key : ENNReal.ofReal ((a * m) ^ p * r ^ (n - 1)) ≤
      ENNReal.ofReal K * perimeter μ ⟨ball x r, isOpen_ball⟩ s :=
    hpow ▸ (ENNReal.rpow_le_rpow hlow hp).trans hiso
  rw [div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos hK]
  exact ENNReal.div_le_of_le_mul (key.trans_eq (mul_comm _ _))

/-- **The perimeter measure at the essential boundary.** In dimension `n ≥ 2`, for a set `s` of
locally finite perimeter in an open set `Ω` and a point `x ∈ Ω` of the essential boundary of `s`,
the perimeter measure `|Dχ_s|` has positive upper `(n - 1)`-dimensional density at `x`: for some
`c > 0` and arbitrarily small radii `r > 0`, `c r ^ (n - 1) ≤ |Dχ_s|(closedBall x r)`. -/
theorem exists_pos_frequently_ofReal_mul_pow_le_variationMeasure_closedBall
    (hn : 2 ≤ finrank ℝ E) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hxΩ : x ∈ Ω) (hx : x ∈ essentialBoundary μ s) :
    ∃ c > 0, ∃ᶠ r in 𝓝[>] 0, ENNReal.ofReal (c * r ^ (finrank ℝ E - 1)) ≤
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨c, hc, hfreq⟩ := exists_pos_frequently_ofReal_mul_pow_le_perimeter_ball hn
    (Ω.isOpen.mem_nhds hxΩ)
    ((aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable) hx
  exact ⟨c, hc, (hfreq.and_eventually (eventually_perimeter_ball_le_variationMeasure_closedBall
    hu hfin hxΩ)).mono fun _ h => h.1.trans h.2⟩

/-- **Federer's theorem in dimension `n ≥ 2`.** For a set `s` of locally finite perimeter in an
open set `Ω`, the part of the essential boundary `∂ᵉs` in `Ω` lying off the reduced boundary `∂*s`
is `Hⁿ⁻¹`-null. -/
private theorem euclideanHausdorffMeasure_sdiff_reducedBoundary_of_two_le
    (hn : 2 ≤ finrank ℝ E) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μHE[finrank ℝ E - 1] ((essentialBoundary μ s ∩ Ω) \ reducedBoundary μ Ω s) = 0 := by
  set n := finrank ℝ E
  set d : ℝ := ((n - 1 : ℕ) : ℝ)
  set lam := variationMeasure μ Ω (s.indicator 1)
  -- The points of `Ω` in the essential boundary but not in the reduced boundary.
  set A : Set Ω := (↑) ⁻¹' (essentialBoundary μ s \ reducedBoundary μ Ω s)
  have hA0 : lam A = 0 := measure_mono_null (t := {y : Ω | ↑y ∉ reducedBoundary μ Ω s})
    (fun _ hy => hy.2) (ae_iff.1 ae_mem_reducedBoundary)
  -- Sort the points of `A` by a lower bound `m⁻¹` on the upper density of `|Dχ_s|`.
  set S : ℕ → Set Ω := fun m => {y | y ∈ A ∧
    ∃ᶠ r in 𝓝[>] 0, (m : ℝ≥0∞)⁻¹ * ENNReal.ofReal (2 * r) ^ d ≤ lam (closedBall y r)}
  have hS (m : ℕ) : μH[d] (S m) = 0 := by
    have h := Measure.mul_hausdorffMeasure_le_measure lam (d := d) (A := S m) fun _ hy => hy.2
    have hSA : S m ⊆ A := fun _ hy => hy.1
    have h0 : (m : ℝ≥0∞)⁻¹ * μH[d] (S m) = 0 :=
      nonpos_iff_eq_zero.1 (h.trans (measure_mono_null hSA hA0).le)
    simpa using h0
  have hAS : A ⊆ ⋃ m, S m := by
    intro y hy
    obtain ⟨c, hc, hfreq⟩ := exists_pos_frequently_ofReal_mul_pow_le_variationMeasure_closedBall
      hn hu hfin y.property hy.1
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt
      (ENNReal.ofReal_pos.2 (by positivity : 0 < c / 2 ^ (n - 1))).ne'
    simp_rw [Subtype.preimage_closedBall] at hfreq
    exact mem_iUnion.2 ⟨m, hy,
      (Measure.frequently_ofReal_div_mul_rpow_le_measure_closedBall hfreq).mono
        fun r hr => le_trans (by gcongr) hr⟩
  have hA : μH[d] A = 0 := measure_mono_null hAS (measure_iUnion_null hS)
  have himg : ((↑) : Ω → E) '' A = (essentialBoundary μ s ∩ Ω) \ reducedBoundary μ Ω s :=
    (Subtype.image_preimage_coe _ _).trans (by rw [← inter_sdiff_assoc, inter_comm])
  rw [Measure.euclideanHausdorffMeasure_eq_zero_iff, ← himg,
    isometry_subtypeVal.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _))]
  exact hA

/-- **Federer's theorem.** For a set `s` of locally finite perimeter in an open set `Ω`, the part of
the essential boundary `∂ᵉs` in `Ω` lying off the reduced boundary `∂*s` is `Hⁿ⁻¹`-null. -/
theorem euclideanHausdorffMeasure_essentialBoundary_inter_sdiff_reducedBoundary_eq_zero
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μHE[finrank ℝ E - 1] ((essentialBoundary μ s ∩ Ω) \ reducedBoundary μ Ω s) = 0 := by
  rcases le_or_gt (finrank ℝ E) 1 with hn | hn
  · rw [inter_comm, ← reducedBoundary_eq_inter_essentialBoundary_of_finrank_le_one hn hu hfin,
      sdiff_self, measure_empty]
  · exact euclideanHausdorffMeasure_sdiff_reducedBoundary_of_two_le
      hn hu hfin

/-- **The essential and reduced boundaries agree up to an `Hⁿ⁻¹`-null set.** For a set `s` of
locally finite perimeter in an open set `Ω`, the part of the essential boundary `∂ᵉs` in `Ω` and
the reduced boundary `∂*s` agree `Hⁿ⁻¹`-almost everywhere. -/
theorem essentialBoundary_inter_ae_eq_reducedBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    (essentialBoundary μ s ∩ Ω : Set E) =ᵐ[μHE[finrank ℝ E - 1]] reducedBoundary μ Ω s := by
  refine ae_eq_set.2
    ⟨euclideanHausdorffMeasure_essentialBoundary_inter_sdiff_reducedBoundary_eq_zero hu hfin, ?_⟩
  rw [sdiff_eq_empty.2 (subset_inter reducedBoundary_subset_essentialBoundary
    reducedBoundary_subset), measure_empty]

end TauCeti
