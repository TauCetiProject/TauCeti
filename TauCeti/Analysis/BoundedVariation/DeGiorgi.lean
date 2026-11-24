/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.BlowUp
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.Analysis.BoundedVariation.Dilation
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Covering.HausdorffDensity
import TauCeti.Topology.MetricSpace.Thickening

/-!
# The perimeter measure is Hausdorff measure on the reduced boundary

Let `Ω` be an open set of a finite-dimensional real inner product space `E` of dimension
`n ≥ 2`, and let `s` be a set of locally finite perimeter in `Ω`. This file proves De Giorgi's
representation of the perimeter measure `|Dχ_s|` (`TauCeti.variationMeasure`) as the
`(n - 1)`-dimensional Euclidean Hausdorff measure `Hⁿ⁻¹ = μHE[n - 1]` of the reduced boundary
`∂*s` (`TauCeti.reducedBoundary`):

`|Dχ_s| = Hⁿ⁻¹ ⌊ ∂*s`

as measures on `Ω` (`TauCeti.variationMeasure_eq_comap_restrict_reducedBoundary`), and in fact
`|Dχ_s|(B) = Hⁿ⁻¹(B)` for every subset `B` of the reduced boundary, measurable or not
(`TauCeti.variationMeasure_eq_euclideanHausdorffMeasure_image`). Consequently:

* `TauCeti.perimeter_eq_euclideanHausdorffMeasure_reducedBoundary`: `P(s; Ω) = Hⁿ⁻¹(∂*s)`;
* `TauCeti.perimeter_le_euclideanHausdorffMeasure_frontier_inter`: `P(s; Ω) ≤ Hⁿ⁻¹(∂s ∩ Ω)`, for
  the topological frontier `∂s`, since `∂*s ⊆ ∂s`;
* `TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal`: the
  Gauss–Green formula with surface measure, `∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`, that is,
  `Dχ_s = -ν_s Hⁿ⁻¹ ⌊ ∂*s`.

The statements about the perimeter require `s` to have locally finite perimeter in `Ω`; the
criterion deducing finite perimeter from a finite measure of the boundary is not proved here.
The rectifiability of the reduced boundary, the remaining part of De Giorgi's structure theorem,
is not used.

## Strategy

At a point `x` of the reduced boundary the perimeter measure has density one with respect to
`Hⁿ⁻¹` (`TauCeti.tendsto_variationMeasure_closedBall_div_volume_closedBall`). The density
comparison `MeasureTheory.Measure.mul_euclideanHausdorffMeasure_le_measure` then gives
`Hⁿ⁻¹ ≤ |Dχ_s|` on `∂*s`.

The reverse inequality needs more than the measure of balls: a set of diameter `d` containing `x`
lies in `closedBall x d`, whose perimeter measure is close to `ω_{n-1} d ^ (n - 1)`, twice to the
power `n - 1` the normalization `ω_{n-1} (d / 2) ^ (n - 1)` of `Hⁿ⁻¹`. Instead we bound the
perimeter measure of all small sets uniformly. The blow-ups of `s` at `x` converge to the
half-space `{y | ⟪y, ν⟫ < 0}`, where `ν = ν_s x`. By lower semicontinuity of the perimeter and the
convergence of `|Dχ_s|(closedBall x r) / r ^ (n - 1)`, the rescaled perimeter measures of a closed
set `C` near `x` are eventually at most `Hⁿ⁻¹(C ∩ ν⊥) + δ`, and by the isodiametric inequality
on the hyperplane `ν⊥` this is at most `ω_{n-1} (diam C / 2) ^ (n - 1) + δ`. Covering the unit ball
by finitely many small balls, every subset `T` of the unit ball lies in one of finitely many
closed unions of these balls of diameter at most `diam T + 4 η`. Thus, for all small radii at once,
every set of diameter `d` containing `x` has perimeter measure at most
`(ω_{n-1} ((1 + 4 η) / 2) ^ (n - 1) + η) d ^ (n - 1)`. The comparison
`MeasureTheory.Measure.measure_le_mul_hausdorffMeasure_of_le_mul_ediam_rpow`, which loses no
covering constant, gives `|Dχ_s| ≤ Hⁿ⁻¹` on `∂*s` as `η → 0`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15 (De Giorgi's
  structure theorem, Theorem 15.9).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.8 (the structure theorem for sets of finite perimeter).
* H. Federer, *Geometric Measure Theory*, 2.10.19 (densities and Hausdorff measures).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure TopologicalSpace Set Filter Metric Module
open scoped ENNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {s : Set E} {x : E}

/-! ### Density bounds at the reduced boundary -/

/-- At a point of the reduced boundary, in dimension `n ≥ 2`, for each `c > 1` the perimeter measure
of every small closed ball `closedBall x ρ` is at most `c ω_{n-1} ρ ^ (n - 1)`. -/
private theorem eventually_variationMeasure_closedBall_le_mul_volume (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary volume Ω s) {c : ℝ≥0∞} (hc : 1 < c) :
    ∀ᶠ ρ in 𝓝[>] 0, variationMeasure volume Ω (s.indicator 1) ((↑) ⁻¹' closedBall x ρ) ≤
      c * volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) ρ) := by
  filter_upwards [(tendsto_variationMeasure_closedBall_div_volume_closedBall hn hx).eventually
    (gt_mem_nhds hc), self_mem_nhdsWithin] with ρ h (hρ : 0 < ρ)
  exact ((ENNReal.div_lt_iff (.inl (measure_closedBall_pos _ _ hρ).ne')
    (.inl measure_closedBall_lt_top.ne)).1 h).le

/-- At a point of the reduced boundary, in dimension `n ≥ 2`, for each `c < 1` the perimeter measure
of every small closed ball `closedBall x ρ` is at least `c ω_{n-1} ρ ^ (n - 1)`. -/
private theorem eventually_mul_volume_le_variationMeasure_closedBall (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary volume Ω s) {c : ℝ≥0∞} (hc : c < 1) :
    ∀ᶠ ρ in 𝓝[>] 0, c * volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) ρ) ≤
      variationMeasure volume Ω (s.indicator 1) ((↑) ⁻¹' closedBall x ρ) := by
  filter_upwards [(tendsto_variationMeasure_closedBall_div_volume_closedBall hn hx).eventually
    (lt_mem_nhds hc), self_mem_nhdsWithin] with ρ h (hρ : 0 < ρ)
  exact ((ENNReal.lt_div_iff_mul_lt (.inl (measure_closedBall_pos _ _ hρ).ne')
    (.inl measure_closedBall_lt_top.ne)).1 h).le

/-! ### Rescaled sets near a point of the reduced boundary -/

/-- At a point `x` of the reduced boundary, let `r > 0` with `ball x (r * R) ⊆ Ω`. For an open set
`V ⊆ ball 0 R`, the perimeter measure of the rescaled copy `{z | r⁻¹ • (z - x) ∈ V}` of `V` is
`r ^ (n - 1)` times the perimeter in `V` of the blow-up `(fun y => x + r • y) ⁻¹' s`. -/
private theorem variationMeasure_preimage_eq_mul_perimeter (hx : x ∈ reducedBoundary volume Ω s)
    {r R : ℝ} (hr : 0 < r) (hrR : ball x (r * R) ⊆ Ω) {V : Opens E}
    (hV : (V : Set E) ⊆ ball 0 R) :
    variationMeasure volume Ω (s.indicator 1)
        ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' (V : Set E))) =
      ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
        perimeter volume V ((fun y => x + r • y) ⁻¹' s) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  have hν1 : ‖outerNormal volume Ω s x‖ = 1 := norm_outerNormal hx
  have : Nontrivial E := ⟨⟨outerNormal volume Ω s x, 0, fun h => by simp [h] at hν1⟩⟩
  -- The rescaled copy `W` of `V` lies in `ball x (r * R) ⊆ Ω`, and the blow-up map pulls it
  -- back to `V`.
  let W : Opens E := Opens.comap ⟨fun z => r⁻¹ • (z - x), by fun_prop⟩ V
  have hW : (W : Set E) = (fun z => r⁻¹ • (z - x)) ⁻¹' (V : Set E) := Opens.coe_comap _ _
  have hWΩ : W ≤ Ω := fun z hz => hrR <| by
    rw [← preimage_inv_smul_sub_ball_zero hr x R]
    exact preimage_mono hV (by rwa [← hW])
  have hVW : Opens.comap ⟨fun y => x + r • y, by fun_prop⟩ W = V := by
    ext y
    simp [hW, hr.ne']
  have h := perimeter_comap_add_smul (μ := volume) (Ω := W) (r := r) (s := s) x
  rw [hVW] at h
  rw [← hW, variationMeasure_preimage_coe hu hfin hWΩ, ← perimeter_def, h, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_of_pos hr]
  -- `r ^ (n - 1) * (r / r ^ n) = 1`.
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ E = m + 1 := ⟨_, (Nat.sub_add_cancel finrank_pos).symm⟩
  rw [hm, Nat.add_sub_cancel, pow_succ, (by field_simp : r ^ m * (r / (r ^ m * r)) = 1),
    ENNReal.ofReal_one, one_mul]

/-- **Lower bound for the perimeter measure of rescaled open sets.** At a point `x` of the reduced
boundary with outer normal `ν`, in dimension `n ≥ 2`, let `V` be a bounded open set and
`b < Hⁿ⁻¹(V ∩ ν⊥)`. Then `b r ^ (n - 1) ≤ |Dχ_s|({z | r⁻¹ • (z - x) ∈ V})` for all small `r > 0`. -/
private theorem eventually_mul_le_variationMeasure_preimage (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary volume Ω s) {V : Opens E} (hV : Bornology.IsBounded (V : Set E))
    {b : ℝ≥0∞}
    (hb : b < μHE[finrank ℝ E - 1] (V ∩ {y | ⟪y, outerNormal volume Ω s x⟫ = 0})) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * b ≤
      variationMeasure volume Ω (s.indicator 1)
        ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' (V : Set E))) := by
  obtain ⟨R, hR, hVR⟩ := hV.subset_ball_lt 0 0
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  -- The perimeter of the limiting half-space in `V` is `Hⁿ⁻¹(V ∩ ν⊥)`.
  have hlim := perimeter_setOf_inner_lt_le_liminf hn hx hV
  rw [perimeter_setOf_inner_lt (norm_outerNormal hx) 0] at hlim
  filter_upwards [eventually_lt_of_lt_liminf (hb.trans_le hlim),
    Ioo_mem_nhdsGT (div_pos hε hR)] with r hb' hr
  rw [variationMeasure_preimage_eq_mul_perimeter hx hr.1
    ((ball_subset_ball ((lt_div_iff₀ hR).1 hr.2).le).trans hεΩ) hVR]
  gcongr

omit [FiniteDimensional ℝ E] in
/-- The set `{z | r⁻¹ • (z - x) ∈ U}` traced on `Ω` is measurable for measurable `U`. -/
private theorem measurableSet_preimage_inv_smul_sub {U : Set E} (hU : MeasurableSet U) (r : ℝ) :
    MeasurableSet (((↑) : Ω → E) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' U)) :=
  (hU.preimage (by fun_prop)).preimage measurable_subtypeVal

/-- At a point `x` of the reduced boundary with outer normal `ν`, the disc `ball 0 R ∩ ν⊥` cut from
the tangent hyperplane has finite `Hⁿ⁻¹` measure. -/
private theorem euclideanHausdorffMeasure_ball_zero_inter_setOf_inner_outerNormal_ne_top
    (hx : x ∈ reducedBoundary volume Ω s) {R : ℝ} (hR : 0 < R) :
    μHE[finrank ℝ E - 1] (ball (0 : E) R ∩ {y | ⟪y, outerNormal volume Ω s x⟫ = 0}) ≠ ∞ := by
  have h := euclideanHausdorffMeasure_ball_inter_setOf_inner_eq (norm_outerNormal hx) (0 : E) hR
  rw [inner_zero_left] at h
  rw [h]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) measure_ball_lt_top.ne

/-- At a point `x` of the reduced boundary with outer normal `ν`, in dimension `n ≥ 2`, for `R > 0`
and `δ > 0`, the rescaled ball `{z | r⁻¹ • (z - x) ∈ ball 0 R}` has perimeter measure at most
`(Hⁿ⁻¹(ball 0 R ∩ ν⊥) + δ) r ^ (n - 1)` for all small `r > 0`, by the density of the perimeter
measure at `x`. -/
private theorem eventually_variationMeasure_preimage_ball_le (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary volume Ω s) {R : ℝ} (hR : 0 < R) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∀ᶠ r in 𝓝[>] 0, variationMeasure volume Ω (s.indicator 1)
        ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' ball 0 R)) ≤
      ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
        (μHE[finrank ℝ E - 1] (ball 0 R ∩ {y | ⟪y, outerNormal volume Ω s x⟫ = 0}) + δ) := by
  have ha := euclideanHausdorffMeasure_ball_inter_setOf_inner_eq (norm_outerNormal hx) (0 : E) hR
  rw [inner_zero_left, ← ENNReal.ofReal_pow hR.le] at ha
  set k := finrank ℝ E - 1
  set a := μHE[k] (ball (0 : E) R ∩ {y | ⟪y, outerNormal volume Ω s x⟫ = 0})
  have hatop : a ≠ ∞ :=
    euclideanHausdorffMeasure_ball_zero_inter_setOf_inner_outerNormal_ne_top hx hR
  -- A constant `c > 1` with `c a ≤ a + δ`.
  obtain ⟨c, hc1, hca⟩ : ∃ c, 1 < c ∧ c * a ≤ a + δ := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · exact ⟨2, ENNReal.one_lt_two, by simp [ha0]⟩
    refine ⟨1 + δ / a, ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.div_pos hδ hatop).ne', ?_⟩
    rw [add_mul, one_mul, ENNReal.div_mul_cancel ha0 hatop]
  have hRmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => mul_pos hr hR)
    have hcont : Continuous fun r : ℝ => r * R := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hRmap.eventually (eventually_variationMeasure_closedBall_le_mul_volume hn
    hx hc1), self_mem_nhdsWithin] with r hden (hr : 0 < r)
  -- The rescaled `ball 0 R` lies in `closedBall x (r * R)`, of perimeter measure at most
  -- `c ω_{n-1} (r R) ^ (n - 1) = c a r ^ (n - 1)`.
  have hball : ((↑) : Ω → E) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' ball 0 R) ⊆
      (↑) ⁻¹' closedBall x (r * R) := by
    rw [preimage_inv_smul_sub_ball_zero hr x R]
    exact preimage_mono ball_subset_closedBall
  have hvol : volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (r * R)) =
      ENNReal.ofReal (r ^ k) * a := by
    rw [Measure.addHaar_closedBall _ _ (by positivity), finrank_euclideanSpace_fin, ha, mul_pow,
      ENNReal.ofReal_mul (by positivity), mul_assoc]
  calc _ ≤ _ := measure_mono hball
    _ ≤ c * (ENNReal.ofReal (r ^ k) * a) := hvol ▸ hden
    _ ≤ ENNReal.ofReal (r ^ k) * (a + δ) := by
      rw [mul_left_comm]
      gcongr

/-- **Upper bound for the perimeter measure of rescaled closed sets.** At a point `x` of the reduced
boundary with outer normal `ν`, in dimension `n ≥ 2`, let `C ⊆ ball 0 R` be closed and `δ > 0`.
Then `|Dχ_s|({z | r⁻¹ • (z - x) ∈ C}) ≤ (Hⁿ⁻¹(C ∩ ν⊥) + δ) r ^ (n - 1)` for all small `r > 0`.

The perimeter measure of the rescaled `ball 0 R` is eventually almost at most
`Hⁿ⁻¹(ball 0 R ∩ ν⊥) r ^ (n - 1)`, and that of the rescaled open set `ball 0 R \ C` is eventually
almost at least `Hⁿ⁻¹((ball 0 R \ C) ∩ ν⊥) r ^ (n - 1)`; the difference bounds the rescaled `C`. -/
private theorem eventually_variationMeasure_preimage_le (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary volume Ω s) {C : Set E} (hC : IsClosed C) {R : ℝ} (hR : 0 < R)
    (hCR : C ⊆ ball 0 R) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝[>] 0, variationMeasure volume Ω (s.indicator 1)
        ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' C)) ≤
      ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
        (μHE[finrank ℝ E - 1] (C ∩ {y | ⟪y, outerNormal volume Ω s x⟫ = 0}) + δ) := by
  set k := finrank ℝ E - 1
  set P := {y : E | ⟪y, outerNormal volume Ω s x⟫ = 0}
  have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ.ne').ne'
  let V : Opens E := ⟨ball 0 R \ C, isOpen_ball.sdiff hC⟩
  have hV : (V : Set E) = ball 0 R \ C := Opens.coe_mk
  -- `a = Hⁿ⁻¹(ball 0 R ∩ ν⊥)` splits as `b + m` along `V` and `C`.
  have habm : μHE[k] (ball (0 : E) R ∩ P) = μHE[k] ((V : Set E) ∩ P) + μHE[k] (C ∩ P) := by
    rw [← measure_inter_add_sdiff (ball (0 : E) R ∩ P) hC.measurableSet, inter_right_comm,
      inter_eq_right.2 hCR, inter_sdiff_right_comm, add_comm, hV]
  have hatop := euclideanHausdorffMeasure_ball_zero_inter_setOf_inner_outerNormal_ne_top hx hR
  set b := μHE[k] ((V : Set E) ∩ P)
  set m := μHE[k] (C ∩ P)
  -- A lower bound `b'` for the rescaled `V`, within `δ / 2` of `b`.
  obtain ⟨b', hb'top, hbb', hlow⟩ : ∃ b', b' ≠ ∞ ∧ b ≤ b' + δ / 2 ∧
      ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal (r ^ k) * b' ≤ variationMeasure volume Ω (s.indicator 1)
        ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' (V : Set E))) := by
    rcases eq_or_ne b 0 with hb | hb
    · exact ⟨0, ENNReal.zero_ne_top, by simp [hb], Eventually.of_forall fun r => by simp⟩
    have hbtop : b ≠ ∞ := ne_top_of_le_ne_top hatop (by rw [habm]; exact le_self_add)
    obtain ⟨b', h1, h2⟩ := exists_between (ENNReal.sub_lt_self hbtop hb hδ2)
    exact ⟨b', ne_top_of_lt h2, tsub_le_iff_right.1 h1.le,
      eventually_mul_le_variationMeasure_preimage hn hx
        (isBounded_ball.subset (hV.trans_subset sdiff_subset)) h2⟩
  filter_upwards [hlow, eventually_variationMeasure_preimage_ball_le hn hx hR hδ2]
    with r hlow hball
  -- The rescaled `C` and `V` make up the rescaled `ball 0 R`.
  have hU : ((↑) : Ω → E) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' C) ∪
      (↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' (V : Set E)) =
        (↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' ball 0 R) := by
    rw [← preimage_union, ← preimage_union, hV, union_sdiff_cancel hCR]
  have hdisj : Disjoint (((↑) : Ω → E) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' C))
      ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' (V : Set E))) := by
    rw [hV]; exact (disjoint_sdiff_right.preimage _).preimage _
  rw [← hU, measure_union hdisj
    (measurableSet_preimage_inv_smul_sub V.isOpen.measurableSet r)] at hball
  refine ENNReal.le_of_add_le_add_right
    (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := r ^ k)) hb'top) ?_
  calc _ ≤ _ := add_le_add_right hlow _
    _ ≤ ENNReal.ofReal (r ^ k) * (b + m + δ / 2) := habm ▸ hball
    _ ≤ ENNReal.ofReal (r ^ k) * (m + δ + b') := by
      gcongr ENNReal.ofReal (r ^ k) * ?_
      calc b + m + δ / 2 ≤ b' + δ / 2 + m + δ / 2 := by gcongr
        _ = m + (δ / 2 + δ / 2) + b' := by ring
        _ = m + δ + b' := by rw [ENNReal.add_halves]
    _ = _ := by rw [mul_add]

/-- **Uniform upper bound near a point of the reduced boundary.** At a point `x` of the reduced
boundary, in dimension `n ≥ 2`, for every `η > 0` and every small `r > 0`, every subset `T` of the
unit ball satisfies

`|Dχ_s|({z | r⁻¹ • (z - x) ∈ T}) ≤ (ω_{n-1} ((diam T + 4 η) / 2) ^ (n - 1) + η) r ^ (n - 1)`.

Finitely many closed unions of balls of radius `η` cover all such `T`, each with diameter at most
`diam T + 4 η`, and the isodiametric inequality on the hyperplane `ν⊥` bounds their parts on it. -/
private theorem eventually_forall_variationMeasure_preimage_le (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary volume Ω s) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] 0, ∀ T ⊆ closedBall (0 : E) 1,
      variationMeasure volume Ω (s.indicator 1) ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' T)) ≤
        ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
          (((ediam T + ENNReal.ofReal (4 * η)) / 2) ^ (finrank ℝ E - 1) *
            volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) 1) + ENNReal.ofReal η) := by
  obtain ⟨J, hJ1, hJfin, hJcov⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : E) 1) hη
  -- The closed unions `C I` of the closed balls of radius `η` about the points of `I ⊆ J`.
  set C : Set E → Set E := fun I => ⋃ p ∈ I, closedBall p η
  have hCball (I : Set E) (hI : I ⊆ J) : C I ⊆ ball 0 (1 + 2 * η) :=
    iUnion₂_subset fun p hp => closedBall_subset_ball' <| by
      have h := mem_closedBall_zero_iff.1 (hJ1 (hI hp))
      rw [dist_zero_right]
      linarith
  have hev : ∀ᶠ r in 𝓝[>] 0, ∀ I ∈ 𝒫 J,
      variationMeasure volume Ω (s.indicator 1) ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' C I)) ≤
        ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
          (μHE[finrank ℝ E - 1] (C I ∩ {y | ⟪y, outerNormal volume Ω s x⟫ = 0}) +
            ENNReal.ofReal η) :=
    (eventually_all_finite hJfin.finite_subsets).2 fun I hI =>
      eventually_variationMeasure_preimage_le hn hx
        ((hJfin.subset hI).isClosed_biUnion fun p _ => isClosed_closedBall) (by positivity)
        (hCball I hI) (ENNReal.ofReal_pos.2 hη)
  filter_upwards [hev] with r hr T hT
  obtain ⟨I, hIJ, hTI, hdiam⟩ := exists_subset_biUnion_closedBall_and_ediam_le hη.le
    (hT.trans hJcov)
  calc _ ≤ variationMeasure volume Ω (s.indicator 1)
        ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' C I)) :=
        measure_mono (preimage_mono (preimage_mono hTI))
    _ ≤ _ := hr I hIJ
    _ ≤ _ := by
        gcongr
        exact (euclideanHausdorffMeasure_inter_setOf_inner_eq_le (norm_outerNormal hx) 0 _).trans
          (by gcongr)

/-- **Small sets near a point of the reduced boundary.** Let `y` be a point of the reduced boundary
of `s` in `Ω`, in dimension `n ≥ 2`. For every `η > 0` there is `ε > 0` such that every set
`t ⊆ Ω` containing `y` with `diam t < ε` satisfies

`|Dχ_s|(t) ≤ (ω_{n-1} ((1 + 4 η) / 2) ^ (n - 1) + η) (diam t) ^ (n - 1)`.

As `η → 0` the constant tends to the normalization `ω_{n-1} / 2 ^ (n - 1)` of `Hⁿ⁻¹`. -/
private theorem exists_forall_variationMeasure_le_mul_ediam_pow (hn : 2 ≤ finrank ℝ E) {y : Ω}
    (hy : (y : E) ∈ reducedBoundary volume Ω s) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ t : Set Ω, y ∈ t → ediam t < ε →
      variationMeasure volume Ω (s.indicator 1) t ≤
        (((1 + ENNReal.ofReal (4 * η)) / 2) ^ (finrank ℝ E - 1) *
          volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) 1) + ENNReal.ofReal η) *
          ediam t ^ (finrank ℝ E - 1) := by
  obtain ⟨ε, hε, hεF⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' one_pos).1
    (eventually_forall_variationMeasure_preimage_le hn hy hη)
  refine ⟨ENNReal.ofReal ε, ENNReal.ofReal_pos.2 hε, fun t hyt ht => ?_⟩
  set x : E := (y : E)
  set t' : Set E := (↑) '' t
  have ht't : ((↑) : Ω → E) ⁻¹' t' = t := Subtype.coe_injective.preimage_image t
  have hdiam : ediam t' = ediam t := isometry_subtypeVal.ediam_image t
  rcases eq_or_ne (ediam t) 0 with h0 | h0
  · -- A set of diameter zero containing `y` lies in `{y}`, which is `Hⁿ⁻¹`-null as `n ≥ 2`.
    have hty : t ⊆ ((↑) : Ω → E) ⁻¹' {x} := fun z hz =>
      congrArg Subtype.val (ediam_eq_zero_iff.1 h0 hz hyt)
    have := nullSingletonClass_hausdorff (X := E) (Nat.cast_pos.2 (by omega : 0 < finrank ℝ E - 1))
    refine (measure_mono_null hty ?_).trans_le zero_le
    rw [← Measure.map_apply measurable_subtypeVal (measurableSet_singleton x)]
    exact map_variationMeasure_absolutelyContinuous_euclideanHausdorffMeasure
      (Measure.euclideanHausdorffMeasure_eq_zero_iff.2 (measure_singleton x))
  have htop : ediam t ≠ ∞ := (ht.trans ENNReal.ofReal_lt_top).ne
  set r := (ediam t).toReal
  have hr : 0 < r := ENNReal.toReal_pos h0 htop
  have hrε : r < ε := ENNReal.toReal_lt_of_lt_ofReal ht
  have hdist {a b : E} (ha : a ∈ t') (hb : b ∈ t') : dist a b ≤ r := by
    rw [← ENNReal.ofReal_le_ofReal_iff hr.le, ← edist_dist, ENNReal.ofReal_toReal htop, ← hdiam]
    exact edist_le_ediam_of_mem ha hb
  -- The blow-up `T` of `t'` at scale `r` lies in the unit ball and has diameter at most one.
  set T := (fun w => x + r • w) ⁻¹' t'
  have hT1 : T ⊆ closedBall 0 1 := fun w hw => by
    have h := hdist hw (mem_image_of_mem _ hyt)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at h
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg w]
  have hTdiam : ediam T ≤ 1 := ediam_le fun w hw w' hw' => by
    have h := hdist hw hw'
    rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hr.le] at h
    rw [edist_dist, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [dist_nonneg (x := w) (y := w')])
  have hNT : (fun z => r⁻¹ • (z - x)) ⁻¹' T = t' := by
    ext z
    simp [T, hr.ne']
  calc variationMeasure volume Ω (s.indicator 1) t
      = variationMeasure volume Ω (s.indicator 1) ((↑) ⁻¹' ((fun z => r⁻¹ • (z - x)) ⁻¹' T)) := by
        rw [hNT, ht't]
    _ ≤ _ := hεF ⟨hr, hrε⟩ T hT1
    _ ≤ ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
          (((1 + ENNReal.ofReal (4 * η)) / 2) ^ (finrank ℝ E - 1) *
            volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) 1) +
              ENNReal.ofReal η) := by
        gcongr
    _ = _ := by rw [mul_comm, ENNReal.ofReal_pow hr.le, ENNReal.ofReal_toReal htop]

/-! ### The perimeter measure on the reduced boundary -/

/-- The perimeter measure is at most `Hⁿ⁻¹` on subsets of the reduced boundary. -/
private theorem variationMeasure_le_euclideanHausdorffMeasure_image (hn : 2 ≤ finrank ℝ E)
    {B : Set Ω} (hB : ∀ y ∈ B, (y : E) ∈ reducedBoundary volume Ω s) :
    variationMeasure volume Ω (s.indicator 1) B ≤ μHE[finrank ℝ E - 1] (((↑) : Ω → E) '' B) := by
  set k := finrank ℝ E - 1
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set c : ℝ → ℝ≥0∞ := fun η => ((1 + ENNReal.ofReal (4 * η)) / 2) ^ k * ω + ENNReal.ofReal η
  have hbound (η : ℝ) (hη : 0 < η) :
      variationMeasure volume Ω (s.indicator 1) B ≤ c η * μH[(k : ℝ)] (((↑) : Ω → E) '' B) := by
    rw [isometry_subtypeVal.hausdorffMeasure_image (.inl k.cast_nonneg)]
    refine measure_le_mul_hausdorffMeasure_of_le_mul_ediam_rpow _
      ((ENNReal.ofReal_pos.2 hη).trans_le le_add_self).ne' (by finiteness) fun y hy => ?_
    simpa only [ENNReal.rpow_natCast] using
      exists_forall_variationMeasure_le_mul_ediam_pow hn (hB y hy) hη
  -- As `η → 0`, the constants tend to the normalization `ω / 2 ^ k` of `μHE[k]`.
  have hc : Tendsto c (𝓝[>] 0) (𝓝 (ω / 2 ^ k)) := by
    have hcont : Continuous c :=
      ((ENNReal.continuous_mul_const hωtop).comp ((ENNReal.continuous_pow k).comp
        ((ENNReal.continuous_div_const 2 two_ne_zero).comp (continuous_const.add
          (ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)))))).add
        ENNReal.continuous_ofReal
    have h0 : c 0 = ω / 2 ^ k := by
      simp [c, div_eq_mul_inv, ENNReal.inv_pow, mul_comm]
    exact h0 ▸ (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [euclideanHausdorffMeasure_eq_smul_hausdorffMeasure, smul_apply, smul_eq_mul]
  exact ge_of_tendsto (ENNReal.Tendsto.mul_const hc
    (.inl (ENNReal.div_pos (measure_ball_pos _ _ one_pos).ne' (by simp)).ne'))
    (eventually_nhdsWithin_of_forall hbound)

/-- The perimeter measure is at least `Hⁿ⁻¹` on subsets of the reduced boundary. -/
private theorem euclideanHausdorffMeasure_image_le_variationMeasure (hn : 2 ≤ finrank ℝ E)
    {B : Set Ω} (hB : ∀ y ∈ B, (y : E) ∈ reducedBoundary volume Ω s) :
    μHE[finrank ℝ E - 1] (((↑) : Ω → E) '' B) ≤ variationMeasure volume Ω (s.indicator 1) B := by
  rw [isometry_subtypeVal.euclideanHausdorffMeasure_image]
  refine ENNReal.le_of_forall_lt_one_mul_le fun c hc =>
    mul_euclideanHausdorffMeasure_le_measure _ _ fun y hy => ?_
  exact (eventually_mul_volume_le_variationMeasure_closedBall hn (hB y hy) hc).frequently

/-- **The perimeter measure is Hausdorff measure on the reduced boundary.** In dimension `n ≥ 2`,
every subset `B` of `Ω` contained in the reduced boundary of `s`, measurable or not, satisfies
`|Dχ_s|(B) = Hⁿ⁻¹(B)`. -/
theorem variationMeasure_eq_euclideanHausdorffMeasure_image (hn : 2 ≤ finrank ℝ E) {B : Set Ω}
    (hB : ∀ y ∈ B, (y : E) ∈ reducedBoundary volume Ω s) :
    variationMeasure volume Ω (s.indicator 1) B = μHE[finrank ℝ E - 1] (((↑) : Ω → E) '' B) :=
  le_antisymm (variationMeasure_le_euclideanHausdorffMeasure_image hn hB)
    (euclideanHausdorffMeasure_image_le_variationMeasure hn hB)

/-- **De Giorgi's representation of the perimeter measure, `|Dχ_s| = Hⁿ⁻¹ ⌊ ∂*s`.** In dimension
`n ≥ 2`, the perimeter measure of `s` in `Ω` is the restriction of the `(n - 1)`-dimensional
Euclidean Hausdorff measure to the reduced boundary, viewed as a measure on `Ω`. When `s` does not
have locally finite perimeter in `Ω`, both sides vanish. -/
theorem variationMeasure_eq_comap_restrict_reducedBoundary (hn : 2 ≤ finrank ℝ E) :
    variationMeasure volume Ω (s.indicator 1) =
      (μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s)).comap (↑) := by
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    MeasurableEmbedding.subtypeVal Ω.isOpen.measurableSet
  -- The perimeter measure is concentrated on the reduced boundary.
  have hR : variationMeasure volume Ω (s.indicator 1)
      {y : Ω | (y : E) ∈ reducedBoundary volume Ω s}ᶜ = 0 := ae_mem_reducedBoundary
  ext A hA
  rw [hemb.comap_apply, Measure.restrict_apply (hemb.measurableSet_image' hA),
    ← measure_inter_conull hR, ← image_inter_preimage]
  exact variationMeasure_eq_euclideanHausdorffMeasure_image hn fun y hy => hy.2

/-- **The perimeter is the Hausdorff measure of the reduced boundary.** In dimension `n ≥ 2`, a set
`s` of locally finite perimeter in `Ω` has `P(s; Ω) = Hⁿ⁻¹(∂*s)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_reducedBoundary (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞) :
    perimeter volume Ω s = μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s) := by
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    MeasurableEmbedding.subtypeVal Ω.isOpen.measurableSet
  rw [perimeter_def, ← variationMeasure_univ hu hfin,
    variationMeasure_eq_comap_restrict_reducedBoundary hn, hemb.comap_apply, image_univ,
    Subtype.range_coe, Measure.restrict_apply Ω.isOpen.measurableSet,
    inter_eq_right.2 reducedBoundary_subset]

/-- **The perimeter is at most the Hausdorff measure of the frontier.** In dimension `n ≥ 2`, a set
`s` of locally finite perimeter in `Ω` has `P(s; Ω) ≤ Hⁿ⁻¹(frontier s ∩ Ω)`. -/
theorem perimeter_le_euclideanHausdorffMeasure_frontier_inter (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞) :
    perimeter volume Ω s ≤ μHE[finrank ℝ E - 1] (frontier s ∩ Ω) := by
  rw [perimeter_eq_euclideanHausdorffMeasure_reducedBoundary hn hu hfin]
  exact measure_mono (subset_inter reducedBoundary_subset_frontier reducedBoundary_subset)

/-- **The Gauss–Green formula with surface measure, `Dχ_s = -ν_s Hⁿ⁻¹ ⌊ ∂*s`.** In dimension
`n ≥ 2`, for a set `s` of locally finite perimeter in `Ω`,

`∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`

for every `C¹` vector field `φ` with compact support in `Ω`, where `div φ = tr (Dφ)`. -/
theorem integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal
    (hn : 2 ≤ finrank ℝ E) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x =
      ∫ x in reducedBoundary volume Ω s, ⟪φ x, outerNormal volume Ω s x⟫
        ∂μHE[finrank ℝ E - 1] := by
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    MeasurableEmbedding.subtypeVal Ω.isOpen.measurableSet
  rw [integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal hu hfin hφ hc hs,
    variationMeasure_eq_comap_restrict_reducedBoundary hn,
    ← hemb.integral_map (g := fun x => ⟪φ x, outerNormal volume Ω s x⟫), hemb.map_comap,
    Subtype.range_coe, Measure.restrict_restrict Ω.isOpen.measurableSet,
    inter_eq_right.2 reducedBoundary_subset]

end TauCeti
