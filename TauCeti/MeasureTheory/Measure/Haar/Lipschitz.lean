/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Measure.Hausdorff
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Hausdorff measure and null-set transport under Lipschitz maps

A map from a finite-dimensional real normed space to one of at least the same dimension that is
Lipschitz on a set `s` sends `s` to a null set whenever `s` is null, for any additive Haar measures
on the source and the target. In dimension `d` the Hausdorff measure `μH[d]` is an additive Haar
measure, so every additive Haar measure is mutually absolutely continuous with it. Lipschitz maps
increase the Hausdorff `d`-measure by at most the factor `K ^ d`
(`LipschitzOnWith.hausdorffMeasure_image_le`), and a set of zero Hausdorff `d`-measure has zero
Hausdorff `d'`-measure for every `d' ≥ d`. The same factor `K ^ d` bounds the growth of the
normalized Euclidean Hausdorff measure `μHE[d]`, a constant multiple of `μH[d]`, and on a
separable extended metric space locally Lipschitz maps preserve `μHE[d]`-null subsets.
Inverse-Lipschitz maps on a parameter set give the reverse measure bound. Together these
bounds give null-set and almost-everywhere equivalences for bi-Lipschitz parametrizations,
for normalized Hausdorff measure and for additive Haar measure on the source. The raw
Hausdorff transport results are in `TauCeti.MeasureTheory.Measure.Hausdorff`.
No measurability of the parameter set or its image is required. One-sided a.e. transport
uses only Lipschitz control in the forward direction and inverse-Lipschitz control in reverse.

## Main statements

* `LipschitzOnWith.addHaar_image_eq_zero` — a map Lipschitz on a Haar-null set has a Haar-null
  image, from a finite-dimensional real normed space to one of at least the same dimension.
* `LipschitzOnWith.euclideanHausdorffMeasure_image_le` — a `K`-Lipschitz map increases `μHE[d]`
  by at most the factor `K ^ d`.
* `LipschitzOnWith.euclideanHausdorffMeasure_image_inter_cone_div_le` — for a map `K`-Lipschitz
  on a set in a `k`-dimensional inner product space, the `μHE[k]` measure of the image of the
  parameters in a thin cone `{v | |ψ v| ≤ t ‖v‖}` within the ball of radius `c r`, divided by the
  volume of the ball of radius `r`, is at most `K ^ k c ^ k` times the share of the cone in the
  unit ball.
* `AntilipschitzWith.le_euclideanHausdorffMeasure_image_of_domRestrict` — localized lower bound.
* `LipschitzOnWith.euclideanHausdorffMeasure_image_eq_zero_iff` — bi-Lipschitz null-set transport.
* `LipschitzOnWith.ae_euclideanHausdorffMeasure_image_iff` — bi-Lipschitz a.e. transport.
* `LipschitzOnWith.euclideanHausdorffMeasure_image_eq_zero_iff_addHaar`,
  `LipschitzOnWith.ae_euclideanHausdorffMeasure_exists_of_addHaar`, and
  `LipschitzOnWith.ae_image_iff_addHaar` — the corresponding source Haar-measure transport and
  equivalences.
* `LocallyLipschitzOn.euclideanHausdorffMeasure_image_eq_zero_of_subset` — a map locally Lipschitz
  on `s` sends every `μHE[d]`-null subset `t ⊆ s` to a `μHE[d]`-null set.
-/

public section

open MeasureTheory MeasureTheory.Measure Module Set
open scoped NNReal ENNReal

namespace LipschitzOnWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Lipschitz maps preserve Haar-null sets.** If `f : E → F` is Lipschitz on a set `s` that is
null for an additive Haar measure `μ` on `E`, and `E` and `F` are finite-dimensional real normed
spaces with `finrank ℝ E ≤ finrank ℝ F`, then `f '' s` is null for every additive Haar measure `ν`
on `F`. -/
theorem addHaar_image_eq_zero (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F)
    [IsAddHaarMeasure ν] (hdim : finrank ℝ E ≤ finrank ℝ F) {K : ℝ≥0} {f : E → F}
    {s : Set E} (hf : LipschitzOnWith K f s) (hs : μ s = 0) : ν (f '' s) = 0 := by
  -- With `d = finrank ℝ E`, `s` is `μH[d]`-null, hence so is its Lipschitz image; that image is
  -- then `μH[finrank ℝ F]`-null, and `ν` is absolutely continuous with respect to this measure.
  have hsE : μH[finrank ℝ E] s = 0 := absolutelyContinuous_isAddHaarMeasure _ μ hs
  have himage : μH[finrank ℝ E] (f '' s) = 0 := by
    simpa [hsE] using hf.hausdorffMeasure_image_le (finrank ℝ E).cast_nonneg
  exact absolutelyContinuous_isAddHaarMeasure ν μH[finrank ℝ F] <|
    nonpos_iff_eq_zero.1 ((hausdorffMeasure_mono (Nat.cast_le.2 hdim) _).trans_eq himage)

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A map that is `K`-Lipschitz on `s` increases the `d`-dimensional Euclidean Hausdorff measure
of `s` by at most the factor `K ^ d`. -/
theorem euclideanHausdorffMeasure_image_le {K : ℝ≥0} {f : X → Y} {s : Set X}
    (hf : LipschitzOnWith K f s) (d : ℕ) :
    μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, _root_.smul_apply, mul_smul_comm,
    ← ENNReal.rpow_natCast]
  gcongr
  exact hf.hausdorffMeasure_image_le d.cast_nonneg

end LipschitzOnWith

namespace LipschitzOnWith

open Metric Set

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Let `f` be `K`-Lipschitz on `s ⊆ E`, with `E` of dimension `k`. Take the parameters `u ∈ s`
with `u - u₀` in the part of a cone `|ψ v| ≤ t ‖v‖` in the closed ball of radius `c r`. The
`μHE[k]` measure of their image, divided by the volume of the ball of radius `r` in `E`, is at most
`K ^ k c ^ k` times the share of the cone in the unit ball. -/
theorem euclideanHausdorffMeasure_image_inter_cone_div_le {f : E → Y} {K : ℝ≥0} {s : Set E}
    (hf : LipschitzOnWith K f s) (u₀ : E) (ψ : E →L[ℝ] ℝ) (t : ℝ) {c r : ℝ} (hc : 0 < c)
    (hr : 0 < r) :
    μHE[finrank ℝ E]
        (f '' (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖}))) /
        volume (closedBall (0 : E) r) ≤
      (K : ℝ≥0∞) ^ finrank ℝ E * ENNReal.ofReal (c ^ finrank ℝ E) *
        volume (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) / volume (ball (0 : E) 1) := by
  set k := finrank ℝ E
  have hcr : 0 < c * r := by positivity
  have himage := (hf.mono (inter_subset_left (t := (fun u ↦ u - u₀) ⁻¹'
    (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖})))).euclideanHausdorffMeasure_image_le k
  have hvol : μHE[k] (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖})) ≤
      ENNReal.ofReal ((c * r) ^ k) * volume (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      ← Measure.addHaar_closedBall_inter_setOf_abs_le_mul_norm volume ψ t hcr]
    refine (measure_mono inter_subset_right).trans_eq ?_
    simp only [sub_eq_add_neg]
    exact measure_preimage_add_right _ _ _
  rw [Measure.addHaar_closedBall _ _ hr.le]
  calc μHE[k] (f '' (s ∩ (fun u ↦ u - u₀) ⁻¹' (closedBall 0 (c * r) ∩ {v | |ψ v| ≤ t * ‖v‖}))) /
        (ENNReal.ofReal (r ^ k) * volume (ball (0 : E) 1))
      ≤ (K : ℝ≥0∞) ^ k * (ENNReal.ofReal ((c * r) ^ k) *
          volume (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖})) /
          (ENNReal.ofReal (r ^ k) * volume (ball (0 : E) 1)) := by
        gcongr
        exact himage.trans (by gcongr)
    _ = ENNReal.ofReal (r ^ k) * ((K : ℝ≥0∞) ^ k * ENNReal.ofReal (c ^ k) *
          volume (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖})) /
          (ENNReal.ofReal (r ^ k) * volume (ball (0 : E) 1)) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity)]
        ac_rfl
    _ = _ := ENNReal.mul_div_mul_left _ _
          (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top

end LipschitzOnWith

namespace AntilipschitzWith

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {L : ℝ≥0} {f : X → Y} {s : Set X}

/-- Inverse-Lipschitz control on `s` bounds its normalized Hausdorff measure by its image. -/
theorem le_euclideanHausdorffMeasure_image_of_domRestrict
    (hi : AntilipschitzWith L (s.domRestrict f)) (d : ℕ) :
    μHE[d] s ≤ (L : ℝ≥0∞) ^ d * μHE[d] (f '' s) := by
  simp_rw [euclideanHausdorffMeasure_def, _root_.smul_apply, mul_smul_comm,
    ← ENNReal.rpow_natCast]
  gcongr
  exact hi.le_hausdorffMeasure_image_of_domRestrict d.cast_nonneg

/-- An inverse-Lipschitz map bounds the normalized Hausdorff measure of its source set
by the measure of its image, with the inverse Lipschitz constant to the dimension. -/
theorem le_euclideanHausdorffMeasure_image (hf : AntilipschitzWith L f) (d : ℕ) (s : Set X) :
    μHE[d] s ≤ (L : ℝ≥0∞) ^ d * μHE[d] (f '' s) :=
  (hf.domRestrict s).le_euclideanHausdorffMeasure_image_of_domRestrict d

/-- Inverse-Lipschitz control pulls image-a.e. assertions back for normalized Hausdorff
measure, with no Lipschitz hypothesis on the parametrization. -/
theorem ae_euclideanHausdorffMeasure_of_image
    (hi : AntilipschitzWith L (s.domRestrict f)) (d : ℕ) {p : Y → Prop}
    (h : ∀ᵐ y ∂(μHE[d] : Measure Y), y ∈ f '' s → p y) :
    ∀ᵐ x ∂(μHE[d] : Measure X), x ∈ s → p (f x) := by
  simp only [ae_iff, euclideanHausdorffMeasure_def, _root_.smul_apply, ENNReal.smul_def,
    smul_eq_mul, mul_eq_zero, ENNReal.coe_eq_zero,
    addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, false_or] at h ⊢
  exact hi.ae_hausdorffMeasure_of_image d.cast_nonneg h

end AntilipschitzWith

namespace LipschitzOnWith

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {K L : ℝ≥0} {f : X → Y} {s : Set X}

/-- A bi-Lipschitz parametrization preserves and reflects normalized Hausdorff null sets.
Neither the source set nor its image needs to be measurable. -/
theorem euclideanHausdorffMeasure_image_eq_zero_iff
    (hf : LipschitzOnWith K f s) (hi : AntilipschitzWith L (s.domRestrict f)) (d : ℕ) :
    μHE[d] (f '' s) = 0 ↔ μHE[d] s = 0 := by
  simpa only [euclideanHausdorffMeasure_def, _root_.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_eq_zero, mul_eq_zero,
    addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, false_or] using
    hf.hausdorffMeasure_image_eq_zero_iff hi d.cast_nonneg

/-- Lipschitz maps send parameter-a.e. assertions to image-a.e. assertions for normalized
Hausdorff measure, without an injectivity hypothesis. -/
theorem ae_euclideanHausdorffMeasure_image (hf : LipschitzOnWith K f s) (d : ℕ)
    {p : Y → Prop} (h : ∀ᵐ x ∂(μHE[d] : Measure X), x ∈ s → p (f x)) :
    ∀ᵐ y ∂(μHE[d] : Measure Y), y ∈ f '' s → p y := by
  simp only [ae_iff, euclideanHausdorffMeasure_def, _root_.smul_apply, ENNReal.smul_def,
    smul_eq_mul, mul_eq_zero, ENNReal.coe_eq_zero,
    addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, false_or] at h ⊢
  exact hf.ae_hausdorffMeasure_image d.cast_nonneg h

/-- Almost-everywhere assertions on a bi-Lipschitz image are equivalent to their pullbacks
for normalized Hausdorff measure, without measurability assumptions on the parameter set. -/
theorem ae_euclideanHausdorffMeasure_image_iff (hf : LipschitzOnWith K f s)
    (hi : AntilipschitzWith L (s.domRestrict f)) (d : ℕ) {p : Y → Prop} :
    (∀ᵐ y ∂(μHE[d] : Measure Y), y ∈ f '' s → p y) ↔
      ∀ᵐ x ∂(μHE[d] : Measure X), x ∈ s → p (f x) := by
  exact ⟨hi.ae_euclideanHausdorffMeasure_of_image d, hf.ae_euclideanHausdorffMeasure_image d⟩

/-- On a finite-dimensional real normed parameter space, the null-set correspondence for a
bi-Lipschitz parametrization also holds for any additive Haar measure on the source. -/
theorem euclideanHausdorffMeasure_image_eq_zero_iff_addHaar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → Y} {s : Set E}
    (hf : LipschitzOnWith K f s) (hi : AntilipschitzWith L (s.domRestrict f))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    μHE[finrank ℝ E] (f '' s) = 0 ↔ μ s = 0 := by
  rw [hf.euclideanHausdorffMeasure_image_eq_zero_iff hi]
  exact ⟨fun h => Measure.absolutelyContinuous_isAddHaarMeasure μ μHE[finrank ℝ E] h,
    fun h => Measure.absolutelyContinuous_isAddHaarMeasure μHE[finrank ℝ E] μ h⟩

/-- A Lipschitz parametrization sends source-Haar-a.e. assertions to normalized
Hausdorff-a.e. assertions on its image, without requiring injectivity. -/
theorem ae_euclideanHausdorffMeasure_image_of_addHaar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → Y} {s : Set E}
    (hf : LipschitzOnWith K f s) (μ : Measure E) [μ.IsAddHaarMeasure] {p : Y → Prop}
    (h : ∀ᵐ x ∂μ, x ∈ s → p (f x)) :
    ∀ᵐ y ∂(μHE[finrank ℝ E] : Measure Y), y ∈ f '' s → p y :=
  hf.ae_euclideanHausdorffMeasure_image _
    ((Measure.absolutelyContinuous_isAddHaarMeasure μHE[finrank ℝ E] μ).ae_le h)

/-- A Lipschitz parametrization transports source-Haar-a.e. parameter assertions `p : E → Prop` to
normalized Hausdorff-a.e. existence of a good preimage in `s`, without requiring injectivity. -/
theorem ae_euclideanHausdorffMeasure_exists_of_addHaar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → Y} {s : Set E}
    (hf : LipschitzOnWith K f s) (μ : Measure E) [μ.IsAddHaarMeasure] {p : E → Prop}
    (h : ∀ᵐ x ∂μ, x ∈ s → p x) :
    ∀ᵐ y ∂(μHE[finrank ℝ E] : Measure Y), y ∈ f '' s → ∃ x ∈ s, f x = y ∧ p x :=
  hf.ae_euclideanHausdorffMeasure_image_of_addHaar μ
    (h.mono fun x hx hxs => ⟨x, hxs, rfl, hx hxs⟩)

/-- Inverse-Lipschitz control pulls normalized Hausdorff-a.e. assertions on the image
back to any source Haar measure, without requiring Lipschitz regularity. -/
theorem _root_.AntilipschitzWith.ae_addHaar_of_euclideanHausdorffMeasure_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → Y} {s : Set E}
    (hi : AntilipschitzWith L (s.domRestrict f)) (μ : Measure E) [μ.IsAddHaarMeasure]
    {p : Y → Prop} (h : ∀ᵐ y ∂(μHE[finrank ℝ E] : Measure Y), y ∈ f '' s → p y) :
    ∀ᵐ x ∂μ, x ∈ s → p (f x) :=
  (Measure.absolutelyContinuous_isAddHaarMeasure μ μHE[finrank ℝ E]).ae_le
    (hi.ae_euclideanHausdorffMeasure_of_image _ h)

/-- A.e. assertions on a bi-Lipschitz image for normalized Hausdorff measure are equivalent
to their pullbacks for any additive Haar measure on a finite-dimensional parameter space. -/
theorem ae_image_iff_addHaar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → Y} {s : Set E}
    (hf : LipschitzOnWith K f s) (hi : AntilipschitzWith L (s.domRestrict f))
    (μ : Measure E) [μ.IsAddHaarMeasure] {p : Y → Prop} :
    (∀ᵐ y ∂(μHE[finrank ℝ E] : Measure Y), y ∈ f '' s → p y) ↔
      ∀ᵐ x ∂μ, x ∈ s → p (f x) := by
  exact ⟨hi.ae_addHaar_of_euclideanHausdorffMeasure_image μ,
    hf.ae_euclideanHausdorffMeasure_image_of_addHaar μ⟩

end LipschitzOnWith

/-- A map locally Lipschitz on `s` maps every `μHE[d]`-null subset `t ⊆ s` to a `μHE[d]`-null
set. -/
theorem LocallyLipschitzOn.euclideanHausdorffMeasure_image_eq_zero_of_subset {X Y : Type*}
    [EMetricSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {s t : Set X} {f : X → Y}
    (hf : LocallyLipschitzOn s f) (hts : t ⊆ s) (d : ℕ) (ht0 : μHE[d] t = 0) :
    μHE[d] (f '' t) = 0 := by
  obtain ⟨U, _, _, hcov, hLip⟩ := hf.exists_open_cover_lipschitzOnWith (.of_separableSpace s)
  have ht : t = ⋃ n, t ∩ U n := by
    rw [← Set.inter_iUnion, Set.inter_eq_self_of_subset_left (hts.trans hcov)]
  rw [ht, Set.image_iUnion]
  refine measure_iUnion_null fun n => nonpos_iff_eq_zero.mp <|
    (((hLip n).mono (Set.inter_subset_inter_left _ hts)).euclideanHausdorffMeasure_image_le d)
      |>.trans_eq (by rw [measure_mono_null Set.inter_subset_left ht0, mul_zero])
