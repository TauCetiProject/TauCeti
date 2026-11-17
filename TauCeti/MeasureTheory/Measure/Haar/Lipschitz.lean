/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Hausdorff measure and null-set transport under Lipschitz maps

A map from a finite-dimensional real normed space to one of at least the same dimension that is
Lipschitz on a set `s` sends `s` to a null set whenever `s` is null, for any additive Haar measures
on the source and the target. In dimension `d` the Hausdorff measure `μH[d]` is an additive Haar
measure, so every additive Haar measure is mutually absolutely continuous with it. Lipschitz maps
increase the Hausdorff `d`-measure by at most the factor `K ^ d`
(`LipschitzOnWith.hausdorffMeasure_image_le`), and a set of zero Hausdorff `d`-measure has zero
Hausdorff `d'`-measure for every `d' ≥ d`. The same factor `K ^ d` bounds the growth of the
normalized Euclidean Hausdorff measure `μHE[d]`, a constant multiple of `μH[d]`.
Inverse-Lipschitz maps on a parameter set give the reverse measure bound. Together these
bounds give null-set and almost-everywhere equivalences for bi-Lipschitz parametrizations,
for raw and normalized Hausdorff measure and for additive Haar measure on the source.
No measurability of the parameter set or its image is required. One-sided a.e. transport
uses only Lipschitz control in the forward direction and inverse-Lipschitz control in reverse.

## Main statements

* `LipschitzOnWith.addHaar_image_eq_zero` — a map Lipschitz on a Haar-null set has a Haar-null
  image, from a finite-dimensional real normed space to one of at least the same dimension.
* `LipschitzOnWith.euclideanHausdorffMeasure_image_le` — a `K`-Lipschitz map increases `μHE[d]`
  by at most the factor `K ^ d`.
* `AntilipschitzWith.le_hausdorffMeasure_image_of_domRestrict` and
  `AntilipschitzWith.le_euclideanHausdorffMeasure_image_of_domRestrict` — localized lower bounds.
* `LipschitzOnWith.hausdorffMeasure_image_eq_zero_iff` and
  `LipschitzOnWith.euclideanHausdorffMeasure_image_eq_zero_iff` — bi-Lipschitz null-set transport.
* `LipschitzOnWith.ae_hausdorffMeasure_image_iff` and
  `LipschitzOnWith.ae_euclideanHausdorffMeasure_image_iff` — bi-Lipschitz a.e. transport.
* `LipschitzOnWith.euclideanHausdorffMeasure_image_eq_zero_iff_addHaar` and
  `LipschitzOnWith.ae_image_iff_addHaar` — the corresponding source Haar-measure equivalences.
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

namespace AntilipschitzWith

/-- Inverse-Lipschitz control on a set restricts to any subset. -/
theorem domRestrict_mono {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {L : ℝ≥0} {f : X → Y} {s t : Set X} (hi : AntilipschitzWith L (s.domRestrict f))
    (ht : t ⊆ s) : AntilipschitzWith L (t.domRestrict f) := by
  intro x y
  simpa only [Set.domRestrict_apply, Subtype.edist_eq, Subtype.edist_mk_mk] using
    hi ⟨x, ht x.property⟩ ⟨y, ht y.property⟩

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {L : ℝ≥0} {f : X → Y} {s : Set X}

/-- Inverse-Lipschitz control on `s` bounds its raw Hausdorff measure by that of its image. -/
theorem le_hausdorffMeasure_image_of_domRestrict
    (hi : AntilipschitzWith L (s.domRestrict f)) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] s ≤ (L : ℝ≥0∞) ^ d * μH[d] (f '' s) := by
  have hle := hi.le_hausdorffMeasure_image hd Set.univ
  rw [← isometry_subtype_coe.hausdorffMeasure_image (Or.inl hd) (Set.univ : Set s),
    Set.image_univ, Subtype.range_coe, Set.image_univ, Set.range_domRestrict] at hle
  exact hle

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

/-- Inverse-Lipschitz control on a parameter set pulls a.e. assertions on its image back
for raw Hausdorff measure. No Lipschitz hypothesis on the parametrization is needed. -/
theorem ae_hausdorffMeasure_of_image (hi : AntilipschitzWith L (s.domRestrict f))
    {d : ℝ} (hd : 0 ≤ d) {p : Y → Prop}
    (h : ∀ᵐ y ∂(μH[d] : Measure Y), y ∈ f '' s → p y) :
    ∀ᵐ x ∂(μH[d] : Measure X), x ∈ s → p (f x) := by
  simp only [ae_iff, not_imp, ofPred_and, ofPred_mem_eq] at h ⊢
  rw [← Set.image_inter_preimage f s {y | ¬p y}] at h
  rw [← Set.preimage_ofPred_eq (f := f) (p := fun y => ¬p y)]
  have hle := (hi.domRestrict_mono Set.inter_subset_left).le_hausdorffMeasure_image_of_domRestrict
    (s := s ∩ f ⁻¹' {y | ¬p y}) hd
  exact nonpos_iff_eq_zero.mp (hle.trans_eq (by rw [h, mul_zero]))

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

/-- A bi-Lipschitz parametrization preserves and reflects raw Hausdorff null sets in every
nonnegative real dimension, without measurability assumptions on the parameter set. -/
theorem hausdorffMeasure_image_eq_zero_iff
    (hf : LipschitzOnWith K f s) (hi : AntilipschitzWith L (s.domRestrict f))
    {d : ℝ} (hd : 0 ≤ d) : μH[d] (f '' s) = 0 ↔ μH[d] s = 0 := by
  constructor
  · intro h
    exact nonpos_iff_eq_zero.mp ((hi.le_hausdorffMeasure_image_of_domRestrict hd).trans_eq
      (by simp [h]))
  · intro h
    exact nonpos_iff_eq_zero.mp ((hf.hausdorffMeasure_image_le hd).trans_eq (by simp [h]))

/-- Lipschitz maps send parameter-a.e. assertions to image-a.e. assertions for raw Hausdorff
measure. No inverse-Lipschitz or injectivity hypothesis is needed. -/
theorem ae_hausdorffMeasure_image (hf : LipschitzOnWith K f s) {d : ℝ} (hd : 0 ≤ d)
    {p : Y → Prop} (h : ∀ᵐ x ∂(μH[d] : Measure X), x ∈ s → p (f x)) :
    ∀ᵐ y ∂(μH[d] : Measure Y), y ∈ f '' s → p y := by
  simp only [ae_iff, not_imp, ofPred_and, ofPred_mem_eq] at h ⊢
  rw [← Set.preimage_ofPred_eq (f := f) (p := fun y => ¬p y)] at h
  rw [← Set.image_inter_preimage f s {y | ¬p y}]
  exact nonpos_iff_eq_zero.mp
    (((hf.mono Set.inter_subset_left).hausdorffMeasure_image_le hd).trans_eq
      (by rw [h, mul_zero]))

/-- Almost-everywhere assertions on a bi-Lipschitz image are equivalent to their pullbacks
for raw Hausdorff measure in any nonnegative real dimension. -/
theorem ae_hausdorffMeasure_image_iff (hf : LipschitzOnWith K f s)
    (hi : AntilipschitzWith L (s.domRestrict f)) {d : ℝ} (hd : 0 ≤ d) {p : Y → Prop} :
    (∀ᵐ y ∂(μH[d] : Measure Y), y ∈ f '' s → p y) ↔
      ∀ᵐ x ∂(μH[d] : Measure X), x ∈ s → p (f x) := by
  exact ⟨hi.ae_hausdorffMeasure_of_image hd, hf.ae_hausdorffMeasure_image hd⟩

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
