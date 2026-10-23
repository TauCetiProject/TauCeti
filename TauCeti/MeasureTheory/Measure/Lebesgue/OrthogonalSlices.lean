/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Orthogonal line coordinates and Lebesgue sections

For a unit vector `e` in a finite-dimensional real inner product space, the coordinates
`(y, t) ↦ y + t • e`, with `y ∈ (ℝ ∙ e)ᗮ`, preserve product volume. Consequently the volume
of a Lebesgue-measurable set is the integral of the lengths of its parallel line sections.
Replacing a set by a volume-a.e. equal representative changes almost every section only
on a one-dimensional null set. This permits line-section arguments for measurable sets
without choosing a Borel representative permanently.
The length of a line section is independent of its base point along the line, in any real module.

Dually, the volume is the integral over heights `t` of the volumes of the hyperplane sections
`{y ∈ (ℝ ∙ e)ᗮ | y + t • e ∈ s}`, and restricting the heights to a Borel set gives the volume
of the corresponding part of the set. Hyperplane sections of bounded sets have finite volume,
and hyperplane sections through interior points have positive volume. The heights of interior
points form an open set, and a set has positive volume at any open set of heights containing the
height of an interior point.

More generally, for any subspace `K`, Tonelli's theorem splits Lebesgue integrals over `E` along
the orthogonal decomposition `E = Kᗮ ⊕ K` (`Submodule.lintegral_eq_lintegral_lintegral_add`),
via Mathlib's `Submodule.measurePreserving_measurableEquivProd`.

The coordinate construction uses Mathlib's `Submodule.orthogonalDecomposition` and
`LinearIsometryEquiv.toSpanUnitSingleton`; its normalization follows Mathlib's volume
preservation for linear isometries and for the `L²` product.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

/-- Moving the base point along the direction does not change the length of a line section. -/
theorem volume_lineSection_add_smul {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (e : E) (s : Set E) (x : E) (c : ℝ) :
    volume {t : ℝ | x + c • e + t • e ∈ s} = volume {t : ℝ | x + t • e ∈ s} := by
  have h : {t : ℝ | x + c • e + t • e ∈ s} = (fun t ↦ t + c) ⁻¹' {t : ℝ | x + t • e ∈ s} := by
    ext t
    simp [add_smul, add_assoc, add_comm (t • e)]
  rw [h, measure_preimage_add_right]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal line coordinates preserve the product of transverse and longitudinal volumes. -/
theorem measurePreserving_orthogonalLineEquiv (e : E) (he : ‖e‖ = 1) :
    MeasurePreserving (orthogonalLineEquiv e he) (volume.prod volume) volume := by
  rw [orthogonalLineEquiv_def]
  exact (orthogonalLineIsometry e he).measurePreserving.comp
    (WithLp.volume_preserving_toLp (ℝ ∙ e)ᗮ ℝ)

/-- Volume-a.e. equal sets have a.e. equal parallel sections for almost every transverse point.
The exceptional transverse null set is allowed to depend on the direction. -/
theorem ae_lineSection_eq (e : E) (he : ‖e‖ = 1) {s u : Set E} (h : s =ᵐ[volume] u) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume]
        {t : ℝ | (y : E) + t • e ∈ u} := by
  have hp := (measurePreserving_orthogonalLineEquiv e he).quasiMeasurePreserving.preimage_ae_eq h
  have hsections := Measure.ae_ae_of_ae_prod hp
  filter_upwards [hsections] with y hy
  filter_upwards [hy] with t ht
  simpa only [mem_preimage, orthogonalLineEquiv_apply, mem_ofPred_eq] using ht

/-- Having interval sections up to null sets is independent of the ambient a.e. representative,
for each fixed unit direction. The intervals may be empty or unbounded. -/
theorem ae_lineSection_ordConnected_iff (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (h : s =ᵐ[volume] u) :
    (∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) ↔
    (∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
      {t : ℝ | (y : E) + t • e ∈ u} =ᵐ[volume] I) := by
  have transport {v w : Set E} (hvw : v =ᵐ[volume] w)
      (hv : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
        {t : ℝ | (y : E) + t • e ∈ v} =ᵐ[volume] I) :
      ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
        {t : ℝ | (y : E) + t • e ∈ w} =ᵐ[volume] I := by
    filter_upwards [ae_lineSection_eq e he hvw, hv] with y hy hI
    obtain ⟨I, hIc, hIe⟩ := hI
    exact ⟨I, hIc, hy.symm.trans hIe⟩
  exact ⟨transport h, transport h.symm⟩

/-- A Lebesgue-measurable set has Lebesgue-measurable sections on almost every parallel line. -/
theorem ae_nullMeasurableSet_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, NullMeasurableSet {t : ℝ | (y : E) + t • e ∈ s} volume := by
  filter_upwards [ae_lineSection_eq e he hs.toMeasurable_ae_eq] with y hy
  have hm : MeasurableSet {t : ℝ | (y : E) + t • e ∈ toMeasurable volume s} :=
    (measurableSet_toMeasurable volume s).preimage
      (continuous_const.add (continuous_id.smul continuous_const)).measurable
  exact hm.nullMeasurableSet.congr hy

/-- The lengths of the parallel sections of a Lebesgue-measurable set form an a.e. measurable
extended nonnegative function on the orthogonal subspace. -/
theorem aemeasurable_volume_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    AEMeasurable (fun y : (ℝ ∙ e)ᗮ => volume {t : ℝ | (y : E) + t • e ∈ s}) volume := by
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure ℝ))
    ((measurableSet_toMeasurable volume s).preimage
      (measurePreserving_orthogonalLineEquiv e he).measurable)
  refine hm.aemeasurable.congr ?_
  filter_upwards [ae_lineSection_eq e he hs.toMeasurable_ae_eq] with y hy
  refine (congrArg volume ?_).trans (measure_congr hy)
  ext t
  simp only [mem_preimage, mem_ofPred_eq, orthogonalLineEquiv_apply]

/-- Cavalieri's formula for Lebesgue-measurable sets in orthogonal line coordinates, with
extended nonnegative values and no finite-volume assumption. -/
theorem volume_eq_lintegral_volume_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = ∫⁻ y : (ℝ ∙ e)ᗮ, volume {t : ℝ | (y : E) + t • e ∈ s} := by
  have hp := hs.preimage (measurePreserving_orthogonalLineEquiv e he).quasiMeasurePreserving
  rw [← (measurePreserving_orthogonalLineEquiv e he).measure_preimage hs,
    Measure.prod_apply₀ hp]
  congr 1 with y
  congr 1
  ext t
  simp only [mem_preimage, mem_ofPred_eq, orthogonalLineEquiv_apply]

/-- Finite ambient volume implies finite length of almost every parallel section. -/
theorem ae_volume_lineSection_lt_top (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (hfinite : volume s ≠ ∞) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume {t : ℝ | (y : E) + t • e ∈ s} < ∞ := by
  apply ae_lt_top' (aemeasurable_volume_lineSection e he hs)
  rwa [← volume_eq_lintegral_volume_lineSection e he hs]

/-- A Lebesgue-measurable set is null exactly when almost every parallel line section is null. -/
theorem volume_eq_zero_iff_ae_volume_lineSection_eq_zero (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = 0 ↔
      ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume {t : ℝ | (y : E) + t • e ∈ s} = 0 := by
  rw [volume_eq_lintegral_volume_lineSection e he hs,
    lintegral_eq_zero_iff' (aemeasurable_volume_lineSection e he hs)]
  rfl

/-- The hyperplane sections of a Borel set along a unit vector have measurable volume as a
function of the height. -/
theorem measurable_volume_hyperplaneSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : MeasurableSet s) :
    Measurable fun t : ℝ ↦ volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} := by
  convert measurable_measure_prodMk_right (μ := (volume : Measure (ℝ ∙ e)ᗮ))
    (hs.preimage (measurePreserving_orthogonalLineEquiv e he).measurable) using 3 with t
  ext y
  simp

/-- Cavalieri's formula along a unit vector: the volume of a Lebesgue-measurable set is the
integral over heights of the volumes of its orthogonal hyperplane sections. -/
theorem volume_eq_lintegral_volume_hyperplaneSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = ∫⁻ t : ℝ, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} := by
  have hBorel {u : Set E} (hu : MeasurableSet u) :
      volume u = ∫⁻ t : ℝ, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ u} := by
    rw [← (measurePreserving_orthogonalLineEquiv e he).measure_preimage hu.nullMeasurableSet,
      Measure.prod_apply_symm (hu.preimage (measurePreserving_orthogonalLineEquiv e he).measurable)]
    congr 1 with t
    congr 1 with y
    simp
  -- The sections of `s` lie between those of a measurable subset and a measurable superset,
  -- both of the same volume as `s`.
  obtain ⟨u, hus, hu, hue⟩ := hs.exists_measurable_subset_ae_eq
  refine le_antisymm ?_ ?_
  · rw [← measure_congr hue, hBorel hu]
    exact lintegral_mono fun t ↦ measure_mono fun y hy ↦ hus hy
  · rw [← measure_toMeasurable s, hBorel (measurableSet_toMeasurable volume s)]
    exact lintegral_mono fun t ↦ measure_mono fun y hy ↦ subset_toMeasurable volume s hy

/-- The hyperplane sections of a bounded set have finite volume. -/
theorem _root_.Bornology.IsBounded.volume_hyperplaneSection_lt_top {s : Set E}
    (hs : Bornology.IsBounded s) (e : E) (t : ℝ) :
    volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} < ∞ :=
  ((Isometry.of_dist_eq fun y z : (ℝ ∙ e)ᗮ ↦ by
    simp [dist_add_right, Subtype.dist_eq]).antilipschitzWith.isBounded_preimage hs).measure_lt_top

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The heights along a unit vector of the interior points of a set form an open set. -/
theorem isOpen_image_inner_interior {e : E} (he : ‖e‖ = 1) (s : Set E) :
    IsOpen ((fun x ↦ ⟪e, x⟫) '' interior s) := by
  refine (innerₛₗ ℝ e).isOpenMap_of_finiteDimensional (fun t ↦ ⟨t • e, ?_⟩) _ isOpen_interior
  simp [he]

/-- The hyperplane section along a unit vector through an interior point of a set has positive
volume. -/
theorem volume_hyperplaneSection_pos (e : E) (he : ‖e‖ = 1) {s : Set E} {c : ℝ}
    (hc : c ∈ (fun x ↦ ⟪e, x⟫) '' interior s) :
    0 < volume {y : (ℝ ∙ e)ᗮ | (y : E) + c • e ∈ s} := by
  obtain ⟨x, hx, rfl⟩ := hc
  dsimp only
  -- The transverse coordinate of `x` lies in the open preimage of the interior of `s`.
  have hU : IsOpen {y : (ℝ ∙ e)ᗮ | (y : E) + ⟪e, x⟫ • e ∈ interior s} :=
    isOpen_interior.preimage (continuous_subtype_val.add continuous_const)
  refine (hU.measure_pos volume ⟨((orthogonalLineEquiv e he).symm x).1, ?_⟩).trans_le
    (measure_mono fun y (hy : (y : E) + ⟪e, x⟫ • e ∈ interior s) ↦
      (interior_subset hy : (y : E) + ⟪e, x⟫ • e ∈ s))
  simpa [orthogonalLineEquiv_symm_fst] using hx

/-- If an interior point of `s` lies at a height along `e` in the open set `I`, then `s` has
positive volume at heights in `I`. -/
theorem volume_sep_inner_mem_pos {e : E} {s : Set E} {I : Set ℝ} (hI : IsOpen I)
    (h : ∃ x ∈ interior s, ⟪e, x⟫ ∈ I) : 0 < volume {x ∈ s | ⟪e, x⟫ ∈ I} := by
  obtain ⟨x, hx, hxI⟩ := h
  have hU : IsOpen (interior s ∩ (fun x ↦ ⟪e, x⟫) ⁻¹' I) :=
    isOpen_interior.inter (hI.preimage (continuous_const.inner continuous_id))
  exact (hU.measure_pos volume ⟨x, hx, hxI⟩).trans_le
    (measure_mono fun y hy ↦ ⟨interior_subset hy.1, hy.2⟩)

/-- Cavalieri's formula for the part of a Lebesgue-measurable set at heights in a Borel set `I`
along a unit vector `e`. -/
theorem volume_sep_inner_mem_eq_setLIntegral (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) {I : Set ℝ} (hI : MeasurableSet I) :
    volume {x ∈ s | ⟪e, x⟫ ∈ I} =
      ∫⁻ t in I, volume {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ s} := by
  have hm : Measurable fun x : E ↦ ⟪e, x⟫ := (continuous_const.inner continuous_id).measurable
  rw [volume_eq_lintegral_volume_hyperplaneSection e he (s := {x ∈ s | ⟪e, x⟫ ∈ I})
    (hs.inter (hI.preimage hm).nullMeasurableSet), ← lintegral_indicator hI]
  congr 1 with t
  by_cases ht : t ∈ I <;> simp [ht, inner_add_smul e he]

end TauCeti

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Tonelli's theorem along an orthogonal decomposition `E = Kᗮ ⊕ K`. -/
theorem lintegral_eq_lintegral_lintegral_add (K : Submodule ℝ E)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g) :
    ∫⁻ x, g x = ∫⁻ w : Kᗮ, ∫⁻ a : K, g (w + a) := by
  set e := K.measurableEquivProd (0 : E)
  have he : MeasurePreserving e := by
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
      K.measurePreserving_measurableEquivProd (0 : E)
  rw [MeasurePreserving.lintegral_map_equiv g e.symm he.symm, Measure.volume_eq_prod,
    lintegral_prod_symm (fun q ↦ g (e.symm q))
      (hg.comp_quasiMeasurePreserving he.symm.quasiMeasurePreserving)]
  simp [e, add_comm]

end Submodule
