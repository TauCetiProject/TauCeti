/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Real
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Steiner symmetrization of Lebesgue-measurable sets

Steiner symmetrization in a unit direction replaces each parallel line section by the open
centered interval of the same length. We use extended-radius balls in `ℝ`: a null section
becomes empty and an infinite-length section becomes the whole line. Thus the construction
is defined without boundedness or finiteness assumptions.

The symmetral of a Lebesgue-measurable set is Lebesgue-measurable and has the same volume.
It is independent, up to null sets, of the input representative. Symmetrization is monotone,
idempotent, and contracts the volume of symmetric differences, equivalently the `L¹`
distance between indicators. The contraction permits approximation of arbitrary measurable
sets before iterating symmetrizations.

Membership has a coordinate-free form: `x` lies in the symmetral exactly when `|⟪e, x⟫|` is
less than half the length of the line section through `x`. From it we obtain the covariance
laws. Translating the input translates the symmetral by the component of the translation
orthogonal to `e`, so translations along `e` have no effect. Nonzero dilations commute with
symmetrization, and a linear isometric equivalence carries the symmetral in direction `e` to
the symmetral of the image in the image direction. Finally, symmetrization preserves
convexity: by the one-dimensional Brunn–Minkowski inequality, section lengths of a convex
set are concave along segments joining points with nonempty sections.

The normalization uses `Real.volume_eball` and the measure-preserving orthogonal coordinates
from `TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices`.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace symmDiff

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Steiner symmetrization along the unit direction `e`, centered on its orthogonal hyperplane.
The section of length `ℓ` is the open centered interval of radius `ℓ / 2`; this includes
empty intervals for `ℓ = 0` and the whole line for `ℓ = ∞`. -/
def steinerSymmetrization (e : E) (he : ‖e‖ = 1) (s : Set E) : Set E :=
  {x | ((orthogonalLineEquiv e he).symm x).2 ∈ Metric.eball (0 : ℝ)
    (volume {t : ℝ | (((orthogonalLineEquiv e he).symm x).1 : E) + t • e ∈ s} / 2)}

/-- The coordinate description of a Steiner symmetral. -/
theorem steinerSymmetrization_def (e : E) (he : ‖e‖ = 1) (s : Set E) :
    steinerSymmetrization e he s =
      {x | ((orthogonalLineEquiv e he).symm x).2 ∈ Metric.eball (0 : ℝ)
        (volume {t : ℝ | (((orthogonalLineEquiv e he).symm x).1 : E) + t • e ∈ s} / 2)} := (rfl)

/-- Membership in a Steiner symmetral in orthogonal line coordinates. -/
@[simp]
theorem mem_steinerSymmetrization (e : E) (he : ‖e‖ = 1) (s : Set E)
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    (y : E) + t • e ∈ steinerSymmetrization e he s ↔
      t ∈ Metric.eball (0 : ℝ) (volume {u : ℝ | (y : E) + u • e ∈ s} / 2) := by
  rw [← orthogonalLineEquiv_apply e he y t]
  simp only [steinerSymmetrization, mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply]

/-- Every parallel section of the symmetral is the centered interval of the prescribed length. -/
theorem lineSection_steinerSymmetrization (e : E) (he : ‖e‖ = 1) (s : Set E)
    (y : (ℝ ∙ e)ᗮ) :
    {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} =
      Metric.eball (0 : ℝ) (volume {t : ℝ | (y : E) + t • e ∈ s} / 2) := by
  ext t
  exact mem_steinerSymmetrization e he s y t

/-- Symmetrization preserves the length of every parallel section, even infinite ones. -/
theorem volume_lineSection_steinerSymmetrization (e : E) (he : ‖e‖ = 1) (s : Set E)
    (y : (ℝ ∙ e)ᗮ) :
    volume {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} =
      volume {t : ℝ | (y : E) + t • e ∈ s} := by
  rw [lineSection_steinerSymmetrization, Real.volume_eball]
  exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- All parallel sections of a Steiner symmetral are intervals. -/
theorem ordConnected_lineSection_steinerSymmetrization (e : E) (he : ‖e‖ = 1)
    (s : Set E) (y : (ℝ ∙ e)ᗮ) :
    OrdConnected {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} := by
  rw [lineSection_steinerSymmetrization]
  exact (convex_eball _ _).ordConnected

/-- Applying the same Steiner symmetrization twice has no further effect. -/
@[simp]
theorem steinerSymmetrization_idem (e : E) (he : ‖e‖ = 1) (s : Set E) :
    steinerSymmetrization e he (steinerSymmetrization e he s) =
      steinerSymmetrization e he s := by
  ext x
  obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
  rw [orthogonalLineEquiv_apply, mem_steinerSymmetrization,
    volume_lineSection_steinerSymmetrization, mem_steinerSymmetrization]

/-- Steiner symmetrization preserves inclusion. -/
theorem steinerSymmetrization_mono (e : E) (he : ‖e‖ = 1) :
    Monotone (steinerSymmetrization e he) := by
  intro s u h x hx
  obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
  rw [orthogonalLineEquiv_apply, mem_steinerSymmetrization] at hx ⊢
  have hlength : volume {v : ℝ | (y : E) + v • e ∈ s} ≤
      volume {v : ℝ | (y : E) + v • e ∈ u} := measure_mono fun v hv ↦ h hv
  exact Metric.eball_subset_eball (ENNReal.div_le_div_right hlength 2) hx

@[simp]
theorem steinerSymmetrization_empty (e : E) (he : ‖e‖ = 1) :
    steinerSymmetrization e he ∅ = ∅ := by
  ext x
  simp [steinerSymmetrization]

@[simp]
theorem steinerSymmetrization_univ (e : E) (he : ‖e‖ = 1) :
    steinerSymmetrization e he univ = univ := by
  ext x
  simp [steinerSymmetrization, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]

/-- Coordinate-free membership in a Steiner symmetral: the longitudinal coordinate `⟪e, x⟫`
lies in the centered interval whose length is that of the line section through `x`. -/
theorem mem_steinerSymmetrization_iff (e : E) (he : ‖e‖ = 1) (s : Set E) (x : E) :
    x ∈ steinerSymmetrization e he s ↔
      ⟪e, x⟫ ∈ Metric.eball (0 : ℝ) (volume {t : ℝ | x + t • e ∈ s} / 2) := by
  rw [steinerSymmetrization_def, mem_ofPred_eq, orthogonalLineEquiv_symm_snd,
    orthogonalLineEquiv_symm_fst, sub_eq_add_neg, ← neg_smul, volume_lineSection_add_smul]

/-- Translating the input translates the symmetral by the component of the translation
orthogonal to the direction. -/
theorem steinerSymmetrization_vadd (e : E) (he : ‖e‖ = 1) (v : E) (s : Set E) :
    steinerSymmetrization e he (v +ᵥ s) =
      (v - ⟪e, v⟫ • e) +ᵥ steinerSymmetrization e he s := by
  ext x
  have hinner : ⟪e, -(v - ⟪e, v⟫ • e) + x⟫ = ⟪e, x⟫ := by
    simp [inner_add_right, inner_sub_right, inner_smul_right, he]
  rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, mem_steinerSymmetrization_iff,
    mem_steinerSymmetrization_iff, hinner]
  simp_rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  have h : ∀ t : ℝ, -v + (x + t • e) = -(v - ⟪e, v⟫ • e) + x + -⟪e, v⟫ • e + t • e := by
    intro t; module
  simp_rw [h, volume_lineSection_add_smul]

/-- Translation along the direction of symmetrization does not change the symmetral. -/
@[simp]
theorem steinerSymmetrization_smul_vadd (e : E) (he : ‖e‖ = 1) (c : ℝ) (s : Set E) :
    steinerSymmetrization e he ((c • e) +ᵥ s) = steinerSymmetrization e he s := by
  rw [steinerSymmetrization_vadd]
  simp [inner_smul_right, he]

/-- Translation orthogonal to the direction of symmetrization commutes with symmetrization. -/
theorem steinerSymmetrization_vadd_of_inner_eq_zero (e : E) (he : ‖e‖ = 1) {v : E}
    (hv : ⟪e, v⟫ = 0) (s : Set E) :
    steinerSymmetrization e he (v +ᵥ s) = v +ᵥ steinerSymmetrization e he s := by
  rw [steinerSymmetrization_vadd, hv, zero_smul, sub_zero]

/-- Steiner symmetrization commutes with nonzero dilations. -/
theorem steinerSymmetrization_smul (e : E) (he : ‖e‖ = 1) {c : ℝ} (hc : c ≠ 0) (s : Set E) :
    steinerSymmetrization e he (c • s) = c • steinerSymmetrization e he s := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hc, mem_steinerSymmetrization_iff,
    mem_steinerSymmetrization_iff]
  have h : {t : ℝ | x + t • e ∈ c • s} = (fun t ↦ c⁻¹ * t) ⁻¹' {t : ℝ | c⁻¹ • x + t • e ∈ s} := by
    ext t
    simp only [mem_ofPred_eq, mem_preimage, mem_smul_set_iff_inv_smul_mem₀ hc, smul_add, smul_smul]
  rw [h, Real.volume_preimage_mul_left (inv_ne_zero hc), inv_inv, inner_smul_right]
  simp only [Metric.mem_eball, edist_zero_right, Real.enorm_eq_ofReal_abs, abs_mul, abs_inv]
  rw [inv_mul_eq_div, ENNReal.ofReal_div_of_pos (abs_pos.2 hc),
    ENNReal.div_lt_iff (.inl (by simpa using hc)) (.inl ENNReal.ofReal_ne_top),
    mul_comm (_ / 2), ← mul_div_assoc]

/-- Steiner symmetrization is equivariant under linear isometric equivalences, which move the
direction of symmetrization along with the set. -/
theorem steinerSymmetrization_image_linearIsometryEquiv (e : E) (he : ‖e‖ = 1)
    (L : E ≃ₗᵢ[ℝ] F) (s : Set E) :
    steinerSymmetrization (L e) ((L.norm_map e).trans he) (L '' s) =
      L '' steinerSymmetrization e he s := by
  ext x
  rw [L.image_eq_preimage_symm, L.image_eq_preimage_symm, mem_preimage,
    mem_steinerSymmetrization_iff, mem_steinerSymmetrization_iff, L.inner_map_eq_flip]
  simp only [mem_preimage, map_add, map_smul, LinearIsometryEquiv.symm_apply_apply]

/-- Steiner symmetrization preserves convexity. -/
theorem convex_steinerSymmetrization (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : Convex ℝ s) : Convex ℝ (steinerSymmetrization e he s) := by
  refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab ↦ ?_
  rw [mem_steinerSymmetrization_iff, Metric.mem_eball, edist_zero_right,
    Real.enorm_eq_ofReal_abs] at hx hy ⊢
  -- The weighted sum of the two sections lies in the section through the weighted point.
  have hsub : a • {t : ℝ | x + t • e ∈ s} + b • {t : ℝ | y + t • e ∈ s} ⊆
      {t : ℝ | a • x + b • y + t • e ∈ s} := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩
    have h := hs ht hu ha.le hb.le hab
    simp only [mem_ofPred_eq] at h ⊢
    convert h using 1
    module
  have hne (z : E) (hz : ENNReal.ofReal |⟪e, z⟫| < volume {t : ℝ | z + t • e ∈ s} / 2) :
      {t : ℝ | z + t • e ∈ s}.Nonempty := by
    refine nonempty_iff_ne_empty.2 fun h ↦ ?_
    simp [h] at hz
  have hconv (z : E) : Convex ℝ {t : ℝ | z + t • e ∈ s} := by
    convert hs.affine_preimage (AffineMap.lineMap z (z + e)) using 1
    ext t
    simp [AffineMap.lineMap_apply_module', add_comm]
  have hlength := (Real.mul_volume_add_mul_volume_le (hne x hx)
    ((hconv x).nullMeasurableSet volume) (hne y hy) ((hconv y).nullMeasurableSet volume)
    ha.le hb.le).trans (measure_mono hsub)
  calc ENNReal.ofReal |⟪e, a • x + b • y⟫|
      ≤ ENNReal.ofReal a * ENNReal.ofReal |⟪e, x⟫| +
          ENNReal.ofReal b * ENNReal.ofReal |⟪e, y⟫| := by
        rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul hb.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inner_add_right, inner_smul_right, inner_smul_right]
        exact (abs_add_le _ _).trans (by simp [abs_mul, abs_of_pos ha, abs_of_pos hb])
    _ < ENNReal.ofReal a * (volume {t : ℝ | x + t • e ∈ s} / 2) +
        ENNReal.ofReal b * (volume {t : ℝ | y + t • e ∈ s} / 2) :=
        ENNReal.add_lt_add
          (ENNReal.mul_lt_mul_right (by simpa using ha) ENNReal.ofReal_ne_top hx)
          (ENNReal.mul_lt_mul_right (by simpa using hb) ENNReal.ofReal_ne_top hy)
    _ ≤ volume {t : ℝ | a • x + b • y + t • e ∈ s} / 2 := by
        rw [← mul_div_assoc, ← mul_div_assoc, ← ENNReal.add_div]
        exact ENNReal.div_le_div_right hlength 2

variable [MeasurableSpace E] [BorelSpace E]

/-- Borel sets have Borel Steiner symmetrals, without a finite-dimensionality assumption. -/
theorem measurableSet_steinerSymmetrization (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : MeasurableSet s) : MeasurableSet (steinerSymmetrization e he s) := by
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure ℝ))
    (hs.preimage (orthogonalLineEquiv e he).continuous.measurable)
  have hlength : Measurable (fun y : (ℝ ∙ e)ᗮ ↦ volume {t : ℝ | (y : E) + t • e ∈ s}) := by
    have hsection (y : (ℝ ∙ e)ᗮ) :
        Prod.mk y ⁻¹' (orthogonalLineEquiv e he) ⁻¹' s =
          {t : ℝ | (y : E) + t • e ∈ s} := by
      ext t
      simp only [mem_preimage, orthogonalLineEquiv_apply, mem_ofPred_eq]
    simpa only [hsection] using hm
  exact measurableSet_lt
    (((orthogonalLineEquiv e he).symm.continuous.measurable.snd).edist measurable_const)
    ((hlength.comp ((orthogonalLineEquiv e he).symm.continuous.measurable.fst)).div_const 2)

variable [FiniteDimensional ℝ E]

/-- Replacing the input by an a.e. equal set changes the symmetral only on a null set. -/
theorem steinerSymmetrization_ae_eq (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (h : s =ᵐ[volume] u) :
    steinerSymmetrization e he s =ᵐ[volume] steinerSymmetrization e he u := by
  have hcoord : MeasurePreserving (orthogonalLineEquiv e he).symm volume (volume.prod volume) :=
    MeasurePreserving.symm (orthogonalLineEquiv e he).toHomeomorph.toMeasurableEquiv
      (measurePreserving_orthogonalLineEquiv e he)
  have hbase := Measure.quasiMeasurePreserving_fst.comp hcoord.quasiMeasurePreserving
  have hsections := ae_lineSection_eq e he h
  have hlength : (fun y : (ℝ ∙ e)ᗮ ↦ volume {t : ℝ | (y : E) + t • e ∈ s}) =ᵐ[volume]
      (fun y : (ℝ ∙ e)ᗮ ↦ volume {t : ℝ | (y : E) + t • e ∈ u}) :=
    hsections.mono fun y hy ↦ measure_congr hy
  filter_upwards [hbase.ae_eq_comp hlength] with x hx
  simp only [Function.comp_apply] at hx
  simp only [steinerSymmetrization, mem_ofPred_eq, hx]

/-- Steiner symmetrization preserves Lebesgue measurability. -/
theorem nullMeasurableSet_steinerSymmetrization (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    NullMeasurableSet (steinerSymmetrization e he s) volume :=
  ((measurableSet_steinerSymmetrization e he
    (measurableSet_toMeasurable volume s)).nullMeasurableSet).congr
      (steinerSymmetrization_ae_eq e he hs.toMeasurable_ae_eq)

/-- Steiner symmetrization preserves volume, with no boundedness or finiteness assumptions. -/
@[simp]
theorem volume_steinerSymmetrization (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) : volume (steinerSymmetrization e he s) = volume s := by
  rw [volume_eq_lintegral_volume_lineSection e he
    (nullMeasurableSet_steinerSymmetrization e he hs),
    volume_eq_lintegral_volume_lineSection e he hs]
  simp only [volume_lineSection_steinerSymmetrization]

/-- Steiner symmetrization contracts the volume of one-sided differences. -/
theorem volume_steinerSymmetrization_sdiff_le (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (hs : NullMeasurableSet s volume) (hu : NullMeasurableSet u volume) :
    volume (steinerSymmetrization e he s \ steinerSymmetrization e he u) ≤ volume (s \ u) := by
  rw [volume_eq_lintegral_volume_lineSection e he
    ((nullMeasurableSet_steinerSymmetrization e he hs).diff
      (nullMeasurableSet_steinerSymmetrization e he hu)),
    volume_eq_lintegral_volume_lineSection e he (hs.diff hu)]
  apply lintegral_mono
  intro y
  dsimp only
  have hsection (v w : Set E) :
      {t : ℝ | (y : E) + t • e ∈ v \ w} =
        {t : ℝ | (y : E) + t • e ∈ v} \ {t : ℝ | (y : E) + t • e ∈ w} :=
    preimage_sdiff (fun t : ℝ ↦ (y : E) + t • e) v w
  rw [hsection, hsection, lineSection_steinerSymmetrization, lineSection_steinerSymmetrization]
  exact volume_eball_sdiff_le _ _

/-- The volume of the symmetric difference, or `L¹` distance between indicators, does not
increase under Steiner symmetrization. Infinite-volume inputs are permitted. -/
theorem volume_steinerSymmetrization_symmDiff_le (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (hs : NullMeasurableSet s volume) (hu : NullMeasurableSet u volume) :
    volume (steinerSymmetrization e he s ∆ steinerSymmetrization e he u) ≤ volume (s ∆ u) := by
  rw [measure_symmDiff_eq (nullMeasurableSet_steinerSymmetrization e he hs)
    (nullMeasurableSet_steinerSymmetrization e he hu), measure_symmDiff_eq hs hu]
  exact add_le_add (volume_steinerSymmetrization_sdiff_le e he hs hu)
    (volume_steinerSymmetrization_sdiff_le e he hu hs)

/-- The `L¹` seminorm distance between real indicators contracts under Steiner symmetrization. -/
theorem eLpNorm_indicator_steinerSymmetrization_sub_le (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (hs : NullMeasurableSet s volume) (hu : NullMeasurableSet u volume) :
    eLpNorm ((steinerSymmetrization e he s).indicator (fun _ ↦ (1 : ℝ)) -
      (steinerSymmetrization e he u).indicator (fun _ ↦ (1 : ℝ))) 1 volume ≤
        eLpNorm (s.indicator (fun _ ↦ (1 : ℝ)) - u.indicator (fun _ ↦ (1 : ℝ))) 1 volume := by
  have hS := nullMeasurableSet_steinerSymmetrization e he hs
  have hU := nullMeasurableSet_steinerSymmetrization e he hu
  rw [eLpNorm_indicator_sub_indicator _ hS hU, eLpNorm_indicator_sub_indicator _ hs hu,
    eLpNorm_indicator_const (hS.symmDiff hU) one_ne_zero ENNReal.one_ne_top,
    eLpNorm_indicator_const (hs.symmDiff hu) one_ne_zero ENNReal.one_ne_top]
  simpa using volume_steinerSymmetrization_symmDiff_le e he hs hu

end TauCeti
