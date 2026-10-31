/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-!
# Continuity of Steiner symmetrization

For a Lebesgue-measurable set of finite volume, Steiner symmetrization is continuous in
its unit direction for the volume of symmetric differences, equivalently the `L¹` distance
between indicators. Together with contraction, this gives joint continuity when both the
direction and the input set vary. These statements allow identification of limits of
successive symmetrizations without regularity or boundedness assumptions on the sets.

The proof combines the covariance and contraction theorems of `Steiner.Basic` with Mathlib's
`MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero`. A local pair of hyperplane
reflections carries the limiting direction to nearby directions and tends to the identity.
-/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace symmDiff Topology

namespace TauCeti

variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

private theorem tendsto_volume_steinerSymmetrization_symmDiff_isometry
    {l : Filter α} (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (hvol : volume s ≠ ∞)
    (R : α → E ≃ₗᵢ[ℝ] E)
    (hR : Tendsto (fun a ↦ (⟨R a, (R a).continuous⟩ : C(E, E))) l
      (𝓝 (ContinuousMap.id E))) :
    Tendsto (fun a ↦ volume (steinerSymmetrization (R a e)
      (((R a).norm_map e).trans he) s ∆ steinerSymmetrization e he s)) l (𝓝 0) := by
  let S := steinerSymmetrization e he s
  have hS : NullMeasurableSet S volume := nullMeasurableSet_steinerSymmetrization e he hs
  have hSV : volume S ≠ ∞ := by simpa [S, volume_steinerSymmetrization e he hs] using hvol
  have hm (t : Set E) (ht : NullMeasurableSet t volume) (hV : volume t ≠ ∞) :
      Tendsto (fun a ↦ volume ((R a ⁻¹' t) ∆ t)) l (𝓝 0) := by
    simpa using tendsto_measure_symmDiff_preimage_nhds_zero hR
      (Eventually.of_forall fun a ↦ (R a).measurePreserving)
      (MeasurePreserving.id volume) ht hV
  have hbound (a : α) :
      volume (steinerSymmetrization (R a e) (((R a).norm_map e).trans he) s ∆ S) ≤
        volume ((R a ⁻¹' s) ∆ s) + volume ((R a ⁻¹' S) ∆ S) := by
    have hpre : R a ⁻¹' steinerSymmetrization (R a e)
        (((R a).norm_map e).trans he) s = steinerSymmetrization e he (R a ⁻¹' s) := by
      have h := steinerSymmetrization_image_linearIsometryEquiv e he (R a) (R a ⁻¹' s)
      simpa only [(R a).surjective.image_preimage, (R a).injective.preimage_image] using
        congrArg (fun t : Set E ↦ R a ⁻¹' t) h
    rw [← (R a).measurePreserving.measure_preimage
      ((nullMeasurableSet_steinerSymmetrization _ _ hs).symmDiff hS), preimage_symmDiff, hpre]
    exact (measure_symmDiff_le _ S _).trans (add_le_add
      (volume_steinerSymmetrization_symmDiff_le e he
        (hs.preimage (R a).measurePreserving.quasiMeasurePreserving) hs)
      (by rw [symmDiff_comm]))
  have hzero := (hm s hs hvol).add (hm S hS hSV)
  simpa using tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun _ ↦ by simp) hbound

/-- Steiner symmetrization of a finite-volume Lebesgue-measurable set is continuous in its
unit direction, measured by the volume of the symmetric difference. -/
theorem tendsto_volume_steinerSymmetrization_symmDiff_direction
    {l : Filter α} {e : E} (he : ‖e‖ = 1) {v : α → E} (hv : ∀ a, ‖v a‖ = 1)
    (hve : Tendsto v l (𝓝 e)) {s : Set E} (hs : NullMeasurableSet s volume)
    (hvol : volume s ≠ ∞) :
    Tendsto (fun a ↦ volume (steinerSymmetrization (v a) (hv a) s ∆
      steinerSymmetrization e he s)) l (𝓝 0) := by
  -- The two reflections agree at the limiting direction, so their composite is the identity.
  let R (w : E) : E ≃ₗᵢ[ℝ] E :=
    (ℝ ∙ e)ᗮ.reflection.trans (ℝ ∙ (e + w))ᗮ.reflection
  have hRe : R e = LinearIsometryEquiv.refl ℝ E := by
    have hspan : (ℝ ∙ (e + e)) = ℝ ∙ e := by
      rw [← two_smul ℝ e]
      exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr two_ne_zero) e
    simp [R, hspan]
  have hRv (a : α) : R (v a) e = v a := by
    simp only [R, LinearIsometryEquiv.trans_apply,
      Submodule.reflection_orthogonalComplement_singleton_eq_neg]
    simpa only [sub_neg_eq_add, map_neg, neg_neg] using
      congrArg Neg.neg (Submodule.reflection_sub (by simpa using he.trans (hv a).symm) :
        (ℝ ∙ (e - -v a))ᗮ.reflection e = -v a)
  -- Away from the antipode the rank-one reflection formula is jointly continuous.
  have hcont : ContinuousOn (fun w ↦ (⟨R w, (R w).continuous⟩ : C(E, E)))
      {w : E | e + w ≠ 0} := by
    apply ContinuousMap.continuousOn_of_continuousOn_uncurry
    intro p hp
    simp only [ContinuousMap.coe_mk, R, LinearIsometryEquiv.trans_apply,
      Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
      RCLike.ofReal_real_eq_id, id_eq]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := simp_all)
  have heU : e + e ≠ 0 := by
    rw [← two_smul ℝ e]
    exact smul_ne_zero two_ne_zero (by intro h; simp [h] at he)
  have hR : Tendsto (fun a ↦ (⟨R (v a), (R (v a)).continuous⟩ : C(E, E))) l
      (𝓝 (ContinuousMap.id E)) := by
    have hopen : IsOpen {w : E | e + w ≠ 0} :=
      isOpen_ne.preimage (continuous_const.add continuous_id)
    have hRid : (⟨R e, (R e).continuous⟩ : C(E, E)) = ContinuousMap.id E := by
      ext x
      simp [hRe]
    simpa only [hRid, Function.comp_def] using
      (hcont.continuousAt (hopen.mem_nhds heU)).tendsto.comp hve
  simpa only [hRv] using
    tendsto_volume_steinerSymmetrization_symmDiff_isometry e he hs hvol (fun a ↦ R (v a)) hR

/-- Joint continuity of Steiner symmetrization for convergent unit directions and inputs
converging in the volume of symmetric differences. Only the limiting set needs finite volume. -/
theorem tendsto_volume_steinerSymmetrization_symmDiff
    {l : Filter α} {e : E} (he : ‖e‖ = 1) {v : α → E} (hv : ∀ a, ‖v a‖ = 1)
    (hve : Tendsto v l (𝓝 e)) {s : Set E} (hs : NullMeasurableSet s volume)
    (hvol : volume s ≠ ∞) {t : α → Set E} (ht : ∀ a, NullMeasurableSet (t a) volume)
    (hts : Tendsto (fun a ↦ volume (t a ∆ s)) l (𝓝 0)) :
    Tendsto (fun a ↦ volume (steinerSymmetrization (v a) (hv a) (t a) ∆
      steinerSymmetrization e he s)) l (𝓝 0) := by
  have hdir := tendsto_volume_steinerSymmetrization_symmDiff_direction he hv hve hs hvol
  have hbound (a : α) :
      volume (steinerSymmetrization (v a) (hv a) (t a) ∆ steinerSymmetrization e he s) ≤
        volume (t a ∆ s) + volume (steinerSymmetrization (v a) (hv a) s ∆
          steinerSymmetrization e he s) :=
    (measure_symmDiff_le _ (steinerSymmetrization (v a) (hv a) s) _).trans
      (add_le_add (volume_steinerSymmetrization_symmDiff_le _ _ (ht a) hs) le_rfl)
  simpa using tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hts.add hdir)
    (fun _ ↦ by simp) hbound

end TauCeti
