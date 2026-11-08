/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smooth compactly supported maps in parabolic Hölder spaces

Smooth compactly supported functions on ordinary space-time give bounded order-two
parabolic Hölder maps on every closed slab. Their norms admit a common bound under
translations of space and time, independently of the endpoints of the slab.
-/

public section
noncomputable section

open Set TauCeti ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction ContDiff

namespace TauCeti.ParabolicSpaceTime

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ≥0}

/-- A compactly supported `C¹` map on ordinary space-time defines Hölder fields on
all translated slabs with one common norm bound. -/
theorem exists_norm_le_holderSpace_comp_coords (hα : α ≤ 1) {f : E × ℝ → F}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : E × ℝ) (a b : ℝ),
      ∃ g : HolderSpace α (slab (E := E) a b) F,
        (∀ p, g p = f ((p : ParabolicSpaceTime E).space - z.1,
          (p : ParabolicSpaceTime E).time - z.2)) ∧ ‖g‖ ≤ C := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by simp)
  obtain ⟨L, hL⟩ := exists_holderWith_comp_coords hα hK hM
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  refine ⟨M + L, by positivity, fun z a b ↦ ?_⟩
  let u : slab (E := E) a b →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p ↦ f ((p : ParabolicSpaceTime E).space - z.1,
      (p : ParabolicSpaceTime E).time - z.2))
    (hf.continuous.comp (by fun_prop)) M (fun p ↦ hM _)
  have hu : HolderWith L α (u : slab (E := E) a b → F) :=
    fun p q ↦ hL z p q
  let g := HolderSpace.ofBoundedContinuousFunction u hu.memHolder
  refine ⟨g, fun p ↦ ?_, ?_⟩
  · simp [g, u]
  · rw [HolderSpace.norm_def]
    simp only [g, HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
    have hnorm : ‖u‖ ≤ M := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM0 _
    have hsemi : nnHolderNorm α (u : slab (E := E) a b → F) ≤ L := by
      exact ENNReal.toNNReal_mono ENNReal.coe_ne_top hu.eHolderNorm_le
    exact add_le_add hnorm (by exact_mod_cast hsemi)

end TauCeti.ParabolicSpaceTime

namespace TauCeti.ParabolicC2HolderSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ≥0}

-- These shortcuts keep nested operator-space instance search shallow.
private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

private theorem hasFDerivAt_comp_spatial_coords {g : E × ℝ → F} (hg : ContDiff ℝ 1 g)
    (z : E × ℝ) (t : ℝ) (x : E) :
    HasFDerivAt (fun y ↦ g (y - z.1, t - z.2))
      ((fderiv ℝ g (x - z.1, t - z.2)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  simpa [Function.comp_def] using (hg.differentiable (by simp) _).hasFDerivAt.comp x
    ((hasFDerivAt_prodMk_left (x - z.1) (t - z.2)).comp x
      ((hasFDerivAt_id x).sub_const z.1))

/-- Compactly supported `C³` functions on ordinary space-time have a common
order-two parabolic Hölder norm bound on all translated closed slabs. -/
theorem exists_norm_le_comp_coords (hα : α ≤ 1) {f : E × ℝ → F}
    (hf : ContDiff ℝ 3 f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : E × ℝ) (a b : ℝ) (hab : a < b),
      ∃ g : ParabolicC2HolderSpace α E F hab,
        (∀ p, g p = f ((p : ParabolicSpaceTime E).space - z.1,
          (p : ParabolicSpaceTime E).time - z.2)) ∧ ‖g‖ ≤ C := by
  -- Restrict the ordinary derivatives to spatial directions and to the unit time direction.
  let ι : E →L[ℝ] E × ℝ := ContinuousLinearMap.inl ℝ E ℝ
  let R : (E × ℝ →L[ℝ] F) →L[ℝ] E →L[ℝ] F := ι.precomp F
  let S : (E × ℝ →L[ℝ] E →L[ℝ] F) →L[ℝ] E →L[ℝ] E →L[ℝ] F :=
    ι.precomp (E →L[ℝ] F)
  let fx : E × ℝ → E →L[ℝ] F := R ∘ fderiv ℝ f
  have hfx : ContDiff ℝ 2 fx :=
    (R.contDiff (n := 2)).comp (hf.fderiv_right (by norm_num))
  have hsfx : HasCompactSupport fx := (hs.fderiv ℝ).comp_left (map_zero R)
  let fxx : E × ℝ → E →L[ℝ] E →L[ℝ] F := S ∘ fderiv ℝ fx
  have hfxx : ContDiff ℝ 1 fxx :=
    (S.contDiff (n := 1)).comp (hfx.fderiv_right (by norm_num))
  have hsfxx : HasCompactSupport fxx :=
    (hsfx.fderiv ℝ).comp_left (map_zero S)
  let ft : E × ℝ → F := (ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)) ∘ fderiv ℝ f
  have hft : ContDiff ℝ 2 ft :=
    ((ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)).contDiff (n := 2)).comp
      (hf.fderiv_right (by norm_num))
  have hsft : HasCompactSupport ft :=
    (hs.fderiv ℝ).comp_left (map_zero (ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)))
  -- All four field bounds are fixed before translating or selecting a slab.
  obtain ⟨C₀, hC₀, hu⟩ :=
    exists_norm_le_holderSpace_comp_coords hα (hf.of_le (by norm_num)) hs
  obtain ⟨C₁, hC₁, hux⟩ :=
    exists_norm_le_holderSpace_comp_coords hα (hfx.of_le (by norm_num)) hsfx
  obtain ⟨C₂, hC₂, huxx⟩ := exists_norm_le_holderSpace_comp_coords hα hfxx hsfxx
  obtain ⟨Cₜ, hCₜ, hut⟩ :=
    exists_norm_le_holderSpace_comp_coords hα (hft.of_le (by norm_num)) hsft
  refine ⟨C₀ + C₁ + C₂ + Cₜ, by positivity, fun z a b hab ↦ ?_⟩
  obtain ⟨u, hu, hnu⟩ := hu z a b
  obtain ⟨ux, hux, hnux⟩ := hux z a b
  obtain ⟨uxx, huxx, hnuxx⟩ := huxx z a b
  obtain ⟨ut, hut, hnut⟩ := hut z a b
  have hx (t : Icc a b) (x : E) :
      HasFDerivAt (fun y ↦ u (slabMk y t)) (ux (slabMk x t)) x := by
    simp only [hu, hux, space_slabMk, time_slabMk]
    simpa [fx, R, ι, Function.comp_def] using
      hasFDerivAt_comp_spatial_coords (hf.of_le (by norm_num)) z t x
  have hxx (t : Icc a b) (x : E) :
      HasFDerivAt (fun y ↦ ux (slabMk y t)) (uxx (slabMk x t)) x := by
    simp only [hux, huxx, space_slabMk, time_slabMk]
    simpa [fxx, S, ι, Function.comp_def] using
      hasFDerivAt_comp_spatial_coords (hfx.of_le (by norm_num)) z t x
  -- On the closed interval the clamped extension agrees with the ordinary time slice,
  -- so its derivative includes the two endpoints.
  have ht (x : E) (t : Icc a b) :
      HasDerivWithinAt (timeExtension hab.le u x) (ut (slabMk x t)) (Icc a b) t := by
    have hd : HasDerivWithinAt (fun s : ℝ ↦ f (x - z.1, s - z.2))
        (ft (x - z.1, (t : ℝ) - z.2)) (Icc a b) t := by
      simpa [ft, Function.comp_def] using
        ((hf.differentiable (by simp) _).hasFDerivAt.comp (t : ℝ)
          ((hasFDerivAt_const (x - z.1) (t : ℝ)).prodMk
            ((hasFDerivAt_id (t : ℝ)).sub_const z.2))).hasDerivAt.hasDerivWithinAt
          (s := Icc a b)
    simp only [hut, space_slabMk, time_slabMk]
    exact hd.congr_of_mem (f₁ := timeExtension hab.le u x) (fun s hs ↦ by
      simp [timeExtension_def, hu, projIcc_of_mem hab.le hs]) t.2
  let g := mk (hab := hab) u.toBoundedContinuousFunction ux.toBoundedContinuousFunction uxx ut
    (by simpa only [HolderSpace.toBoundedContinuousFunction_apply] using hx)
    (by simpa only [HolderSpace.toBoundedContinuousFunction_apply] using hxx)
    (by simpa only [HolderSpace.coe_toBoundedContinuousFunction] using ht)
  refine ⟨g, fun p ↦ ?_, ?_⟩
  · rw [mk_apply, HolderSpace.toBoundedContinuousFunction_apply, hu]
  · rw [norm_eq, valueL_mk, spatialFDerivL_mk, spatialSecondFDerivL_mk, timeDerivL_mk]
    linarith [u.norm_toBoundedContinuousFunction_le, ux.norm_toBoundedContinuousFunction_le]

end TauCeti.ParabolicC2HolderSpace
