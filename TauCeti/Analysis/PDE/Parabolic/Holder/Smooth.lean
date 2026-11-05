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

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Bounded Lipschitz maps on ordinary space-time are uniformly Hölder for the
parabolic distance, even when time ranges over the whole real line. -/
theorem exists_holderWith_comp_coords (hα : α ≤ 1) {f : E × ℝ → F}
    {K : ℝ≥0} (hf : LipschitzWith K f) {M : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ M) :
    ∃ C : ℝ≥0, ∀ z : E × ℝ,
      HolderWith C α (fun p : ParabolicSpaceTime E ↦ f (p.space - z.1, p.time - z.2)) := by
  let C : ℝ≥0 := ⟨max (K : ℝ) (2 * M), le_max_of_le_left K.coe_nonneg⟩
  refine ⟨C, fun z ↦ ?_⟩
  have hdist (p q : ParabolicSpaceTime E) :
      dist (f (p.space - z.1, p.time - z.2)) (f (q.space - z.1, q.time - z.2)) ≤
        C * dist p q := by
    by_cases hd : dist p q ≤ 1
    · have ht : |p.time - q.time| ≤ dist p q := by
        have hs := sqrt_abs_time_sub_le_dist p q
        have hsq := Real.sq_sqrt (abs_nonneg (p.time - q.time))
        nlinarith [Real.sqrt_nonneg |p.time - q.time|]
      calc
        _ ≤ K * dist (p.space - z.1, p.time - z.2) (q.space - z.1, q.time - z.2) :=
          hf.dist_le_mul _ _
        _ ≤ K * dist p q := by
          gcongr
          simpa [Prod.dist_eq, dist_sub_right, Real.dist_eq] using
            max_le (dist_space_le p q) ht
        _ ≤ C * dist p q := by gcongr; exact le_max_left _ _
    · calc
        _ ≤ ‖f (p.space - z.1, p.time - z.2)‖ + ‖f (q.space - z.1, q.time - z.2)‖ :=
          dist_le_norm_add_norm _ _
        _ ≤ 2 * M := by
          linarith [hbound (p.space - z.1, p.time - z.2),
            hbound (q.space - z.1, q.time - z.2)]
        _ ≤ C * dist p q := by
          have hc : 2 * M ≤ (C : ℝ) := le_max_right _ _
          nlinarith [C.coe_nonneg]
  have hlip : LipschitzWith C
      (fun p : ParabolicSpaceTime E ↦ f (p.space - z.1, p.time - z.2)) :=
    LipschitzWith.of_dist_le_mul hdist
  have hzero : HolderWith C 0
      (fun p : ParabolicSpaceTime E ↦ f (p.space - z.1, p.time - z.2)) := by
    intro p q
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hc : 2 * M ≤ (C : ℝ) := le_max_right _ _
    exact (dist_le_norm_add_norm _ _).trans (by
      linarith [hbound (p.space - z.1, p.time - z.2), hbound (q.space - z.1, q.time - z.2)])
  simpa using hzero.of_le_of_le hlip.holderWith (by positivity : 0 ≤ α) hα

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
  have hi : (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ) = ι := by
    ext x <;> simp [ι]
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
    simpa [fx, R, Function.comp_def, hi] using
      (hf.differentiable (by simp) _).hasFDerivAt.comp x
        (((hasFDerivAt_id x).sub_const z.1).prodMk (hasFDerivAt_const ((t : ℝ) - z.2) x))
  have hxx (t : Icc a b) (x : E) :
      HasFDerivAt (fun y ↦ ux (slabMk y t)) (uxx (slabMk x t)) x := by
    simp only [hux, huxx, space_slabMk, time_slabMk]
    simpa [fxx, S, Function.comp_def, hi] using
      (hfx.differentiable (by simp) _).hasFDerivAt.comp x
        (((hasFDerivAt_id x).sub_const z.1).prodMk (hasFDerivAt_const ((t : ℝ) - z.2) x))
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
