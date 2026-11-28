/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Topology.UnitInterval

/-!
# Semicircle paths on the unit circle

This file packages the upper and lower semicircle paths from `1` to `-1` in `ℂ` together with
their shared real-part parameter `TauCeti.circleParam : sphere (0 : ℂ) 1 → unitInterval`.

## Main declarations

* `TauCeti.semicircleCoord`: the affine homeomorphism `t ↦ 1 - 2 * t` from `unitInterval` onto
  `[-1, 1]`.
* `TauCeti.upperSemicirclePath`, `TauCeti.lowerSemicirclePath`: the upper and lower semicircle
  paths from `1` to `-1` in `ℂ`, both injective, covering `sphere (0 : ℂ) 1` and meeting only
  at `{1, -1}`.
* `TauCeti.circleParam`: the semicircle parameter `(1 - u.re) / 2 ∈ unitInterval` on
  `sphere (0 : ℂ) 1`, inverting both semicircle paths.
* `TauCeti.mem_range_upperSemicirclePath_iff`, `TauCeti.mem_range_lowerSemicirclePath_iff`:
  characterizations of the upper and lower semicircles by the sign of the imaginary part.
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric Set

/-- The affine homeomorphism `t ↦ 1 - 2 * t` from `unitInterval` onto `[-1, 1]`. -/
def semicircleCoord : unitInterval ≃ₜ Set.Icc (-1 : ℝ) 1 :=
  unitInterval.symmHomeomorph.trans (iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm

theorem coe_semicircleCoord (t : unitInterval) :
    (semicircleCoord t : ℝ) = 1 - 2 * (t : ℝ) := by
  simp only [semicircleCoord, Homeomorph.trans_apply, unitInterval.symmHomeomorph_apply,
    iccHomeoI_symm_apply_coe, unitInterval.coe_symm_eq]
  ring

theorem coe_semicircleCoord_symm (x : Set.Icc (-1 : ℝ) 1) :
    (semicircleCoord.symm x : ℝ) = (1 - (x : ℝ)) / 2 := by
  have h := congrArg Subtype.val (semicircleCoord.apply_symm_apply x)
  rw [coe_semicircleCoord] at h
  linarith

@[simp]
theorem coe_semicircleCoord_zero : (semicircleCoord 0 : ℝ) = 1 := by
  simp [coe_semicircleCoord]

@[simp]
theorem coe_semicircleCoord_one : (semicircleCoord 1 : ℝ) = -1 := by
  simp [coe_semicircleCoord]; norm_num

/-- The upper semicircle path from `1` to `-1` in `ℂ`. -/
def upperSemicirclePath : Path (1 : ℂ) (-1 : ℂ) where
  toFun t := Circle.upperSemicircle (semicircleCoord t)
  continuous_toFun := continuous_subtypeVal.comp
    (Circle.continuous_upperSemicircle.comp semicircleCoord.continuous)
  source' := Complex.ext (by simp) (by simp)
  target' := Complex.ext (by simp) (by simp)

/-- The lower semicircle path from `1` to `-1` in `ℂ`. -/
def lowerSemicirclePath : Path (1 : ℂ) (-1 : ℂ) :=
  (upperSemicirclePath.map Complex.continuous_conj).cast (by simp) (by simp)

theorem upperSemicirclePath_apply (t : unitInterval) :
    upperSemicirclePath t = Circle.upperSemicircle (semicircleCoord t) :=
  (rfl)

/-- The lower semicircle path is the complex conjugate of the upper semicircle path, as a
function. -/
theorem coe_lowerSemicirclePath :
    (lowerSemicirclePath : unitInterval → ℂ) = starRingEnd ℂ ∘ upperSemicirclePath :=
  (Path.cast_coe _ _ _).trans (Path.map_coe _ _)

/-- The lower semicircle path is the complex conjugate of the upper semicircle path. -/
theorem lowerSemicirclePath_eq_conj (t : unitInterval) :
    lowerSemicirclePath t = starRingEnd ℂ (upperSemicirclePath t) :=
  congrFun coe_lowerSemicirclePath t

theorem lowerSemicirclePath_apply (t : unitInterval) :
    lowerSemicirclePath t = ((Circle.upperSemicircle (semicircleCoord t))⁻¹ : Circle) := by
  rw [lowerSemicirclePath_eq_conj, upperSemicirclePath_apply, Circle.coe_inv_eq_conj]

theorem upperSemicirclePath_mem_sphere (t : unitInterval) :
    upperSemicirclePath t ∈ sphere (0 : ℂ) 1 :=
  (Circle.upperSemicircle (semicircleCoord t)).property

theorem lowerSemicirclePath_mem_sphere (t : unitInterval) :
    lowerSemicirclePath t ∈ sphere (0 : ℂ) 1 := by
  rw [lowerSemicirclePath_eq_conj, mem_sphere_zero_iff_norm, Complex.norm_conj,
    ← mem_sphere_zero_iff_norm]
  exact upperSemicirclePath_mem_sphere t

theorem upperSemicirclePath_im_nonneg (t : unitInterval) :
    0 ≤ (upperSemicirclePath t).im := by
  rw [upperSemicirclePath_apply, Circle.im_upperSemicircle]
  exact Real.sqrt_nonneg _

theorem lowerSemicirclePath_im_nonpos (t : unitInterval) :
    (lowerSemicirclePath t).im ≤ 0 := by
  rw [lowerSemicirclePath_eq_conj, conj_im]
  exact neg_nonpos.mpr (upperSemicirclePath_im_nonneg t)

theorem upperSemicirclePath_injective : Function.Injective upperSemicirclePath := fun _ _ h ↦
  semicircleCoord.injective (Circle.upperSemicircle_injective (Circle.coe_injective h))

theorem lowerSemicirclePath_injective : Function.Injective lowerSemicirclePath := by
  rw [coe_lowerSemicirclePath]
  exact (starRingEnd ℂ).injective.comp upperSemicirclePath_injective

/-- The upper and lower semicircle paths cover the unit circle. -/
theorem range_upperSemicirclePath_union_lowerSemicirclePath :
    range upperSemicirclePath ∪ range lowerSemicirclePath = sphere (0 : ℂ) 1 := by
  refine Subset.antisymm (union_subset (range_subset_iff.mpr upperSemicirclePath_mem_sphere)
    (range_subset_iff.mpr lowerSemicirclePath_mem_sphere)) fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := Circle.exists_upperSemicircle_eq_or_inv_eq ⟨z, hz⟩
  rcases hx with hx | hx
  · exact Or.inl ⟨semicircleCoord.symm x, by
      simpa [upperSemicirclePath_apply] using congrArg Subtype.val hx⟩
  · exact Or.inr ⟨semicircleCoord.symm x, by
      simpa [lowerSemicirclePath_apply] using congrArg Subtype.val hx⟩

/-- The upper and lower semicircle paths meet only at `1` and `-1`. -/
theorem range_upperSemicirclePath_inter_lowerSemicirclePath :
    range upperSemicirclePath ∩ range lowerSemicirclePath = {1, -1} := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨⟨s, rfl⟩, ⟨t, hst⟩⟩
    rw [upperSemicirclePath_apply, lowerSemicirclePath_apply] at hst
    obtain ⟨_, hsq⟩ := Circle.upperSemicircle_eq_inv_iff.mp (Circle.coe_injective hst.symm)
    rcases sq_eq_one_iff.mp hsq with hs1 | hs1
    · have hs : s = 0 := semicircleCoord.injective (Subtype.ext (by simp [hs1]))
      exact Or.inl (hs ▸ upperSemicirclePath.source)
    · have hs : s = 1 := semicircleCoord.injective (Subtype.ext (by simp [hs1]))
      exact Or.inr (hs ▸ upperSemicirclePath.target)
  · rintro z (rfl | rfl)
    · exact ⟨upperSemicirclePath.source_mem_range, lowerSemicirclePath.source_mem_range⟩
    · exact ⟨upperSemicirclePath.target_mem_range, lowerSemicirclePath.target_mem_range⟩

/-- The semicircle parameter `(1 - u.re) / 2 ∈ unitInterval` on the unit circle. -/
def circleParam (u : sphere (0 : ℂ) 1) : unitInterval :=
  semicircleCoord.symm ⟨(u : ℂ).re, abs_le.1 (by simpa using abs_re_le_norm (u : ℂ))⟩

theorem coe_circleParam (u : sphere (0 : ℂ) 1) :
    (circleParam u : ℝ) = (1 - (u : ℂ).re) / 2 :=
  coe_semicircleCoord_symm _

@[simp]
theorem coe_semicircleCoord_circleParam (u : sphere (0 : ℂ) 1) :
    (semicircleCoord (circleParam u) : ℝ) = (u : ℂ).re := by
  simp [circleParam]

@[fun_prop]
theorem continuous_circleParam : Continuous circleParam :=
  semicircleCoord.symm.continuous.comp
    (Continuous.subtype_mk (continuous_re.comp continuous_subtypeVal) _)

@[simp]
theorem circleParam_upperSemicirclePath (t : unitInterval) :
    circleParam ⟨upperSemicirclePath t, upperSemicirclePath_mem_sphere t⟩ = t :=
  semicircleCoord.injective (Subtype.ext (by simp [upperSemicirclePath_apply]))

@[simp]
theorem circleParam_lowerSemicirclePath (t : unitInterval) :
    circleParam ⟨lowerSemicirclePath t, lowerSemicirclePath_mem_sphere t⟩ = t :=
  semicircleCoord.injective (Subtype.ext (by simp [lowerSemicirclePath_apply]))

/-- Complex conjugation leaves `TauCeti.circleParam` invariant. -/
@[simp]
theorem circleParam_conj (u : sphere (0 : ℂ) 1) :
    circleParam ⟨starRingEnd ℂ (u : ℂ), by simp⟩ = circleParam u := by
  apply Subtype.ext
  simp [coe_circleParam]

@[simp]
theorem upperSemicirclePath_circleParam {u : sphere (0 : ℂ) 1} (hu : 0 ≤ (u : ℂ).im) :
    upperSemicirclePath (circleParam u) = u := by
  have hnorm : (u : ℂ).re ^ 2 + (u : ℂ).im ^ 2 = 1 := by
    simpa [Circle.coe_homeomorphSphere_symm_apply] using
      (Circle.homeomorphSphere.symm u).re_sq_add_im_sq
  have himsq : 1 - (u : ℂ).re ^ 2 = (u : ℂ).im ^ 2 := by linarith
  apply Complex.ext
  · simp [upperSemicirclePath_apply]
  · simp only [upperSemicirclePath_apply, Circle.im_upperSemicircle,
      coe_semicircleCoord_circleParam]
    rw [himsq, Real.sqrt_sq hu]

@[simp]
theorem lowerSemicirclePath_circleParam {u : sphere (0 : ℂ) 1} (hu : (u : ℂ).im ≤ 0) :
    lowerSemicirclePath (circleParam u) = u := by
  let u' : sphere (0 : ℂ) 1 := ⟨starRingEnd ℂ (u : ℂ), by simp⟩
  have hu' : 0 ≤ (u' : ℂ).im := by simp [u', hu]
  rw [lowerSemicirclePath_eq_conj, ← circleParam_conj u, upperSemicirclePath_circleParam hu']
  simp [u']

/-- A complex number lies on `TauCeti.upperSemicirclePath` iff it lies on the unit circle with
nonnegative imaginary part. -/
theorem mem_range_upperSemicirclePath_iff {z : ℂ} :
    z ∈ range upperSemicirclePath ↔ z ∈ sphere (0 : ℂ) 1 ∧ 0 ≤ z.im :=
  ⟨fun ⟨t, ht⟩ ↦ ht ▸ ⟨upperSemicirclePath_mem_sphere t, upperSemicirclePath_im_nonneg t⟩,
   fun ⟨hz, him⟩ ↦ ⟨circleParam ⟨z, hz⟩, upperSemicirclePath_circleParam him⟩⟩

/-- A complex number lies on `TauCeti.lowerSemicirclePath` iff it lies on the unit circle with
nonpositive imaginary part. -/
theorem mem_range_lowerSemicirclePath_iff {z : ℂ} :
    z ∈ range lowerSemicirclePath ↔ z ∈ sphere (0 : ℂ) 1 ∧ z.im ≤ 0 :=
  ⟨fun ⟨t, ht⟩ ↦ ht ▸ ⟨lowerSemicirclePath_mem_sphere t, lowerSemicirclePath_im_nonpos t⟩,
   fun ⟨hz, him⟩ ↦ ⟨circleParam ⟨z, hz⟩, lowerSemicirclePath_circleParam him⟩⟩

theorem circleParam_eq_zero_of_coe_eq_one {u : sphere (0 : ℂ) 1} (hu : (u : ℂ) = 1) :
    circleParam u = 0 := by
  apply Subtype.ext
  simp [coe_circleParam, hu]

theorem circleParam_eq_one_of_coe_eq_neg_one {u : sphere (0 : ℂ) 1} (hu : (u : ℂ) = -1) :
    circleParam u = 1 := by
  apply Subtype.ext
  simp [coe_circleParam, hu]

end TauCeti
