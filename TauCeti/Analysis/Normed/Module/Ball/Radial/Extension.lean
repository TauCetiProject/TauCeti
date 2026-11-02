/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-!
# Radial extension of a homeomorphism between unit spheres

A homeomorphism `h` from the unit sphere of a real normed space `E` to the unit sphere of a real
normed space `F` extends radially to a homeomorphism `E ≃ₜ F`, the cone on `h`:

`x ↦ ‖x‖ • h (‖x‖⁻¹ • x)` for `x ≠ 0`, and `0 ↦ 0`.

It preserves norms, so it restricts to a homeomorphism between the closed balls of each radius
about the origin which is `h` on the unit sphere. This is how a gluing of two closed discs along a
homeomorphism of their boundary spheres is compared with the standard sphere, and more generally
how a homeomorphism of the boundary sphere of a disc is extended over the disc.

Away from the origin the extension is `h × id` in the polar coordinates
`homeomorphUnitSphereProd`; continuity at the origin follows from the preservation of norms.

## Main definitions

* `Homeomorph.radialExtension`: the radial extension of a homeomorphism between unit spheres.

## Main results

* `Homeomorph.radialExtension_smul`: the formula `t • u ↦ t • h u` for `t ≥ 0` and `u` on the
  unit sphere.
* `Homeomorph.norm_radialExtension`: the radial extension preserves norms.
* `Homeomorph.radialExtension_symm`: its inverse is the radial extension of `h.symm`.
-/

public section

noncomputable section

open Metric Set Filter Topology

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The homeomorphism `h × id` of the complement of the origin, in the polar coordinates
`homeomorphUnitSphereProd`. -/
private def polarCongr (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) :
    ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set F) :=
  (homeomorphUnitSphereProd E).trans
    ((h.prodCongr (Homeomorph.refl _)).trans (homeomorphUnitSphereProd F).symm)

/-- In polar coordinates, `polarCongr h` is `h × id`. -/
private theorem polarCongr_symm_apply (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)
    (q : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
    polarCongr h ((homeomorphUnitSphereProd E).symm q) =
      (homeomorphUnitSphereProd F).symm (h q.1, q.2) := by
  simp only [polarCongr, trans_apply, apply_symm_apply]
  rfl

private theorem polarCongr_symm_apply_polarCongr (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)
    (x : ({0}ᶜ : Set E)) : polarCongr h.symm (polarCongr h x) = x := by
  obtain ⟨q, rfl⟩ := (homeomorphUnitSphereProd E).symm.surjective x
  simp [polarCongr_symm_apply]

open scoped Classical in
/-- The underlying function of the radial extension. -/
private def radialExtensionFun (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : E) : F :=
  if hx : x = 0 then 0 else polarCongr h ⟨x, hx⟩

private theorem radialExtensionFun_of_ne_zero (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)
    (x : ({0}ᶜ : Set E)) : radialExtensionFun h x = polarCongr h x := by
  unfold radialExtensionFun
  split_ifs with hx
  · exact absurd hx x.2
  · rfl

private theorem radialExtensionFun_zero (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) :
    radialExtensionFun h 0 = 0 := by
  simp [radialExtensionFun]

private theorem norm_radialExtensionFun (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : E) :
    ‖radialExtensionFun h x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, radialExtensionFun_zero]
  · rw [radialExtensionFun_of_ne_zero h ⟨x, hx⟩]
    simp [polarCongr, norm_smul, norm_eq_of_mem_sphere]

private theorem radialExtensionFun_symm_apply (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)
    (x : E) : radialExtensionFun h.symm (radialExtensionFun h x) = x := by
  by_cases hx : x = 0
  · simp [hx, radialExtensionFun_zero]
  · rw [radialExtensionFun_of_ne_zero h ⟨x, hx⟩,
      radialExtensionFun_of_ne_zero h.symm (polarCongr h ⟨x, hx⟩),
      polarCongr_symm_apply_polarCongr]

private theorem continuous_radialExtensionFun (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) :
    Continuous (radialExtensionFun h) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x = 0
  · -- At the origin, continuity follows from the preservation of norms.
    subst hx
    rw [ContinuousAt, radialExtensionFun_zero, tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_radialExtensionFun] using (continuous_norm (E := E)).tendsto 0
  · -- Away from the origin, the extension is the homeomorphism `polarCongr h`.
    have hon : ContinuousOn (radialExtensionFun h) ({0}ᶜ : Set E) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hres : ({0}ᶜ : Set E).domRestrict (radialExtensionFun h) =
          Subtype.val ∘ polarCongr h := funext (radialExtensionFun_of_ne_zero h)
      rw [hres]
      exact continuous_subtype_val.comp (polarCongr h).continuous
    exact hon.continuousAt (isOpen_compl_singleton.mem_nhds hx)

/-- The **radial extension** of a homeomorphism `h` from the unit sphere of a real normed space `E`
to the unit sphere of a real normed space `F`: the homeomorphism `E ≃ₜ F` sending `t • u` to
`t • h u` for `t ≥ 0` and `u` on the unit sphere (`Homeomorph.radialExtension_smul`). It preserves
norms (`Homeomorph.norm_radialExtension`) and its inverse is the radial extension of `h.symm`
(`Homeomorph.radialExtension_symm`). -/
def radialExtension (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) : E ≃ₜ F where
  toFun := radialExtensionFun h
  invFun := radialExtensionFun h.symm
  left_inv := radialExtensionFun_symm_apply h
  right_inv x := by simpa using radialExtensionFun_symm_apply h.symm x
  continuous_toFun := continuous_radialExtensionFun h
  continuous_invFun := continuous_radialExtensionFun h.symm

variable (h : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)

private theorem coe_radialExtension : ⇑(radialExtension h) = radialExtensionFun h :=
  (rfl)

/-- The radial extension preserves norms. -/
@[simp]
theorem norm_radialExtension (x : E) : ‖radialExtension h x‖ = ‖x‖ :=
  norm_radialExtensionFun h x

/-- The inverse of the radial extension of `h` is the radial extension of `h.symm`. -/
@[simp]
theorem radialExtension_symm : (radialExtension h).symm = radialExtension h.symm :=
  (rfl)

/-- The radial extension fixes the origin. -/
@[simp]
theorem radialExtension_zero : radialExtension h 0 = 0 :=
  radialExtensionFun_zero h

/-- **The radial extension in polar coordinates.** For `t ≥ 0` and `u` on the unit sphere, the
radial extension of `h` sends `t • u` to `t • h u`. -/
theorem radialExtension_smul (u : sphere (0 : E) 1) {t : ℝ} (ht : 0 ≤ t) :
    radialExtension h (t • (u : E)) = t • (h u : F) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  -- `t • u` has polar coordinates `(u, t)`.
  have hpolar : (⟨t • (u : E), smul_ne_zero ht.ne' (ne_zero_of_mem_unit_sphere u)⟩ :
      ({0}ᶜ : Set E)) = (homeomorphUnitSphereProd E).symm (u, ⟨t, ht⟩) :=
    Subtype.ext (homeomorphUnitSphereProd_symm_apply_coe E (u, ⟨t, ht⟩)).symm
  rw [coe_radialExtension, radialExtensionFun_of_ne_zero h
      ⟨_, smul_ne_zero ht.ne' (ne_zero_of_mem_unit_sphere u)⟩, hpolar, polarCongr_symm_apply,
    homeomorphUnitSphereProd_symm_apply_coe]

/-- On the unit sphere, the radial extension of `h` is `h`. -/
@[simp]
theorem radialExtension_coe_sphere (u : sphere (0 : E) 1) :
    radialExtension h (u : E) = h u := by
  simpa using radialExtension_smul h u zero_le_one

end Homeomorph
