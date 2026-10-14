/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Radial coordinates in a seminormed space

The positive-norm locus of a real seminormed space is homeomorphic to any sphere of positive radius
times the positive real numbers. The inverse map is scalar multiplication, so these coordinates give
product neighbourhoods of the sphere even when the seminorm has a nonzero kernel.

`TauCeti.homeomorphSphereProdOfNormPos` and its unit-sphere specialization
`TauCeti.homeomorphUnitSphereProdOfNormPos` generalize Mathlib's `homeomorphSphereProd` and
`homeomorphUnitSphereProd`: the positive-norm locus replaces the complement of the origin. The
construction follows those homeomorphisms, with the domain and the proof that the inverse lands in
it adapted to seminorms.
-/

public section

namespace TauCeti

open Metric Set

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial coordinates on the positive-norm locus of a real seminormed space, using the sphere
of radius `r > 0`. The forward map sends `x` to `(r • ‖x‖⁻¹ • x, ‖x‖ / r)` and the inverse
sends `(u, d)` to `d • u`. -/
noncomputable def homeomorphSphereProdOfNormPos (r : ℝ) (hr : 0 < r) :
    {x : E | 0 < ‖x‖} ≃ₜ (sphere (0 : E) r × Ioi (0 : ℝ)) where
  toFun x :=
    have hx : 0 < ‖x.1‖ := x.2
    (⟨r • ‖x.1‖⁻¹ • x.1, by simp [norm_smul, abs_of_pos hr, hx.ne']⟩,
      ⟨‖x.1‖ / r, mem_Ioi.mpr (div_pos hx hr)⟩)
  invFun p := ⟨p.2.1 • p.1.1, by
    have hd : 0 < (p.2 : ℝ) := mem_Ioi.mp p.2.2
    simpa only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere p.1,
      abs_of_pos hd] using mul_pos hd hr⟩
  left_inv x := by
    have hx : 0 < ‖x.1‖ := x.2
    ext
    calc
      (‖x.1‖ / r) • (r • ‖x.1‖⁻¹ • x.1) =
          ‖x.1‖ • ‖x.1‖⁻¹ • x.1 := by rw [smul_smul, div_mul_cancel₀ _ hr.ne']
      _ = x.1 := smul_inv_smul₀ hx.ne' x.1
  right_inv p := by
    obtain ⟨⟨u, hu⟩, ⟨d, hd⟩⟩ := p
    rw [mem_Ioi] at hd
    rw [mem_sphere_zero_iff_norm] at hu
    simp [norm_smul, smul_smul, abs_of_pos hd, hu, hr.ne', hd.ne']
  continuous_toFun := by
    have hnorm : Continuous (fun x : {x : E | 0 < ‖x‖} => ‖x.1‖) :=
      continuous_subtype_val.norm
    have hdir := ((hnorm.inv₀ fun x => ne_of_gt x.2).smul continuous_subtype_val).const_smul r
    exact (hdir.subtype_mk _).prodMk ((hnorm.div_const r).subtype_mk _)
  continuous_invFun := by fun_prop

@[simp]
theorem homeomorphSphereProdOfNormPos_apply_fst_coe (r : ℝ) (hr : 0 < r)
    (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphSphereProdOfNormPos E r hr x).1 : E) = r • ‖x.1‖⁻¹ • x.1 :=
  (rfl)

@[simp]
theorem homeomorphSphereProdOfNormPos_apply_snd_coe (r : ℝ) (hr : 0 < r)
    (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphSphereProdOfNormPos E r hr x).2 : ℝ) = ‖x.1‖ / r :=
  (rfl)

@[simp]
theorem homeomorphSphereProdOfNormPos_symm_apply_coe (r : ℝ) (hr : 0 < r)
    (p : sphere (0 : E) r × Ioi (0 : ℝ)) :
    ((homeomorphSphereProdOfNormPos E r hr).symm p : E) = (p.2 : ℝ) • (p.1 : E) :=
  (rfl)

/-- Radial coordinates on the positive-norm locus of a real seminormed space, using the unit
sphere. The forward map sends `x` to `(‖x‖⁻¹ • x, ‖x‖)` and the inverse sends `(u, r)` to
`r • u`. -/
noncomputable def homeomorphUnitSphereProdOfNormPos :
    {x : E | 0 < ‖x‖} ≃ₜ (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
  homeomorphSphereProdOfNormPos E 1 one_pos

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_apply_fst_coe (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphUnitSphereProdOfNormPos E x).1 : E) = ‖x.1‖⁻¹ • x.1 := by
  simp [homeomorphUnitSphereProdOfNormPos]

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_apply_snd_coe (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphUnitSphereProdOfNormPos E x).2 : ℝ) = ‖x.1‖ := by
  simp [homeomorphUnitSphereProdOfNormPos]

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_symm_apply_coe
    (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
    ((homeomorphUnitSphereProdOfNormPos E).symm p : E) = (p.2 : ℝ) • (p.1 : E) := by
  simp [homeomorphUnitSphereProdOfNormPos]

end TauCeti
