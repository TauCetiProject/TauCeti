/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Radial coordinates in a seminormed space

The positive-norm locus of a real seminormed space is homeomorphic to its unit sphere times the
positive real numbers. The inverse map is scalar multiplication, so these coordinates give product
neighbourhoods of the unit sphere even when the seminorm has a nonzero kernel.

`TauCeti.homeomorphUnitSphereProdOfNormPos` generalizes Mathlib's `homeomorphUnitSphereProd`:
the positive-norm locus replaces the complement of the origin. The construction follows that
homeomorphism, with the domain and the proof that the inverse lands in it adapted to seminorms.
-/

public section

namespace TauCeti

open Metric Set

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial coordinates on the positive-norm locus of a real seminormed space. The forward map
sends `x` to `(‖x‖⁻¹ • x, ‖x‖)` and the inverse sends `(u, r)` to `r • u`. -/
noncomputable def homeomorphUnitSphereProdOfNormPos :
    {x : E | 0 < ‖x‖} ≃ₜ (sphere (0 : E) 1 × Ioi (0 : ℝ)) where
  toFun x :=
    have hx : 0 < ‖x.1‖ := x.2
    (⟨‖x.1‖⁻¹ • x.1, by simp [norm_smul, hx.ne']⟩, ⟨‖x.1‖, hx⟩)
  invFun p := ⟨p.2.1 • p.1.1, by
    simpa only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere p.1, mul_one,
      abs_of_pos p.2.2.out] using p.2.2.out⟩
  left_inv x := by
    have hx : 0 < ‖x.1‖ := x.2
    ext
    exact smul_inv_smul₀ hx.ne' x.1
  right_inv p := by
    obtain ⟨⟨u, hu⟩, ⟨r, hr⟩⟩ := p
    rw [mem_sphere_zero_iff_norm] at hu
    simp [norm_smul, abs_of_pos hr, hu, smul_smul, hr.ne']
  continuous_toFun := by
    have hnorm : Continuous (fun x : {x : E | 0 < ‖x‖} => ‖x.1‖) :=
      continuous_subtype_val.norm
    exact (((hnorm.inv₀ fun x => ne_of_gt x.2).smul continuous_subtype_val).subtype_mk _).prodMk
      (hnorm.subtype_mk _)
  continuous_invFun := by fun_prop

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_apply_fst_coe (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphUnitSphereProdOfNormPos E x).1 : E) = ‖x.1‖⁻¹ • x.1 :=
  (rfl)

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_apply_snd_coe (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphUnitSphereProdOfNormPos E x).2 : ℝ) = ‖x.1‖ :=
  (rfl)

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_symm_apply_coe
    (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
    ((homeomorphUnitSphereProdOfNormPos E).symm p : E) = (p.2 : ℝ) • (p.1 : E) :=
  (rfl)

end TauCeti
