/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import TauCeti.Analysis.Complex.Cayley.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Cayley coordinates for the punctured circle

`Real.boundaryCayleyHomeomorph` sends the real line onto the circle with `1` removed.
The boundary map and its homeomorphism come from the Tau Ceti modules
`Analysis.Complex.UpperHalfPlane.Cayley` and `Analysis.Complex.Pick.Nevanlinna`,
by the Tau Ceti contributors, Jon Crall, Claude Opus 5 and OpenAI gpt-6.1-sol.
-/

public section

noncomputable section

open Complex Metric Set Topology TauCeti

namespace Real

/-- The boundary Cayley map from the real line to the unit circle, sending
`x` to `(x - i) / (x + i)`. -/
noncomputable def boundaryCayley (x : ℝ) : Circle :=
  ⟨((x : ℂ) - I) / ((x : ℂ) + I), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, norm_sub_I_div_norm_add_I_ofReal]⟩

/-- The boundary Cayley map as a complex-valued formula. -/
@[simp]
theorem coe_boundaryCayley (x : ℝ) :
    (boundaryCayley x : ℂ) = ((x : ℂ) - I) / ((x : ℂ) + I) :=
  by rw [boundaryCayley]

/-- The boundary Cayley map never takes the omitted value `1`. -/
@[simp]
theorem boundaryCayley_ne_one (x : ℝ) : boundaryCayley x ≠ 1 := by
  intro h
  have hx : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hquotient := congrArg ((↑) : Circle → ℂ) h
  rw [coe_boundaryCayley, Circle.coe_one, div_eq_one_iff_eq hx] at hquotient
  have him := congrArg Complex.im hquotient
  norm_num at him

/-- Inverse Cayley coordinates recover every circle point other than the omitted point. -/
theorem boundaryCayley_inverseCayleyCoord {z : Circle} (hz : z ≠ 1) :
    boundaryCayley (inverseCayleyCoord z) = z := by
  apply Circle.ext
  rw [coe_boundaryCayley]
  exact cayley_inverseCayleyCoord (Circle.norm_coe z) fun h ↦ hz (Circle.ext h)

/-- The boundary Cayley map is continuous. -/
@[fun_prop]
theorem continuous_boundaryCayley : Continuous boundaryCayley := by
  apply continuous_induced_rng.mpr
  -- The topology on the circle is induced from ℂ, so the coercion exposes the Cayley quotient.
  change Continuous (fun x : ℝ ↦ (boundaryCayley x : ℂ))
  simp_rw [coe_boundaryCayley]
  exact continuous_iff_continuousAt.mpr fun x ↦
    (continuousAt_sub_I_div_add_I (add_I_ne_zero_of_im_nonneg (by simp : 0 ≤ (x : ℂ).im))).comp
      continuous_ofReal.continuousAt

/-- The boundary Cayley homeomorphism from the real line onto the circle punctured at `1`. -/
def boundaryCayleyHomeomorph : ℝ ≃ₜ {z : Circle // z ≠ 1} where
  toFun x := ⟨boundaryCayley x, boundaryCayley_ne_one x⟩
  invFun z := inverseCayleyCoord (z : Circle)
  left_inv x := by simp
  right_inv z := Subtype.ext (boundaryCayley_inverseCayleyCoord z.property)
  continuous_toFun := continuous_boundaryCayley.subtype_mk _
  continuous_invFun := continuous_iff_continuousAt.mpr fun z ↦ by
    have hz : ((z : Circle) : ℂ) ≠ 1 := fun h ↦ z.property (Circle.ext h)
    exact (continuousAt_inverseCayleyCoord hz).comp (x := z)
      (f := fun w : {u : Circle // u ≠ 1} ↦ (w.val : ℂ)) (by fun_prop)

@[simp]
theorem boundaryCayleyHomeomorph_apply (x : ℝ) :
    (boundaryCayleyHomeomorph x : Circle) = boundaryCayley x :=
  by simp [boundaryCayleyHomeomorph]

@[simp]
theorem boundaryCayleyHomeomorph_symm_apply (z : {z : Circle // z ≠ 1}) :
    boundaryCayleyHomeomorph.symm z = inverseCayleyCoord (z : Circle) :=
  by simp [boundaryCayleyHomeomorph]

/-- The angular displacement of the boundary Cayley point from `-1` is twice the arctangent. -/
theorem boundaryCayley_eq_neg_exp (x : ℝ) :
    boundaryCayley x = -Circle.exp (2 * Real.arctan x) := by
  apply Circle.ext
  rw [coe_boundaryCayley, Circle.coe_neg, Circle.coe_exp, ← one_add_mul_I_div_one_sub_mul_I_eq_exp]
  have h₁ : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have h₂ : 1 - (x : ℂ) * I ≠ 0 := ne_zero_of_re_pos (by simp)
  field_simp
  linear_combination 2 * (x : ℂ) * Complex.I_sq

/-- The real coordinate zero corresponds to the circle point `-1`. -/
@[simp] theorem boundaryCayley_zero : boundaryCayley 0 = -1 := by
  simp [boundaryCayley_eq_neg_exp]

end Real
