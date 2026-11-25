/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
import TauCeti.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Cayley coordinates for the punctured circle and the cylinder

`Real.boundaryCayleyHomeomorph` sends the real line onto the circle with `1` removed.
`Complex.boundaryCayleyParametrization` pairs it at half the real coordinate with the imaginary
coordinate to give oriented cylinder coordinates centred at `(-1, 0)`.
The angular and covector coordinates follow `CircleCotangent.lean` of the Lean-Atiyah-Singer
formalization.
The boundary map and its homeomorphism come from the Tau Ceti modules
`Analysis.Complex.UpperHalfPlane.Cayley` and `Analysis.Complex.Pick.Nevanlinna`,
by the Tau Ceti contributors, Jon Crall, Claude Opus 5 and OpenAI gpt-6.1-sol.
[Lean-Atiyah-Singer](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer)
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
  have hx := (bijOn_sub_I_div_add_I_im_nonneg.mapsTo (x := (x : ℂ)) (by simp)).2
  apply hx
  simpa only [Set.mem_singleton_iff, ← coe_boundaryCayley, Circle.coe_one] using
    (congrArg ((↑) : Circle → ℂ) h)

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
    (continuousAt_sub_I_div_add_I x).comp continuous_ofReal.continuousAt

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
  ring_nf
  simp [I_sq]

end Real

namespace Complex

open Real (boundaryCayley boundaryCayley_ne_one boundaryCayleyHomeomorph
  boundaryCayleyHomeomorph_apply boundaryCayley_eq_neg_exp)

/-- Oriented cylinder coordinates. The angular displacement from `-1` is
`2 * arctan (w.re / 2)` and `w.im` is the normalized covector. -/
def boundaryCayleyParametrization (w : ℂ) : Circle × ℝ := (boundaryCayley (w.re / 2), w.im)

/-- The angular and covector coordinates of the Cayley parametrization. -/
theorem boundaryCayleyParametrization_apply (w : ℂ) :
    boundaryCayleyParametrization w = (boundaryCayley (w.re / 2), w.im) := (rfl)

/-- The origin maps to the zero covector over `-1`. -/
@[simp] theorem boundaryCayleyParametrization_zero : boundaryCayleyParametrization 0 = (-1, 0) := by
  simp [boundaryCayleyParametrization_apply, boundaryCayley_eq_neg_exp]

/-- The parametrization is an open embedding into the cylinder. -/
theorem isOpenEmbedding_boundaryCayleyParametrization :
    IsOpenEmbedding boundaryCayleyParametrization := by
  let scale := (OrderIso.divRight₀ (2 : ℝ) zero_lt_two).toHomeomorph
  have he : IsOpenEmbedding (fun u : ℝ ↦ boundaryCayley (u / 2)) := by
    have h : (fun u : ℝ ↦ boundaryCayley (u / 2)) =
        Subtype.val ∘ boundaryCayleyHomeomorph ∘ scale := by
      funext u
      simp only [Function.comp_apply, boundaryCayleyHomeomorph_apply, scale,
        OrderIso.coe_toHomeomorph, OrderIso.divRight₀_apply]
    rw [h]
    exact isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp
      (boundaryCayleyHomeomorph.isOpenEmbedding.comp scale.isOpenEmbedding)
  unfold boundaryCayleyParametrization
  simpa [Function.comp_def, Prod.map] using
    (he.prodMap (IsOpenEmbedding.id (X := ℝ))).comp equivRealProdCLM.toHomeomorph.isOpenEmbedding

/-- The parametrization covers exactly the covectors based away from `1`. -/
theorem range_boundaryCayleyParametrization :
    range boundaryCayleyParametrization = {p : Circle × ℝ | p.1 ≠ 1} := by
  ext p
  constructor
  · rintro ⟨w, rfl⟩
    exact boundaryCayley_ne_one _
  · intro hz
    obtain ⟨z, s⟩ := p
    obtain ⟨x, hx⟩ := boundaryCayleyHomeomorph.surjective ⟨z, hz⟩
    refine ⟨⟨2 * x, s⟩, Prod.ext ?_ rfl⟩
    simpa [boundaryCayleyParametrization] using congrArg Subtype.val hx

end Complex
