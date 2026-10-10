/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic

-- The model is a type synonym with the charts of its coordinate space. Access that
-- identification when proving smoothness and computing the differential of a linear map.
import all TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic

/-!
# Lifted reflection of the hyperbolic plane on `SL₂ℝ~`

The hyperbolic reflection `x + i eʸ ↦ -x + i eʸ` lifts to the Riemannian isometry
`(x, y, z) ↦ (-x, y, -z)` of the unwound unit tangent bundle. Reversing the fibre coordinate
as well as the horizontal coordinate negates the connection form `dz + e⁻ʸ dx`, and hence
preserves its square in the Sasaki metric. Reflection fixes the origin, has order two,
and conjugates `translate a s c` to `translate (-a) s (-c)`.

This provides the reflection generator alongside the existing orientation-preserving
affine lifts. It is needed to include base-orientation-reversing isometries when describing
the full isometry group; no exhaustion of that group is asserted here.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4 (the geometry of the universal cover of the unit tangent bundle).
* The construction follows the linear isometries in
  `TauCeti.Geometry.Manifold.Riemannian.Sol.Isotropy` and the coordinate differential
  calculation for `SL2Tilde.translate`.
-/

public section

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

namespace TauCeti.SL2Tilde

private def reflectionL : (ℝ × ℝ × ℝ) ≃L[ℝ] ℝ × ℝ × ℝ :=
  (ContinuousLinearEquiv.neg ℝ).prodCongr
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ))

private theorem reflectionL_apply (v : ℝ × ℝ × ℝ) :
    reflectionL v = (-v.1, v.2.1, -v.2.2) := (rfl)

private def reflectionFun (p : SL2Tilde) : SL2Tilde :=
  toProd.symm (reflectionL (toProd p))

private theorem reflectionFun_apply (p : SL2Tilde) :
    reflectionFun p = mk (-p.x) p.y (-p.z) := (rfl)

private theorem reflectionFun_involutive : Function.Involutive reflectionFun := by
  intro p
  ext <;> simp [reflectionFun_apply]

private theorem contMDiff_reflectionFun :
    ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ reflectionFun :=
  -- `SL2Tilde` has exactly the coordinate-space charts, and both coordinate equivalences
  -- are the identity; the manifold regularity is that of the linear coordinate map.
  reflectionL.contDiff.contMDiff

private theorem hasMFDerivAt_reflectionFun (p : SL2Tilde) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) reflectionFun p
      reflectionL.toContinuousLinearMap :=
  -- The coordinate-space identification also identifies the tangent spaces and derivatives.
  reflectionL.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt

private theorem inner_mfderiv_reflectionFun (p : SL2Tilde)
    (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) reflectionFun p v)
      (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) reflectionFun p w) = inner ℝ v w := by
  rw [(hasMFDerivAt_reflectionFun p).mfderiv, inner_def, inner_def]
  -- The coordinate-space identification makes the tangent casts identities. Explicitly
  -- evaluate them and the linear map here: their inferred tangent-space instances prevent
  -- the model-space coercion simp lemmas from matching under the inner-product formula.
  change Real.exp (-2 * p.y) * (-v.1) * (-w.1) + v.2.1 * w.2.1 +
      (-v.2.2 + Real.exp (-p.y) * (-v.1)) *
        (-w.2.2 + Real.exp (-p.y) * (-w.1)) =
    Real.exp (-2 * p.y) * v.1 * w.1 + v.2.1 * w.2.1 +
      (v.2.2 + Real.exp (-p.y) * v.1) * (w.2.2 + Real.exp (-p.y) * w.1)
  ring

/-- The lifted hyperbolic reflection, reversing both the horizontal and fibre coordinates
of `SL₂ℝ~`, as an isometry of its Sasaki metric. -/
def reflection : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) SL2Tilde where
  toFun := reflectionFun
  invFun := reflectionFun
  left_inv := reflectionFun_involutive
  right_inv := reflectionFun_involutive
  contMDiff_toFun := contMDiff_reflectionFun
  contMDiff_invFun := contMDiff_reflectionFun
  inner_mfderiv' := inner_mfderiv_reflectionFun

/-- Reflection reverses the horizontal and fibre coordinates and preserves the height. -/
@[simp] theorem reflection_apply (p : SL2Tilde) :
    reflection p = mk (-p.x) p.y (-p.z) := reflectionFun_apply p

/-- The differential of reflection in global tangent coordinates. -/
@[simp] theorem tangentSpaceCastModel_mfderiv_reflection (p : SL2Tilde)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (reflection p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) reflection p v) =
      (-(tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1,
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1,
        -(tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.2) := by
  -- The isometry's underlying function is the linear coordinate map `reflectionFun`.
  have hd : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) reflection p
      reflectionL.toContinuousLinearMap := hasMFDerivAt_reflectionFun p
  rw [hd.mfderiv]
  -- Both tangent casts are identities in the coordinate model.
  exact reflectionL_apply v

/-- The lifted reflection is an involution in the isometry group. -/
@[simp] theorem reflection_mul_self : reflection * reflection = 1 := by
  apply RiemannianIsometry.ext
  intro p
  simp [RiemannianIsometry.mul_apply, RiemannianIsometry.one_apply]

/-- Reflection is its own inverse. -/
@[simp] theorem reflection_inv : reflection⁻¹ = reflection :=
  inv_eq_of_mul_eq_one_left reflection_mul_self

/-- Reflection conjugates an affine lift by reversing its horizontal and fibre translations. -/
@[simp] theorem reflection_mul_translate_mul_reflection (a s c : ℝ) :
    reflection * translate a s c * reflection = translate (-a) s (-c) := by
  apply RiemannianIsometry.ext
  intro p
  ext <;> simp [RiemannianIsometry.mul_apply] <;> ring

/-- Reflection fixes exactly the height axis in the coordinate space. -/
theorem reflection_apply_eq_self_iff (p : SL2Tilde) :
    reflection p = p ↔ p.x = 0 ∧ p.z = 0 := by
  constructor
  · intro h
    have hx := congrArg x h
    have hz := congrArg z h
    simp only [reflection_apply, x_mk, z_mk] at hx hz
    constructor <;> linarith
  · rintro ⟨hx, hz⟩
    ext <;> simp [hx, hz]

/-- No orientation-preserving affine lift equals the lifted reflection. -/
theorem reflection_ne_translate (a s c : ℝ) : reflection ≠ translate a s c := by
  intro h
  have hzero := DFunLike.congr_fun h (mk 0 0 0)
  have ha : a = 0 := by simpa using (congrArg x hzero).symm
  have hs : s = 0 := by simpa using (congrArg y hzero).symm
  have hone := congrArg x (DFunLike.congr_fun h (mk 1 0 0))
  norm_num [ha, hs] at hone

end TauCeti.SL2Tilde
