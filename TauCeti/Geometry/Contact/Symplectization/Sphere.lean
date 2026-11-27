/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Sphere
public import TauCeti.Geometry.Contact.Symplectization.Basic
public import TauCeti.Geometry.Manifold.Instances.Cylinder
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.Flow.NormedSpace
import TauCeti.Geometry.Symplectic.Liouville.Collar.Basic

/-!
# The symplectization of the contact sphere is the punctured symplectic vector space

Let `ω` be a linear symplectic form on a finite-dimensional real inner product space `E` of
dimension `n + 1`, with radial primitive `λₓ(v) = ω(x, v) / 2`
(`TauCeti.SymplecticForm.radialPrimitive`), so that `dλ = ω`, and Liouville field `Z(x) = x / 2`.
Its restriction `α = λ|S` to the unit sphere `S` is the contact form of the sphere
(`TauCeti.SymplecticForm.sphereContactForm`). This file identifies the symplectization
`(ℝ × S, d(eˢ α))` of the contact sphere with the punctured space `(E ∖ {0}, ω)`.

The identification is the flow-out of the sphere along the Liouville field, whose flow is the
dilation `x ↦ e^(s/2) x`:

`Φ(s, y) = e^(s/2) y`.

It is a diffeomorphism from `ℝ × S` onto the punctured space `E ∖ {0}`
(`TauCeti.sphereSymplectizationDiffeomorph`), with inverse `x ↦ (2 log ‖x‖, x / ‖x‖)`
(`TauCeti.sphereSymplectizationDiffeomorph_symm_apply_fst`,
`TauCeti.coe_sphereSymplectizationDiffeomorph_symm_apply_snd`): it is the polar coordinate
diffeomorphism `TauCeti.sphereProdRealDiffeomorph` with the logarithmic radius read at half speed.
Since `λ` is homogeneous of degree two, `Φ` pulls `λ` back to the symplectization form `eˢ α`
(`TauCeti.SymplecticForm.mpullback_sphereSymplectizationDiffeomorph_radialPrimitive`), and so it
pulls `ω = dλ` back to the symplectic form `d(eˢ α)`
(`TauCeti.SymplecticForm.mpullback_sphereSymplectizationDiffeomorph_constSmooth`). The half speed
matches the Liouville field `x / 2`: since `λ` scales by `c²` under `x ↦ c x`, the dilation
`(s, y) ↦ eˢ y` would pull `λ` back to `e^(2s) α` instead.

For `E = ℝ^(2m+2)` with coordinates `(x, y)` and `ω = 2 Σⱼ dxⱼ ∧ dyⱼ`, the contact form is
`α = Σⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` on `S^(2m+1)`, and the symplectization of the standard contact sphere is
`ℝ^(2m+2) ∖ {0}` with this form.

## Main definitions

* `TauCeti.sphereSymplectizationDiffeomorph`: the diffeomorphism `(s, y) ↦ e^(s/2) y` from
  `ℝ × S` onto the punctured space.

## Main results

* `TauCeti.SymplecticForm.mpullback_sphereSymplectizationDiffeomorph_radialPrimitive`: it pulls the
  radial primitive `λ` back to the symplectization form `eˢ α` of the contact sphere.
* `TauCeti.SymplecticForm.mpullback_sphereSymplectizationDiffeomorph_constSmooth`: it pulls `ω`
  back to the symplectic form `d(eˢ α)`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Example 2.1.7 and Section 5.4 (the symplectization of the standard contact sphere).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their symplectizations).
-/

public section

noncomputable section

open Metric Module
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The symplectization collar of the unit sphere**: the diffeomorphism `(s, y) ↦ e^(s/2) y`
from `ℝ × S` onto the punctured space `E ∖ {0}`, with inverse `x ↦ (2 log ‖x‖, x / ‖x‖)`. It is
the flow-out of the sphere along the Liouville field `x / 2` of a linear symplectic form, and it
identifies the symplectization of the contact sphere with the punctured space
(`TauCeti.SymplecticForm.mpullback_sphereSymplectizationDiffeomorph_radialPrimitive`). -/
def sphereSymplectizationDiffeomorph :
    Diffeomorph (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (ℝ × sphere (0 : E) 1) (puncturedSpace E) (⊤ : ℕ∞) :=
  ((Diffeomorph.prodComm 𝓘(ℝ) (𝓡 n) ℝ (sphere (0 : E) 1) _).trans
    (Diffeomorph.prodCongr (Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) _)
      ((ContinuousLinearEquiv.smulLeft (Units.mk0 (2⁻¹ : ℝ) (by norm_num))).toDiffeomorph))).trans
    sphereProdRealDiffeomorph

/-- The collar `sphereSymplectizationDiffeomorph` sends `(s, y)` to `e^(s/2) y`. -/
@[simp]
theorem coe_sphereSymplectizationDiffeomorph_apply (p : ℝ × sphere (0 : E) 1) :
    (sphereSymplectizationDiffeomorph (n := n) p : E) = Real.exp (p.1 / 2) • (p.2 : E) := by
  simp [sphereSymplectizationDiffeomorph, div_eq_inv_mul]

/-- The inverse of the collar reads off twice the logarithm of the norm. -/
@[simp]
theorem sphereSymplectizationDiffeomorph_symm_apply_fst (v : puncturedSpace E) :
    (sphereSymplectizationDiffeomorph (n := n) |>.symm v).1 = 2 * Real.log ‖(v : E)‖ := by
  simp [sphereSymplectizationDiffeomorph, ContinuousLinearEquiv.symm_apply_eq]

/-- The inverse of the collar sends `x` to the direction `x / ‖x‖` on the sphere. -/
@[simp]
theorem coe_sphereSymplectizationDiffeomorph_symm_apply_snd (v : puncturedSpace E) :
    ((sphereSymplectizationDiffeomorph (n := n) |>.symm v).2 : E) = ‖(v : E)‖⁻¹ • (v : E) := by
  simp [sphereSymplectizationDiffeomorph]

namespace SymplecticForm

variable [FiniteDimensional ℝ E] (ω : SymplecticForm E)

/-- **The symplectization of the contact sphere is the punctured space: primitives.** The collar
`Φ(s, y) = e^(s/2) y` pulls the radial primitive `λₓ(v) = ω(x, v) / 2`, restricted to the punctured
space, back to the symplectization form `eˢ α` of the contact form `α = λ|S` of the unit sphere:
`Φ^* λ = eˢ α`. -/
theorem mpullback_sphereSymplectizationDiffeomorph_radialPrimitive :
    SmoothForm.mpullback (sphereSymplectizationDiffeomorph (n := n))
        (sphereSymplectizationDiffeomorph (n := n)).contMDiff
        (SmoothForm.mpullback (Subtype.val : puncturedSpace E → E) contMDiff_subtypeVal
          ω.radialPrimitive) =
      (ω.sphereContactForm n).symplectization := by
  -- The collar is the flow-out of the sphere along the complete Liouville field `x / 2`.
  have hΦ : Subtype.val ∘ ⇑(sphereSymplectizationDiffeomorph (n := n) (E := E)) =
      fun p ↦ flowOf (I := 𝓘(ℝ, E)) (fun x : E ↦ (2⁻¹ : ℝ) • x) p.1 (p.2 : E) := by
    funext p
    rw [Function.comp_apply, coe_sphereSymplectizationDiffeomorph_apply, flowOf_dilation,
      inv_mul_eq_div]
  have hZα : (mextDeriv ω.radialPrimitive.val).interior (fun x : E ↦ (2⁻¹ : ℝ) • x) =
      ω.radialPrimitive.val := by
    rw [mextDeriv_radialPrimitive]
    exact ω.constSmooth_interior_two_inv_smul
  refine Subtype.ext <| funext fun p ↦ ?_
  rw [SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback, hΦ, sphereContactForm_def]
  exact mpullback_flowOf_comp_apply_eq_symplectization (contMDiff_dilation _ _)
    contMDiff_coe_sphere hZα ((isCompleteVectorField_dilation _).mem_flowDomain _ _)

/-- **The symplectization of the contact sphere is the punctured space.** The collar
`Φ(s, y) = e^(s/2) y` pulls the constant symplectic form `ω`, restricted to the punctured space,
back to the symplectization form `d(eˢ α)` of the contact form `α = λ|S` of the unit sphere. So
`Φ` is a symplectomorphism from the symplectization `(ℝ × S, d(eˢ α))` of the contact sphere onto
`(E ∖ {0}, ω)`. -/
theorem mpullback_sphereSymplectizationDiffeomorph_constSmooth :
    SmoothForm.mpullback (sphereSymplectizationDiffeomorph (n := n))
        (sphereSymplectizationDiffeomorph (n := n)).contMDiff
        (SmoothForm.mpullback (Subtype.val : puncturedSpace E → E) contMDiff_subtypeVal
          ω.constSmooth) =
      mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1 (ω.sphereContactForm n).symplectization := by
  have hω : ω.constSmooth = mextDerivₗ 𝓘(ℝ, E) 1 ω.radialPrimitive :=
    Subtype.ext ((mextDerivₗ_apply (I := 𝓘(ℝ, E)) 1 _).trans ω.mextDeriv_radialPrimitive).symm
  rw [hω, ← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_sphereSymplectizationDiffeomorph_radialPrimitive]

end SymplecticForm

end TauCeti
