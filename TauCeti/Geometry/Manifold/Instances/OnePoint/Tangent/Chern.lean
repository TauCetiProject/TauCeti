/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Clutching
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern

/-!
# The first Chern number of the Riemann sphere

A fiberwise nondegenerate two-form `σ` on a manifold has a first Chern number
`c₁ : π₂(M, x) → ℤ` (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom`), the clutching number of
the tangent bundle made complex by any almost complex structure tamed by `σ`. This file evaluates it
on the Riemann sphere `OnePoint ℂ`, regarded as a real surface.

If `σ` tames the complex structure of `OnePoint ℂ`, multiplication by `i` on its tangent spaces,
then on the class of the standard sphere `TauCeti.riemannSphereSquare`, which carries the complex
orientation, the first Chern number of `σ` is `2`
(`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_apply_mk_riemannSphereSquare`): it is the
clutching number of the holomorphic tangent bundle
(`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom_tangentSpace`), which is
`2` on this sphere (`TauCeti.clutchingNumber_tangentSpace_riemannSphereSquare`). On a surface a
two-form tames the complex structure exactly when it is an area form positive for the complex
orientation, so this applies to every such form, in particular to the Fubini–Study form
(`OnePoint.firstChernHom_fubiniStudyForm_apply_mk_riemannSphereSquare`). This is the value
`c₁(TS²)[S²] = χ(S²) = 2` of the first Chern number with which the grading of capped Hamiltonian
Floer theory on the two-sphere changes under recapping by a sphere.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_apply_mk_riemannSphereSquare`: the first
  Chern number of a two-form taming the complex structure of the Riemann sphere is `2` on the
  standard sphere.
* `OnePoint.firstChernHom_fubiniStudyForm_apply_mk_riemannSphereSquare`: the case of the
  Fubini–Study form.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a surface by clutching).
-/

public section

open OnePoint
open scoped Manifold TauCeti.ComplexManifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open SmoothAlmostComplexStructure

/-- **The first Chern number of the Riemann sphere is `2`.** If a fiberwise nondegenerate two-form
`σ` on the Riemann sphere tames its complex structure, then its first Chern number on the class of
the standard sphere `TauCeti.riemannSphereSquare`, which carries the complex orientation, is `2`. -/
theorem firstChernHom_apply_mk_riemannSphereSquare {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (h : σ.IsNondegenerate) (hJ : σ.Tames (ofComplexManifold ℂ (OnePoint ℂ))) :
    h.firstChernHom ∞ (Additive.ofMul (Quotient.mk _ riemannSphereSquare)) = 2 := by
  rw [h.firstChernHom_eq_clutchingNumberHom_tangentSpace hJ, clutchingNumberHom_apply_mk,
    clutchingNumber_tangentSpace_riemannSphereSquare]

end TauCeti.SmoothTwoForm.IsNondegenerate

namespace OnePoint

/-- The first Chern number of the Fubini–Study form of the Riemann sphere is `2` on the class of the
standard sphere `TauCeti.riemannSphereSquare`. -/
theorem firstChernHom_fubiniStudyForm_apply_mk_riemannSphereSquare :
    isSymplectic_fubiniStudyForm.isNondegenerate.firstChernHom ∞
      (Additive.ofMul (Quotient.mk _ TauCeti.riemannSphereSquare)) = 2 :=
  isSymplectic_fubiniStudyForm.isNondegenerate.firstChernHom_apply_mk_riemannSphereSquare
    compatible_fubiniStudyForm.tames

end OnePoint
