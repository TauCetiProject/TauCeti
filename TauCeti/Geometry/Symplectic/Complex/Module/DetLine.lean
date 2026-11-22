/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Hom
public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap

/-!
# Complex orientations of real maps intertwining almost complex structures

A real-linear map `F : V → W` intertwining almost complex structures `J` and `J'`
(`TauCeti.IsComplexLinearMap`) is complex linear for the induced complex vector space structures
(`TauCeti.IsComplexLinearMap.toComplexLinearMap`). Its real determinant line
`det (ker F) ⊗ (det (coker F))^*` therefore carries the complex orientation
`LinearMap.IsComplexPositiveDetLine` of the determinant lines of complex-linear maps
(`TauCeti.IsComplexLinearMap.IsComplexPositiveDetLine`). This is how
an elliptic operator between real function spaces which is complex linear for pointwise complex
structures, such as a linearized vortex or Cauchy–Riemann operator, is oriented.

When `F` is onto, its determinant line is the real determinant line of its kernel
(`LinearMap.detLineEquivOfSurjective`). If a real isomorphism `e` from the kernel to a complex
vector space `K` turns `J` into multiplication by `i`, then an element of the determinant line of
`F` is complex positive exactly when its image in the real determinant line of `K` is complex
positive (`TauCeti.IsComplexLinearMap.isComplexPositiveDetLine_iff_of_surjective`). So
the complex orientation of a surjective complex-linear map can be read off any complex coordinates
of its kernel.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section A.2.
-/

public section

noncomputable section

namespace TauCeti

open Complex

variable {V W K : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup K] [Module ℂ K] [Module ℝ K] [IsScalarTower ℝ ℂ K]
  {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W}

/-- The **complex orientation** of the determinant line of a real map `F` intertwining the almost
complex structures `J` and `J'`: the complex orientation `LinearMap.IsComplexPositiveDetLine` of
`F` regarded as a complex-linear map for the complex vector space structures induced by `J` and
`J'` (`TauCeti.IsComplexLinearMap.toComplexLinearMap`), whose underlying real map is `F`. -/
def IsComplexLinearMap.IsComplexPositiveDetLine (hF : IsComplexLinearMap J J' F) (z : F.detLine) :
    Prop :=
  letI := J.complexModule
  letI := J'.complexModule
  letI := J.complexModule_isScalarTower
  letI := J'.complexModule_isScalarTower
  hF.toComplexLinearMap.IsComplexPositiveDetLine z

/-- The complex orientation of the determinant line of `F` is that of the complex-linear map
`F`. -/
theorem IsComplexLinearMap.isComplexPositiveDetLine_iff (hF : IsComplexLinearMap J J' F)
    (z : F.detLine) :
    hF.IsComplexPositiveDetLine z ↔
      letI := J.complexModule
      letI := J'.complexModule
      letI := J.complexModule_isScalarTower
      letI := J'.complexModule_isScalarTower
      hF.toComplexLinearMap.IsComplexPositiveDetLine z :=
  Iff.rfl

/-- **Complex coordinates of the kernel read off the complex orientation.** Let `F` intertwine the
almost complex structures `J` and `J'` and be onto, and let `e` be a real isomorphism from the
kernel of `F` to a complex vector space `K` with `e (J v) = i • e v`. Then an element of the
determinant line of `F` lies in its complex orientation exactly when the corresponding element of
the real determinant line of `K`, through `LinearMap.detLineEquivOfSurjective` and `e`, is complex
positive. -/
theorem IsComplexLinearMap.isComplexPositiveDetLine_iff_of_surjective
    (hF : IsComplexLinearMap J J' F) (hsurj : Function.Surjective F)
    (e : LinearMap.ker F ≃ₗ[ℝ] K)
    (he : ∀ v w : LinearMap.ker F, (w : V) = J v → e w = I • e v) (z : F.detLine) :
    hF.IsComplexPositiveDetLine z ↔
      IsComplexPositive (LinearEquiv.detLineCongr e (F.detLineEquivOfSurjective hsurj z)) := by
  rw [hF.isComplexPositiveDetLine_iff]
  let := J.complexModule
  let := J'.complexModule
  let := J.complexModule_isScalarTower
  let := J'.complexModule_isScalarTower
  let L := hF.toComplexLinearMap
  -- `e`, read on the complex kernel of `L`, commutes with multiplication by `i`.
  let e₁ := (L.kerRestrictScalarsEquiv ℝ).trans e
  have he₁ (v : LinearMap.ker L) : e₁ (I • v) = I • e₁ v :=
    he _ _ ((L.coe_kerRestrictScalarsEquiv_apply ℝ (I • v)).trans
      ((Submodule.coe_smul I v).trans ((J.complexModule_I_smul _).trans
        (congrArg J (L.coe_kerRestrictScalarsEquiv_apply ℝ v).symm))))
  let e₂ : LinearMap.ker L ≃ₗ[ℂ] K :=
    LinearEquiv.ofBijective (LinearMap.complexOfMapISmul e₁.toLinearMap he₁)
      (by rw [LinearMap.coe_complexOfMapISmul]; exact e₁.bijective)
  have he₂ : ((L.kerRestrictScalarsEquiv ℝ).symm.trans (e₂.restrictScalars ℝ) :
      LinearMap.ker (L.restrictScalars ℝ) ≃ₗ[ℝ] K) = e :=
    LinearEquiv.ext fun v ↦ by
      rw [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, LinearEquiv.ofBijective_apply,
        LinearMap.coe_complexOfMapISmul, LinearEquiv.coe_coe]
      exact congrArg e ((L.kerRestrictScalarsEquiv ℝ).apply_symm_apply v)
  refine (LinearMap.isComplexPositiveDetLine_iff_of_surjective (f := L) hsurj).trans ?_
  rw [← isComplexPositive_detLineCongr_iff e₂, ← LinearEquiv.trans_apply,
    ← LinearEquiv.detLineCongr_trans, he₂]
  -- The two sides differ only in the kernel of `L` viewed as that of `F`.
  exact Iff.rfl

end TauCeti
