/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.Modules.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits

/-!
# Zeroth Fitting ideal of a cokernel in the structure sheaf

For any morphism `φ : M ⟶ 𝒪_X` from a quasi-coherent `𝒪_X`-module into the structure sheaf, the
cokernel `cokernel φ` is a quasi-coherent module of finite type whose sections over an affine open
`U` identify with `Γ(X, U) ⧸ φ.imageIdeal U`. Since `Fitt₀(R ⧸ I) = I`, the image ideal sheaf
`φ.imageIdealSheaf` agrees with the zeroth Fitting ideal sheaf `Fitt₀(cokernel φ)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.Hom.imageIdealSheaf_eq_fittingIdeal_cokernel`:
  `φ.imageIdealSheaf = Fitt₀(cokernel φ)` for any morphism `φ : M ⟶ 𝟙_ X.Modules` from a
  quasi-coherent `𝒪_X`-module.

## References

* [The Stacks Project, Tag 0C3C](https://stacks.math.columbia.edu/tag/0C3C) (Fitting ideals of
  finite-type quasi-coherent modules).
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Hom

universe u

noncomputable section

/-- The image ideal sheaf of a morphism `φ : M ⟶ 𝟙_ X.Modules` from a quasi-coherent `𝒪_X`-module
equals the zeroth Fitting ideal sheaf of `cokernel φ`. -/
theorem imageIdealSheaf_eq_fittingIdeal_cokernel {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] (φ : M ⟶ 𝟙_ X.Modules) :
    φ.imageIdealSheaf =
      (cokernel φ).fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) 0 := by
  apply Scheme.IdealSheafData.ext
  funext U
  have := (cokernel φ).finite_sections_of_isAffineOpen U.val U.property
  let eUnit :
      Γ(X, U.val) ≃ₗ[Γ(X, U.val)] (Scheme.Modules.sectionsFunctor U.val).obj (𝟙_ X.Modules) :=
    LinearEquiv.refl Γ(X, U.val) _
  have hI : Submodule.map eUnit.toLinearMap (φ.imageIdeal U.val) =
      LinearMap.range ((Scheme.Modules.sectionsFunctor U.val).map φ).hom := by
    ext s
    exact ⟨fun ⟨_, hx, rfl⟩ ↦ φ.mem_imageIdeal.mp hx,
      fun ⟨t, ht⟩ ↦ ⟨s, φ.mem_imageIdeal.mpr ⟨t, ht⟩, rfl⟩⟩
  let e : (Γ(X, U.val) ⧸ φ.imageIdeal U.val) ≃ₗ[Γ(X, U.val)] Γ(cokernel φ, U.val) :=
    (Submodule.Quotient.equiv _ _ eUnit hI).trans
      (TauCeti.AlgebraicGeometry.cokernelSectionsEquiv φ U)
  rw [φ.imageIdealSheaf_ideal U, Scheme.Modules.fittingIdeal_ideal]
  exact (TauCeti.fittingIdeal_quotient_zero (φ.imageIdeal U.val)).symm.trans
    (TauCeti.fittingIdeal_congr e 0)

end

end AlgebraicGeometry.Scheme.Modules.Hom
