/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# The structure-sheaf sequence of a dominant morphism

For a quasi-compact, scheme-theoretically dominant morphism `f : X ⟶ Y`, the map
`𝒪_Y → f_* 𝒪_X` is injective. Together with its cokernel it forms a short exact sequence
of sheaves of modules. If `f` is affine, the cokernel is quasicoherent, and its sections over every
affine open `U` of `Y` identify `Γ(Y, U)`-linearly with the quotient `Γ(X, f ⁻¹ᵁ U) ⧸ Γ(Y, U)`
(`AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardSectionsEquiv`). When `f` is finite, the
cokernel is of finite type without any Noetherian hypothesis
(`AlgebraicGeometry.Scheme.Hom.isFiniteType_cokernel_unitToPushforwardObjUnit`).

For a normalization this cokernel measures the failure of regular functions on the
normalization to descend. Its exact sequence is the input to the cohomological comparison
between a curve and its normalization. Quasi-compactness suffices for injectivity, and no
finiteness or Noetherian hypothesis is imposed on the affine cokernel results.

The sequence is Mathlib's `ShortComplex.cokernelSequence`, and its first map is Mathlib's
`SheafOfModules.unitToPushforwardObjUnit`. Its short exactness follows from the generic
`TauCeti.cokernelSequence_shortExact` applied to that monomorphism.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise IV.1.8 (the normalization sequence).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TauCeti
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a quasi-compact scheme-theoretically dominant morphism, pullback of regular functions
is a monomorphism of sheaves of modules. -/
instance mono_unitToPushforwardObjUnit
    [QuasiCompact f] [IsSchemeTheoreticallyDominant f] :
    Mono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply _root_.PresheafOfModules.mono_of_injective
  intro U
  -- The component of the module-sheaf unit is the structure-presheaf map `f.app`.
  exact f.app_injective U.unop

/-- For an affine morphism the quotient of the direct image of the structure sheaf by the
image of the base's structure sheaf is quasicoherent. Injectivity is not required. -/
instance isQuasicoherent_cokernel_unitToPushforwardObjUnit
    [IsAffineHom f] :
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).IsQuasicoherent := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_structureSheaf X
  have h := Scheme.Modules.isQuasicoherent_pushforward (SheafOfModules.unit X.ringCatSheaf) f
  have : ((SheafOfModules.pushforward f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent := by
    simpa only [Scheme.Modules.pushforward] using h
  exact Scheme.Modules.isQuasicoherent_cokernel _

/-- Over an affine open `U` of `Y`, the sections of `coker(𝒪_Y ⟶ f_* 𝒪_X)` for an affine morphism
`f : X ⟶ Y` identify `Γ(Y, U)`-linearly with the quotient `Γ(X, f ⁻¹ᵁ U) ⧸ Γ(Y, U)`. -/
def cokernelUnitToPushforwardSectionsEquiv [IsAffineHom f] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Γ(cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom), U) ≃ₗ[Γ(Y, U)]
      (Γ(X, f ⁻¹ᵁ U) ⧸ (1 : Submodule Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) :=
  letI := (f.app U).hom.toAlgebra
  let M : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let N : Y.Modules := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  let φ : M ⟶ N := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let _ : M.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  let _ : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_structureSheaf X
  let _ : N.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward (SheafOfModules.unit X.ringCatSheaf) f
  -- Identify `Γ(N, U)` with `Γ(X, f ⁻¹ᵁ U)` equipped with the algebra scalar action of `Γ(Y, U)`,
  -- which matches the restriction-of-scalars action of `pushforward` definitionally.
  let eN : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U) :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  (Scheme.Modules.sectionsCokernelEquiv φ hU).trans <|
    Submodule.Quotient.equiv _ _ eN <| by
      ext b
      simp only [Submodule.mem_one]
      exact ⟨fun ⟨_, ⟨a, rfl⟩, hb⟩ ↦ ⟨a, hb⟩,
        fun ⟨a, hb⟩ ↦ ⟨((Scheme.Modules.sectionsFunctor U).map φ).hom a, ⟨a, rfl⟩, hb⟩⟩

/-- Under `cokernelUnitToPushforwardSectionsEquiv`, the projection to the cokernel acts on sections
over `U` as the quotient map `Γ(X, f ⁻¹ᵁ U) → Γ(X, f ⁻¹ᵁ U) ⧸ Γ(Y, U)`. -/
@[simp]
theorem cokernelUnitToPushforwardSectionsEquiv_π_app [IsAffineHom f] {U : Y.Opens}
    (hU : IsAffineOpen U) (s : Γ(X, f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    f.cokernelUnitToPushforwardSectionsEquiv hU
      (Scheme.Modules.Hom.app
        (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) U s) =
      Submodule.Quotient.mk s := by
  let _ := (f.app U).hom.toAlgebra
  let M : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let N : Y.Modules := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  let φ : M ⟶ N := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : M.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_structureSheaf X
  have : N.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward (SheafOfModules.unit X.ringCatSheaf) f
  exact congrArg _ (Scheme.Modules.sectionsCokernelEquiv_π_app φ hU s)

/-- For a finite morphism `f : X ⟶ Y`, the cokernel `coker(𝒪_Y ⟶ f_* 𝒪_X)` is of finite type,
with no Noetherian hypothesis on `X` or `Y`. -/
instance isFiniteType_cokernel_unitToPushforwardObjUnit [IsFinite f] :
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
      Y.Modules).IsFiniteType := by
  have : (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
      Y.Modules).IsQuasicoherent :=
    f.isQuasicoherent_cokernel_unitToPushforwardObjUnit
  refine Scheme.Modules.isFiniteType_of_finite_sections
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) fun U hU ↦ ?_
  let := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  exact .equiv (f.cokernelUnitToPushforwardSectionsEquiv hU).symm

end

end AlgebraicGeometry.Scheme.Hom
