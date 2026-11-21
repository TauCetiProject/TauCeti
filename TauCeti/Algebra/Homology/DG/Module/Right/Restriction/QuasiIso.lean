/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Functor

/-!
# Quasi-isomorphisms and restriction of scalars

Restriction along a DG algebra morphism preserves and reflects quasi-isomorphisms, between
modules in independent universes. Restriction does not change cohomology, and the identification
of cohomology is natural, so no flatness or splitting hypothesis is needed.

The resulting morphism of localizers is the input for restriction on derived categories.

## References

* B. Keller, *Deriving DG categories*, Sections 2--3 and 6.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uB uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGRightModuleHom

variable {M : Type uM} {N : Type uN}
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}
  {hM : IsDGRightModule hB ℳ dM} {hN : IsDGRightModule hB 𝒩 dN}
  (f : DGAlgHom hA hB)

/-- The cohomology map of a restricted morphism is the original cohomology map, read through the
identifications of the cohomology of restricted modules. -/
private theorem coe_cohomologyMap_restrictScalars (g : DGRightModuleHom hM hN) :
    ⇑(g.restrictScalars f).cohomologyMap =
      (hN.restrictScalarsCohomologyEquiv f).symm ∘ g.cohomologyMap ∘
        hM.restrictScalarsCohomologyEquiv f := by
  funext c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [Function.comp_apply, Function.comp_apply, IsDGRightModule.restrictScalarsCohomologyEquiv_mk,
    cohomologyMap_mk, cohomologyMap_mk, IsDGRightModule.restrictScalarsCohomologyEquiv_symm_mk]
  congr 1
  ext1
  apply DGRightModule.RestrictScalars.ext
  simp only [cyclesMap_apply_coe, val_restrictScalars]

/-- Restriction of scalars preserves and reflects quasi-isomorphisms of DG right modules. -/
@[simp]
theorem isQuasiIso_restrictScalars_iff (g : DGRightModuleHom hM hN) :
    (g.restrictScalars f).IsQuasiIso ↔ g.IsQuasiIso := by
  rw [isQuasiIso_iff, isQuasiIso_iff, coe_cohomologyMap_restrictScalars, EquivLike.comp_bijective,
    EquivLike.bijective_comp]

end DGRightModuleHom

namespace DGRightModuleCat

/-- Restriction of scalars preserves and reflects membership in the quasi-isomorphisms. -/
@[simp]
theorem quasiIsos_restrictScalars_map_iff (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N) :
    quasiIsos hA ((restrictScalars f).map g) ↔ quasiIsos hB g := by
  rw [quasiIsos_iff, quasiIsos_iff, isQuasiIso_restrictScalars_map_iff]

/-- Ordinary restriction, regarded as a morphism of the localizers defined by
quasi-isomorphisms. -/
noncomputable def restrictScalarsLocalizerMorphism (f : DGAlgHom hA hB) :
    LocalizerMorphism (quasiIsos.{uR, uB, uM} hB) (quasiIsos hA) where
  functor := restrictScalars f
  map _ _ g hg := (quasiIsos_restrictScalars_map_iff f g).mpr hg

/-- The underlying functor of the restriction localizer morphism is ordinary restriction. -/
@[simp]
theorem restrictScalarsLocalizerMorphism_functor (f : DGAlgHom hA hB) :
    (restrictScalarsLocalizerMorphism.{uR, uA, uB, uM} f).functor = restrictScalars f := (rfl)

/-- Quasi-isomorphisms of DG modules are exactly the maps whose restriction is a
quasi-isomorphism. -/
instance (f : DGAlgHom hA hB) :
    (restrictScalarsLocalizerMorphism.{uR, uA, uB, uM} f).IsInduced where
  inverseImage_eq := by
    rw [restrictScalarsLocalizerMorphism_functor]
    ext M N g
    exact quasiIsos_restrictScalars_map_iff f g

end DGRightModuleCat

end TauCeti
