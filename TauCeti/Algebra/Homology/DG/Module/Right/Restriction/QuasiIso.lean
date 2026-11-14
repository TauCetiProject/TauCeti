/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Functor

/-!
# Quasi-isomorphisms and restriction of scalars

Restriction along a DG algebra morphism preserves and reflects quasi-isomorphisms. We transport
relative cycles and their primitives through the existing carrier equivalences; the elementwise
criterion for quasi-isomorphisms then applies without flatness or splitting hypotheses.

The resulting morphism of localizers is the input for restriction on derived categories.

## References

* B. Keller, *Deriving DG categories*, Sections 2--3 and 6.
-/

public section

open CategoryTheory

namespace TauCeti.DGRightModuleCat

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- Restriction of scalars preserves and reflects quasi-isomorphisms of DG right modules. -/
@[simp]
theorem isQuasiIso_restrictScalars_map_iff (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N) :
    IsQuasiIso ((restrictScalars f).map g) ↔ IsQuasiIso g := by
  simp only [IsQuasiIso]
  rw [DGRightModuleHom.isQuasiIso_iff_forall_exists,
    DGRightModuleHom.isQuasiIso_iff_forall_exists]
  constructor
  · intro H x y hx hxy
    let x' := (restrictScalarsEquiv f M).symm x
    let y' := (restrictScalarsEquiv f N).symm y
    have hx' : ((restrictScalars f).obj M).differential x' = 0 := by
      apply (restrictScalarsEquiv f M).injective
      simpa [x', restrictScalarsEquiv_differential] using hx
    have hxy' : (restrictScalars f).map g x' =
        ((restrictScalars f).obj N).differential y' := by
      apply (restrictScalarsEquiv f N).injective
      simpa [x', y', restrictScalarsEquiv_differential] using hxy
    obtain ⟨u, v, hu, huv⟩ := H x' y' hx' hxy'
    refine ⟨restrictScalarsEquiv f M u, restrictScalarsEquiv f N v, ?_, ?_⟩
    · have := congrArg (restrictScalarsEquiv f M) hu
      simpa [x', restrictScalarsEquiv_differential] using this
    · have := congrArg (restrictScalarsEquiv f N) huv
      simpa [y', restrictScalarsEquiv_differential, restrictScalars_map_apply f g] using this
  · intro H x y hx hxy
    have hx' := congrArg (restrictScalarsEquiv f M) hx
    have hxy' := congrArg (restrictScalarsEquiv f N) hxy
    simp only [restrictScalarsEquiv_differential, map_zero] at hx'
    simp only [restrictScalars_map_apply f g, restrictScalarsEquiv_differential] at hxy'
    obtain ⟨u, v, hu, huv⟩ := H _ _ hx' hxy'
    refine ⟨(restrictScalarsEquiv f M).symm u, (restrictScalarsEquiv f N).symm v, ?_, ?_⟩
    · apply (restrictScalarsEquiv f M).injective
      simpa only [restrictScalarsEquiv_differential, LinearEquiv.apply_symm_apply] using hu
    · apply (restrictScalarsEquiv f N).injective
      simpa only [_root_.map_add, restrictScalars_map_apply f g, restrictScalarsEquiv_differential,
        LinearEquiv.apply_symm_apply] using huv

/-- Ordinary restriction, regarded as a morphism of the localizers defined by
quasi-isomorphisms. -/
noncomputable def restrictScalarsLocalizerMorphism (f : DGAlgHom hA hB) :
    LocalizerMorphism (quasiIsos.{uR, uB, uM} hB) (quasiIsos hA) where
  functor := restrictScalars f
  map _ _ g hg := (quasiIsos_iff _).mpr
    ((isQuasiIso_restrictScalars_map_iff f g).mpr ((quasiIsos_iff g).mp hg))

/-- The underlying functor of the restriction localizer morphism is ordinary restriction. -/
@[simp]
theorem restrictScalarsLocalizerMorphism_functor (f : DGAlgHom hA hB) :
    (restrictScalarsLocalizerMorphism.{uR, uA, uB, uM} f).functor = restrictScalars f := (rfl)

end TauCeti.DGRightModuleCat
