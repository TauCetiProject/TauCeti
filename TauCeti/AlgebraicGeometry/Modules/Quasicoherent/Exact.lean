/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Exactness of sections of quasicoherent modules over affine opens

Over an affine open of an arbitrary scheme, taking sections carries a complex
`M₁ ⟶ M₂ ⟶ M₃` of quasicoherent module sheaves that is exact in the category of all module
sheaves to an exact sequence of modules. Sections are left exact, the kernel of `M₂ ⟶ M₃` is
quasicoherent, and an epimorphism between quasicoherent modules is surjective on sections over
an affine open (`AlgebraicGeometry.Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen`);
applied to the map from `M₁` onto that kernel, this gives exactness in the middle.

This turns resolutions of quasicoherent sheaves into resolutions of their modules of sections over
affine opens, as used for pseudo-coherent sheaves.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.6.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Sections over an affine open are exact on quasicoherent modules: a complex
`M₁ ⟶ M₂ ⟶ M₃` of quasicoherent module sheaves that is exact in the ambient category of module
sheaves gives an exact sequence of sections over every affine open. -/
theorem exact_app_of_isAffineOpen {S : ShortComplex X.Modules} (hS : S.Exact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (U : X.Opens)
    (hU : IsAffineOpen U) : Function.Exact (S.f.app U) (S.g.app U) := by
  -- Sections are left exact: a section killed by `S.g` comes from the kernel of `S.g`.
  let T : X.Modules ⥤ _ := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)
  have : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf _))
  have : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_preserves_terminal_object
  let K : ShortComplex X.Modules := ShortComplex.mk (kernel.ι S.g) S.g (kernel.condition S.g)
  have hK : (K.map T).Exact :=
    (ShortComplex.exact_of_f_is_kernel K (kernelIsKernel S.g)).map_of_mono_of_preservesKernel T
      (inferInstanceAs (Mono (kernel.ι S.g))) inferInstance
  -- The map from `S.X₁` to the quasicoherent kernel is an epimorphism, hence surjective on `U`.
  have : Epi (kernel.lift S.g S.f S.zero) := hS.epi_kernelLift
  refine fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).mp hK y hy
    obtain ⟨x, rfl⟩ := (kernel.lift S.g S.f S.zero).app_surjective_of_epi_of_isAffineOpen U hU z
    have h := ConcreteCategory.congr_hom
      (congrArg (Hom.app · U) (kernel.lift_ι S.g S.f S.zero)) x
    rw [Hom.comp_app, ConcreteCategory.comp_apply] at h
    -- `(K.map T).f` is the component of `kernel.ι S.g` at `U`, as a map of modules.
    exact ⟨x, h.symm⟩
  · rintro ⟨x, rfl⟩
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, S.zero, Hom.zero_app]
    simp

end AlgebraicGeometry.Scheme.Modules
