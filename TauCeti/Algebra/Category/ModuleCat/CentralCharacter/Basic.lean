/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Smooth.Basic
public import TauCeti.Algebra.Subalgebra.Center
public import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# Strict central-character modules

For an associative `R`-algebra `A` and a character `χ : Subalgebra.center R A →ₐ[R] R`,
`centralCharacterModules χ` is the object property on `ModuleCat A` given by
`z • m = algebraMap R A (χ z) • m`. Writing the scalar through `algebraMap` avoids choosing
an additional `R`-module structure on a bundled `A`-module. This is equivalent to requiring
that every element of `ker χ` annihilate the module. Restriction through the inverse of an
algebra equivalence transports this property to the character precomposed with the inverse
center equivalence; `discreteCentralCharacterTwist` lifts this functor to the discrete fibers.

The property is closed under subobjects, quotients, all limits and all colimits. Its native
full subcategory is therefore abelian. Intersecting with `discreteModules A` gives
`discreteCentralCharacterModules χ`, the strict character fiber in the category of discrete
modules over a topological algebra. This fiber is also abelian, with exact inclusion into
`ModuleCat A`. No closure under arbitrary ambient extensions is asserted: a self-extension
can have a nonzero off-diagonal central action.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups* (2007), §1.3: categories of
  smooth modules with a prescribed central character.
-/

public section

universe v u

open CategoryTheory Limits

namespace TauCeti

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A]

/-- Modules on which every central element acts by its value under `χ`. -/
def centralCharacterModules (χ : Subalgebra.center R A →ₐ[R] R) :
    ObjectProperty (ModuleCat.{v} A) :=
  fun M => ∀ (z : Subalgebra.center R A) (m : M),
    (z : A) • m = algebraMap R A (χ z) • m

/-- The defining scalar-action equation of a strict central character. -/
theorem centralCharacterModules_iff (χ : Subalgebra.center R A →ₐ[R] R)
    (M : ModuleCat.{v} A) :
    centralCharacterModules χ M ↔ ∀ (z : Subalgebra.center R A) (m : M),
      (z : A) • m = algebraMap R A (χ z) • m :=
  Iff.rfl

variable (χ : Subalgebra.center R A →ₐ[R] R)

/-- The strict character equation is equivalent to annihilation by the character kernel. -/
theorem centralCharacterModules_iff_ker_smul_eq_zero (M : ModuleCat.{v} A) :
    centralCharacterModules χ M ↔
      ∀ z : Subalgebra.center R A, z ∈ RingHom.ker χ → ∀ m : M, (z : A) • m = 0 := by
  constructor
  · intro h z hz m
    simpa only [RingHom.mem_ker.mp hz, map_zero, zero_smul] using h z m
  · intro h z m
    have hz : z - algebraMap R (Subalgebra.center R A) (χ z) ∈ RingHom.ker χ := by
      simp
    have hm := h _ hz m
    simpa only [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, sub_smul, sub_eq_zero] using hm

/-- A strict character passes to submodules. -/
instance : (centralCharacterModules.{v} χ).IsClosedUnderSubobjects where
  prop_of_mono f hf hN z m := by
    apply (ModuleCat.mono_iff_injective f).mp hf
    simpa only [map_smul] using hN z (f m)

/-- A strict character passes to quotients. -/
instance : (centralCharacterModules.{v} χ).IsClosedUnderQuotients where
  prop_of_epi f hf hM z n := by
    obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective f).mp hf n
    simpa only [map_smul] using congrArg f (hM z m)

/-- Limits of modules with the same strict central character have that character. -/
instance (J : Type*) [Category* J] :
    (centralCharacterModules.{v} χ).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro M ⟨p⟩ z m
    have h := p.isLimit.hom_ext (f := ModuleCat.ofHom (Module.End.smulLeft (M := M) (z : A) z.2))
      (f' := ModuleCat.ofHom (Module.End.smulLeft (M := M) (algebraMap R A (χ z))
        (Set.algebraMap_mem_center _))) (fun j => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro n
          simpa [Module.End.smulLeft] using p.prop_diag_obj j z (p.π.app j n))
    exact congrArg (fun f : M ⟶ M => f.hom m) h

/-- Colimits of modules with the same strict central character have that character. -/
instance (J : Type*) [Category* J] :
    (centralCharacterModules.{v} χ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro M ⟨p⟩ z m
    have h := p.isColimit.hom_ext
      (f := ModuleCat.ofHom (Module.End.smulLeft (M := M) (z : A) z.2))
      (f' := ModuleCat.ofHom (Module.End.smulLeft (M := M) (algebraMap R A (χ z))
        (Set.algebraMap_mem_center _))) (fun j => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro n
          simpa [Module.End.smulLeft] using congrArg (p.ι.app j) (p.prop_diag_obj j z n))
    exact congrArg (fun f : M ⟶ M => f.hom m) h

/-- The zero module has every strict central character. -/
instance : (centralCharacterModules.{v} χ).ContainsZero where
  exists_zero := ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _,
    fun _ _ => Subsingleton.elim _ _⟩

/-- A strict central-character property is closed under finite limits. -/
instance : (centralCharacterModules.{v} χ).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape _ _ _ := inferInstance

section Discrete

variable [TopologicalSpace A]

/-- The strict central-character fiber among pointwise-continuous discrete `A`-modules.
Its full subcategory inherits an abelian structure from `ModuleCat A`. -/
def discreteCentralCharacterModules : ObjectProperty (ModuleCat.{v} A) :=
  discreteModules A ⊓ centralCharacterModules χ

/-- Membership consists of discrete continuity and the strict character equation. -/
theorem discreteCentralCharacterModules_iff (M : ModuleCat.{v} A) :
    discreteCentralCharacterModules χ M ↔
      discreteModules A M ∧ centralCharacterModules χ M :=
  Iff.rfl

/-- Discrete strict-character modules are closed under subobjects. -/
instance : (discreteCentralCharacterModules.{v} χ).IsClosedUnderSubobjects where
  prop_of_mono f _ h := ⟨(discreteModules A).prop_of_mono f h.1,
    (centralCharacterModules χ).prop_of_mono f h.2⟩

/-- Discrete strict-character modules are closed under quotients. -/
instance : (discreteCentralCharacterModules.{v} χ).IsClosedUnderQuotients where
  prop_of_epi f _ h := ⟨(discreteModules A).prop_of_epi f h.1,
    (centralCharacterModules χ).prop_of_epi f h.2⟩

/-- Discrete strict-character modules contain zero. -/
instance : (discreteCentralCharacterModules.{v} χ).ContainsZero :=
  inferInstanceAs ((discreteModules A ⊓ centralCharacterModules.{v} χ).ContainsZero)

/-- Finite limits in a discrete strict-character fiber are computed in all modules. -/
instance : (discreteCentralCharacterModules.{v} χ).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ := ⟨by
    rintro M ⟨p⟩
    exact ⟨(discreteModules A).prop_of_isLimit p.isLimit (fun j => (p.prop_diag_obj j).1),
      (centralCharacterModules χ).prop_of_isLimit p.isLimit (fun j => (p.prop_diag_obj j).2)⟩⟩

/-- Arbitrary colimits in a discrete strict-character fiber are computed in all modules. -/
instance (J : Type*) [Category* J] :
    (discreteCentralCharacterModules.{v} χ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro M ⟨p⟩
    exact ⟨(discreteModules A).prop_of_isColimit p.isColimit (fun j => (p.prop_diag_obj j).1),
      (centralCharacterModules χ).prop_of_isColimit p.isColimit (fun j => (p.prop_diag_obj j).2)⟩

end Discrete

section Transport

variable {B : Type*} [Ring B] [Algebra R B]

/-- Restriction through `e⁻¹` transports a strict central character by the inverse center map. -/
theorem centralCharacterModules_restrictScalars_iff (e : A ≃ₐ[R] B) (M : ModuleCat.{v} A) :
    centralCharacterModules (χ.comp (centerCongr e).symm.toAlgHom)
        ((ModuleCat.restrictScalars e.symm.toRingHom).obj M) ↔
      centralCharacterModules χ M := by
  rw [centralCharacterModules_iff, centralCharacterModules_iff]
  constructor
  · intro h z m
    -- Rewrite before substituting the vector of `M`, so the restricted action is still
    -- syntactically visible. The center comparison and the scalar map then cancel with `e⁻¹`.
    simp only [ModuleCat.restrictScalars.smul_def e.symm.toRingHom] at h
    simpa using! h (centerCongr e z) m
  · intro h z m
    simp only [ModuleCat.restrictScalars.smul_def e.symm.toRingHom]
    simpa using! h ((centerCongr e).symm z) m

variable [TopologicalSpace A] [TopologicalSpace B]

/-- A continuous inverse algebra equivalence carries discrete strict-character modules to
modules for the transported character. -/
theorem discreteCentralCharacterModules_restrictScalars (e : A ≃ₐ[R] B)
    (he : Continuous e.symm) {M : ModuleCat.{v} A}
    (hM : discreteCentralCharacterModules χ M) :
    discreteCentralCharacterModules (χ.comp (centerCongr e).symm.toAlgHom)
      ((ModuleCat.restrictScalars e.symm.toRingHom).obj M) :=
  ⟨discreteModules_restrictScalars he hM.1,
    (centralCharacterModules_restrictScalars_iff χ e M).mpr hM.2⟩

/-- Twisting discrete strict-character modules through the inverse of an algebra equivalence.
The underlying modules and morphisms are the native restrictions of scalars. -/
-- Exposed so that the underlying restricted module is available in the types of morphism
-- formulas and elements, not merely up to transport along an equality of bundled modules.
@[expose] noncomputable def discreteCentralCharacterTwist (e : A ≃ₐ[R] B)
    (he : Continuous e.symm) :
    (discreteCentralCharacterModules.{v} χ).FullSubcategory ⥤
      (discreteCentralCharacterModules.{v}
        (χ.comp (centerCongr e).symm.toAlgHom)).FullSubcategory :=
  (discreteCentralCharacterModules _).lift
    ((discreteCentralCharacterModules χ).ι ⋙ ModuleCat.restrictScalars e.symm.toRingHom)
    (fun M => discreteCentralCharacterModules_restrictScalars χ e he M.property)

/-- The underlying module of a twist is restriction through the inverse equivalence. -/
@[simp]
theorem discreteCentralCharacterTwist_obj_obj (e : A ≃ₐ[R] B) (he : Continuous e.symm)
    (M : (discreteCentralCharacterModules.{v} χ).FullSubcategory) :
    ((discreteCentralCharacterTwist χ e he).obj M).obj =
      (ModuleCat.restrictScalars e.symm.toRingHom).obj M.obj :=
  rfl

/-- Twisting does not change the underlying maps of modules. -/
@[simp]
theorem discreteCentralCharacterTwist_map_hom (e : A ≃ₐ[R] B) (he : Continuous e.symm)
    {M N : (discreteCentralCharacterModules.{v} χ).FullSubcategory} (f : M ⟶ N) :
    ((discreteCentralCharacterTwist χ e he).map f).hom =
      (ModuleCat.restrictScalars e.symm.toRingHom).map f.hom :=
  rfl

/-- The forgetful inclusion of a twisted character fiber is exactly restriction of scalars
following the source inclusion. -/
@[simp]
theorem discreteCentralCharacterTwist_comp_ι (e : A ≃ₐ[R] B) (he : Continuous e.symm) :
    discreteCentralCharacterTwist.{v} χ e he ⋙ (discreteCentralCharacterModules _).ι =
      (discreteCentralCharacterModules χ).ι ⋙ ModuleCat.restrictScalars e.symm.toRingHom :=
  rfl

end Transport

end TauCeti
