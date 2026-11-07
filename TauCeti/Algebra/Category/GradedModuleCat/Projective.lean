/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Module.GradedModule.HomogeneousPart

/-!
# Projective objects in the category of graded modules

A graded module whose underlying module is projective is projective in the graded category.
An ungraded lift exists by module projectivity; taking its degree-zero part gives a graded lift
without changing its composite with the given graded epimorphism.

This makes projective terms in graded module resolutions into categorical projectives, so the
categorical Ext-vanishing and projective Euler-evaluation theorems apply to them. The coefficient
ring need not be a field, and no finite-generation or boundedness hypothesis is imposed.

Underlying projectivity after restriction along a ring homomorphism is invariant under graded
isomorphisms, and holds for a zero graded module. These statements use the explicit restricted
action, so they also apply to either factor of a tensor-product algebra.

Projectivity is stable under the grading shifts, since these are autoequivalences. Consequently
a projective graded module lifts not only degree-zero maps but maps of every degree `p` along
graded epimorphisms: such a map is a degree-zero map into the shift by `-p`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* Mathlib's `ModuleCat.projective_of_categoryTheory_projective` supplies the corresponding
  ungraded lifting argument; here the lift is additionally made homogeneous.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- A graded isomorphism transports projectivity of the underlying modules restricted along
any ring homomorphism. -/
theorem projective_restrictScalars_of_iso {R : Type*} [Ring R] (φ : R →+* A)
    {M N : GradedModuleCat.{v} 𝒜} (f : M ≅ N)
    (hN : letI := Module.compHom N φ; Module.Projective R N) :
    letI := Module.compHom M φ; Module.Projective R M := by
  let := Module.compHom M φ
  let := Module.compHom N φ
  -- The scalar-restriction functor retains N's carrier and its Module.compHom action.
  let : Module.Projective R ((ModuleCat.restrictScalars φ).obj (toModuleCat.obj N)) := hN
  exact Module.Projective.of_equiv'
    (((ModuleCat.restrictScalars φ).mapIso (toModuleCat.mapIso f)).toLinearEquiv.symm)

/-- The underlying module of a zero graded module is projective after any restriction of
scalars. -/
theorem projective_restrictScalars_of_isZero {R : Type*} [Ring R] (φ : R →+* A)
    (M : GradedModuleCat.{v} 𝒜) (hM : Limits.IsZero M) :
    letI := Module.compHom M φ; Module.Projective R M := by
  let := Module.compHom M φ
  let : Subsingleton M := ModuleCat.subsingleton_of_isZero (toModuleCat.map_isZero hM)
  infer_instance

/-- A grading shift of a projective graded module is projective. -/
instance projective_shiftObj (P : GradedModuleCat.{v} 𝒜) [Projective P] (n : ℤ) :
    Projective (P.shiftObj n) :=
  Projective.of_iso ((shiftPowIso 𝒜 n).app P) ((((shift 𝒜) ^ n).map_projective_iff P).2 ‹_›)

/-- **Lifting maps of any degree out of a projective graded module.** Along a graded
epimorphism `g : L ⟶ M`, every `A`-linear map of degree `p` from a projective graded module to `M`
lifts to a map of degree `p` into `L`. -/
theorem exists_isHomogeneous_comp_eq_of_epi (P : GradedModuleCat.{v} 𝒜) [Projective P]
    {L M : GradedModuleCat.{v} 𝒜} (g : L ⟶ M) [Epi g] {p : ℤ} (u : P →ₗ[A] M)
    (hu : LinearMap.IsHomogeneous u P.grading.piece M.grading.piece p) :
    ∃ v : P →ₗ[A] L, LinearMap.IsHomogeneous v P.grading.piece L.grading.piece p ∧
      g.hom ∘ₗ v = u := by
  -- A map of degree `p` into `N` is a map of degree zero into the shift `N{-p}`.
  have : Epi ((shiftFunctor (-p)).map g) :=
    (epi_iff_surjective _).2 ((epi_iff_surjective g).1 ‹_›)
  let u' : P ⟶ M.shiftObj (-p) := ofHom u (by
    rw [_root_.LinearMap.isHomogeneous_shiftObj_iff]
    simpa only [zero_sub, neg_neg] using hu)
  refine ⟨(Projective.factorThru u' ((shiftFunctor (-p)).map g)).hom, ?_, ?_⟩
  · simpa only [zero_sub, neg_neg] using
      (_root_.LinearMap.isHomogeneous_shiftObj_iff (M := P) (N := L) _ (-p) 0).1
        (Projective.factorThru u' ((shiftFunctor (-p)).map g)).isHomogeneous
  · have hl := congrArg Hom.hom (Projective.factorThru_comp u' ((shiftFunctor (-p)).map g))
    rwa [hom_comp, hom_shiftFunctor_map] at hl

variable [DirectSum.Decomposition 𝒜]

/-- An ungraded-projective module is a projective object of the graded module category.
Taking the degree-zero part of an ungraded lift produces the required graded lift. -/
instance projective_of_module_projective (P : GradedModuleCat.{v} 𝒜)
    [Module.Projective A P] : CategoryTheory.Projective P := by
  refine ⟨fun X E hE => ?_⟩
  obtain ⟨f, hf⟩ := Module.projective_lifting_property E.hom X.hom
    ((epi_iff_surjective E).mp hE)
  refine ⟨ofHom (P.grading.homogeneousPartOfGradedSMul _ 𝒜 f 0)
    (P.grading.isHomogeneous_homogeneousPartOfGradedSMul _ 𝒜 f 0), hom_ext ?_⟩
  simp only [hom_comp]
  simpa using (P.grading.comp_homogeneousPartOfGradedSMul _ 𝒜 _ f 0 E.isHomogeneous).trans
    ((congrArg (fun f ↦ P.grading.homogeneousPartOfGradedSMul _ 𝒜 f 0) hf).trans
      (P.grading.homogeneousPartOfGradedSMul_eq_self _ 𝒜 X.hom 0 X.isHomogeneous))

end TauCeti.GradedModuleCat
