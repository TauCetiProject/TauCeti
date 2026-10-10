/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Geometry.Manifold.Complex.Chart

/-!
# The holomorphic structure sheaf

The holomorphic structure sheaf of a complex manifold assigns to an open set `U` the ring
of complex analytic maps `U → ℂ`. Its sections are Mathlib's `ContMDiffMap` at regularity
`ω`, so their pointwise ring and complex vector space structures are reused directly.
The same restriction maps give a sheaf of complex vector spaces, suitable for cohomology.
On a complex curve, these sections are precisely the manifold-differentiable functions.

On a compact connected complex manifold, the constant-section map is an algebra
isomorphism `ℂ ≃ₐ[ℂ] H⁰(X, 𝒪)`. The inverse is evaluation at any point, independently of
which point is chosen. In particular, the space of global sections has dimension one.

The structure sheaf's object representation is exposed so that the existing
`ContMDiffMap` algebraic API applies directly to its sections. The sheaf of modules has
exactly the same underlying presheaf of functions.

The sheaf construction follows `smoothSheafCommRing` in
`Mathlib/Geometry/Manifold/Sheaf/Smooth.lean` by Heather Macbeth and Adam Topaz, using
`StructureGroupoid.LocalInvariantProp.sheaf` at analytic rather than smooth regularity.
The global-sections computation uses Mathlib's
`MDifferentiable.exists_eq_const_of_compactSpace` (the maximum principle).
For the classical structure sheaf and its global sections, see Otto Forster,
*Lectures on Riemann Surfaces*, §§1, 6.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (X : Type) [TopologicalSpace X] [ChartedSpace H X]

/-- The holomorphic structure sheaf of a complex manifold, as a sheaf of commutative rings.
Its sections on `U` are the complex analytic maps `U → ℂ`. -/
@[expose]
def holomorphicStructureSheaf : TopCat.Sheaf CommRingCat (TopCat.of X) where
  obj :=
    { obj := fun U ↦ CommRingCat.of C^ω⟮I, (unop U : Opens X); ℂ⟯
      map := fun h ↦ CommRingCat.ofHom <|
        ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ (leOfHom h.unop)
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)]
    exact ((contDiffWithinAt_localInvariantProp (I := I) (I' := 𝓘(ℂ)) ω).sheaf X ℂ).property

namespace holomorphicStructureSheaf

/-- Sections of the structure sheaf are bundled complex analytic functions. -/
theorem obj_eq (U : (Opens (TopCat.of X))ᵒᵖ) :
    (holomorphicStructureSheaf I X).obj.obj U =
      CommRingCat.of C^ω⟮I, (unop U : Opens X); ℂ⟯ := (rfl)

instance (U : (Opens (TopCat.of X))ᵒᵖ) :
    CoeFun ((holomorphicStructureSheaf I X).obj.obj U) (fun _ ↦ ↥(unop U) → ℂ) where
  coe f := f.1

instance (U : (Opens (TopCat.of X))ᵒᵖ) :
    Algebra ℂ ((holomorphicStructureSheaf I X).obj.obj U) :=
  inferInstanceAs <| Algebra ℂ C^ω⟮I, (unop U : Opens X); ℂ⟯

variable {I X}

/-- Sections of the structure sheaf are equal if they agree at every point. -/
@[ext]
theorem ext {U : (Opens (TopCat.of X))ᵒᵖ}
    {f g : (holomorphicStructureSheaf I X).obj.obj U} (h : ∀ x, f x = g x) : f = g :=
  ContMDiffMap.ext h

/-- A section of the structure sheaf is complex analytic on its domain. -/
theorem contMDiff {U : (Opens (TopCat.of X))ᵒᵖ}
    (f : (holomorphicStructureSheaf I X).obj.obj U) : ContMDiff I 𝓘(ℂ) ω f := f.2

@[simp]
theorem map_apply {U V : (Opens (TopCat.of X))ᵒᵖ} (h : U ⟶ V)
    (f : (holomorphicStructureSheaf I X).obj.obj U) (x : ↥(unop V)) :
    (holomorphicStructureSheaf I X).obj.map h f x =
      f (Opens.inclusion (leOfHom h.unop) x) := (rfl)

@[simp]
theorem algebraMap_apply (U : (Opens (TopCat.of X))ᵒᵖ) (c : ℂ) (x : ↥(unop U)) :
    algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj U) c x = c := (rfl)

/-- A section of the structure sheaf is holomorphic on its domain. -/
theorem mdifferentiable {U : (Opens (TopCat.of X))ᵒᵖ}
    (f : (holomorphicStructureSheaf I X).obj.obj U) : MDifferentiable I 𝓘(ℂ) f :=
  (contMDiff f).mdifferentiable (by simp)

/-- Holomorphic functions on a complex curve give sections of its structure sheaf. -/
def ofMDifferentiable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] {U : Opens (TopCat.of X)} (f : U → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (holomorphicStructureSheaf 𝓘(ℂ) X).obj.obj (op U) := ⟨f, hf.contMDiff⟩

@[simp]
theorem ofMDifferentiable_apply {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] {U : Opens (TopCat.of X)} (f : U → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (x : U) :
    ofMDifferentiable f hf x = f x := (rfl)

end holomorphicStructureSheaf

/-- The holomorphic structure sheaf viewed as a sheaf of complex vector spaces. -/
def holomorphicStructureSheafModules : TopCat.Sheaf (ModuleCat ℂ) (TopCat.of X) where
  obj :=
    { obj := fun U ↦ ModuleCat.of ℂ ((holomorphicStructureSheaf I X).obj.obj U)
      map := fun h ↦ ModuleCat.ofHom
        { toFun := (holomorphicStructureSheaf I X).obj.map h
          map_add' := fun f g ↦ map_add _ f g
          map_smul' := fun _ _ ↦ rfl }
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat ℂ))]
    exact ((contDiffWithinAt_localInvariantProp (I := I) (I' := 𝓘(ℂ)) ω).sheaf X ℂ).property

namespace holomorphicStructureSheafModules

/-- Sections of the module sheaf are the same complex vector spaces as the ring sections. -/
theorem obj_eq (U : (Opens (TopCat.of X))ᵒᵖ) :
    (holomorphicStructureSheafModules I X).obj.obj U =
      ModuleCat.of ℂ ((holomorphicStructureSheaf I X).obj.obj U) := (rfl)

/-- Forgetting the ring or module structure gives the same presheaf of functions. -/
theorem forget_eq :
    (holomorphicStructureSheafModules I X).obj ⋙ forget (ModuleCat ℂ) =
      (holomorphicStructureSheaf I X).obj ⋙ forget CommRingCat := (rfl)

end holomorphicStructureSheafModules

namespace holomorphicStructureSheaf

variable [I.Boundaryless] [IsManifold I 1 X] [CompactSpace X] [PreconnectedSpace X]
  [Nonempty X]

/-- On a nonempty compact connected complex manifold, every global holomorphic section
is a unique constant section. -/
theorem bijective_algebraMap :
    Function.Bijective (algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ⊤))) := by
  constructor
  · intro c d h
    exact congrArg (fun f ↦ f ⟨Classical.arbitrary X, trivial⟩) h
  · intro f
    have hf : ContMDiff I 𝓘(ℂ) ∞ (fun x : X ↦ f ⟨x, trivial⟩) := by
      apply ((contMDiff f).of_le le_top).comp (I' := I)
      apply (ContMDiff.subtypeVal_comp_iff (I := I) (I' := I) ⊤ _).1
      exact contMDiff_id
    obtain ⟨c, hc⟩ := (hf.mdifferentiable (by simp)).exists_eq_const_of_compactSpace
    refine ⟨c, ContMDiffMap.ext fun x ↦ ?_⟩
    exact (congrFun hc x).symm

/-- Constants identify the global sections of the holomorphic structure sheaf with `ℂ`. -/
def globalSectionsEquiv :
    ℂ ≃ₐ[ℂ] ((holomorphicStructureSheaf I X).obj.obj (op ⊤)) :=
  AlgEquiv.ofBijective (Algebra.ofId ℂ _) (bijective_algebraMap I X)

@[simp]
theorem globalSectionsEquiv_apply (c : ℂ) (x : X) :
    globalSectionsEquiv I X c ⟨x, trivial⟩ = c := (rfl)

/-- Evaluation at any point is the inverse of the constant-section isomorphism. -/
@[simp]
theorem globalSectionsEquiv_symm_apply
    (f : (holomorphicStructureSheaf I X).obj.obj (op ⊤)) (x : X) :
    (globalSectionsEquiv I X).symm f = f ⟨x, trivial⟩ := by
  obtain ⟨c, rfl⟩ := (globalSectionsEquiv I X).surjective f
  rw [AlgEquiv.symm_apply_apply]
  exact (globalSectionsEquiv_apply I X c x).symm

instance : FiniteDimensional ℂ ((holomorphicStructureSheaf I X).obj.obj (op ⊤)) :=
  (globalSectionsEquiv I X).toLinearEquiv.finiteDimensional

/-- The space of global holomorphic sections on a nonempty compact connected complex
manifold is one-dimensional over `ℂ`. -/
theorem finrank_globalSections :
    Module.finrank ℂ ((holomorphicStructureSheaf I X).obj.obj (op ⊤)) = 1 := by
  rw [← (globalSectionsEquiv I X).toLinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

end holomorphicStructureSheaf

end TauCeti
