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

The function coercions and algebra instance use the object identification lemmas.
Pointwise computation is provided by section evaluation lemmas.
The sheaf of modules has exactly the same underlying presheaf of functions.

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

-- Keep the transport behind a function so simp indexes section evaluation uniformly.
/-- The function underlying a section of the structure sheaf. -/
def toFun (U : (Opens (TopCat.of X))ᵒᵖ)
    (f : (holomorphicStructureSheaf I X).obj.obj U) : ↥(unop U) → ℂ :=
  (cast (congrArg (fun R : CommRingCat ↦ (R : Type _)) (obj_eq I X U)) f :
    C^ω⟮I, (unop U : Opens X); ℂ⟯)

instance (U : (Opens (TopCat.of X))ᵒᵖ) :
    CoeFun ((holomorphicStructureSheaf I X).obj.obj U) (fun _ ↦ ↥(unop U) → ℂ) where
  coe := toFun I X U

instance (U : (Opens (TopCat.of X))ᵒᵖ) :
    Algebra ℂ ((holomorphicStructureSheaf I X).obj.obj U) := by
  rw [obj_eq]
  infer_instance

variable {I X}

@[simp]
theorem zero_apply {U : (Opens (TopCat.of X))ᵒᵖ} (x : ↥(unop U)) :
    (0 : (holomorphicStructureSheaf I X).obj.obj U) x = 0 := (rfl)

@[simp]
theorem one_apply {U : (Opens (TopCat.of X))ᵒᵖ} (x : ↥(unop U)) :
    (1 : (holomorphicStructureSheaf I X).obj.obj U) x = 1 := (rfl)

@[simp]
theorem add_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (f g : (holomorphicStructureSheaf I X).obj.obj U) (x : ↥(unop U)) :
    (f + g) x = f x + g x := (rfl)

@[simp]
theorem mul_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (f g : (holomorphicStructureSheaf I X).obj.obj U) (x : ↥(unop U)) :
    (f * g) x = f x * g x := (rfl)

@[simp]
theorem neg_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (f : (holomorphicStructureSheaf I X).obj.obj U) (x : ↥(unop U)) :
    (-f) x = -f x := (rfl)

@[simp]
theorem sub_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (f g : (holomorphicStructureSheaf I X).obj.obj U) (x : ↥(unop U)) :
    (f - g) x = f x - g x := (rfl)

@[simp]
theorem smul_apply {U : (Opens (TopCat.of X))ᵒᵖ} (c : ℂ)
    (f : (holomorphicStructureSheaf I X).obj.obj U) (x : ↥(unop U)) :
    (c • f) x = c • f x := (rfl)

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

-- Concrete opens must use the section instances too, as they do in importing modules.
attribute [local irreducible] holomorphicStructureSheaf

/-- Complex analytic functions give sections of the structure sheaf for any complex model. -/
def ofContMDiff {U : Opens X} (f : U → ℂ)
    (hf : ContMDiff I 𝓘(ℂ) ω f) :
    (holomorphicStructureSheaf I X).obj.obj (op (α := Opens X) U) := by
  unfold holomorphicStructureSheaf
  exact ⟨f, hf⟩

@[simp]
theorem ofContMDiff_apply {U : Opens X} (f : U → ℂ)
    (hf : ContMDiff I 𝓘(ℂ) ω f) (x : U) :
    ofContMDiff f hf x = f x := by
  -- Reduce the object transport while keeping the statement's section coercion.
  with_unfolding_all rfl

/-- Holomorphic functions on a complex curve give sections of its structure sheaf. -/
def ofMDifferentiable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] {U : Opens X} (f : U → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (holomorphicStructureSheaf 𝓘(ℂ) X).obj.obj (op (α := Opens X) U) := ofContMDiff f hf.contMDiff

@[simp]
theorem ofMDifferentiable_apply {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] {U : Opens X} (f : U → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (x : U) :
    ofMDifferentiable f hf x = f x := ofContMDiff_apply f hf.contMDiff x

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

instance (U : (Opens (TopCat.of X))ᵒᵖ) :
    CoeFun ((holomorphicStructureSheafModules I X).obj.obj U) (fun _ ↦ ↥(unop U) → ℂ) where
  -- Transport through the object API so the module sheaf's body can remain hidden.
  coe f := (cast (congrArg (fun M : ModuleCat ℂ ↦ (M : Type _)) (obj_eq I X U)) f :
    (holomorphicStructureSheaf I X).obj.obj U)

variable {I X}

@[simp]
theorem zero_apply {U : (Opens (TopCat.of X))ᵒᵖ} (x : ↥(unop U)) :
    (0 : (holomorphicStructureSheafModules I X).obj.obj U) x = 0 :=
  holomorphicStructureSheaf.zero_apply (I := I) (X := X) x

@[simp]
theorem add_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (f g : (holomorphicStructureSheafModules I X).obj.obj U) (x : ↥(unop U)) :
    (f + g) x = f x + g x := holomorphicStructureSheaf.add_apply f g x

@[simp]
theorem neg_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (f : (holomorphicStructureSheafModules I X).obj.obj U) (x : ↥(unop U)) :
    (-f) x = -f x := holomorphicStructureSheaf.neg_apply f x

@[simp]
theorem sub_apply {U : (Opens (TopCat.of X))ᵒᵖ}
    (f g : (holomorphicStructureSheafModules I X).obj.obj U) (x : ↥(unop U)) :
    (f - g) x = f x - g x := holomorphicStructureSheaf.sub_apply f g x

@[simp]
theorem smul_apply {U : (Opens (TopCat.of X))ᵒᵖ} (c : ℂ)
    (f : (holomorphicStructureSheafModules I X).obj.obj U) (x : ↥(unop U)) :
    (c • f) x = c • f x := holomorphicStructureSheaf.smul_apply c f x

/-- Sections of the module sheaf are equal if they agree at every point. -/
@[ext]
theorem ext {U : (Opens (TopCat.of X))ᵒᵖ}
    {f g : (holomorphicStructureSheafModules I X).obj.obj U}
    (h : ∀ x, f x = g x) : f = g := holomorphicStructureSheaf.ext h

variable (I X)

@[simp]
theorem map_apply {U V : (Opens (TopCat.of X))ᵒᵖ} (h : U ⟶ V)
    (f : (holomorphicStructureSheafModules I X).obj.obj U) (x : ↥(unop V)) :
    (holomorphicStructureSheafModules I X).obj.map h f x =
      f (Opens.inclusion (leOfHom h.unop) x) := (rfl)

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
theorem algebraMap_bijective :
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
  AlgEquiv.ofBijective (Algebra.ofId ℂ _) (algebraMap_bijective I X)

@[simp]
theorem globalSectionsEquiv_apply (c : ℂ) (x : X) :
    globalSectionsEquiv I X c ⟨x, trivial⟩ = c := by
  simpa only [Algebra.algebraMap_self_apply, algebraMap_apply] using
    congrArg (fun f : (holomorphicStructureSheaf I X).obj.obj (op ⊤) ↦ f ⟨x, trivial⟩)
      ((globalSectionsEquiv I X).commutes c)

/-- Evaluation at any point is the inverse of the constant-section isomorphism. -/
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
@[simp]
theorem finrank_globalSections :
    Module.finrank ℂ ((holomorphicStructureSheaf I X).obj.obj (op ⊤)) = 1 := by
  rw [← (globalSectionsEquiv I X).toLinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

end holomorphicStructureSheaf

end TauCeti
