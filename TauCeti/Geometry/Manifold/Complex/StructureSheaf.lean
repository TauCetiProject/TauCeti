/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Sheaves.Functors
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
Evaluation of germs gives a surjective ring homomorphism from each stalk to `ℂ`.
Holomorphic maps induce morphisms to the pushed-forward structure sheaf by precomposition.

The sheaf construction follows `smoothSheafCommRing` in
`Mathlib/Geometry/Manifold/Sheaf/Smooth.lean` by Heather Macbeth and Adam Topaz, using
`StructureGroupoid.LocalInvariantProp.sheaf` at analytic rather than smooth regularity.
The stalk evaluation and precomposition constructions follow `smoothSheafCommRing.evalHom`
and `ContMDiff.smoothSheafCommRingHom` in the same file.
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

-- Allow the categorical constructions below to compute with section operations locally.
attribute [local semireducible] holomorphicStructureSheaf

open CategoryTheory.Limits

variable (I X)

/-- Evaluation of a holomorphic section at a point of its domain, as a ring homomorphism. -/
def evalAt (x : X) (U : OpenNhds (X := TopCat.of X) x) :
    (holomorphicStructureSheaf I X).obj.obj (op (α := Opens X) U.1) →+* ℂ :=
    { toFun := fun f ↦ f ⟨x, U.2⟩
      map_one' := one_apply _
      map_mul' := fun f g ↦ mul_apply f g _
      map_zero' := zero_apply _
      map_add' := fun f g ↦ add_apply f g _ }

-- Keep computation lemmas on the public coercions, as in the constructors above.
attribute [local irreducible] holomorphicStructureSheaf evalAt

@[simp]
theorem evalAt_apply (x : X) (U : OpenNhds (X := TopCat.of X) x)
    (f : (holomorphicStructureSheaf I X).obj.obj (op (α := Opens X) U.1)) :
    evalAt I X x U f = toFun I X (op (α := Opens X) U.1) f ⟨x, U.2⟩ := (by
  with_unfolding_all rfl)

attribute [local semireducible] holomorphicStructureSheaf

/-- Evaluation of germs at their base point, as a morphism of commutative rings. -/
def evalHom (x : X) : (holomorphicStructureSheaf I X).presheaf.stalk x ⟶ CommRingCat.of ℂ :=
  colimit.desc _
    { pt := CommRingCat.of ℂ
      ι :=
        { app := fun U ↦ CommRingCat.ofHom (evalAt I X x (unop U))
          naturality := by
            intro U V h
            apply CommRingCat.hom_ext
            apply RingHom.ext
            intro f
            -- Restriction and evaluation use the same point of the neighbourhood.
            with_unfolding_all rfl } }

/-- The ring homomorphism evaluating a holomorphic germ at its base point. -/
def eval (x : X) : (holomorphicStructureSheaf I X).presheaf.stalk x →+* ℂ :=
  (evalHom I X x).hom

attribute [local irreducible] holomorphicStructureSheaf evalHom eval

/-- Evaluation of a germ, in the categorical form of the stalk evaluation map. -/
theorem evalHom_germ (U : Opens X) (x : X) (hx : x ∈ U)
    (f : (holomorphicStructureSheaf I X).obj.obj (op (α := Opens X) U)) :
    ConcreteCategory.hom (evalHom I X x)
      (no_index (ConcreteCategory.hom
        ((holomorphicStructureSheaf I X).presheaf.germ U x hx) f)) =
      toFun I X (op (α := Opens X) U) f ⟨x, hx⟩ := (by
  have h : (holomorphicStructureSheaf I X).presheaf.germ U x hx ≫ evalHom I X x =
      CommRingCat.ofHom (evalAt I X x ⟨U, hx⟩) := by
    unfold evalHom
    exact colimit.ι_desc _ _
  rw [← ConcreteCategory.comp_apply]
  exact (congrArg (fun a : (holomorphicStructureSheaf I X).obj.obj (op (α := Opens X) U) ⟶
    CommRingCat.of ℂ ↦ ConcreteCategory.hom a f) h).trans (by
      simpa only [ConcreteCategory.hom_ofHom] using evalAt_apply I X x ⟨U, hx⟩ f))

-- Avoid indexing on carrier projections that normalize differently after import.
/-- Evaluating the germ of a section returns its value at the base point. -/
@[simp]
theorem eval_germ (U : Opens X) (x : X) (hx : x ∈ U)
    (f : (holomorphicStructureSheaf I X).obj.obj (op (α := Opens X) U)) :
    eval I X x
      (no_index (ConcreteCategory.hom
        ((holomorphicStructureSheaf I X).presheaf.germ U x hx) f)) =
      toFun I X (op (α := Opens X) U) f ⟨x, hx⟩ := (by
  unfold eval
  exact evalHom_germ I X U x hx f)

/-- Every complex number is the value of a constant holomorphic germ. -/
theorem eval_surjective (x : X) : Function.Surjective (eval I X x) := by
  intro c
  refine ⟨(holomorphicStructureSheaf I X).presheaf.germ ⊤ x trivial (algebraMap ℂ _ c), ?_⟩
  exact (eval_germ I X ⊤ x trivial _).trans (algebraMap_apply (op ⊤) c ⟨x, trivial⟩)

instance (x : X) : Nontrivial ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  (eval_surjective I X x).nontrivial

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

attribute [local semireducible] holomorphicStructureSheaf

/-- Precomposition by a complex analytic map, on the rings of holomorphic sections. -/
def precomp (f : X → Y) (hf : ContMDiff I J ω f) (U : (Opens Y)ᵒᵖ) :
    (holomorphicStructureSheaf J Y).obj.obj U →+*
      (holomorphicStructureSheaf I X).obj.obj (op (α := Opens X)
        ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj (unop U))) :=
    { toFun := fun g ↦ ofContMDiff (fun x ↦ g ⟨f x.1, x.2⟩) (by
        apply (contMDiff g).comp (I' := J)
        intro x
        exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ Set.univ x).mp
          ((hf.comp contMDiff_subtype_val) x))
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

attribute [local irreducible] holomorphicStructureSheaf precomp

-- Index on evaluation rather than the categorical preimage and carrier projections.
@[simp]
theorem precomp_apply (f : X → Y) (hf : ContMDiff I J ω f) (U : (Opens Y)ᵒᵖ)
    (g : (holomorphicStructureSheaf J Y).obj.obj U)
    (x : ↥((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj (unop U))) :
    toFun I X (no_index (op (α := Opens X)
      ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj (unop U))))
      (no_index (precomp I X f hf U g)) x = toFun J Y U g ⟨f x.1, x.2⟩ := (by
  with_unfolding_all rfl)

attribute [local semireducible] holomorphicStructureSheaf

/-- A complex analytic map induces a morphism `𝒪_Y ⟶ f_*𝒪_X` by precomposition. -/
def homOfContMDiff (f : X → Y) (hf : ContMDiff I J ω f) :
    holomorphicStructureSheaf J Y ⟶
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom ⟨f, hf.continuous⟩)).obj
        (holomorphicStructureSheaf I X) where
  hom.app U := CommRingCat.ofHom (precomp I X f hf U)
  hom.naturality := by
    intro U V h
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro g
    apply holomorphicStructureSheaf.ext
    intro x
    -- Restriction and precomposition both evaluate the original section at `f x`.
    with_unfolding_all rfl

attribute [local irreducible] holomorphicStructureSheaf homOfContMDiff

@[simp]
theorem homOfContMDiff_app (f : X → Y) (hf : ContMDiff I J ω f) (U : (Opens Y)ᵒᵖ) :
    (homOfContMDiff I X f hf).hom.app U = CommRingCat.ofHom (precomp I X f hf U) := (by
  with_unfolding_all rfl)

/-- A holomorphic map between complex curves induces a morphism of structure sheaves. -/
def homOfMDifferentiable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X]
    [IsManifold 𝓘(ℂ) 1 Y] (f : X → Y) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    holomorphicStructureSheaf 𝓘(ℂ) Y ⟶
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom ⟨f, hf.continuous⟩)).obj
        (holomorphicStructureSheaf 𝓘(ℂ) X) :=
  homOfContMDiff 𝓘(ℂ) X f hf.contMDiff

attribute [local irreducible] homOfMDifferentiable

@[simp]
theorem homOfMDifferentiable_app {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X]
    [IsManifold 𝓘(ℂ) 1 Y] (f : X → Y) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (U : (Opens Y)ᵒᵖ) :
    (homOfMDifferentiable f hf).hom.app U =
      CommRingCat.ofHom (precomp 𝓘(ℂ) X f hf.contMDiff U) := (by
  unfold homOfMDifferentiable
  exact homOfContMDiff_app 𝓘(ℂ) X f hf.contMDiff U)

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

/-- Ring sections and module sections have the same complex vector space structure. -/
def sectionsLinearEquiv (U : (Opens (TopCat.of X))ᵒᵖ) :
    (holomorphicStructureSheafModules I X).obj.obj U ≃ₗ[ℂ]
      (holomorphicStructureSheaf I X).obj.obj U := by
  rw [obj_eq]
  exact LinearEquiv.refl ℂ _

@[simp]
theorem sectionsLinearEquiv_apply (U : (Opens (TopCat.of X))ᵒᵖ)
    (f : (holomorphicStructureSheafModules I X).obj.obj U) (x : ↥(unop U)) :
    sectionsLinearEquiv I X U f x = f x := (rfl)

@[simp]
theorem sectionsLinearEquiv_symm_apply (U : (Opens (TopCat.of X))ᵒᵖ)
    (f : (holomorphicStructureSheaf I X).obj.obj U) (x : ↥(unop U)) :
    (sectionsLinearEquiv I X U).symm f x = f x := (rfl)

variable {I X}

/-- A section of the module sheaf is complex analytic on its domain. -/
theorem contMDiff {U : (Opens (TopCat.of X))ᵒᵖ}
    (f : (holomorphicStructureSheafModules I X).obj.obj U) : ContMDiff I 𝓘(ℂ) ω f :=
  (holomorphicStructureSheaf.contMDiff (sectionsLinearEquiv I X U f)).congr
    (fun x ↦ (sectionsLinearEquiv_apply I X U f x).symm)

/-- A section of the module sheaf is holomorphic on its domain. -/
theorem mdifferentiable {U : (Opens (TopCat.of X))ᵒᵖ}
    (f : (holomorphicStructureSheafModules I X).obj.obj U) : MDifferentiable I 𝓘(ℂ) f :=
  (contMDiff f).mdifferentiable (by simp)

attribute [local irreducible] holomorphicStructureSheafModules holomorphicStructureSheaf

/-- Complex analytic functions give sections of the module sheaf for any complex model. -/
def ofContMDiff {U : Opens X} (f : U → ℂ) (hf : ContMDiff I 𝓘(ℂ) ω f) :
    (holomorphicStructureSheafModules I X).obj.obj (op (α := Opens X) U) :=
  (sectionsLinearEquiv I X (op (α := Opens X) U)).symm
    (holomorphicStructureSheaf.ofContMDiff f hf)

@[simp]
theorem ofContMDiff_apply {U : Opens X} (f : U → ℂ)
    (hf : ContMDiff I 𝓘(ℂ) ω f) (x : U) :
    ofContMDiff f hf x = f x := by
  rw [ofContMDiff, sectionsLinearEquiv_symm_apply, holomorphicStructureSheaf.ofContMDiff_apply]

attribute [local semireducible] holomorphicStructureSheafModules holomorphicStructureSheaf

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

namespace holomorphicStructureSheafModules

variable [I.Boundaryless] [IsManifold I 1 X] [CompactSpace X] [PreconnectedSpace X]
  [Nonempty X]

-- Keep the dimension rule on the public module carrier after import.
attribute [local irreducible] holomorphicStructureSheafModules holomorphicStructureSheaf

instance : FiniteDimensional ℂ
    ((holomorphicStructureSheafModules I X).obj.obj (op (α := Opens X) ⊤)) :=
  (sectionsLinearEquiv I X (op (α := Opens X) ⊤)).symm.finiteDimensional

/-- The module sheaf's global sections on a nonempty compact connected complex manifold
form a one-dimensional complex vector space. -/
@[simp]
theorem finrank_globalSections :
    Module.finrank ℂ
      ((holomorphicStructureSheafModules I X).obj.obj (op (α := Opens X) ⊤)) = 1 := by
  rw [(sectionsLinearEquiv I X (op (α := Opens X) ⊤)).finrank_eq]
  exact holomorphicStructureSheaf.finrank_globalSections I X

end holomorphicStructureSheafModules

end TauCeti
