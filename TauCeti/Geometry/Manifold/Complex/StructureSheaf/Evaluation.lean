/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Vanishing
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Evaluation of holomorphic sections at a point

Evaluation at `p` gives a surjection from the holomorphic structure sheaf to the skyscraper
sheaf with fibre `ℂ` at `p`. Its kernel is the sheaf of holomorphic functions vanishing at `p`.
Thus `0 → 𝓘_p → 𝒪 → ℂ_p → 0` is a short exact sequence of complex vector-space sheaves.
On a complex curve, `𝓘_p` is the ideal sheaf of the negative point divisor. This is the
point-evaluation sequence used in computing the cohomology of divisor sheaves.

Evaluation is surjective even on sections: on an open containing `p`, any desired value is
represented by a constant holomorphic function. No compactness, connectedness, or manifold
regularity hypothesis is needed.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §16.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (X : Type) [TopologicalSpace X] [ChartedSpace H X] (p : X)

/-- Evaluation of a holomorphic module section at a point of its domain. -/
def sectionEval (U : Opens X) (hp : p ∈ U) :
    (holomorphicStructureSheafModules I X).obj.obj (op U) →ₗ[ℂ] ℂ where
  toFun f := f ⟨p, hp⟩
  map_add' _ _ := holomorphicStructureSheafModules.add_apply _ _ _
  map_smul' _ _ := holomorphicStructureSheafModules.smul_apply _ _ _

-- Supply the model arguments when using simp through the opaque section carriers.
/-- Point evaluation sends a section to its value. -/
@[simp]
theorem sectionEval_apply (U : Opens X) (hp : p ∈ U)
    (f : (holomorphicStructureSheafModules I X).obj.obj (op U)) :
    sectionEval I X p U hp f = f ⟨p, hp⟩ := (rfl)

/-- Evaluation of holomorphic module germs at their base point. -/
def stalkEval : TopCat.Presheaf.stalk (X := TopCat.of X)
    (holomorphicStructureSheafModules I X).obj p ⟶ ModuleCat.of ℂ ℂ :=
  colimit.desc _
    { pt := ModuleCat.of ℂ ℂ
      ι :=
        { app := fun U ↦ ModuleCat.ofHom (sectionEval I X p U.unop.1 U.unop.2)
          naturality := by
            intro U V h
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro f
            exact holomorphicStructureSheafModules.map_apply I X
              ((OpenNhds.inclusion (X := TopCat.of X) p).map h.unop).op f ⟨p, V.unop.2⟩ } }

/-- Evaluation after taking a germ is evaluation of the original section. -/
@[reassoc (attr := simp)]
theorem germ_stalkEval (U : Opens X) (hp : p ∈ U) :
    TopCat.Presheaf.germ (X := TopCat.of X)
      (holomorphicStructureSheafModules I X).obj U p hp ≫ stalkEval I X p =
      ModuleCat.ofHom (sectionEval I X p U hp) :=
  colimit.ι_desc _ _

variable [∀ U : Opens (TopCat.of X), Decidable (p ∈ U)]

/-- Evaluation of holomorphic sections as a morphism to the skyscraper sheaf at `p`. -/
def evaluationToSkyscraper : holomorphicStructureSheafModules I X ⟶
    skyscraperSheaf (X := TopCat.of X) p (ModuleCat.of ℂ ℂ) :=
  ⟨StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
    (X := TopCat.of X) (𝓕 := (holomorphicStructureSheafModules I X).obj) p (stalkEval I X p)⟩

/-- On an open set containing `p`, skyscraper evaluation is ordinary point evaluation. -/
theorem evaluationToSkyscraper_app_of_mem (U : Opens X) (hp : p ∈ U) :
    (evaluationToSkyscraper I X p).hom.app (op U) =
      ModuleCat.ofHom (sectionEval I X p U hp) ≫
        eqToHom (by simp only [skyscraperSheaf_obj_obj, ite_eq_left hp]) := by
  simp only [evaluationToSkyscraper,
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app,
    ← Category.assoc, germ_stalkEval]
  exact dite_eq_left hp

private theorem evaluationToSkyscraper_app_eq_of_not_mem (U : Opens X) (hp : p ∉ U)
    (f : (holomorphicStructureSheafModules I X).obj.obj (op U))
    (c : (skyscraperSheaf (X := TopCat.of X) p (ModuleCat.of ℂ ℂ)).obj.obj (op U)) :
    (evaluationToSkyscraper I X p).hom.app (op U) f = c :=
  (ModuleCat.isZero_iff_subsingleton.mp
    (isTerminalSkyscraperSheafObjObjOfNotMem
      (X := TopCat.of X) (p₀ := p) (U := op U) (A := ModuleCat.of ℂ ℂ) hp).isZero).elim _ _

/-- Evaluation onto the skyscraper is surjective on every open set. -/
theorem evaluationToSkyscraper_app_surjective (U : Opens X) :
    Function.Surjective ((evaluationToSkyscraper I X p).hom.app (op U)) := by
  by_cases hp : p ∈ U
  · rw [evaluationToSkyscraper_app_of_mem I X p U hp]
    rw [ConcreteCategory.coe_comp]
    apply Function.Surjective.comp (ConcreteCategory.bijective_of_isIso _).2
    intro c
    refine ⟨holomorphicStructureSheafModules.ofContMDiff (fun _ : U ↦ c) contMDiff_const, ?_⟩
    exact holomorphicStructureSheafModules.ofContMDiff_apply _ _ _
  · intro c
    exact ⟨0, evaluationToSkyscraper_app_eq_of_not_mem I X p U hp 0 c⟩

/-- A section maps to zero under skyscraper evaluation precisely when it vanishes at `p`
if `p` belongs to its domain. -/
@[simp]
theorem evaluationToSkyscraper_app_eq_zero_iff (U : Opens X)
    (f : (holomorphicStructureSheafModules I X).obj.obj (op U)) :
    (evaluationToSkyscraper I X p).hom.app (op U) f = 0 ↔
      ∀ hp : p ∈ U, f ⟨p, hp⟩ = 0 := by
  by_cases hp : p ∈ U
  · rw [evaluationToSkyscraper_app_of_mem I X p U hp]
    rw [ConcreteCategory.comp_apply]
    rw [LinearMap.map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1]
    exact ⟨fun h _ ↦ h, fun h ↦ h hp⟩
  · exact iff_of_true (evaluationToSkyscraper_app_eq_of_not_mem I X p U hp f 0)
      (fun h ↦ (hp h).elim)

/-- On every open set, the functions vanishing at `p` are exactly the kernel of evaluation. -/
theorem exact_vanishingSheafι_evaluationToSkyscraper_app (U : Opens X) :
    Function.Exact ((vanishingSheafι I X (Finsupp.single p 1)).hom.app (op U))
      ((evaluationToSkyscraper I X p).hom.app (op U)) := by
  intro f
  rw [evaluationToSkyscraper_app_eq_zero_iff]
  constructor
  · intro hf
    let s := holomorphicStructureSheafModules.sectionsLinearEquiv I X (op U) f
    have hs : s ∈ vanishingIdeal I X (Finsupp.single p 1) U := by
      rw [mem_vanishingIdeal_single_one]
      intro hp
      simpa only [s, holomorphicStructureSheafModules.sectionsLinearEquiv_apply] using hf hp
    refine ⟨(vanishingSheafSectionsEquiv I X _ U).symm ⟨s, hs⟩, ?_⟩
    apply holomorphicStructureSheafModules.ext
    intro x
    rw [vanishingSheafι_app_apply, LinearEquiv.apply_symm_apply]
    exact holomorphicStructureSheafModules.sectionsLinearEquiv_apply I X (op U) f x
  · rintro ⟨g, rfl⟩ hp
    rw [vanishingSheafι_app_apply]
    exact (mem_vanishingIdeal_single_one I X p U _).mp
      (vanishingSheafSectionsEquiv I X _ U g).2 hp

/-- The inclusion of functions vanishing at `p` followed by evaluation is zero. -/
@[reassoc (attr := simp)]
theorem vanishingSheafι_evaluationToSkyscraper :
    vanishingSheafι I X (Finsupp.single p 1) ≫ evaluationToSkyscraper I X p = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  -- The sheaf zero and the pointwise ModuleCat zero have different bundled presentations.
  change (evaluationToSkyscraper I X p).hom.app U
    ((vanishingSheafι I X (Finsupp.single p 1)).hom.app U f) = 0
  exact (exact_vanishingSheafι_evaluationToSkyscraper_app I X p U.unop).apply_apply_eq_zero f

/-- The point-evaluation complex `𝓘_p → 𝒪 → ℂ_p`. -/
def pointEvaluationSequence : ShortComplex (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of X)) :=
  ShortComplex.mk (vanishingSheafι I X (Finsupp.single p 1)) (evaluationToSkyscraper I X p)
    (vanishingSheafι_evaluationToSkyscraper I X p)

/-- The vanishing sheaf is the first object of the point-evaluation complex. -/
@[simp]
theorem pointEvaluationSequence_X₁ :
    (pointEvaluationSequence I X p).X₁ = vanishingSheaf I X (Finsupp.single p 1) := (rfl)

/-- The holomorphic module sheaf is the middle object of the point-evaluation complex. -/
@[simp]
theorem pointEvaluationSequence_X₂ :
    (pointEvaluationSequence I X p).X₂ = holomorphicStructureSheafModules I X := (rfl)

/-- The skyscraper sheaf is the last object of the point-evaluation complex. -/
@[simp]
theorem pointEvaluationSequence_X₃ : (pointEvaluationSequence I X p).X₃ =
    skyscraperSheaf (X := TopCat.of X) p (ModuleCat.of ℂ ℂ) := (rfl)

-- Transport along the object equations keeps these arrow lemmas usable without exposing the def.
/-- The first arrow of the point-evaluation complex is inclusion. -/
@[simp]
theorem pointEvaluationSequence_f : (pointEvaluationSequence I X p).f =
    eqToHom (pointEvaluationSequence_X₁ I X p) ≫ vanishingSheafι I X (Finsupp.single p 1) ≫
      eqToHom (pointEvaluationSequence_X₂ I X p).symm := (rfl)

/-- The second arrow of the point-evaluation complex is evaluation. -/
@[simp]
theorem pointEvaluationSequence_g : (pointEvaluationSequence I X p).g =
    eqToHom (pointEvaluationSequence_X₂ I X p) ≫ evaluationToSkyscraper I X p ≫
      eqToHom (pointEvaluationSequence_X₃ I X p).symm := (rfl)

/-- The objects and arrows of the point-evaluation complex. -/
theorem pointEvaluationSequence_def : pointEvaluationSequence I X p =
    ShortComplex.mk (vanishingSheafι I X (Finsupp.single p 1)) (evaluationToSkyscraper I X p)
      (vanishingSheafι_evaluationToSkyscraper I X p) := (rfl)

/-- The ideal sheaf of `p` is the categorical kernel of point evaluation. -/
def isLimitPointEvaluationKernel : IsLimit (KernelFork.ofι
    (vanishingSheafι I X (Finsupp.single p 1))
    (vanishingSheafι_evaluationToSkyscraper I X p)) := by
  let F := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat ℂ)
  apply isLimitOfReflects F
  apply evaluationJointlyReflectsLimits
  intro U
  -- Select the functor-category zero instance explicitly across the presheaf wrapper.
  letI := Functor.preservesZeroMorphisms_evaluation_obj (C := ModuleCat ℂ) U
  have : (F ⋙ (evaluation _ (ModuleCat ℂ)).obj U).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_comp
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat ℂ)) _
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (vanishingSheafι I X (Finsupp.single p 1))
      (vanishingSheafι_evaluationToSkyscraper I X p))
    (F ⋙ (evaluation _ _).obj U)).symm <|
    ModuleCat.isLimitKernelFork _ _ (exact_vanishingSheafι_evaluationToSkyscraper_app I X p U.unop)
      (vanishingSheafι_app_injective I X _ U.unop)

/-- Evaluation onto the skyscraper sheaf is an epimorphism. -/
instance evaluationToSkyscraper_epi : Epi (evaluationToSkyscraper I X p) := by
  have (U : (Opens X)ᵒᵖ) : Epi ((evaluationToSkyscraper I X p).hom.app U) :=
    ConcreteCategory.epi_of_surjective _ (evaluationToSkyscraper_app_surjective I X p U.unop)
  exact (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat ℂ)).epi_of_epi_map
    (NatTrans.epi_of_epi_app (evaluationToSkyscraper I X p).hom)

/-- **The point-evaluation exact sequence** `0 → 𝓘_p → 𝒪 → ℂ_p → 0`. -/
theorem pointEvaluationSequence_shortExact : (pointEvaluationSequence I X p).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (isLimitPointEvaluationKernel I X p)
  mono_f := inferInstanceAs (Mono (vanishingSheafι I X (Finsupp.single p 1)))
  epi_g := inferInstanceAs (Epi (evaluationToSkyscraper I X p))

end TauCeti.holomorphicStructureSheaf
