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

attribute [local instance] Classical.propDecidable

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

/-- Evaluation of holomorphic sections as a morphism to the skyscraper sheaf at `p`. -/
def evaluationToSkyscraper : holomorphicStructureSheafModules I X ⟶
    skyscraperSheaf (X := TopCat.of X) p (ModuleCat.of ℂ ℂ) := by
  classical
  exact { hom := {
    app := fun U ↦ if hp : p ∈ U.unop then
      ModuleCat.ofHom (sectionEval I X p U.unop hp) ≫
        eqToHom (by simp only [skyscraperSheaf_obj_obj, ite_eq_left hp])
      else 0
    naturality := by
      intro U V h
      by_cases hpV : p ∈ V.unop
      · have hpU : p ∈ U.unop := h.unop.le hpV
        simp only [hpV, hpU, ↓reduceDIte, skyscraperSheaf_obj_map]
        -- Casts between the bundled opens require unfolding the TopCat carrier here.
        erw [Category.assoc, eqToHom_trans, ← Category.assoc, cancel_mono]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
        -- Expose section evaluation across the op/unop presentation of the domain.
        change ((holomorphicStructureSheafModules I X).obj.map h f) ⟨p, hpV⟩ = f ⟨p, hpU⟩
        exact holomorphicStructureSheafModules.map_apply I X h f ⟨p, hpV⟩
      · have hz : IsZero ((skyscraperSheaf (X := TopCat.of X) p
            (ModuleCat.of ℂ ℂ)).obj.obj V) := by
          simp only [skyscraperSheaf_obj_obj, ite_eq_right hpV]
          exact (isZero_zero _).of_iso HasZeroObject.zeroIsoTerminal.symm
        exact hz.eq_of_tgt _ _ } }

/-- On an open set containing `p`, skyscraper evaluation is ordinary point evaluation. -/
theorem evaluationToSkyscraper_app_of_mem (U : Opens X) (hp : p ∈ U) :
    (evaluationToSkyscraper I X p).hom.app (op U) =
      ModuleCat.ofHom (sectionEval I X p U hp) ≫
        eqToHom (by classical simp only [skyscraperSheaf_obj_obj, ite_eq_left hp]) := by
  classical
  simp only [evaluationToSkyscraper, dite_eq_left hp]

/-- Evaluation onto the skyscraper is surjective on every open set. -/
theorem evaluationToSkyscraper_app_surjective (U : Opens X) :
    Function.Surjective ((evaluationToSkyscraper I X p).hom.app (op U)) := by
  classical
  by_cases hp : p ∈ U
  · rw [evaluationToSkyscraper_app_of_mem I X p U hp]
    rw [ConcreteCategory.coe_comp]
    apply Function.Surjective.comp (ConcreteCategory.bijective_of_isIso
      (eqToHom (C := ModuleCat ℂ) (by simp only [skyscraperSheaf_obj_obj, ite_eq_left hp]))).2
    intro c
    refine ⟨holomorphicStructureSheafModules.ofContMDiff (fun _ : U ↦ c) contMDiff_const, ?_⟩
    exact holomorphicStructureSheafModules.ofContMDiff_apply _ _ _
  · have hz : IsZero ((skyscraperSheaf (X := TopCat.of X) p
        (ModuleCat.of ℂ ℂ)).obj.obj (op U)) := by
      simp only [skyscraperSheaf_obj_obj, ite_eq_right hp]
      exact (isZero_zero _).of_iso HasZeroObject.zeroIsoTerminal.symm
    intro c
    exact ⟨0, (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _⟩

/-- A section maps to zero under skyscraper evaluation precisely when it vanishes at `p`
if `p` belongs to its domain. -/
@[simp]
theorem evaluationToSkyscraper_app_eq_zero_iff (U : Opens X)
    (f : (holomorphicStructureSheafModules I X).obj.obj (op U)) :
    (evaluationToSkyscraper I X p).hom.app (op U) f = 0 ↔
      ∀ hp : p ∈ U, f ⟨p, hp⟩ = 0 := by
  classical
  by_cases hp : p ∈ U
  · rw [evaluationToSkyscraper_app_of_mem I X p U hp]
    rw [ConcreteCategory.comp_apply]
    let e : ModuleCat.of ℂ ℂ ≅ (skyscraperSheaf (X := TopCat.of X) p
        (ModuleCat.of ℂ ℂ)).obj.obj (op U) :=
      eqToIso (by simp only [skyscraperSheaf_obj_obj, ite_eq_left hp])
    -- Name the transport to avoid rewriting through the opaque skyscraper carrier.
    change e.hom.hom (sectionEval I X p U hp f) = 0 ↔ _
    rw [LinearMap.map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.hom).1]
    exact ⟨fun h _ ↦ h, fun h ↦ h hp⟩
  · have hz : IsZero ((skyscraperSheaf (X := TopCat.of X) p
        (ModuleCat.of ℂ ℂ)).obj.obj (op U)) := by
      simp only [skyscraperSheaf_obj_obj, ite_eq_right hp]
      exact (isZero_zero _).of_iso HasZeroObject.zeroIsoTerminal.symm
    exact iff_of_true ((ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _) (fun h ↦ (hp h).elim)

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
  rw [evaluationToSkyscraper_app_eq_zero_iff]
  intro hp
  rw [vanishingSheafι_app_apply]
  exact (mem_vanishingIdeal_single_one I X p U.unop _).mp
    (vanishingSheafSectionsEquiv I X _ U.unop f).2 hp

/-- The point-evaluation complex `𝓘_p → 𝒪 → ℂ_p`. -/
def pointEvaluationSequence : ShortComplex (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of X)) :=
  ShortComplex.mk (vanishingSheafι I X (Finsupp.single p 1)) (evaluationToSkyscraper I X p)
    (vanishingSheafι_evaluationToSkyscraper I X p)

/-- The objects and arrows of the point-evaluation complex. -/
theorem pointEvaluationSequence_def : pointEvaluationSequence I X p =
    ShortComplex.mk (vanishingSheafι I X (Finsupp.single p 1)) (evaluationToSkyscraper I X p)
      (vanishingSheafι_evaluationToSkyscraper I X p) := (rfl)

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

/-- The ideal sheaf of `p` is the categorical kernel of point evaluation. -/
def isLimitPointEvaluationKernel : IsLimit (KernelFork.ofι
    (vanishingSheafι I X (Finsupp.single p 1))
    (vanishingSheafι_evaluationToSkyscraper I X p)) := by
  let F := TopCat.Sheaf.forget (ModuleCat ℂ) (TopCat.of X)
  apply isLimitOfReflects F
  apply evaluationJointlyReflectsLimits
  intro U
  have : (F ⋙ (evaluation _ (ModuleCat ℂ)).obj U).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
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
