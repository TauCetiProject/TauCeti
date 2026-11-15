/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.RestrictedYoneda

/-!
# Finitely presented modules as finitely presented functors

For a ring `R`, a module is finitely presented exactly when it is the cokernel of a morphism between
finitely generated projective modules. So the Yoneda description of the finitely presented functors
on a category of projective objects identifies the finitely presented `R`-modules with
`mod (proj R)`, the finitely presented functors on the category of finitely generated projective
`R`-modules. Evaluating the functor attached to a module at the regular module `R` recovers the
underlying abelian group of the module.

## Main declarations

* `TauCeti.finitePresentationModules`: the finitely presented modules, as a property of objects of
  `ModuleCat R`.
* `TauCeti.presented_finiteProjectiveModules`: the finitely presented modules are the modules with a
  presentation by finitely generated projective modules.
* `TauCeti.finitePresentationEquivalenceMod`: the equivalence between the finitely presented
  `R`-modules and `mod (proj R)`.
* `TauCeti.finitePresentationEquivalenceModCompEvaluationIso`: the composite of this equivalence
  with evaluation at `R` is the underlying abelian group of a module.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace TauCeti

variable (R : Type u) [Ring R]

/-- The object property of being a finitely presented module. -/
def finitePresentationModules : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.FinitePresentation R M

variable {R} in
@[simp]
theorem finitePresentationModules_iff {M : ModuleCat.{u} R} :
    finitePresentationModules R M ↔ Module.FinitePresentation R M :=
  Iff.rfl

/-- A module is finitely presented exactly when it is the cokernel of a morphism between finitely
generated projective modules. -/
theorem presented_finiteProjectiveModules :
    (finiteProjectiveModules R).presented = finitePresentationModules R := by
  ext M
  constructor
  · rintro @⟨A, B, f, c, hc, hA, hB⟩
    obtain ⟨hA, -⟩ := finiteProjectiveModules_iff.1 hA
    obtain ⟨hB, hB'⟩ := finiteProjectiveModules_iff.1 hB
    have hepi : Epi c.π := Cofork.IsColimit.epi hc
    have hS : (ShortComplex.mk f c.π c.condition).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _)))
    have := Module.finitePresentation_of_projective R B
    refine Module.finitePresentation_of_surjective c.π.hom
      ((ModuleCat.epi_iff_surjective _).1 hepi) ?_
    rw [← (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 hS]
    exact Module.Finite.iff_fg.1 inferInstance
  · intro hM
    rw [finitePresentationModules_iff] at hM
    obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' R M
    let S : ShortComplex (ModuleCat.{u} R) :=
      .mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (LinearMap.ext hfg.apply_apply_eq_zero))
    have hS : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hg
    have hf : MorphismProperty.ofObjectProperty _ _ S.f :=
      ⟨finiteProjectiveModules_iff.2 ⟨inferInstanceAs (Module.Finite R (Fin m → R)),
          inferInstanceAs (Module.Projective R (Fin m → R))⟩,
        finiteProjectiveModules_iff.2 ⟨inferInstanceAs (Module.Finite R (Fin n → R)),
          inferInstanceAs (Module.Projective R (Fin n → R))⟩⟩
    exact (MorphismProperty.cokernels.of_isColimit S.f _ hS.gIsCokernel hf :)

instance : (finitePresentationModules R).IsClosedUnderIsomorphisms :=
  presented_finiteProjectiveModules R ▸ inferInstance

/-- **The finitely presented modules are `mod (proj R)`.** The functor `M ↦ (-, M)|_{proj R}` is an
equivalence from the finitely presented `R`-modules to the finitely presented functors on the
finitely generated projective `R`-modules. -/
noncomputable def finitePresentationEquivalenceMod :
    (finitePresentationModules R).FullSubcategory ≌
      (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory :=
  ObjectProperty.equivalenceMod (finiteProjectiveModules_le_categoryTheory_isProjective R)
    (presented_finiteProjectiveModules R).symm

/-- The regular module `R`, as a finitely generated projective `R`-module. -/
def finiteProjectiveModulesRegular : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R R, finiteProjectiveModules_iff.2
    ⟨inferInstanceAs (Module.Finite R R), inferInstanceAs (Module.Projective R R)⟩⟩

/-- The functor of `finitePresentationEquivalenceMod` is `M ↦ (-, M)|_{proj R}`. -/
noncomputable def finitePresentationEquivalenceModCompιIso :
    (finitePresentationEquivalenceMod R).functor ⋙ (isFinitelyPresentedFunctor _).ι ≅
      (finitePresentationModules R).ι ⋙ (finiteProjectiveModules R).restrictedPreadditiveYoneda :=
  ObjectProperty.equivalenceModCompιIso _ _

/-- The functor attached to a finitely presented `R`-module `M` takes the value `(R, M)` at the
regular module, and `(R, M)` is the underlying abelian group of `M`, naturally in `M`. -/
noncomputable def finitePresentationEquivalenceModCompEvaluationIso :
    ((finitePresentationEquivalenceMod R).functor ⋙ (isFinitelyPresentedFunctor _).ι) ⋙
        (evaluation _ _).obj (op (finiteProjectiveModulesRegular R)) ≅
      (finitePresentationModules R).ι ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight (finitePresentationEquivalenceModCompιIso R) _ ≪≫
    NatIso.ofComponents (fun M ↦ (ModuleCat.homAddEquiv.trans
      (LinearMap.ringLmapEquivSelf R ℕ M.obj).toAddEquiv).toAddCommGrpIso) fun {M N} f ↦ by
      ext (g : ModuleCat.of R R ⟶ M.obj)
      -- Both sides are `f (g 1)`.
      rfl

end TauCeti
