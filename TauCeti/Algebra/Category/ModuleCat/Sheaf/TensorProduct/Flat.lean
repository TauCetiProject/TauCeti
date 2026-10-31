/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Flat
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Yoneda
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import TauCeti.CategoryTheory.Abelian.Exact

/-!
# Flatness of free module sheaves on representables

Let `R` be a sheaf of commutative rings on a small site. A sheaf of `R`-modules `M` is flat when
`M ⊗ -` is an exact functor, that is, when `tensorLeft M` preserves finite limits; this is the
condition Mathlib's `Module.Flat.iff_preservesFiniteLimits_tensorLeft` gives for modules.

The tensor product of sheaves of modules is the sheafification of the sectionwise tensor product,
and sheafification is exact. Hence if tensoring with a presheaf of modules `P` preserves
monomorphisms, so does tensoring with its sheafification
(`PresheafOfModules.preservesMonomorphisms_tensorLeft_sheafification_obj`). Tensoring with a sheaf
of modules is right exact, since it has a right adjoint, so preserving monomorphisms already makes
it exact (`CategoryTheory.Functor.preservesFiniteLimits_of_preservesMonomorphisms`, for any right
exact functor between abelian categories).
Hence the sheafification of a sectionwise flat presheaf of modules is flat
(`PresheafOfModulesOfCommRing.preservesFiniteLimits_tensorLeft_sheafification_obj_of_flat`).

Applied to the free presheaf of modules on a representable presheaf, which is sectionwise free,
this shows that the free module sheaf `SheafOfModules.freeYonedaFunctor R U` on an object `U` of
the site, the extension by zero `j_{U!} R|_U` of the structure sheaf, is flat
(`SheafOfModules.preservesFiniteLimits_tensorLeft_freeYonedaFunctor_obj`). Together with the
fact that these sheaves form a separating family (`SheafOfModules.isSeparating_freeYonedaFunctor`),
they provide flat generators of the category of sheaves of modules, from which flat resolutions
of complexes of sheaves of modules are built.

## References

* The Stacks Project, Modules on Sites, Section 18.28 (flat modules), in particular
  Lemma 18.28.7 (Tag 03EV).
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

open TauCeti.SheafOfModules

namespace PresheafOfModules

/-- If tensoring with a presheaf of modules `P` preserves monomorphisms, then so does tensoring
with its sheafification. -/
lemma preservesMonomorphisms_tensorLeft_sheafification_obj
    (P : PresheafOfModules.{u} (ringCatSheaf R).obj) [(tensorLeft P).PreservesMonomorphisms] :
    (tensorLeft ((sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj P)).PreservesMonomorphisms
    where
  preserves {M N} f _ := by
    let a := sheafification.{u} (𝟙 (ringCatSheaf R).obj)
    -- Up to the identifications `a.obj M.val ≅ M` and the tensor map of the monoidal functor
    -- `a`, the morphism `a.obj P ◁ f` is the sheafification of `P ◁ f.val`.
    let e : a.obj P ⊗ N ⟶ a.obj (P ⊗ N.val) :=
      (a.obj P ◁ (sheafificationIso _ N).inv) ≫ Functor.LaxMonoidal.μ a P N.val
    have hfac : (a.obj P ◁ f) ≫ e =
        ((a.obj P ◁ (sheafificationIso _ M).inv) ≫ Functor.LaxMonoidal.μ a P M.val) ≫
          a.map (P ◁ f.val) := by
      rw [← whiskerLeft_comp_assoc, sheafificationIso_inv_naturality, whiskerLeft_comp_assoc,
        Category.assoc, Functor.LaxMonoidal.μ_natural_right]
    have : Mono f.val := (SheafOfModules.forget _).map_mono f
    have : Mono (P ◁ f.val) := (tensorLeft P).map_mono f.val
    have : Mono ((a.obj P ◁ f) ≫ e) := by
      rw [hfac]
      infer_instance
    -- The goal `Mono ((tensorLeft (a.obj P)).map f)` is stated through `tensorLeft`.
    exact (mono_of_mono _ e : Mono (a.obj P ◁ f))

end PresheafOfModules

namespace PresheafOfModulesOfCommRing

/-- The sheafification of a presheaf of modules whose modules of sections are all flat is a flat
sheaf of modules: tensoring with it is exact. -/
instance preservesFiniteLimits_tensorLeft_sheafification_obj_of_flat
    (P : PresheafOfModulesOfCommRing.{u} R.obj) [∀ X, Module.Flat (R.obj.obj X) (P.obj X)] :
    PreservesFiniteLimits (tensorLeft
      ((PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj P)) := by
  -- The underlying presheaf of rings of `ringCatSheaf R` is `R.obj ⋙ forget₂ _ _` by definition,
  -- so presheaves of modules over it are `PresheafOfModulesOfCommRing R.obj`, with the same
  -- sectionwise tensor product.
  have : (tensorLeft (C := PresheafOfModules.{u} (ringCatSheaf R).obj) P).PreservesMonomorphisms :=
    inferInstanceAs (tensorLeft P).PreservesMonomorphisms
  have := PresheafOfModules.preservesMonomorphisms_tensorLeft_sheafification_obj (R := R) P
  -- Tensoring with a sheaf of modules is a left adjoint, hence right exact.
  exact Functor.preservesFiniteLimits_of_preservesMonomorphisms _

end PresheafOfModulesOfCommRing

namespace SheafOfModules

/-- The free module sheaf on an object `U` of the site is flat: tensoring with it is exact. -/
instance preservesFiniteLimits_tensorLeft_freeYonedaFunctor_obj (U : C) :
    PreservesFiniteLimits (tensorLeft ((freeYonedaFunctor (ringCatSheaf R)).obj U)) := by
  -- `freeYonedaFunctor` sheafifies the free presheaf of modules `freeObj (yoneda.obj U)`, which
  -- is sectionwise free over the rings of sections of `R`; it is read over `R.obj ⋙ forget₂ _ _`,
  -- the underlying presheaf of rings of `ringCatSheaf R` by definition.
  rw [freeYonedaFunctor_obj, PresheafOfModules.free_obj]
  exact PresheafOfModulesOfCommRing.preservesFiniteLimits_tensorLeft_sheafification_obj_of_flat
    (PresheafOfModules.freeObj (yoneda.obj U))

end SheafOfModules
