/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import TauCeti.Algebra.Category.ModuleCat.Presheaf.FreeYoneda

/-!
# Free sheaves of modules on representables

For a sheaf of rings `R`, the sheafification of the free `R`-module presheaf on a
representable represents sections of module sheaves. A monomorphism of representables
induces a monomorphism between these free module sheaves. In particular, on the site
of open subsets, these monomorphisms allow injective module sheaves to extend sections.
Since sheafification is left adjoint to the faithful inclusion of sheaves of modules into
presheaves of modules, it carries Mathlib's separating family of free presheaves of modules on
representables to a separating (`SheafOfModules.isSeparating_freeYonedaFunctor`) and detecting
family of the category of sheaves of modules. Their flatness over a sheaf of commutative rings is in
`TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Flat`.

The construction combines Mathlib's `PresheafOfModules.freeYonedaEquiv` with
`PresheafOfModules.sheafificationAdjunction`; the separating family is the sheaf analogue of
Mathlib's `PresheafOfModules.freeYoneda.isSeparating`.

## References

* The Stacks Project, Modules on Sites, Section 18.19 (Tag 03DH).
-/

public section

open CategoryTheory Opposite

universe v u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{v})
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

section

variable [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The free sheaf of `R`-modules on each representable presheaf. -/
def freeYonedaFunctor : C ⥤ SheafOfModules.{v} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

/-- The free sheaf of `R`-modules on `U` is the sheafification of the free presheaf of modules
on the presheaf represented by `U`. -/
lemma freeYonedaFunctor_obj (U : C) :
    (freeYonedaFunctor R).obj U = (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.free R.obj).obj (yoneda.obj U)) :=
  (rfl)

/-- A morphism from the free sheaf on `U` to `M` is a section of `M` over `U`. -/
def freeYonedaEquiv (U : C) (M : SheafOfModules.{v} R) :
    ((freeYonedaFunctor R).obj U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeYonedaEquiv

/-- The sections correspondence respects morphisms of coefficient sheaves. -/
@[simp]
lemma freeYonedaEquiv_comp {U : C} {M N : SheafOfModules.{v} R}
    (m : (freeYonedaFunctor R).obj U ⟶ M) (φ : M ⟶ N) :
    freeYonedaEquiv R U N (m ≫ φ) = φ.val.app (op U) (freeYonedaEquiv R U M m) := by
  rfl

/-- Precomposition with a map of representables corresponds to restriction of sections.

This is a named equation: coefficient-composition simplification selects a different
presentation of the dependent module carrier, so this statement has no robust canonical
simp form. -/
lemma freeYonedaEquiv_naturality {U V : C} (i : U ⟶ V) (M : SheafOfModules.{v} R)
    (m : (freeYonedaFunctor R).obj V ⟶ M) :
    freeYonedaEquiv R U M ((freeYonedaFunctor R).map i ≫ m) =
      M.val.map i.op (freeYonedaEquiv R V M m) := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left
    ((PresheafOfModules.free R.obj).map (yoneda.map i)) m
  -- Pin the scalar-restriction carrier in the adjunction before evaluating its morphisms.
  change PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map
          ((PresheafOfModules.free R.obj).map (yoneda.map i)) ≫ m)) = _
  rw [h]
  -- The free-Yoneda correspondence evaluates the morphism at the identity generator.
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ m).app
      (op U)) (((ModuleCat.free (R.obj.obj (op U))).map ((yoneda.map i).app (op U)))
        (ModuleCat.freeMk (𝟙 U))) =
    M.val.map i.op
      ((((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ m).app
        (op V)) (ModuleCat.freeMk (𝟙 V)))
  rw [ModuleCat.free_map_apply]
  have hn := TauCeti.PresheafOfModules.freeYonedaEquiv_symm_app_freeMk
    (PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ m)) i
  rw [Equiv.symm_apply_apply] at hn
  -- Restriction of scalars along the identity changes only the module presentation.
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ m).app
      (op U)) (ModuleCat.freeMk i) =
    M.val.map i.op
      ((((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ m).app
        (op V)) (ModuleCat.freeMk (𝟙 V))) at hn
  simpa using hn

/-- The free module sheaves on representables form a separating family: two morphisms
`M ⟶ N` agreeing after precomposition with every morphism out of every `freeYonedaFunctor R`
object are equal, since such morphisms are exactly the local sections of `M`. -/
lemma isSeparating_freeYonedaFunctor :
    ObjectProperty.IsSeparating (.ofObj (freeYonedaFunctor R).obj) := by
  -- Sheafification is left adjoint to a faithful functor, so it carries Mathlib's separating
  -- family of free presheaves of modules to a separating family.
  refine ((PresheafOfModules.freeYoneda.isSeparating R.obj).strictMap_leftAdjoint
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))).of_le ?_
  rintro _ ⟨_, ⟨U⟩⟩
  exact ⟨U⟩

end

variable [HasSheafify J AddCommGrpCat.{v}]

/-- Free module sheaves carry monomorphisms between representables to monomorphisms. -/
instance mono_freeYonedaFunctor_map {U V : C} (i : U ⟶ V) [Mono i] :
    Mono ((freeYonedaFunctor R).map i) := by
  have hmono : Mono ((PresheafOfModules.free R.obj).map (yoneda.map i)) := by
    apply PresheafOfModules.mono_of_injective
    intro W
    -- The component is the free-module map on postcomposition by `i`.
    exact Finsupp.mapDomain_injective (fun f g h ↦ (cancel_mono i).mp h)
  exact Functor.map_mono (PresheafOfModules.sheafification (𝟙 R.obj)) _

/-- The free module sheaves on representables form a detecting family. -/
lemma isDetecting_freeYonedaFunctor :
    ObjectProperty.IsDetecting (.ofObj (freeYonedaFunctor R).obj) :=
  (isSeparating_freeYonedaFunctor R).isDetecting

end SheafOfModules
