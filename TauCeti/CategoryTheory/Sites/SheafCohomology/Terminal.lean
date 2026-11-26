/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.ConstantSheaf

public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

/-!
# Sheaf cohomology at a terminal object

Mathlib carries two accounts of the cohomology of an abelian sheaf `F` on a site `(C, J)`:

* `CategoryTheory.Sheaf.H F n`, the `Ext`-groups from the constant sheaf `ℤ`, which is the
  cohomology of the site as a whole;
* `CategoryTheory.Sheaf.H' F n X`, the `Ext`-groups from the sheafification of the free abelian
  presheaf on `yoneda.obj X`, which is the cohomology of the object `X`.

They agree when `X` is a terminal object, and this file supplies that comparison. The abstract
Mayer-Vietoris sequence of `Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris` is stated
in terms of `Sheaf.H'`, so the comparison is what lets a covering of the whole site compute
`Sheaf.H`. The source comparison identifies the free generator with the constant section one,
as characterized by `Limits.IsTerminal.freeYonedaSheafSectionsEquiv_inv_comp`. This makes the
terminal-object comparison compatible with inverse image on sheaf cohomology.

## Main declarations

* `CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH`: the comparison as a natural
  isomorphism in the coefficient sheaf;
* `CategoryTheory.Sheaf.cohomologyPresheafObjIsoH`: its specialization
  `Hⁿ(T, F) ≅ Hⁿ(F)` at a terminal object `T`, as an isomorphism of abelian groups;
* `CategoryTheory.Sheaf.H.equiv₀_cohomologyPresheafObjIsoH_hom_apply`: in degree `0` the
  comparison is the identity on sections over `T`.

Terminal-object comparisons identify the native section restriction and cohomology maps.
-/

public section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

noncomputable section

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

-- Mathlib's `extFunctorObj` and `functorH` use definitionally equal object and map data.
-- Naming that identification here isolates the definitional coincidence used below.
private def extFunctorObjIsoFunctorH (n : ℕ) :
    (_root_.CategoryTheory.Abelian.extFunctor n).obj
        (op ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)))) ≅
      _root_.CategoryTheory.Sheaf.functorH J n :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      intros
      ext
      rfl)

end

end CategoryTheory

end TauCeti

namespace CategoryTheory.Limits.IsTerminal

open TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

private noncomputable def constantIntegersCorepresentableBy {T : C} (hT : IsTerminal T) :
    ((sheafSections J AddCommGrpCat.{v}).obj (Opposite.op T) ⋙
      forget AddCommGrpCat).CorepresentableBy
      ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ))) :=
  ((constantSheafAdj J AddCommGrpCat.{v} hT).corepresentableBy _).ofIso
    (Functor.isoWhiskerLeft _ AddCommGrpCat.coyonedaObjIsoForget)

/-- The free abelian sheaf on a terminal object is the constant sheaf of integers. -/
noncomputable def freeYonedaSheafIsoConstant {T : C} (hT : IsTerminal T) :
    (freeYonedaSheafFunctor J).obj T ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)) :=
  (freeYonedaSheafCorepresentableBy J T).uniqueUpToIso
    (constantIntegersCorepresentableBy hT)

/-- The terminal-object comparison identifies the free generator with the constant section
one, so precomposition with its inverse preserves the represented section. -/
lemma freeYonedaSheafSectionsEquiv_inv_comp {T : C} (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{v}) (a : (freeYonedaSheafFunctor J).obj T ⟶ F) :
    AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ _
          (hT.freeYonedaSheafIsoConstant.inv ≫ a)) =
      freeYonedaSheafSectionsEquiv J T F a := by
  let e := constantIntegersCorepresentableBy (J := J) hT
  have he : hT.freeYonedaSheafIsoConstant.inv =
      e.homEquiv.symm ((freeYonedaSheafCorepresentableBy J T).homEquiv (𝟙 _)) := rfl
  -- The left side is the corepresentation bijection for the constant integer sheaf.
  change e.homEquiv (hT.freeYonedaSheafIsoConstant.inv ≫ a) = _
  rw [he, e.homEquiv_comp, Equiv.apply_symm_apply,
    freeYonedaSheafCorepresentableBy_homEquiv]
  exact (freeYonedaSheafSectionsEquiv_naturality_right J (𝟙 _) a).symm.trans
    (congrArg (freeYonedaSheafSectionsEquiv J T F) (Category.id_comp a))

end CategoryTheory.Limits.IsTerminal

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (J) in
/-- At a terminal object `T`, the cohomology presheaf evaluated at `T` is the cohomology of the
site, naturally in the coefficient sheaf. -/
noncomputable def cohomologyPresheafEvaluationIsoFunctorH (n : ℕ) {T : C} (hT : IsTerminal T) :
    cohomologyPresheafFunctor J n ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op T) ≅
      functorH J n :=
  (Abelian.extFunctor n).mapIso
      hT.freeYonedaSheafIsoConstant.symm.op ≪≫
    TauCeti.CategoryTheory.extFunctorObjIsoFunctorH n

/-- At a terminal object, the cohomology of the object is the cohomology of the site. -/
noncomputable abbrev cohomologyPresheafObjIsoH (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {T : C} (hT : IsTerminal T) :
    H' F n T ≅ AddCommGrpCat.of (H F n) :=
  (cohomologyPresheafEvaluationIsoFunctorH J n hT).app F

/-- The terminal-object comparison is precomposition of extensions with the inverse
of the free-sheaf comparison. -/
lemma cohomologyPresheafObjIsoH_hom_apply (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {T : C} (hT : IsTerminal T) (x : F.H' n T) :
    (F.cohomologyPresheafObjIsoH n hT).hom x =
      (Abelian.Ext.mk₀ hT.freeYonedaSheafIsoConstant.inv).comp x (zero_add n) :=
  (rfl)

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- In degree `0`, the terminal-object comparison is compatible with the identifications of both
`H⁰(T, F)` and `H⁰(F)` with the sections of `F` over the terminal object `T`. -/
lemma H.equiv₀_cohomologyPresheafObjIsoH_hom_apply (F : Sheaf J AddCommGrpCat.{v})
    {T : C} (hT : IsTerminal T) (x : F.H' 0 T) :
    H.equiv₀ F hT ((F.cohomologyPresheafObjIsoH 0 hT).hom x) =
      TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv F T x := by
  rw [cohomologyPresheafObjIsoH_hom_apply, TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv_apply,
    ← hT.freeYonedaSheafSectionsEquiv_inv_comp]
  exact congrArg (fun a ↦ AddCommGrpCat.uliftZMultiplesAddEquiv _
    ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ _ a))
    (TauCeti.ext_addEquiv₀_mk₀_comp _ _)

end CategoryTheory.Sheaf

/-! ### Terminal comparison and its actual global-sections component -/

universe u' v'
open TauCeti.CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.Limits.IsTerminal
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J} in
/-- The free-Yoneda identifications at terminal objects commute with their unique maps. -/
lemma freeYonedaSheafIsoConstant_naturality {S T : C} (hS : IsTerminal S)
    (hT : IsTerminal T) (i : S ⟶ T) :
    (freeYonedaSheafFunctor J).map i ≫ hT.freeYonedaSheafIsoConstant.hom =
      hS.freeYonedaSheafIsoConstant.hom := by
  let Z := (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ))
  have hTn := hT.freeYonedaSheafSectionsEquiv_inv_comp (J := J) Z
    (hT.freeYonedaSheafIsoConstant.hom)
  have hSn := hS.freeYonedaSheafSectionsEquiv_inv_comp (J := J) Z
    (hS.freeYonedaSheafIsoConstant.hom)
  rw [Iso.inv_hom_id] at hTn hSn
  apply (freeYonedaSheafSectionsEquiv J S Z).injective
  rw [freeYonedaSheafSectionsEquiv_naturality_left, ← hTn, ← hSn]
  exact ConcreteCategory.congr_hom
    (constantSheafAdj_homEquiv_comp_map J hS hT i
      (AddCommGrpCat.of (ULift ℤ)) Z (𝟙 Z)) (ULift.up (1 : ℤ))

end CategoryTheory.Limits.IsTerminal

namespace CategoryTheory.Sheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
variable {J} in
/-- Changing the terminal object transports cohomology by the actual restriction map. -/
lemma cohomologyPresheafObjIsoH_terminal_change (F : Sheaf J AddCommGrpCat.{v})
    {S T : C} (hS : IsTerminal S) (hT : IsTerminal T) (i : S ⟶ T)
    (n : ℕ) (x : F.H' n T) :
    (F.cohomologyPresheafObjIsoH n hS).inv ((F.cohomologyPresheafObjIsoH n hT).hom x) =
      (F.cohomologyPresheaf n).map i.op x := by
  let xE : Ext.{w} ((freeYonedaSheafFunctor J).obj T) F n := x
  -- The terminal comparison composes with the constant/free-Yoneda isomorphism in Ext;
  -- the cohomology presheaf map precomposes with the free-Yoneda map of `i`.
  change (Ext.mk₀ hS.freeYonedaSheafIsoConstant.hom).comp
      ((Ext.mk₀ hT.freeYonedaSheafIsoConstant.inv).comp xE (zero_add n)) (zero_add n) =
    (Ext.mk₀ ((freeYonedaSheafFunctor J).map i)).comp xE (zero_add n)
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  congr 1
  rw [← hS.freeYonedaSheafIsoConstant_naturality (J := J) hT i, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
end CategoryTheory.Sheaf
