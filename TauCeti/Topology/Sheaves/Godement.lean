/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Skyscraper
public import TauCeti.Topology.Sheaves.Flasque.Products

/-!
# The Godement sheaf and the canonical flasque embedding

Let `C` be a category with colimits and products, and `X` a topological space. Taking all stalks of
a sheaf is a functor `stalksFunctor C X : X.Sheaf C ⥤ (X → C)` to families of objects indexed by
the points of `X`. It has the right adjoint `skyscraperProductFunctor C X`, which sends a family
`M` to the product `∏ₓ (iₓ)_* (M x)` of the skyscraper sheaves at the points of `X`
(`stalksSkyscraperProductAdjunction`). Informally, families indexed by `X` are the sheaves on `X`
with the discrete topology, and this is the adjunction `f^* ⊣ f_*` for the identity map `f` from
`X` with the discrete topology to `X`.

The composite `godement C X = stalksFunctor C X ⋙ skyscraperProductFunctor C X` is the *Godement
sheaf* functor `F ↦ ∏ₓ (iₓ)_* Fₓ`, and the unit of the adjunction is the canonical morphism
`toGodement C X : F ⟶ godement C X F`, whose coordinate at `x` sends a section over an open
containing `x` to its germ at `x` (`toGodement_app_π_hom_app`).

When `C` has a zero object every Godement sheaf is flasque (`isFlasque_godement_obj`): the
restriction maps of a skyscraper presheaf are split epimorphisms
(`isSplitEpi_skyscraperPresheaf_map`), and so are their products. At each point `x` the map of
stalks `Fₓ ⟶ (godement C X F)ₓ` is a split monomorphism, retracted through the coordinate at `x`
(`isSplitMono_stalkFunctor_map_toGodement_app`), so for sheaves valued in a concrete category with
the usual stalk hypotheses, such as modules over a ring or abelian groups, `toGodement C X` is a
monomorphism (`mono_toGodement_app`). Thus every such sheaf embeds functorially in a flasque sheaf.
This embedding is the first step of the Godement resolution, which iterates it on cokernels.

## Main definitions

* `TopCat.Sheaf.stalksFunctor C X`: the family of all stalks of a sheaf.
* `TopCat.Sheaf.skyscraperProductFunctor C X`: the product of skyscraper sheaves of a family.
* `TopCat.Sheaf.stalksSkyscraperProductAdjunction C X`: the adjunction between them.
* `TopCat.Sheaf.godement C X`: the Godement sheaf functor `F ↦ ∏ₓ (iₓ)_* Fₓ`.
* `TopCat.Sheaf.toGodement C X`: the canonical morphism `F ⟶ godement C X F`.

## Main results

* `TopCat.Sheaf.toGodement_app_π`: the coordinate of `toGodement` at `x` is the unit of the
  adjunction between the stalk at `x` and the skyscraper sheaf at `x`.
* `TopCat.Sheaf.toGodement_app_π_hom_app`: this coordinate sends a section to its germ at `x`.
* `TopCat.Sheaf.isFlasque_godement_obj`: Godement sheaves are flasque.
* `TopCat.Sheaf.isSplitMono_stalkFunctor_map_toGodement_app`: `toGodement` is a split
  monomorphism on stalks.
* `TopCat.Sheaf.mono_toGodement_app`: `toGodement` is a monomorphism for sheaves valued in a
  concrete category.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Chapitre II, §4.3.
* The Stacks Project, Cohomology of Sheaves, Section 20.30 (Godement resolution), tag 0FKR.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace TopCat.Sheaf

section Adjunction

variable (C : Type*) [Category.{u} C] (X : TopCat.{u})

section Stalks

variable [HasColimits C]

/-- The family of all stalks of a sheaf on `X`, as a functor to families of objects of `C`
indexed by the points of `X`. -/
@[expose] def stalksFunctor : X.Sheaf C ⥤ (X → C) :=
  Functor.pi' fun x ↦ Sheaf.forget C X ⋙ Presheaf.stalkFunctor C x

/-- The value of `stalksFunctor C X` on `F` at `x` is the stalk of `F` at `x`. -/
@[simp]
theorem stalksFunctor_obj (F : X.Sheaf C) (x : X) :
    (stalksFunctor C X).obj F x = F.presheaf.stalk x :=
  rfl

/-- The value of `stalksFunctor C X` on a morphism at `x` is its map of stalks at `x`. -/
@[simp]
theorem stalksFunctor_map {F G : X.Sheaf C} (α : F ⟶ G) (x : X) :
    (stalksFunctor C X).map α x = (Presheaf.stalkFunctor C x).map α.hom :=
  rfl

end Stalks

variable [HasProducts.{u} C]

open scoped Classical in
/-- The product `∏ₓ (iₓ)_* (M x)` of the skyscraper sheaves at the points of `X` of a family `M`
of objects of `C`, as a functor of the family. -/
abbrev skyscraperProductFunctor : (X → C) ⥤ X.Sheaf C where
  obj M := ∏ᶜ fun x ↦ (skyscraperSheafFunctor x).obj (M x)
  map f := Limits.Pi.map fun x ↦ (skyscraperSheafFunctor x).map (f x)
  map_id M := Pi.hom_ext _ _ fun x ↦ by simp
  map_comp f g := Pi.hom_ext _ _ fun x ↦ by simp

open scoped Classical in
/-- The value of `skyscraperProductFunctor C X` on `M` is the product of the skyscraper sheaves
`(iₓ)_* (M x)`. -/
@[simp]
theorem skyscraperProductFunctor_obj (M : X → C) :
    (skyscraperProductFunctor C X).obj M = ∏ᶜ fun x ↦ (skyscraperSheafFunctor x).obj (M x) :=
  rfl

variable [HasColimits C]

open scoped Classical in
/-- Morphisms from a sheaf `F` to `∏ₓ (iₓ)_* (M x)` are families of morphisms `Fₓ ⟶ M x`. -/
private def homEquiv (F : X.Sheaf C) (M : X → C) :
    ((stalksFunctor C X).obj F ⟶ M) ≃ (F ⟶ (skyscraperProductFunctor C X).obj M) where
  toFun f := Pi.lift fun x ↦ (stalkSkyscraperSheafAdjunction x).homEquiv _ _ (f x)
  invFun g x := ((stalkSkyscraperSheafAdjunction x).homEquiv _ _).symm (g ≫ Pi.π _ x)
  left_inv f := funext fun x ↦ by
    dsimp only [skyscraperProductFunctor_obj]
    rw [Pi.lift_comp_π]
    exact Equiv.symm_apply_apply _ _
  right_inv g := Pi.hom_ext _ _ fun x ↦ by
    dsimp only [skyscraperProductFunctor_obj]
    rw [Pi.lift_comp_π]
    exact Equiv.apply_symm_apply _ _

open scoped Classical in
private theorem homEquiv_apply_π {F : X.Sheaf C} {M : X → C}
    (f : (stalksFunctor C X).obj F ⟶ M) (x : X) :
    homEquiv C X F M f ≫ Pi.π _ x = (stalkSkyscraperSheafAdjunction x).homEquiv _ _ (f x) :=
  Pi.lift_comp_π _ x

open scoped Classical in
private theorem homEquiv_symm_apply {F : X.Sheaf C} {M : X → C}
    (g : F ⟶ (skyscraperProductFunctor C X).obj M) (x : X) :
    (homEquiv C X F M).symm g x =
      ((stalkSkyscraperSheafAdjunction x).homEquiv _ _).symm (g ≫ Pi.π _ x) :=
  rfl

open scoped Classical in
/-- Taking all stalks is left adjoint to the product of skyscraper sheaves: a morphism from a
sheaf `F` to `∏ₓ (iₓ)_* (M x)` is a family of morphisms `Fₓ ⟶ M x`. -/
def stalksSkyscraperProductAdjunction :
    stalksFunctor C X ⊣ skyscraperProductFunctor C X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv C X
      homEquiv_naturality_left_symm f g := funext fun x ↦ by
        rw [Pi.comp_apply, homEquiv_symm_apply, homEquiv_symm_apply, Category.assoc,
          Adjunction.homEquiv_naturality_left_symm]
        rfl
      homEquiv_naturality_right f g := Pi.hom_ext _ _ fun x ↦ by
        rw [homEquiv_apply_π, Category.assoc, Limits.Pi.map_π, ← Category.assoc,
          homEquiv_apply_π, Pi.comp_apply]
        exact Adjunction.homEquiv_naturality_right _ _ _ }

open scoped Classical in
/-- The coordinate at `x` of the morphism `F ⟶ ∏ₓ (iₓ)_* (M x)` corresponding to a family of
morphisms `Fₓ ⟶ M x` is the morphism `F ⟶ (iₓ)_* (M x)` corresponding to its member at `x`. -/
@[reassoc (attr := simp)]
theorem stalksSkyscraperProductAdjunction_homEquiv_apply_π {F : X.Sheaf C} {M : X → C}
    (f : (stalksFunctor C X).obj F ⟶ M) (x : X) :
    (stalksSkyscraperProductAdjunction C X).homEquiv F M f ≫ Pi.π _ x =
      (stalkSkyscraperSheafAdjunction x).homEquiv _ _ (f x) := by
  rw [stalksSkyscraperProductAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact homEquiv_apply_π C X f x

open scoped Classical in
/-- The family of morphisms `Fₓ ⟶ M x` corresponding to a morphism `F ⟶ ∏ₓ (iₓ)_* (M x)`
consists of the morphisms corresponding to its coordinates. -/
@[simp]
theorem stalksSkyscraperProductAdjunction_homEquiv_symm_apply {F : X.Sheaf C} {M : X → C}
    (g : F ⟶ (skyscraperProductFunctor C X).obj M) (x : X) :
    ((stalksSkyscraperProductAdjunction C X).homEquiv F M).symm g x =
      ((stalkSkyscraperSheafAdjunction x).homEquiv _ _).symm (g ≫ Pi.π _ x) := by
  rw [stalksSkyscraperProductAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact homEquiv_symm_apply C X g x

open scoped Classical in
/-- The counit of `stalksSkyscraperProductAdjunction` at a family `M` is, at `x`, the stalk at `x`
of the coordinate at `x`, followed by the counit `((iₓ)_* (M x))ₓ ⟶ M x` of the adjunction between
the stalk at `x` and the skyscraper sheaf at `x`. -/
theorem stalksSkyscraperProductAdjunction_counit_app_apply (M : X → C) (x : X) :
    (stalksSkyscraperProductAdjunction C X).counit.app M x =
      (Presheaf.stalkFunctor C x).map
          (Pi.π (fun y ↦ (skyscraperSheafFunctor y).obj (M y)) x).hom ≫
        (stalkSkyscraperSheafAdjunction x).counit.app (M x) := by
  rw [← Adjunction.homEquiv_symm_id, stalksSkyscraperProductAdjunction_homEquiv_symm_apply,
    Category.id_comp]
  exact (stalkSkyscraperSheafAdjunction (C := C) x).homEquiv_counit _ _ _

/-- The *Godement sheaf* functor `F ↦ ∏ₓ (iₓ)_* Fₓ`: the product over the points `x` of `X` of
the skyscraper sheaves at `x` with value the stalk of `F` at `x`. -/
abbrev godement : X.Sheaf C ⥤ X.Sheaf C :=
  stalksFunctor C X ⋙ skyscraperProductFunctor C X

/-- The canonical morphism `F ⟶ ∏ₓ (iₓ)_* Fₓ` from a sheaf to its Godement sheaf, the unit of
`stalksSkyscraperProductAdjunction`. -/
def toGodement : 𝟭 (X.Sheaf C) ⟶ godement C X :=
  (stalksSkyscraperProductAdjunction C X).unit

open scoped Classical in
/-- The coordinate at `x` of `F ⟶ ∏ₓ (iₓ)_* Fₓ` is the unit `F ⟶ (iₓ)_* Fₓ` of the adjunction
between the stalk at `x` and the skyscraper sheaf at `x`. -/
@[reassoc (attr := simp)]
theorem toGodement_app_π (F : X.Sheaf C) (x : X) :
    (toGodement C X).app F ≫ Pi.π (fun y ↦ (skyscraperSheafFunctor y).obj (F.presheaf.stalk y)) x =
      (stalkSkyscraperSheafAdjunction x).unit.app F := by
  have h :=
    stalksSkyscraperProductAdjunction_homEquiv_apply_π C X (𝟙 ((stalksFunctor C X).obj F)) x
  rw [Adjunction.homEquiv_id] at h
  exact h.trans ((stalkSkyscraperSheafAdjunction x).homEquiv_id F)

open scoped Classical in
/-- The coordinate at `x` of `F ⟶ ∏ₓ (iₓ)_* Fₓ` sends a section over an open `U` containing `x`
to its germ at `x`. -/
theorem toGodement_app_π_hom_app (F : X.Sheaf C) (x : X) (U : Opens X) (hx : x ∈ U) :
    ((toGodement C X).app F ≫
        Pi.π (fun y ↦ (skyscraperSheafFunctor y).obj (F.presheaf.stalk y)) x).hom.app (op U) =
      F.presheaf.germ U x hx ≫ eqToHom (ite_eq_left hx).symm := by
  rw [toGodement_app_π]
  -- The unit of the adjunction at `x` is `toSkyscraperPresheaf` of the identity of the stalk, whose
  -- value on `U ∋ x` is the germ at `x`.
  exact (dite_eq_left hx).trans (congrArg (_ ≫ ·) (Category.id_comp _))

end Adjunction

section Flasque

variable {C : Type*} [Category.{u} C] [HasZeroObject C] {X : TopCat.{u}}

/-- In a category with a zero object, the restriction maps of a skyscraper presheaf are split
epimorphisms: each is an identity or a morphism to a terminal object, which is a zero object. -/
instance _root_.isSplitEpi_skyscraperPresheaf_map (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]
    (A : C) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : IsSplitEpi ((skyscraperPresheaf p₀ A).map i) := by
  by_cases hV : p₀ ∈ unop V
  · have hU : p₀ ∈ unop U := leOfHom i.unop hV
    refine ⟨⟨eqToHom (by simp [hU, hV]), ?_⟩⟩
    simp only [skyscraperPresheaf_map, dite_eq_left hV]
    -- The composite passes through `(skyscraperPresheaf p₀ A).obj U`, which is `A` only up to
    -- unfolding, so the two `eqToHom`s are composed as a term.
    exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)
  · have hZ : IsZero ((skyscraperPresheaf p₀ A).obj V) :=
      (isZero_zero C).of_iso (HasZeroObject.zeroIsoIsTerminal
        (isTerminalSkyscraperSheafObjObjOfNotMem (A := A) hV)).symm
    exact ⟨⟨hZ.to_ _, hZ.eq_of_src _ _⟩⟩

variable (C X) [HasProducts.{u} C]

open scoped Classical in
/-- A product of skyscraper sheaves, valued in a category with a zero object, is flasque. -/
instance isFlasque_skyscraperProductFunctor_obj (M : X → C) :
    ((skyscraperProductFunctor C X).obj M).IsFlasque :=
  have : (∏ᶜ fun x ↦ (Sheaf.forget C X).obj ((skyscraperSheafFunctor x).obj (M x))).IsFlasque :=
    Presheaf.isFlasque_piObj_of_isSplitEpi _ fun x _ _ i ↦
      isSplitEpi_skyscraperPresheaf_map x (M x) i
  -- Products of sheaves are computed in presheaves.
  .of_iso (PreservesProduct.iso (Sheaf.forget C X) _).symm

/-- The Godement sheaf of a sheaf valued in a category with a zero object is flasque. -/
instance isFlasque_godement_obj [HasColimits C] (F : X.Sheaf C) :
    ((godement C X).obj F).IsFlasque :=
  isFlasque_skyscraperProductFunctor_obj C X _

end Flasque

section Mono

variable (C : Type*) [Category.{u} C] [HasColimits C] [HasProducts.{u} C] (X : TopCat.{u})

/-- On the stalk at `x`, the canonical morphism `F ⟶ ∏ₓ (iₓ)_* Fₓ` is a split monomorphism: it is
retracted by the counit of `stalksSkyscraperProductAdjunction` at `x`, that is, by the stalk at `x`
of the coordinate at `x` followed by the counit `((iₓ)_* Fₓ)ₓ ⟶ Fₓ`
(`stalksSkyscraperProductAdjunction_counit_app_apply`). -/
instance isSplitMono_stalkFunctor_map_toGodement_app (F : X.Sheaf C) (x : X) :
    IsSplitMono ((Presheaf.stalkFunctor C x).map ((toGodement C X).app F).hom) :=
  ⟨⟨(stalksSkyscraperProductAdjunction C X).counit.app ((stalksFunctor C X).obj F) x,
    -- The triangle identity, evaluated at `x`: composition and identities of families are
    -- pointwise, and `stalksFunctor` takes stalks pointwise.
    congrFun ((stalksSkyscraperProductAdjunction C X).left_triangle_components F) x⟩⟩

section Concrete

variable {FC : C → C → Type*} {CC : C → Type u} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [instCC : ConcreteCategory.{u} C FC] [PreservesFilteredColimits (CategoryTheory.forget C)]
  [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]

include instCC in
/-- For sheaves valued in a concrete category with the usual stalk hypotheses, such as modules
over a ring or abelian groups, the canonical morphism `F ⟶ ∏ₓ (iₓ)_* Fₓ` is a monomorphism: a
section is determined by its germs. -/
instance mono_toGodement_app (F : X.Sheaf C) : Mono ((toGodement C X).app F) :=
  Presheaf.mono_of_stalk_mono _

end Concrete

end Mono

end TopCat.Sheaf
