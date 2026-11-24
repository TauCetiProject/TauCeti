/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk

/-!
# Skyscraper presheaves of modules

Let `S` be a presheaf of commutative rings on a topological space `X`, let `x` be a point of `X`
and let `T` be a module over the stalk `S_x`. The skyscraper presheaf of modules `x_* T` has
sections `T` over the opens containing `x` and `0` over the others, an element `r` of `S(U)`
acting on `T` through its germ at `x`. Its sections over `U` are modelled as the functions
`PLift (x ∈ U) → T`, so that restriction maps are precomposition and need no case split.

The skyscraper is right adjoint to the stalk at `x`: morphisms `N ⟶ x_* T` of presheaves of
modules correspond to `S_x`-linear maps `N_x → T` (`PresheafOfModules.skyscraperHomEquiv`). This is
the module analogue of Mathlib's adjunctions `skyscraperPresheafStalkAdjunction` and
`stalkSkyscraperSheafAdjunction` for presheaves and sheaves with values in a category.
Through this adjunction a linear map out of a stalk is the same thing as a morphism of presheaves
of modules, which is how stalks of functors given by universal properties, such as pullback, are
computed.

## Main declarations

* `TauCeti.PresheafOfModules.skyscraper`: the skyscraper presheaf of modules at `x` with value
  `T`;
* `TauCeti.PresheafOfModules.skyscraperHomEquiv`: the bijection between `S_x`-linear maps
  `N_x → T` and morphisms `N ⟶ x_* T`, computed on sections by
  `TauCeti.PresheafOfModules.skyscraperHomEquiv_apply_app_apply` and on germs by
  `TauCeti.PresheafOfModules.skyscraperHomEquiv_symm_apply_germ`.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Exercise 1.17 (skyscraper sheaves).
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TauCeti

noncomputable section

namespace PresheafOfModules

variable {X : TopCat.{u}} (S : X.Presheaf CommRingCat.{u}) (x : X)
  (T : Type u) [AddCommGroup T] [Module (S.stalk x) T]

/-- The `S(U)`-module structure on the sections `PLift (x ∈ U) → T` of the skyscraper over `U`:
a section `r` acts through its germ `r_x` at `x`. -/
abbrev skyscraperSectionsModule (U : Opens X) : Module (S.obj (op U)) (PLift (x ∈ U) → T) :=
  @Pi.module _ _ _ _ _ fun p ↦ Module.compHom T (S.germ U x p.down).hom

/-- The sections of the skyscraper presheaf of modules over `U`: a value in `T` when `x ∈ U`, and
nothing otherwise. Its body is exposed so that sections are functions out of `PLift (x ∈ U)`. -/
@[expose] def skyscraperObj (U : Opens X) :
    ModuleCat.{u} ((S ⋙ forget₂ CommRingCat RingCat.{u}).obj (op U)) :=
  letI := skyscraperSectionsModule S x T U
  ModuleCat.of (S.obj (op U)) (PLift (x ∈ U) → T)

/-- The skyscraper presheaf of modules at `x` with value the `S_x`-module `T`. Its sections over
`U` are `T` when `x ∈ U` and `0` otherwise, and `S(U)` acts through germs at `x`. Its body is
exposed so that sections and restriction maps compute. -/
@[expose] def skyscraper : _root_.PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat.{u}) where
  obj U := skyscraperObj S x T U.unop
  map {U V} f := ModuleCat.ofHom (X := skyscraperObj S x T U.unop)
      (Y := (ModuleCat.restrictScalars ((S ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        (skyscraperObj S x T V.unop))
    { toFun := fun s p ↦ s ⟨f.unop.le p.down⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r s ↦ funext fun p ↦
        congrArg (· • s ⟨f.unop.le p.down⟩) (S.germ_res_apply f.unop x p.down r).symm }

variable {S x T}

/-- A section of `S` acts on a section of the skyscraper through its germ at `x`. -/
@[simp]
lemma skyscraper_smul_apply (U : Opens X) (r : S.obj (op U))
    (s : (skyscraper S x T).obj (op U)) (p : PLift (x ∈ U)) :
    (r • s) p = S.germ U x p.down r • s p :=
  rfl

/-- The restriction maps of the skyscraper are precomposition. -/
@[simp]
lemma skyscraper_map_apply {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (s : (skyscraper S x T).obj U)
    (p : PLift (x ∈ V.unop)) :
    dsimp% only [Functor.comp_obj, CommRingCat.forgetToRingCat_obj, Functor.comp_map,
      CommRingCat.forgetToRingCat_map_hom]
    ((skyscraper S x T).map f s p = s ⟨f.unop.le p.down⟩) :=
  rfl

variable (x T) (N : _root_.PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat.{u}))

/-- The morphism into the skyscraper induced by a linear map `g` out of the stalk at `x`: a
section `m` over `U ∋ x` goes to `g (m_x)`. -/
private def toSkyscraper (g : ↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[S.stalk x] T) :
    N ⟶ skyscraper S x T where
  app U := ModuleCat.ofHom (X := N.obj U) (Y := (skyscraper S x T).obj U)
    { toFun m p := g (TopCat.Presheaf.germ N.presheaf U.unop x p.down m)
      map_add' m m' := funext fun p ↦
        (congrArg g ((TopCat.Presheaf.germ N.presheaf U.unop x p.down).hom.map_add m m')).trans
          (g.map_add _ _)
      map_smul' r m := funext fun p ↦
        (congrArg g (N.germ_smul x U.unop p.down r m)).trans (g.map_smul _ _) }
  naturality {U V} f := by
    ext m
    funext p
    exact congrArg g (TopCat.Presheaf.germ_res_apply N.presheaf f.unop x p.down m)

/-- The component at `U ∋ x` of a morphism into the skyscraper, as an additive map to `T`. -/
private def ofSkyscraperSection (α : N ⟶ skyscraper S x T) (U : Opens X) (hx : x ∈ U) :
    N.obj (op U) →+ T :=
  AddMonoidHom.mk' (fun m ↦ α.app (op U) m ⟨hx⟩)
    (fun m m' ↦ congrFun ((α.app (op U)).hom.map_add m m') ⟨hx⟩)

private lemma ofSkyscraperSection_res (α : N ⟶ skyscraper S x T) {U V : Opens X} (i : U ⟶ V)
    (hx : x ∈ U) (m : N.obj (op V)) :
    ofSkyscraperSection x T N α U hx (N.map i.op m) =
      ofSkyscraperSection x T N α V (i.le hx) m :=
  congrFun (_root_.PresheafOfModules.naturality_apply α i.op m) ⟨hx⟩

private lemma ofSkyscraperSection_smul (α : N ⟶ skyscraper S x T) (U : Opens X) (hx : x ∈ U)
    (r : S.obj (op U)) (m : N.obj (op U)) :
    ofSkyscraperSection x T N α U hx (r • m) =
      S.germ U x hx r • ofSkyscraperSection x T N α U hx m :=
  congrFun ((α.app (op U)).hom.map_smul r m) ⟨hx⟩

/-- The linear map out of the stalk at `x` induced by a morphism `α` into the skyscraper: the
germ of `m` goes to the value of `α m` at `x`. -/
private def ofSkyscraper (α : N ⟶ skyscraper S x T) :
    ↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[S.stalk x] T :=
  N.stalkLiftCommRing x (ofSkyscraperSection x T N α) (ofSkyscraperSection_res x T N α)
    (ofSkyscraperSection_smul x T N α)

private lemma ofSkyscraper_germ (α : N ⟶ skyscraper S x T) (U : Opens X) (hx : x ∈ U)
    (m : N.obj (op U)) :
    ofSkyscraper x T N α (TopCat.Presheaf.germ N.presheaf U x hx m) = α.app (op U) m ⟨hx⟩ :=
  N.stalkLiftCommRing_germ x _ (ofSkyscraperSection_res x T N α)
    (ofSkyscraperSection_smul x T N α) U hx m

/-- The skyscraper at `x` is right adjoint to the stalk at `x`: `S_x`-linear maps `N_x → T`
correspond to morphisms `N ⟶ x_* T` of presheaves of modules. -/
def skyscraperHomEquiv :
    (↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[S.stalk x] T) ≃ (N ⟶ skyscraper S x T) where
  toFun := toSkyscraper x T N
  invFun := ofSkyscraper x T N
  left_inv g := by
    refine LinearMap.ext fun m ↦ ?_
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq N.presheaf m
    exact ofSkyscraper_germ x T N _ U hx m
  right_inv α := by
    ext U m
    funext p
    exact ofSkyscraper_germ x T N α U.unop p.down m

/-- The morphism into the skyscraper attached to `g` sends a section `m` over `U ∋ x` to
`g (m_x)`. -/
@[simp]
lemma skyscraperHomEquiv_apply_app_apply
    (g : ↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[S.stalk x] T) (U : (Opens X)ᵒᵖ)
    (m : N.obj U) (p : PLift (x ∈ U.unop)) :
    dsimp% only [Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((skyscraperHomEquiv x T N g).app U m p =
      g (TopCat.Presheaf.germ N.presheaf U.unop x p.down m)) :=
  (rfl)

/-- The linear map attached to a morphism `α` into the skyscraper sends the germ of `m` to the
value of `α m` at `x`. -/
@[simp]
lemma skyscraperHomEquiv_symm_apply_germ (α : N ⟶ skyscraper S x T) (U : Opens X)
    (hx : x ∈ U) (m : N.obj (op U)) :
    dsimp% only [_root_.PresheafOfModules.presheaf_obj_coe, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj]
    ((skyscraperHomEquiv x T N).symm α (TopCat.Presheaf.germ N.presheaf U x hx m) =
      α.app (op U) m ⟨hx⟩) :=
  ofSkyscraper_germ x T N α U hx m

/-- Naturality of `skyscraperHomEquiv` in the source: precomposing with `β : N' ⟶ N` corresponds
to precomposing with the stalk map of `β`. -/
lemma skyscraperHomEquiv_naturality_left
    {N' : _root_.PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat.{u})} (β : N' ⟶ N)
    (g : ↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[S.stalk x] T) :
    skyscraperHomEquiv x T N' (g ∘ₗ _root_.PresheafOfModules.stalkMapCommRing x β) =
      β ≫ skyscraperHomEquiv x T N g := by
  ext U m
  funext p
  exact congrArg g (_root_.PresheafOfModules.stalkMapCommRing_germ x β U.unop p.down m)

end PresheafOfModules

end

end TauCeti
