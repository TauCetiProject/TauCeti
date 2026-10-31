/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
import TauCeti.Algebra.Homology.Ext.Basic

/-!
# Free sheaves of modules on objects of a site and relative `Ext`

Let `R` be a commutative ring and `(C, J)` a site. For an object `U` of `C`, the free sheaf of
`R`-modules `R_U` is the sheafification of the presheaf `W ↦ R[Hom(W, U)]`, the free `R`-module on
the representable presheaf. It corepresents the sections over `U`: morphisms `R_U ⟶ F` to a sheaf of
`R`-modules are `R`-linearly the sections `F(U)`, naturally in `U` and in `F`.

For a morphism `i : U ⟶ V` the *relative free sheaf* `R_{V,U}` is the cokernel of `R_U ⟶ R_V`.
Morphisms `R_{V,U} ⟶ F` are the sections of `F` over `V` whose restriction along `i` vanishes, and
when `i` is a monomorphism `0 ⟶ R_U ⟶ R_V ⟶ R_{V,U} ⟶ 0` is short exact. Thus the `R`-modules
`Extⁿ(R_{V,U}, F)` are the relative cohomology of `F` with coefficients in sheaves of `R`-modules,
whose degree-zero part is the module of sections over `V` restricting to zero along `i`.

These are the `R`-linear counterparts of the free abelian sheaves
`TauCeti.CategoryTheory.freeYonedaSheafFunctor` and of the relative free abelian sheaves
`TauCeti.CategoryTheory.relativeFreeYonedaSheaf`. On the site of open subsets of a topological
space, with `i` the inclusion `W ∖ S ⟶ W` for a closed subset `S`, they give cohomology with
supports in `S` for sheaves of `R`-modules; this is developed in
`TauCeti.Topology.Sheaves.SupportedCohomology.Module`.

## Main declarations

* `TauCeti.CategoryTheory.freeModuleYonedaSheafFunctor J R`: the functor `U ↦ R_U`;
* `TauCeti.CategoryTheory.freeModuleYonedaSheafSectionsEquiv`: the `R`-linear equivalence
  `(R_U ⟶ F) ≃ₗ[R] F(U)`, natural in `F` (`freeModuleYonedaSheafSectionsEquiv_naturality_right`)
  and in `U` (`freeModuleYonedaSheafSectionsEquiv_naturality_left`);
* `TauCeti.CategoryTheory.mono_freeModuleYonedaSheafFunctor_map`: a monomorphism of the site
  induces a monomorphism of free module sheaves;
* `TauCeti.CategoryTheory.relativeFreeModuleYonedaSheaf J R i`: the relative free sheaf
  `R_{V,U}`, with `relativeFreeModuleYonedaSheafHomEquiv`, the `R`-linear equivalence between
  morphisms `R_{V,U} ⟶ F` and sections of `F` over `V` restricting to zero along `i`;
* `TauCeti.CategoryTheory.relativeFreeModuleYonedaSequence_shortExact`: the sequence
  `0 ⟶ R_U ⟶ R_V ⟶ R_{V,U} ⟶ 0` is short exact for a monomorphism `i`;
* `TauCeti.CategoryTheory.relativeFreeModuleYonedaExtZeroEquiv`: the `R`-linear identification of
  `Ext⁰(R_{V,U}, F)` with the sections of `F` over `V` restricting to zero along `i`.

## Implementation notes

`R_U` is built from Mathlib's free-forgetful adjunction `ModuleCat.adj R` and the sheafification
adjunction, exactly as the free abelian sheaf is built from `AddCommGrpCat.adj`. Mathlib's
`CategoryTheory.Sheaf.freeYoneda J U (ModuleCat.of R R)` is isomorphic to `R_U`, but it is neither
functorial in `U` nor equipped with the `R`-linear universal property, both of which the relative
construction uses.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite Abelian

universe w v u

namespace TauCeti

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type v) [CommRing R]
  [HasSheafify J (ModuleCat.{v} R)]

noncomputable section

/-- The free sheaf of `R`-modules `R_U` on an object `U` of the site: the sheafification of the free
`R`-module presheaf on `yoneda.obj U`, functorial in `U`. -/
def freeModuleYonedaSheafFunctor : C ⥤ Sheaf J (ModuleCat.{v} R) :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
    presheafToSheaf J (ModuleCat.{v} R)

/-- Morphisms from the free sheaf of `R`-modules on `U` to a sheaf of `R`-modules `F` are
`R`-linearly equivalent to the sections of `F` over `U`. -/
def freeModuleYonedaSheafSectionsEquiv (U : C) (F : Sheaf J (ModuleCat.{v} R)) :
    ((freeModuleYonedaSheafFunctor J R).obj U ⟶ F) ≃ₗ[R] F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J (ModuleCat.{v} R)).homEquiv _ _).trans <|
    ((Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj R)).homEquiv _ _).trans yonedaEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def freeModuleYonedaSheafSectionsFormula (U : C) (F : Sheaf J (ModuleCat.{v} R))
    (f : (freeModuleYonedaSheafFunctor J R).obj U ⟶ F) : F.obj.obj (op U) :=
  yonedaEquiv
    ((Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj R)).homEquiv _ _
      ((sheafificationAdjunction J (ModuleCat.{v} R)).homEquiv _ _ f))

private lemma freeModuleYonedaSheafSectionsEquiv_apply (U : C) (F : Sheaf J (ModuleCat.{v} R))
    (f : (freeModuleYonedaSheafFunctor J R).obj U ⟶ F) :
    freeModuleYonedaSheafSectionsEquiv J R U F f = freeModuleYonedaSheafSectionsFormula J R U F f :=
  (rfl)

/-- The equivalence `freeModuleYonedaSheafSectionsEquiv` is natural in the coefficient sheaf. -/
@[simp]
lemma freeModuleYonedaSheafSectionsEquiv_naturality_right {U : C}
    {F G : Sheaf J (ModuleCat.{v} R)} (f : (freeModuleYonedaSheafFunctor J R).obj U ⟶ F)
    (g : F ⟶ G) :
    freeModuleYonedaSheafSectionsEquiv J R U G (f ≫ g) =
      g.hom.app (op U) (freeModuleYonedaSheafSectionsEquiv J R U F f) := by
  rw [freeModuleYonedaSheafSectionsEquiv_apply, freeModuleYonedaSheafSectionsEquiv_apply]
  dsimp only [freeModuleYonedaSheafSectionsFormula, freeModuleYonedaSheafFunctor,
    Functor.comp_obj] at f ⊢
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    yonedaEquiv_comp]
  rfl

/-- The equivalence `freeModuleYonedaSheafSectionsEquiv` is natural in the object of the site:
precomposing with the map induced by `i : U ⟶ V` is restricting sections along `i`. -/
lemma freeModuleYonedaSheafSectionsEquiv_naturality_left {U V : C} (i : U ⟶ V)
    (F : Sheaf J (ModuleCat.{v} R)) (f : (freeModuleYonedaSheafFunctor J R).obj V ⟶ F) :
    freeModuleYonedaSheafSectionsEquiv J R U F ((freeModuleYonedaSheafFunctor J R).map i ≫ f) =
      F.obj.map i.op (freeModuleYonedaSheafSectionsEquiv J R V F f) := by
  rw [freeModuleYonedaSheafSectionsEquiv_apply, freeModuleYonedaSheafSectionsEquiv_apply]
  dsimp only [freeModuleYonedaSheafSectionsFormula, freeModuleYonedaSheafFunctor,
    Functor.comp_obj, Functor.comp_map] at f ⊢
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ _).symm

/-- A monomorphism of site objects induces a monomorphism between the corresponding free sheaves of
`R`-modules. -/
instance mono_freeModuleYonedaSheafFunctor_map {U V : C} (i : U ⟶ V) [Mono i] :
    Mono ((freeModuleYonedaSheafFunctor J R).map i) := by
  dsimp only [freeModuleYonedaSheafFunctor, Functor.comp_map]
  let φ := ((Functor.whiskeringRight Cᵒᵖ (Type v) (ModuleCat.{v} R)).obj
      (ModuleCat.free R)).map (yoneda.map i)
  -- each component of `φ` is `Finsupp.mapDomain` along the injective postcomposition with `i`
  have (W : Cᵒᵖ) : Mono (φ.app W) := (ModuleCat.mono_iff_injective _).2 <|
    Finsupp.mapDomain_injective fun _ _ h ↦ (cancel_mono i).1 h
  have : Mono φ := NatTrans.mono_of_mono_app φ
  exact Functor.map_mono _ φ

/-! ### The relative free sheaf -/

/-- The free sheaf of `R`-modules on `V` relative to `U`: the cokernel of the map `R_U ⟶ R_V`
induced by `i : U ⟶ V`. -/
abbrev relativeFreeModuleYonedaSheaf {U V : C} (i : U ⟶ V) : Sheaf J (ModuleCat.{v} R) :=
  cokernel ((freeModuleYonedaSheafFunctor J R).map i)

/-- Morphisms from the relative free sheaf of `i : U ⟶ V` to a sheaf of `R`-modules `F` are
`R`-linearly equivalent to the sections of `F` over `V` whose restriction along `i` vanishes. -/
def relativeFreeModuleYonedaSheafHomEquiv {U V : C} (i : U ⟶ V) (F : Sheaf J (ModuleCat.{v} R)) :
    (relativeFreeModuleYonedaSheaf J R i ⟶ F) ≃ₗ[R] LinearMap.ker (F.obj.map i.op).hom where
  toFun g := ⟨freeModuleYonedaSheafSectionsEquiv J R V F (cokernel.π _ ≫ g), by
    rw [LinearMap.mem_ker, ModuleCat.Hom.hom, ← freeModuleYonedaSheafSectionsEquiv_naturality_left,
      cokernel.condition_assoc, zero_comp, map_zero]⟩
  invFun s := cokernel.desc _ ((freeModuleYonedaSheafSectionsEquiv J R V F).symm s) <| by
    apply (freeModuleYonedaSheafSectionsEquiv J R U F).injective
    rw [freeModuleYonedaSheafSectionsEquiv_naturality_left, LinearEquiv.apply_symm_apply,
      map_zero]
    exact s.2
  left_inv g := by
    refine (cancel_epi (cokernel.π _)).1 ?_
    exact (cokernel.π_desc _ _ _).trans (LinearEquiv.symm_apply_apply _ _)
  right_inv s := by
    apply Subtype.ext
    simp
  map_add' g h := by
    apply Subtype.ext
    simp
  map_smul' r g := by
    apply Subtype.ext
    simp

@[simp]
lemma coe_relativeFreeModuleYonedaSheafHomEquiv_apply {U V : C} (i : U ⟶ V)
    (F : Sheaf J (ModuleCat.{v} R)) (g : relativeFreeModuleYonedaSheaf J R i ⟶ F) :
    (relativeFreeModuleYonedaSheafHomEquiv J R i F g : F.obj.obj (op V)) =
      freeModuleYonedaSheafSectionsEquiv J R V F (cokernel.π _ ≫ g) :=
  (rfl)

@[simp]
lemma cokernel_π_comp_relativeFreeModuleYonedaSheafHomEquiv_symm_apply {U V : C} (i : U ⟶ V)
    (F : Sheaf J (ModuleCat.{v} R)) (s : LinearMap.ker (F.obj.map i.op).hom) :
    cokernel.π _ ≫ (relativeFreeModuleYonedaSheafHomEquiv J R i F).symm s =
      (freeModuleYonedaSheafSectionsEquiv J R V F).symm s :=
  cokernel.π_desc _ _ _

/-- The equivalence `relativeFreeModuleYonedaSheafHomEquiv` is natural in the coefficient
sheaf. -/
lemma relativeFreeModuleYonedaSheafHomEquiv_naturality_right {U V : C} (i : U ⟶ V)
    {F G : Sheaf J (ModuleCat.{v} R)} (g : relativeFreeModuleYonedaSheaf J R i ⟶ F) (f : F ⟶ G) :
    (relativeFreeModuleYonedaSheafHomEquiv J R i G (g ≫ f) : G.obj.obj (op V)) =
      f.hom.app (op V) (relativeFreeModuleYonedaSheafHomEquiv J R i F g) := by
  simp

/-- The sequence `R_U ⟶ R_V ⟶ R_{V,U}` of free sheaves of `R`-modules attached to
`i : U ⟶ V`. -/
abbrev relativeFreeModuleYonedaSequence {U V : C} (i : U ⟶ V) :
    ShortComplex (Sheaf J (ModuleCat.{v} R)) :=
  ShortComplex.cokernelSequence ((freeModuleYonedaSheafFunctor J R).map i)

/-- For a monomorphism `i : U ⟶ V`, the sequence `0 ⟶ R_U ⟶ R_V ⟶ R_{V,U} ⟶ 0` is short
exact. -/
lemma relativeFreeModuleYonedaSequence_shortExact {U V : C} (i : U ⟶ V) [Mono i] :
    (relativeFreeModuleYonedaSequence J R i).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := inferInstanceAs (Mono ((freeModuleYonedaSheafFunctor J R).map i))

/-- If `i` is an isomorphism, the relative free sheaf of `i` is zero. -/
lemma isZero_relativeFreeModuleYonedaSheaf {U V : C} (i : U ⟶ V) [IsIso i] :
    IsZero (relativeFreeModuleYonedaSheaf J R i) :=
  isZero_cokernel_of_epi _

section map

variable {U' V' U V : C} (i' : U' ⟶ V') (i : U ⟶ V) (a : U' ⟶ U) (b : V' ⟶ V)
  (w : i' ≫ b = a ≫ i)

/-- The map of relative free sheaves `R_{V',U'} ⟶ R_{V,U}` induced by a commutative square
`i' ≫ b = a ≫ i` from `i' : U' ⟶ V'` to `i : U ⟶ V`. -/
def relativeFreeModuleYonedaSheafMap :
    relativeFreeModuleYonedaSheaf J R i' ⟶ relativeFreeModuleYonedaSheaf J R i :=
  cokernel.map _ _ ((freeModuleYonedaSheafFunctor J R).map a)
    ((freeModuleYonedaSheafFunctor J R).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, w])

@[reassoc (attr := simp)]
lemma cokernel_π_relativeFreeModuleYonedaSheafMap :
    cokernel.π _ ≫ relativeFreeModuleYonedaSheafMap J R i' i a b w =
      (freeModuleYonedaSheafFunctor J R).map b ≫ cokernel.π _ :=
  cokernel.π_desc _ _ _

@[simp]
lemma relativeFreeModuleYonedaSheafMap_id :
    relativeFreeModuleYonedaSheafMap J R i i (𝟙 U) (𝟙 V) (by simp) = 𝟙 _ :=
  (cancel_epi (cokernel.π _)).1 (by simp)

lemma relativeFreeModuleYonedaSheafMap_comp {U'' V'' : C} (i'' : U'' ⟶ V'') (a' : U'' ⟶ U')
    (b' : V'' ⟶ V') (w' : i'' ≫ b' = a' ≫ i') :
    relativeFreeModuleYonedaSheafMap J R i'' i' a' b' w' ≫
        relativeFreeModuleYonedaSheafMap J R i' i a b w =
      relativeFreeModuleYonedaSheafMap J R i'' i (a' ≫ a) (b' ≫ b)
        (by rw [reassoc_of% w', w, Category.assoc]) :=
  (cancel_epi (cokernel.π _)).1 (by simp)

/-- Under `relativeFreeModuleYonedaSheafHomEquiv`, precomposition with
`relativeFreeModuleYonedaSheafMap` is the restriction of sections along `b`. -/
lemma coe_relativeFreeModuleYonedaSheafHomEquiv_map_comp (F : Sheaf J (ModuleCat.{v} R))
    (g : relativeFreeModuleYonedaSheaf J R i ⟶ F) :
    (relativeFreeModuleYonedaSheafHomEquiv J R i' F
        (relativeFreeModuleYonedaSheafMap J R i' i a b w ≫ g) : F.obj.obj (op V')) =
      F.obj.map b.op (relativeFreeModuleYonedaSheafHomEquiv J R i F g) := by
  rw [coe_relativeFreeModuleYonedaSheafHomEquiv_apply,
    coe_relativeFreeModuleYonedaSheafHomEquiv_apply,
    cokernel_π_relativeFreeModuleYonedaSheafMap_assoc,
    freeModuleYonedaSheafSectionsEquiv_naturality_left]

end map

/-! ### Relative `Ext` in degree zero -/

variable [HasExt.{w} (Sheaf J (ModuleCat.{v} R))]

/-- The degree-zero relative cohomology `Ext⁰(R_{V,U}, F)` is `R`-linearly the module of sections
of `F` over `V` whose restriction along `i` vanishes. -/
def relativeFreeModuleYonedaExtZeroEquiv {U V : C} (i : U ⟶ V) (F : Sheaf J (ModuleCat.{v} R)) :
    Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F 0 ≃ₗ[R]
      LinearMap.ker (F.obj.map i.op).hom :=
  Ext.linearEquiv₀.trans (relativeFreeModuleYonedaSheafHomEquiv J R i F)

@[simp]
lemma coe_relativeFreeModuleYonedaExtZeroEquiv_apply {U V : C} (i : U ⟶ V)
    (F : Sheaf J (ModuleCat.{v} R)) (x : Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F 0) :
    (relativeFreeModuleYonedaExtZeroEquiv J R i F x : F.obj.obj (op V)) =
      freeModuleYonedaSheafSectionsEquiv J R V F (cokernel.π _ ≫ Ext.addEquiv₀ x) :=
  (rfl)

/-- The equivalence `relativeFreeModuleYonedaExtZeroEquiv` is natural in the coefficient sheaf. -/
lemma coe_relativeFreeModuleYonedaExtZeroEquiv_comp_mk₀ {U V : C} (i : U ⟶ V)
    {F G : Sheaf J (ModuleCat.{v} R)} (x : Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F 0)
    (f : F ⟶ G) :
    (relativeFreeModuleYonedaExtZeroEquiv J R i G (x.comp (Ext.mk₀ f) (add_zero 0)) :
        G.obj.obj (op V)) =
      f.hom.app (op V) (relativeFreeModuleYonedaExtZeroEquiv J R i F x) := by
  rw [coe_relativeFreeModuleYonedaExtZeroEquiv_apply,
    coe_relativeFreeModuleYonedaExtZeroEquiv_apply, TauCeti.ext_addEquiv₀_comp_mk₀,
    ← Category.assoc, freeModuleYonedaSheafSectionsEquiv_naturality_right]

/-- Under `relativeFreeModuleYonedaExtZeroEquiv`, precomposition with the map of relative free
sheaves induced by a commutative square `i' ≫ b = a ≫ i` is the restriction of sections
along `b`. -/
lemma coe_relativeFreeModuleYonedaExtZeroEquiv_mk₀_comp {U' V' U V : C} (i' : U' ⟶ V')
    (i : U ⟶ V) (a : U' ⟶ U) (b : V' ⟶ V) (w : i' ≫ b = a ≫ i) (F : Sheaf J (ModuleCat.{v} R))
    (x : Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F 0) :
    (relativeFreeModuleYonedaExtZeroEquiv J R i' F
        ((Ext.mk₀ (relativeFreeModuleYonedaSheafMap J R i' i a b w)).comp x (zero_add 0)) :
        F.obj.obj (op V')) =
      F.obj.map b.op (relativeFreeModuleYonedaExtZeroEquiv J R i F x) := by
  rw [coe_relativeFreeModuleYonedaExtZeroEquiv_apply, TauCeti.ext_addEquiv₀_mk₀_comp,
    ← coe_relativeFreeModuleYonedaSheafHomEquiv_apply,
    coe_relativeFreeModuleYonedaSheafHomEquiv_map_comp]
  rfl

end

end CategoryTheory

end TauCeti
