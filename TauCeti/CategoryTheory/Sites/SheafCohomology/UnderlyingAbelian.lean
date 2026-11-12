/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Module
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Relative

/-!
# Relative cohomology of a sheaf of modules and of its underlying abelian sheaf

Let `R` be a commutative ring, `(C, J)` a site and `i : U ⟶ V` a morphism of `C`. A sheaf of
`R`-modules `F` has two relative cohomologies along `i`: the `R`-modules
`Extⁿ(R_{V,U}, F)` computed in sheaves of `R`-modules
(`TauCeti.CategoryTheory.relativeFreeModuleYonedaSheaf`), and the abelian groups
`Hⁿ(V, U; F) = Extⁿ(ℤ_{V,U}, F)` of its underlying abelian sheaf
(`CategoryTheory.Sheaf.relativeH'`). This file constructs the comparison map between them.

The section of the underlying abelian sheaf of `R_{V,U}` over `V` corresponding to the identity
of `R_{V,U}` restricts to zero along `i`, so it is a morphism `ℤ_{V,U} ⟶ R_{V,U}` of abelian
sheaves (`TauCeti.CategoryTheory.relativeFreeYonedaSheafToForget`). Composing it with the map on
`Ext` groups induced by the exact functor forgetting the module structures gives the comparison
`Extⁿ(R_{V,U}, F) ⟶ Hⁿ(V, U; F)` (`TauCeti.CategoryTheory.relativeExtToForget`). It is natural in
the coefficient sheaf, including the connecting maps of short exact sequences of coefficients,
and in commutative squares of morphisms of the site, and in degree zero it is the identity on
the sections of `F` over `V` restricting to zero along `i`, hence bijective.

On the site of open subsets of a topological space the comparison is bijective in every degree
(`TauCeti.CategoryTheory.relativeExtToForget_bijective`), because injective sheaves of modules
are flasque and flasque abelian sheaves have no relative cohomology in positive degrees; this is
developed in `TauCeti.Topology.Sheaves.SupportedCohomology.UnderlyingAbelian`.

## Main declarations

* `TauCeti.CategoryTheory.relativeFreeYonedaSheafToForget J R i`: the morphism
  `ℤ_{V,U} ⟶ R_{V,U}` of abelian sheaves, characterized by
  `TauCeti.CategoryTheory.coe_relativeFreeYonedaSheafHomEquiv_toForget_comp`;
* `TauCeti.CategoryTheory.relativeExtToForget J R i F n`: the comparison
  `Extⁿ(R_{V,U}, F) →+ Hⁿ(V, U; F)`;
* `TauCeti.CategoryTheory.relativeExtToForget_comp`: naturality in `Ext` classes between
  coefficient sheaves;
* `TauCeti.CategoryTheory.relativeExtToForget_mk₀_relativeFreeModuleYonedaSheafMap_comp`:
  naturality in commutative squares of the site;
* `TauCeti.CategoryTheory.ext_addEquiv₀_relativeExtToForget`,
  `TauCeti.CategoryTheory.coe_relativeH'_zeroEquiv_relativeExtToForget` and
  `TauCeti.CategoryTheory.relativeExtToForget_zero_bijective`: the comparison in degree zero.

## References

* A. Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J. 9 (1957), §3.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite Abelian

universe w w' v u

namespace TauCeti

namespace CategoryTheory

section unit

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type v) [CommRing R]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify J (ModuleCat.{v} R)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})]

omit [HasSheafify J AddCommGrpCat.{v}] [HasSheafify J (ModuleCat.{v} R)] in
/-- A section of a sheaf of `R`-modules lies in the kernel of a restriction map exactly when it
lies in the kernel of the corresponding restriction map of the underlying abelian sheaf. -/
private lemma mem_ker_sheafCompose_forget₂_map_iff {U V : C} (i : U ⟶ V)
    (F : Sheaf J (ModuleCat.{v} R)) (s : F.obj.obj (op V)) :
    s ∈ (((sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).obj F).obj.map
        i.op).hom.ker ↔ s ∈ LinearMap.ker (F.obj.map i.op).hom :=
  -- both say that `s` restricts to zero along `i`
  AddMonoidHom.mem_ker.trans (LinearMap.mem_ker (f := (F.obj.map i.op).hom)).symm

noncomputable section

/-- The morphism of abelian sheaves `ℤ_{V,U} ⟶ R_{V,U}` from the relative free abelian sheaf of
`i : U ⟶ V` to the underlying abelian sheaf of the relative free sheaf of `R`-modules. It
corresponds to the section of `R_{V,U}` over `V` given by the identity of `R_{V,U}`. -/
def relativeFreeYonedaSheafToForget {U V : C} (i : U ⟶ V) :
    relativeFreeYonedaSheaf J i ⟶
      (sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).obj
        (relativeFreeModuleYonedaSheaf J R i) :=
  (relativeFreeYonedaSheafHomEquiv J i _).symm
    ⟨(relativeFreeModuleYonedaSheafHomEquiv J R i _ (𝟙 _)).1,
      (mem_ker_sheafCompose_forget₂_map_iff J R i _ _).2
        (relativeFreeModuleYonedaSheafHomEquiv J R i _ (𝟙 _)).2⟩

/-- Under the identification of morphisms out of `ℤ_{V,U}` with sections,
`relativeFreeYonedaSheafToForget` is the section of `R_{V,U}` over `V` given by its identity. -/
lemma coe_relativeFreeYonedaSheafHomEquiv_relativeFreeYonedaSheafToForget {U V : C}
    (i : U ⟶ V) :
    ((relativeFreeYonedaSheafHomEquiv J i _ (relativeFreeYonedaSheafToForget J R i)).1 :
        (relativeFreeModuleYonedaSheaf J R i).obj.obj (op V)) =
      (relativeFreeModuleYonedaSheafHomEquiv J R i _ (𝟙 _)).1 := by
  rw [relativeFreeYonedaSheafToForget, AddEquiv.apply_symm_apply]

/-- Under the identifications of morphisms out of relative free sheaves with sections, composing
`relativeFreeYonedaSheafToForget` with the underlying morphism of abelian sheaves of
`g : R_{V,U} ⟶ F` gives the same section of `F` as `g`. -/
lemma coe_relativeFreeYonedaSheafHomEquiv_toForget_comp {U V : C} (i : U ⟶ V)
    (F : Sheaf J (ModuleCat.{v} R)) (g : relativeFreeModuleYonedaSheaf J R i ⟶ F) :
    ((relativeFreeYonedaSheafHomEquiv J i _ (relativeFreeYonedaSheafToForget J R i ≫
        (sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).map g)).1 :
        F.obj.obj (op V)) =
      (relativeFreeModuleYonedaSheafHomEquiv J R i F g).1 := by
  rw [relativeFreeYonedaSheafHomEquiv_naturality_right,
    coe_relativeFreeYonedaSheafHomEquiv_relativeFreeYonedaSheafToForget]
  conv_rhs => rw [← Category.id_comp g, relativeFreeModuleYonedaSheafHomEquiv_naturality_right]
  -- the underlying additive map of `forget₂` applied to `g` is the linear map of `g` on sections
  rfl

/-- The morphisms `relativeFreeYonedaSheafToForget` are natural in commutative squares of the
site. -/
@[reassoc]
lemma relativeFreeYonedaSheafMap_comp_relativeFreeYonedaSheafToForget {U' V' U V : C}
    (i' : U' ⟶ V') (i : U ⟶ V) (a : U' ⟶ U) (b : V' ⟶ V) (w : i' ≫ b = a ≫ i) :
    relativeFreeYonedaSheafMap J i' i a b w ≫ relativeFreeYonedaSheafToForget J R i =
      relativeFreeYonedaSheafToForget J R i' ≫
        (sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).map
          (relativeFreeModuleYonedaSheafMap J R i' i a b w) := by
  refine (relativeFreeYonedaSheafHomEquiv J i' _).injective (Subtype.ext ?_)
  -- the left side is the restriction along `b` of the section of `R_{V,U}` given by its identity
  rw [coe_relativeFreeYonedaSheafHomEquiv_map_comp,
    coe_relativeFreeYonedaSheafHomEquiv_relativeFreeYonedaSheafToForget]
  -- and so is the right side
  rw [coe_relativeFreeYonedaSheafHomEquiv_toForget_comp,
    ← Category.comp_id (relativeFreeModuleYonedaSheafMap J R i' i a b w),
    coe_relativeFreeModuleYonedaSheafHomEquiv_map_comp]
  -- the restriction maps of the underlying abelian sheaf are those of the sheaf of modules
  rfl

end

end unit

section comparison

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) (R : Type v) [CommRing R]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify J (ModuleCat.{v} R)]
  [HasExt.{w} (Sheaf J (ModuleCat.{v} R))] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

noncomputable section

/-- The comparison `Extⁿ(R_{V,U}, F) ⟶ Hⁿ(V, U; F)` from the relative cohomology of a sheaf of
`R`-modules `F` along `i : U ⟶ V` to the relative cohomology of its underlying abelian sheaf: the
map induced on `Ext` by forgetting the module structures, followed by precomposition with
`ℤ_{V,U} ⟶ R_{V,U}`. -/
def relativeExtToForget {U V : C} (i : U ⟶ V) (F : Sheaf J (ModuleCat.{v} R)) (n : ℕ) :
    Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F n →+
      ((sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).obj F).relativeH' i n :=
  ((Ext.mk₀ (relativeFreeYonedaSheafToForget J R i)).precomp _ (zero_add n)).comp
    ((sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).mapExtAddHom _ _ n)

lemma relativeExtToForget_apply {U V : C} (i : U ⟶ V) (F : Sheaf J (ModuleCat.{v} R)) {n : ℕ}
    (x : Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F n) :
    relativeExtToForget J R i F n x =
      (Ext.mk₀ (relativeFreeYonedaSheafToForget J R i)).comp
        (x.mapExactFunctor (sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})))
        (zero_add n) :=
  (rfl)

/-- In degree zero the comparison sends the class of a morphism `g : R_{V,U} ⟶ F` to the class of
the composite `ℤ_{V,U} ⟶ R_{V,U} ⟶ F` of abelian sheaves. -/
lemma ext_addEquiv₀_relativeExtToForget {U V : C} (i : U ⟶ V) (F : Sheaf J (ModuleCat.{v} R))
    (x : Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F 0) :
    Ext.addEquiv₀ (relativeExtToForget.{w, w'} J R i F 0 x) =
      relativeFreeYonedaSheafToForget J R i ≫
        (sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).map (Ext.addEquiv₀ x) := by
  apply (Ext.mk₀_bijective _ _).1
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, ← Ext.mapExactFunctor_mk₀,
    Ext.mk₀_addEquiv₀_apply, relativeExtToForget_apply]

/-- The comparison is natural in the coefficients: it carries the Yoneda product with an `Ext`
class `α` between sheaves of `R`-modules to the Yoneda product with the underlying `Ext` class of
abelian sheaves. This covers morphisms of coefficient sheaves and the connecting classes of short
exact sequences (`Abelian.Ext.mapExactFunctor_mk₀`, `Abelian.Ext.mapExactFunctor_extClass`). -/
lemma relativeExtToForget_comp {U V : C} (i : U ⟶ V) {F G : Sheaf J (ModuleCat.{v} R)}
    {m n k : ℕ} (x : Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F m) (α : Ext.{w} F G n)
    (h : m + n = k) :
    relativeExtToForget J R i G k (x.comp α h) =
      (relativeExtToForget J R i F m x).comp
        (α.mapExactFunctor (sheafCompose J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}))) h := by
  rw [relativeExtToForget_apply, relativeExtToForget_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add m) h (by omega)).symm

/-- The comparison is natural in commutative squares `i' ≫ b = a ≫ i` of the site: it carries
precomposition with `R_{V',U'} ⟶ R_{V,U}` to precomposition with `ℤ_{V',U'} ⟶ ℤ_{V,U}`. -/
lemma relativeExtToForget_mk₀_relativeFreeModuleYonedaSheafMap_comp {U' V' U V : C}
    (i' : U' ⟶ V') (i : U ⟶ V) (a : U' ⟶ U) (b : V' ⟶ V) (w : i' ≫ b = a ≫ i)
    (F : Sheaf J (ModuleCat.{v} R)) {n : ℕ}
    (x : Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F n) :
    relativeExtToForget J R i' F n
        ((Ext.mk₀ (relativeFreeModuleYonedaSheafMap J R i' i a b w)).comp x (zero_add n)) =
      (Ext.mk₀ (relativeFreeYonedaSheafMap J i' i a b w)).comp (relativeExtToForget J R i F n x)
        (zero_add n) := by
  simp only [relativeExtToForget_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    relativeFreeYonedaSheafMap_comp_relativeFreeYonedaSheafToForget]

/-- In degree zero the comparison is the identity on the sections of `F` over `V` restricting to
zero along `i`. -/
lemma coe_relativeH'_zeroEquiv_relativeExtToForget {U V : C} (i : U ⟶ V)
    (F : Sheaf J (ModuleCat.{v} R)) (x : Ext.{w} (relativeFreeModuleYonedaSheaf J R i) F 0) :
    ((Sheaf.relativeH'.zeroEquiv _ i (relativeExtToForget J R i F 0 x)).1 : F.obj.obj (op V)) =
      (relativeFreeModuleYonedaExtZeroEquiv J R i F x).1 := by
  -- both sides are the sections corresponding to morphisms out of relative free sheaves
  rw [Sheaf.relativeH'.coe_zeroEquiv_apply, coe_relativeFreeModuleYonedaExtZeroEquiv_apply,
    ext_addEquiv₀_relativeExtToForget, ← coe_relativeFreeYonedaSheafHomEquiv_apply,
    ← coe_relativeFreeModuleYonedaSheafHomEquiv_apply]
  exact coe_relativeFreeYonedaSheafHomEquiv_toForget_comp J R i F _

/-- In degree zero the comparison is bijective. -/
theorem relativeExtToForget_zero_bijective {U V : C} (i : U ⟶ V)
    (F : Sheaf J (ModuleCat.{v} R)) : Function.Bijective (relativeExtToForget J R i F 0) := by
  refine ⟨fun x y hxy ↦ (relativeFreeModuleYonedaExtZeroEquiv J R i F).injective <|
    Subtype.ext ?_, fun c ↦ ?_⟩
  · rw [← coe_relativeH'_zeroEquiv_relativeExtToForget,
      ← coe_relativeH'_zeroEquiv_relativeExtToForget, hxy]
  · let s := Sheaf.relativeH'.zeroEquiv _ i c
    refine ⟨(relativeFreeModuleYonedaExtZeroEquiv J R i F).symm
        ⟨s.1, (mem_ker_sheafCompose_forget₂_map_iff J R i F s.1).1 s.2⟩,
      (Sheaf.relativeH'.zeroEquiv _ i).injective (Subtype.ext ?_)⟩
    rw [coe_relativeH'_zeroEquiv_relativeExtToForget, LinearEquiv.apply_symm_apply]

end

end comparison

end CategoryTheory

end TauCeti
