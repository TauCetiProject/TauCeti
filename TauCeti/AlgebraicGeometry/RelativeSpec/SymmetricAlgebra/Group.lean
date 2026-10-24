/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic

/-!
# The additive group structure of `Spec_X (Sym F)`

For a quasicoherent sheaf `F` on a scheme `X`, the relative spectrum `𝕍(F) = Spec_X (Sym F)`
represents the functor `T ↦ Hom_{𝒪_X}(F, q_* 𝒪_T)` on schemes `q : T ⟶ X` over `X`
(`relativeSpecSymmetricAlgebraHomEquiv`). These hom sets are abelian groups, and composing with a
morphism over `X` is additive, so by the Yoneda lemma `𝕍(F)` is a commutative group object of the
cartesian monoidal category `Over X`, a commutative group scheme over `X` (Stacks Project,
Tag 01M1, and EGA II, 1.7). Its zero section `X ⟶ 𝕍(F)` corresponds to the zero map `F ⟶ 𝒪_X`, and
its addition `𝕍(F) ×_X 𝕍(F) ⟶ 𝕍(F)` corresponds to the sum of the maps `F ⟶ q_* 𝒪` of the two
projections. The group structure is natural in `F`.

## Main declarations

* `TauCeti.AlgebraicGeometry.addGrpObjRelativeSpecSymmetricAlgebra` and
  `TauCeti.AlgebraicGeometry.isCommAddMonObjRelativeSpecSymmetricAlgebra`: `Spec_X (Sym F)` is a
  commutative additive group object of `Over X`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraHomAddEquiv`: its group of `T`-points is
  the group `Hom(F, q_* 𝒪_T)`, naturally in `T` and in `F`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraPullbackHomAddEquiv`: equivalently, the
  group `Hom(q^* F, 𝒪_T)` of linear functionals on `q^* F`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraHomAddEquiv_zero_hom` and
  `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraHomAddEquiv_add_hom`: the zero section and
  the addition morphism in terms of module maps;
* `TauCeti.AlgebraicGeometry.isAddMonHom_relativeSpec_map` and
  `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraAddGrp`: a map `F' ⟶ F` induces a
  homomorphism of group schemes `Spec_X (Sym F) ⟶ Spec_X (Sym F')`, functorially.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite AddMonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

variable (X) in
/-- The presheaf of abelian groups `T ↦ Hom(F, q_* 𝒪_T)` on schemes `q : T ⟶ X` over `X`,
contravariant in the quasicoherent sheaf `F`. By the adjunction between pullback and pushforward,
these are the linear functionals `q^* F ⟶ 𝒪_T`. -/
-- exposed so that its groups are seen to be groups of module maps `F ⟶ q_* 𝒪_T`
@[expose]
def linearFunctionalsPresheaf : (QuasicoherentSheaf X)ᵒᵖ ⥤ (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules).op ⋙ preadditiveCoyoneda ⋙
    (Functor.whiskeringLeft _ _ _).obj (overFunctions X ⋙ CommMon.forget X.Modules)

/-- The restriction maps of `linearFunctionalsPresheaf` compose a module map `F ⟶ q_* 𝒪_T` with
pullback of regular functions along a morphism `g : T' ⟶ T` over `X`. -/
@[simp]
lemma linearFunctionalsPresheaf_obj_map_apply (F : (QuasicoherentSheaf X)ᵒᵖ) {T' T : Over X}
    (g : T' ⟶ T) (φ : ToType (((linearFunctionalsPresheaf X).obj F).obj (op T))) :
    ((linearFunctionalsPresheaf X).obj F).map g.op φ =
      (φ : F.unop.obj ⟶ (Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)) ≫
        (Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g)).hom.hom :=
  (rfl)

/-- The map of `linearFunctionalsPresheaf` induced by `a : F' ⟶ F` precomposes module maps with
`a`. -/
@[simp]
lemma linearFunctionalsPresheaf_map_app_apply {F' F : QuasicoherentSheaf X} (a : F' ⟶ F)
    (T : (Over X)ᵒᵖ) (φ : ToType (((linearFunctionalsPresheaf X).obj (op F)).obj T)) :
    ((linearFunctionalsPresheaf X).map a.op).app T φ =
      a.hom ≫ (φ : F.obj ⟶ (Scheme.Modules.pushforward T.unop.hom).obj
        (𝟙_ T.unop.left.Modules)) :=
  (rfl)

variable (F : QuasicoherentSheaf X)

/-- `Spec_X (Sym F)` represents the presheaf `T ↦ Hom(F, q_* 𝒪_T)`. -/
def relativeSpecSymmetricAlgebraRepresentableBy :
    ((linearFunctionalsPresheaf X).obj (op F) ⋙ forget _).RepresentableBy
      ((MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) where
  homEquiv {T} := relativeSpecSymmetricAlgebraHomEquiv F T
  homEquiv_comp g t := relativeSpecSymmetricAlgebraHomEquiv_comp F g t

/-- **`Spec_X (Sym F)` is an additive group scheme over `X`.** Its group structure, as an object of
the cartesian monoidal category `Over X`, is the one for which `T`-points form the group
`Hom(F, q_* 𝒪_T)` (`relativeSpecSymmetricAlgebraHomAddEquiv`). -/
instance addGrpObjRelativeSpecSymmetricAlgebra :
    AddGrpObj ((MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :=
  .ofRepresentableBy _ ((linearFunctionalsPresheaf X).obj (op F) ⋙ forget₂ _ _)
    (relativeSpecSymmetricAlgebraRepresentableBy F)

/-- **The group of points of `Spec_X (Sym F)`.** For a scheme `q : T ⟶ X` over `X`, the group of
morphisms `T ⟶ Spec_X (Sym F)` over `X`, for the additive group structure of
`addGrpObjRelativeSpecSymmetricAlgebra`, is the group `Hom(F, q_* 𝒪_T)` of module maps. -/
def relativeSpecSymmetricAlgebraHomAddEquiv (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) ≃+
      ToType (((linearFunctionalsPresheaf X).obj (op F)).obj (op T)) where
  toEquiv := (relativeSpecSymmetricAlgebraRepresentableBy F).homEquiv'
  map_add' := ((yonedaAddGrpObjIsoOfRepresentableBy _
    ((linearFunctionalsPresheaf X).obj (op F) ⋙ forget₂ _ _)
      (relativeSpecSymmetricAlgebraRepresentableBy F)).hom.app (op T)).hom.map_add

/-- The module map of a point of `Spec_X (Sym F)` in the group `Hom(F, q_* 𝒪_T)` is the one given
by the universal property `relativeSpecSymmetricAlgebraHomEquiv`. -/
lemma relativeSpecSymmetricAlgebraHomAddEquiv_apply (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraHomAddEquiv F T t = relativeSpecSymmetricAlgebraHomEquiv F T t :=
  (rfl)

/-- The point of `Spec_X (Sym F)` of a module map in `Hom(F, q_* 𝒪_T)` is the one given by the
universal property `relativeSpecSymmetricAlgebraHomEquiv`. -/
lemma relativeSpecSymmetricAlgebraHomAddEquiv_symm_apply (T : Over X)
    (φ : ToType (((linearFunctionalsPresheaf X).obj (op F)).obj (op T))) :
    (relativeSpecSymmetricAlgebraHomAddEquiv F T).symm φ =
      (relativeSpecSymmetricAlgebraHomEquiv F T).symm φ :=
  (rfl)

/-- The isomorphism `relativeSpecSymmetricAlgebraHomAddEquiv` is natural in the scheme over `X`:
composing with `g : T' ⟶ T` over `X` corresponds to composing the module map with pullback of
regular functions along `g`. -/
lemma relativeSpecSymmetricAlgebraHomAddEquiv_comp {T' T : Over X} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraHomAddEquiv F T' (g ≫ t) =
      ((linearFunctionalsPresheaf X).obj (op F)).map g.op
        (relativeSpecSymmetricAlgebraHomAddEquiv F T t) :=
  (relativeSpecSymmetricAlgebraRepresentableBy F).homEquiv'_comp g t

/-- The zero section `X ⟶ Spec_X (Sym F)` corresponds to the zero module map from `F` to the
pushforward of `𝒪_X` along the identity. -/
lemma relativeSpecSymmetricAlgebraHomAddEquiv_zero_hom :
    relativeSpecSymmetricAlgebraHomAddEquiv F (𝟙_ (Over X))
      (ζ : 𝟙_ (Over X) ⟶ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) = 0 :=
  (relativeSpecSymmetricAlgebraRepresentableBy F).homEquiv'.apply_symm_apply 0

/-- The addition morphism `Spec_X (Sym F) ×_X Spec_X (Sym F) ⟶ Spec_X (Sym F)` corresponds to the
sum of the module maps of the two projections. -/
lemma relativeSpecSymmetricAlgebraHomAddEquiv_add_hom :
    relativeSpecSymmetricAlgebraHomAddEquiv F _
      (σ : _ ⟶ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) =
      relativeSpecSymmetricAlgebraHomAddEquiv F _ (fst _ _) +
        relativeSpecSymmetricAlgebraHomAddEquiv F _ (snd _ _) :=
  (relativeSpecSymmetricAlgebraRepresentableBy F).homEquiv'.apply_symm_apply _

/-- **The additive group structure of `Spec_X (Sym F)` is commutative.** -/
instance isCommAddMonObjRelativeSpecSymmetricAlgebra :
    IsCommAddMonObj ((MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) where
  add_comm := (relativeSpecSymmetricAlgebraHomAddEquiv F _).injective (by
    rw [relativeSpecSymmetricAlgebraHomAddEquiv_comp,
      relativeSpecSymmetricAlgebraHomAddEquiv_add_hom, map_add,
      ← relativeSpecSymmetricAlgebraHomAddEquiv_comp,
      ← relativeSpecSymmetricAlgebraHomAddEquiv_comp, braiding_hom_fst, braiding_hom_snd, add_comm])

/-- The isomorphism `relativeSpecSymmetricAlgebraHomAddEquiv` is natural in the quasicoherent
sheaf: composing with the relative-spectrum map of `Sym a` for `a : F' ⟶ F` corresponds to
precomposing the module map with `a`. -/
lemma relativeSpecSymmetricAlgebraHomAddEquiv_comp_relativeSpec_map {F' F : QuasicoherentSheaf X}
    (a : F' ⟶ F) (T : Over X) (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraHomAddEquiv F' T
        (t ≫ (MorphismProperty.Over.forget _ _ X).map
          ((relativeSpec X).map ((symmetricAlgebra X).map a).op)) =
      ((linearFunctionalsPresheaf X).map a.op).app (op T)
        (relativeSpecSymmetricAlgebraHomAddEquiv F T t) :=
  relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map a T t

/-- **The morphism `Spec_X (Sym F) ⟶ Spec_X (Sym F')` induced by `a : F' ⟶ F` is a homomorphism of
group schemes over `X`.** -/
instance isAddMonHom_relativeSpec_map {F' F : QuasicoherentSheaf X} (a : F' ⟶ F) :
    IsAddMonHom ((MorphismProperty.Over.forget _ _ X).map
      ((relativeSpec X).map ((symmetricAlgebra X).map a).op)) where
  zero_hom := (relativeSpecSymmetricAlgebraHomAddEquiv F' _).injective (by
    rw [relativeSpecSymmetricAlgebraHomAddEquiv_comp_relativeSpec_map,
      relativeSpecSymmetricAlgebraHomAddEquiv_zero_hom,
      relativeSpecSymmetricAlgebraHomAddEquiv_zero_hom, map_zero])
  add_hom := (relativeSpecSymmetricAlgebraHomAddEquiv F' _).injective (by
    -- both sides have module map `a ≫ φ₁ + a ≫ φ₂`, for `φᵢ` the module maps of the projections
    rw [relativeSpecSymmetricAlgebraHomAddEquiv_comp_relativeSpec_map,
      relativeSpecSymmetricAlgebraHomAddEquiv_comp, relativeSpecSymmetricAlgebraHomAddEquiv_add_hom,
      relativeSpecSymmetricAlgebraHomAddEquiv_add_hom, map_add, map_add,
      ← relativeSpecSymmetricAlgebraHomAddEquiv_comp_relativeSpec_map,
      ← relativeSpecSymmetricAlgebraHomAddEquiv_comp_relativeSpec_map,
      ← relativeSpecSymmetricAlgebraHomAddEquiv_comp,
      ← relativeSpecSymmetricAlgebraHomAddEquiv_comp, tensorHom_fst, tensorHom_snd])

variable (X) in
/-- `F ↦ Spec_X (Sym F)` as a contravariant functor from quasicoherent sheaves on `X` to
commutative group schemes over `X`: the relative-spectrum map of `Sym a` for `a : F' ⟶ F` is a
homomorphism of group schemes by `isAddMonHom_relativeSpec_map`. -/
-- exposed so that its underlying objects and morphisms are seen to be those of relative Spec
@[expose]
def relativeSpecSymmetricAlgebraAddGrp : (QuasicoherentSheaf X)ᵒᵖ ⥤ AddGrp (Over X) where
  obj F := .mk ((MorphismProperty.Over.forget _ _ X).obj
    ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F.unop))))
  map a := AddGrp.ofHom ((MorphismProperty.Over.forget _ _ X).map
    ((relativeSpec X).map ((symmetricAlgebra X).map a.unop).op))
  map_id F := by
    ext1
    simp
  map_comp a b := by
    ext1
    simp

/-- The group scheme `(relativeSpecSymmetricAlgebraAddGrp X).obj F` is `Spec_X (Sym F)`. -/
@[simp]
lemma relativeSpecSymmetricAlgebraAddGrp_obj_X (F : (QuasicoherentSheaf X)ᵒᵖ) :
    ((relativeSpecSymmetricAlgebraAddGrp X).obj F).X = (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F.unop))) :=
  (rfl)

/-- The homomorphism of group schemes `(relativeSpecSymmetricAlgebraAddGrp X).map a` is the
relative-spectrum map of `Sym a`. -/
@[simp]
lemma relativeSpecSymmetricAlgebraAddGrp_map_hom_hom {F G : (QuasicoherentSheaf X)ᵒᵖ}
    (a : F ⟶ G) :
    ((relativeSpecSymmetricAlgebraAddGrp X).map a).hom.hom =
      (MorphismProperty.Over.forget _ _ X).map
        ((relativeSpec X).map ((symmetricAlgebra X).map a.unop).op) :=
  (rfl)

/-- **The group of points of `Spec_X (Sym F)` as linear functionals.** For a scheme `q : T ⟶ X`
over `X`, the group of morphisms `T ⟶ Spec_X (Sym F)` over `X` is the group of morphisms of
`𝒪_T`-modules `q^* F ⟶ 𝒪_T`. It is `relativeSpecSymmetricAlgebraHomAddEquiv` followed by the
adjunction between pullback and pushforward of modules. -/
def relativeSpecSymmetricAlgebraPullbackHomAddEquiv (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) ≃+
      ((Scheme.Modules.pullback T.hom).obj F.obj ⟶ 𝟙_ T.left.Modules) :=
  (relativeSpecSymmetricAlgebraHomAddEquiv F T).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homAddEquiv _ _).symm

/-- The linear functional of a point of `Spec_X (Sym F)` in the group `Hom(q^* F, 𝒪_T)` is the one
given by `relativeSpecSymmetricAlgebraPullbackHomEquiv`. -/
lemma relativeSpecSymmetricAlgebraPullbackHomAddEquiv_apply (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraPullbackHomAddEquiv F T t =
      relativeSpecSymmetricAlgebraPullbackHomEquiv F T t :=
  (relativeSpecSymmetricAlgebraPullbackHomEquiv_apply F T t).symm

end

end TauCeti.AlgebraicGeometry
