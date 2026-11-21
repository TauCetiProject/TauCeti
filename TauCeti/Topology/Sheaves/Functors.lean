/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.CategoryTheory.Sites.Pullback

/-!
# Pushforward, pullback, and transport of sheaves on topological spaces

Mathlib's `TopCat.Sheaf.pushforward_sheaf_of_sheaf` says that the pushforward of a sheaf along a
continuous map is a sheaf. Along a homeomorphism the converse holds as well, since pushing forward
along the inverse undoes the pushforward. This file records the resulting criterion: a presheaf
isomorphic to the pushforward of another along a homeomorphism is a sheaf exactly when the other
is.

For `TopCat.Sheaf.pushforward`, an equality of a continuous map with an identity or a composite
gives an equality on pushforward objects, and the resulting `eqToHom` transports commute with
pushforward morphisms, evaluate componentwise as `eqToHom` on sections, and agree on underlying
presheaves with right whiskering along `Opens.map`.

It also records that the restriction maps of Mathlib's restriction of a sheaf along an open
embedding, `Topology.IsOpenEmbedding.sheafPullback`, are restriction maps of the original sheaf
between the image opens, and supplies general open-subspace restriction helpers for sheaves and
sheaf morphisms (`TopologicalSpace.Opens.sheafInclusionHom`, `TopologicalSpace.Opens.resLE`,
`TopologicalSpace.Opens.sheafHomResLE`, and `TopologicalSpace.Opens.coversTop_map`).

Finally, it records that the inverse image functor `f⁻¹` of abelian sheaves along a continuous map
`f` is left exact, and that it carries constant sheaves to constant sheaves. Its right exactness
and additivity hold for the pullback along any continuous functor of sites
(`TauCeti/CategoryTheory/Sites/Pullback.lean`).

## Main results

* `TopCat.Presheaf.isSheaf_iff_of_iso_pushforward`: the sheaf condition transfers along an
  isomorphism with a pushforward along a homeomorphism, in both directions.
* `TopCat.Sheaf.pushforward_obj_of_eq_id`, `TopCat.Sheaf.pushforward_obj_of_eq_comp`:
  pushforward of a sheaf along a map equal to an identity or a composite.
* `TopCat.Sheaf.eqToHom_hom_app`: sections of `eqToHom` between equal sheaves.
* `TopCat.Sheaf.eqToHom_symm_comp_pushforward_map_of_eq_id`,
  `TopCat.Sheaf.eqToHom_symm_comp_pushforward_map_of_eq_comp`: naturality of pushforward object
  transport with respect to sheaf morphisms.
* `TopCat.Sheaf.eqToHom_hom_comp_whiskerRight_of_eq_id`,
  `TopCat.Sheaf.eqToHom_hom_eq_whiskerRight_of_eq_comp`: comparison of `eqToHom` on pushforward
  sheaves with right whiskering along `Opens.map`.
* `Topology.IsOpenEmbedding.sheafPullback_obj_obj_map`: the restriction maps of the restriction of
  a sheaf along an open embedding.
* `TopologicalSpace.Opens.sheafInclusionHom`, `TopologicalSpace.Opens.resLE`,
  `TopologicalSpace.Opens.sheafHomResLE`, and `TopologicalSpace.Opens.coversTop_map`: the
  canonical sheaf morphism `F ⟶ (U.inclusion')_* (F|_U)`, the restricted map between open
  subspaces, the restriction of `φ : S ⟶ f_* R` to opens `V ⊆ Y` and `U ⊆ f⁻¹(V)`, and pullback
  of covering families.
* `TopCat.Hom.pullbackConstantSheafIso`: the inverse image of a constant abelian sheaf is
  constant.
-/

public section

universe w v u

open CategoryTheory TopologicalSpace

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X Y : TopCat.{w}}

/-- **The sheaf condition transfers along a homeomorphism.** If `F` is isomorphic to the pushforward
of `G` along a homeomorphism `h`, then `F` is a sheaf exactly when `G` is. -/
theorem isSheaf_iff_of_iso_pushforward (h : Y ≅ X) {F : X.Presheaf C} {G : Y.Presheaf C}
    (α : F ≅ (pushforward C h.hom).obj G) : F.IsSheaf ↔ G.IsSheaf := by
  refine ⟨fun hF ↦ ?_, fun hG ↦ isSheaf_of_iso α.symm (Sheaf.pushforward_sheaf_of_sheaf _ hG)⟩
  -- `G` is the pushforward of `F` along the inverse homeomorphism
  exact isSheaf_of_iso ((pushforward C h.inv).mapIso α ≪≫ (Pushforward.comp h.hom h.inv G).symm ≪≫
      pushforwardEq h.hom_inv_id G ≪≫ Pushforward.id G)
    (Sheaf.pushforward_sheaf_of_sheaf h.inv hF)

end TopCat.Presheaf

namespace TopCat.Sheaf

open Opposite

variable {C : Type u} [Category.{v} C] {X Y Z : TopCat.{w}}

/-- Pushing a sheaf forward along a continuous map equal to the identity returns the sheaf
itself. -/
theorem pushforward_obj_of_eq_id {f : X ⟶ X} (hf : f = 𝟙 X) (F : X.Sheaf C) :
    (pushforward C f).obj F = F := by
  rw [hf]
  rfl

/-- Pushing a sheaf forward along a continuous map equal to a composite agrees with the iterated
pushforward. -/
theorem pushforward_obj_of_eq_comp {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : h = f ≫ g)
    (F : X.Sheaf C) :
    (pushforward C h).obj F = (pushforward C g).obj ((pushforward C f).obj F) := by
  rw [hfg]
  rfl

/-- On sections over `U`, `eqToHom` between equal sheaves is `eqToHom` of the induced equality of
section objects. -/
theorem eqToHom_hom_app {F G : X.Sheaf C} (h : F = G) (U : (Opens X)ᵒᵖ) :
    (eqToHom h).hom.app U = eqToHom (congrArg (fun S ↦ S.obj.obj U) h) := by
  subst h
  rfl

/-- Transporting along `pushforward_obj_of_eq_id` commutes with pushforward of a sheaf
morphism. -/
@[reassoc]
theorem eqToHom_symm_comp_pushforward_map_of_eq_id {f : X ⟶ X} (hf : f = 𝟙 X)
    {F G : X.Sheaf C} (α : F ⟶ G) :
    eqToHom (pushforward_obj_of_eq_id hf F).symm ≫ (pushforward C f).map α =
      α ≫ eqToHom (pushforward_obj_of_eq_id hf G).symm := by
  subst hf
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Transporting along `pushforward_obj_of_eq_comp` intertwines pushforward of a sheaf morphism
along the composite with iterated pushforward. -/
@[reassoc]
theorem eqToHom_symm_comp_pushforward_map_of_eq_comp {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (hfg : h = f ≫ g) {F G : X.Sheaf C} (α : F ⟶ G) :
    eqToHom (pushforward_obj_of_eq_comp hfg F).symm ≫ (pushforward C h).map α =
      (pushforward C g).map ((pushforward C f).map α) ≫
        eqToHom (pushforward_obj_of_eq_comp hfg G).symm := by
  subst hfg
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- For a continuous map equal to the identity, the underlying presheaf morphism of `eqToHom` into
the pushforward cancels right whiskering along `Opens.map`. -/
@[reassoc]
theorem eqToHom_hom_comp_whiskerRight_of_eq_id {f : X ⟶ X} (hf : f = 𝟙 X) {F : X.Sheaf C}
    (hobj : F = (pushforward C f).obj F) (hop : (Opens.map f).op = 𝟭 (Opens X)ᵒᵖ) :
    (eqToHom hobj).hom ≫ Functor.whiskerRight (eqToHom hop) F.obj = 𝟙 F.obj := by
  subst hf
  ext U : 2
  exact (Category.id_comp _).trans (F.obj.map_id U)

/-- For a continuous map equal to a composite, the underlying presheaf morphism of `eqToHom`
between the composite and iterated pushforwards is right whiskering along `Opens.map`. -/
theorem eqToHom_hom_eq_whiskerRight_of_eq_comp {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (hfg : h = f ≫ g) {F : X.Sheaf C}
    (hobj : (pushforward C h).obj F = (pushforward C g).obj ((pushforward C f).obj F))
    (hop : (Opens.map h).op = (Opens.map g).op ⋙ (Opens.map f).op) :
    (eqToHom hobj).hom = Functor.whiskerRight (eqToHom hop) F.obj := by
  subst hfg
  ext U : 2
  exact (F.obj.map_id _).symm

end TopCat.Sheaf

namespace Topology.IsOpenEmbedding

open TopCat

/-- The restriction maps of the restriction of a sheaf along an open embedding are restriction maps
of the original sheaf between the image opens. -/
theorem sheafPullback_obj_obj_map {C : Type u} [Category.{w} C] {X Y : TopCat.{w}} {f : Y ⟶ X}
    (hf : IsOpenEmbedding f) (F : Sheaf C X) {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    ((hf.sheafPullback C).obj F).obj.map i = F.obj.map (hf.functor.map i.unop).op :=
  rfl

end Topology.IsOpenEmbedding

namespace TopCat.Hom

open Limits Opposite

noncomputable section

variable {X Y : TopCat.{w}} (f : X ⟶ Y)

/-- The inverse image of abelian sheaves along a continuous map is left exact. -/
instance : PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{w}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
  have : RepresentablyFlat (Opens.map f) := flat_of_preservesFiniteLimits _
  Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) AddCommGrpCat.{w} _ _

/-- The inverse image of the constant sheaf with value `A` is the constant sheaf with value `A`.
Both functors `A ↦ f⁻¹ A_Y` and `A ↦ A_X` are left adjoint to taking global sections, because
global sections of `f_* G` are global sections of `G`. -/
def pullbackConstantSheafIso (A : AddCommGrpCat.{w}) :
    ((Opens.map f).sheafPullback AddCommGrpCat.{w} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w}).obj A) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj A :=
  (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{w} isTerminalTop).comp
    ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{w} _ _)).leftAdjointUniq
      (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{w} isTerminalTop)).app A

/-- Under the adjunctions between constant sheaves and global sections, precomposing with the
inverse of `pullbackConstantSheafIso` corresponds to composing with the unit `F ⟶ f_* f⁻¹ F` on
global sections. -/
lemma constantSheafAdj_homEquiv_pullbackConstantSheafIso_inv
    {A : AddCommGrpCat.{w}}
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w}}
    (a : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w}).obj A ⟶ F) :
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{w} isTerminalTop).homEquiv _ _
        ((f.pullbackConstantSheafIso A).inv ≫
          ((Opens.map f).sheafPullback AddCommGrpCat.{w} _ _).map a) =
      (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{w} isTerminalTop).homEquiv _ _
        a ≫ (((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{w}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app F).hom.app
            (op ⊤) := by
  let adj₁ := (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{w}
    isTerminalTop).comp ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{w}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
  let adj₂ := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{w} isTerminalTop
  have e : (f.pullbackConstantSheafIso A).inv = (adj₂.leftAdjointUniq adj₁).hom.app A := rfl
  rw [e, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  -- The two adjunctions have definitionally equal right adjoints, but not syntactically equal ones.
  erw [Adjunction.unit_leftAdjointUniq_hom_app adj₂ adj₁ A]
  -- The left side is the unit form of `adj₁.homEquiv`; `adj₁`'s right adjoint is only
  -- definitionally the one of `adj₂`, so `Adjunction.homEquiv_unit` cannot fold it back.
  change adj₁.homEquiv _ _ (((Opens.map f).sheafPullback AddCommGrpCat.{w}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map a) = _
  rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  -- `(unit.app F).hom.app (op ⊤)` is the map on global sections of the unit, written as the
  -- image of the unit under the global sections functor so that `homEquiv_naturality_right`
  -- applies.
  change _ = _ ≫ ((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{w}).obj (op ⊤)).map
    (((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{w} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).unit.app F)
  rw [← Adjunction.homEquiv_naturality_right]
  congr 1
  rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]

end

end TopCat.Hom

namespace TopologicalSpace.Opens

open Opposite Topology

section SheafRestriction

noncomputable section

variable {X Y : TopCat.{u}}

/-- For an open subset `U` of `X` and a sheaf `F` on `X`, the canonical morphism
`F ⟶ (U.inclusion')_* (F|_U)` induced by the counit
`(U.inclusion') '' ((U.inclusion')⁻¹ W) ≤ W` of `U.isOpenEmbedding.isOpenMap.adjunction`. -/
def sheafInclusionHom (U : Opens X) (A : Type*) [Category.{u} A] (F : X.Sheaf A) :
    F ⟶ ((Opens.map U.inclusion').sheafPushforwardContinuous A
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))).obj
        ((U.isOpenEmbedding.sheafPullback A).obj F) where
  hom :=
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit) F.obj

/-- On sections over `W`, `sheafInclusionHom` restricts along `W ⊓ U ≤ W`. -/
@[simp]
theorem sheafInclusionHom_hom_app (U : Opens X) (A : Type*) [Category.{u} A]
    (F : X.Sheaf A) (W : (Opens X)ᵒᵖ) :
    (U.sheafInclusionHom A F).hom.app W =
      F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop).op :=
  (rfl)

/-- The continuous map `(Opens.toTopCat X).obj U ⟶ (Opens.toTopCat Y).obj V` between open
subspaces induced by `f : X ⟶ Y` when `U ≤ (Opens.map f).obj V`. -/
def resLE (f : X ⟶ Y) (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    (Opens.toTopCat X).obj U ⟶ (Opens.toTopCat Y).obj V :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x.1, e x.2⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- `Opens.resLE` commutes with the open inclusions `Opens.inclusion'` into `X` and `Y`. -/
@[reassoc (attr := simp)]
theorem resLE_comp_inclusion' (f : X ⟶ Y) (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    Opens.resLE f V U e ≫ V.inclusion' = U.inclusion' ≫ f := by
  ext x
  rfl

/-- Underlying point value of `Opens.resLE`. -/
@[simp]
theorem inclusion'_resLE_apply (f : X ⟶ Y) (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) (x : (Opens.toTopCat X).obj U) :
    V.inclusion' (Opens.resLE f V U e x) = f (U.inclusion' x) :=
  (rfl)

/-- For an open `W` of `(Opens.toTopCat Y).obj V` and `e : U ≤ (Opens.map f).obj V`, the image in
`X` of the preimage of `W` under `Opens.resLE f V U e` is contained in the preimage under `f` of
the image of `W` in `Y`. -/
theorem functor_map_resLE_le (f : X ⟶ Y) (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) (W : Opens ((Opens.toTopCat Y).obj V)) :
    U.isOpenEmbedding.functor.obj ((Opens.map (Opens.resLE f V U e)).obj W) ≤
      (Opens.map f).obj (V.isOpenEmbedding.functor.obj W) := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨⟨f u.1, e u.2⟩, hu, rfl⟩

/-- Restriction of a sheaf morphism `φ : S ⟶ f_* R` to open subspaces `V ⊆ Y` and `U ⊆ f⁻¹(V)`
along `Opens.resLE f V U e`. -/
def sheafHomResLE {A : Type*} [Category.{u} A] {f : X ⟶ Y}
    {S : Y.Sheaf A} {R : X.Sheaf A}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    (V.isOpenEmbedding.sheafPullback A).obj S ⟶
      ((Opens.map (Opens.resLE f V U e)).sheafPushforwardContinuous A
        (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V))
        (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))).obj
          ((U.isOpenEmbedding.sheafPullback A).obj R) where
  hom :=
    { app W := φ.hom.app (op (V.isOpenEmbedding.functor.obj W.unop)) ≫
        R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e W.unop)).op
      naturality W₁ W₂ g := by
        let a := S.obj.map (V.isOpenEmbedding.functor.map g.unop).op
        let b₁ : S.obj.obj (op (V.isOpenEmbedding.functor.obj W₁.unop)) ⟶
            R.obj.obj (op ((Opens.map f).obj (V.isOpenEmbedding.functor.obj W₁.unop))) :=
          φ.hom.app (op (V.isOpenEmbedding.functor.obj W₁.unop))
        let b₂ : S.obj.obj (op (V.isOpenEmbedding.functor.obj W₂.unop)) ⟶
            R.obj.obj (op ((Opens.map f).obj (V.isOpenEmbedding.functor.obj W₂.unop))) :=
          φ.hom.app (op (V.isOpenEmbedding.functor.obj W₂.unop))
        let c₁ := R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e W₁.unop)).op
        let c₂ := R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e W₂.unop)).op
        let d := R.obj.map
          (U.isOpenEmbedding.functor.map ((Opens.map (Opens.resLE f V U e)).map g.unop)).op
        let e₀ := R.obj.map ((Opens.map f).map (V.isOpenEmbedding.functor.map g.unop)).op
        have hnat : a ≫ b₂ = b₁ ≫ e₀ :=
          φ.hom.naturality (V.isOpenEmbedding.functor.map g.unop).op
        have hR : e₀ ≫ c₂ = c₁ ≫ d := by
          rw [← R.obj.map_comp, ← R.obj.map_comp, ← op_comp, ← op_comp]
          exact congrArg (R.obj.map ∘ Quiver.Hom.op) (Subsingleton.elim _ _)
        exact (Category.assoc a b₂ c₂).symm.trans
          ((congrArg (· ≫ c₂) hnat).trans
            ((Category.assoc b₁ e₀ c₂).trans
              ((congrArg (b₁ ≫ ·) hR).trans (Category.assoc b₁ c₁ d).symm))) }

/-- Component of `Opens.sheafHomResLE` on an open `W` of `(Opens.toTopCat Y).obj V`. -/
@[simp]
theorem sheafHomResLE_hom_app {A : Type*} [Category.{u} A] {f : X ⟶ Y}
    {S : Y.Sheaf A} {R : X.Sheaf A}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V)
    (W : (Opens ((Opens.toTopCat Y).obj V))ᵒᵖ) :
    (Opens.sheafHomResLE φ V U e).hom.app W =
      φ.hom.app (op (V.isOpenEmbedding.functor.obj W.unop)) ≫
        R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e W.unop)).op :=
  (rfl)

/-- Natural isomorphism between composed open-preimage functors witnessing the commutative square
`resLE_comp_inclusion'`. -/
def mapCompResLEIso (f : X ⟶ Y) (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    Opens.map f ⋙ Opens.map U.inclusion' ≅
      Opens.map V.inclusion' ⋙ Opens.map (Opens.resLE f V U e) :=
  Opens.mapIso (U.inclusion' ≫ f) (Opens.resLE f V U e ≫ V.inclusion')
    (Opens.resLE_comp_inclusion' f V U e).symm

/-- Compatibility of `sheafHomResLE` with `sheafInclusionHom`: restricting `S` to `V` and applying
`sheafHomResLE` agrees with applying `φ` and restricting `R` to `U` along the commutative square
`resLE_comp_inclusion'`. -/
theorem sheafInclusionHom_comp_map_sheafHomResLE {A : Type*} [Category.{u} A] {f : X ⟶ Y}
    {S : Y.Sheaf A} {R : X.Sheaf A}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    letI : (Opens.map f ⋙ Opens.map U.inclusion').IsContinuous
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
      Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
    letI : (Opens.map V.inclusion' ⋙ Opens.map (Opens.resLE f V U e)).IsContinuous
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
      Functor.isContinuous_comp _ _ _
        (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V)) _
    (V.sheafInclusionHom A S ≫
          ((Opens.map V.inclusion').sheafPushforwardContinuous A
            (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V))).map
              (Opens.sheafHomResLE φ V U e) :
        S ⟶ ((Opens.map V.inclusion' ⋙
            Opens.map (Opens.resLE f V U e)).sheafPushforwardContinuous
          A (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))).obj
            ((U.isOpenEmbedding.sheafPullback A).obj R)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (Opens.mapCompResLEIso f V U e).hom A
          (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))).app
            ((U.isOpenEmbedding.sheafPullback A).obj R) =
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous A
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map
            (U.sheafInclusionHom A R) :
        S ⟶ ((Opens.map f ⋙ Opens.map U.inclusion').sheafPushforwardContinuous
          A (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))).obj
            ((U.isOpenEmbedding.sheafPullback A).obj R)) := by
  have : (Opens.map f ⋙ Opens.map U.inclusion').IsContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
  have : (Opens.map V.inclusion' ⋙ Opens.map (Opens.resLE f V U e)).IsContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V)) _
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Z ↦ ?_))
  let τ := (Opens.mapCompResLEIso f V U e).hom
  let a := S.obj.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app Z.unop).op
  let b₁ : S.obj.obj Z ⟶ R.obj.obj (op ((Opens.map f).obj Z.unop)) := φ.hom.app Z
  let b₂ : S.obj.obj (op (V.isOpenEmbedding.functor.obj
        ((Opens.map V.inclusion').obj Z.unop))) ⟶
      R.obj.obj (op ((Opens.map f).obj (V.isOpenEmbedding.functor.obj
        ((Opens.map V.inclusion').obj Z.unop)))) :=
    φ.hom.app (op (V.isOpenEmbedding.functor.obj ((Opens.map V.inclusion').obj Z.unop)))
  let c := R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e
    ((Opens.map V.inclusion').obj Z.unop))).op
  let d := R.obj.map (U.isOpenEmbedding.functor.map (τ.app Z.unop)).op
  let e₀ := R.obj.map ((Opens.map f).map
    (V.isOpenEmbedding.isOpenMap.adjunction.counit.app Z.unop)).op
  let e₁ := R.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
    ((Opens.map f).obj Z.unop)).op
  have hnat : a ≫ b₂ = b₁ ≫ e₀ :=
    φ.hom.naturality (V.isOpenEmbedding.isOpenMap.adjunction.counit.app Z.unop).op
  have hR : (e₀ ≫ c) ≫ d = e₁ := by
    rw [← R.obj.map_comp, ← R.obj.map_comp, ← op_comp, ← op_comp]
    exact congrArg (R.obj.map ∘ Quiver.Hom.op) (Subsingleton.elim _ _)
  exact (congrArg (· ≫ d) ((Category.assoc a b₂ c).symm.trans
    ((congrArg (· ≫ c) hnat).trans (Category.assoc b₁ e₀ c)))).trans
      ((Category.assoc b₁ (e₀ ≫ c) d).trans (congrArg (b₁ ≫ ·) hR))

/-- Pulling back a covering family of opens along a continuous map `f : X ⟶ Y` gives a covering
family of opens of `X`. -/
theorem coversTop_map (f : X ⟶ Y) {ι : Type*} {V : ι → Opens Y}
    (hV : (Opens.grothendieckTopology Y).CoversTop V) :
    (Opens.grothendieckTopology X).CoversTop (fun i ↦ (Opens.map f).obj (V i)) := by
  rw [Opens.coversTop_iff] at hV ⊢
  rw [IsOpenCover, ← Function.comp_def, ← Opens.map_iSup, hV.iSup_eq_top, Opens.map_top]

end

end SheafRestriction

end TopologicalSpace.Opens
