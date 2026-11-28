/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Sites.CoversTop
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor
public import TauCeti.CategoryTheory.Sites.Over.Basic
public import TauCeti.CategoryTheory.Sites.PseudofunctorSheafOver

/-!
# Torsors on slice sites and the pseudofunctor of torsors

Let `G` be a sheaf of groups on a site `(C, J)`. For `U : C`, the restriction `G.over U` of `G`
(Mathlib's `CategoryTheory.Sheaf.over`) is a sheaf of groups on the slice site `J.over U`. This
file restricts torsors under `G.over U` along a morphism `a : V ⟶ U` to torsors under `G.over V`
(`CategoryTheory.Sheaf.Torsor.overMapPullback`): the sheaf is restricted along `Over.map a`, by
Mathlib's `GrothendieckTopology.overMapPullback`, the sections of `G` act as before, since the
sections of `G.over V` over `X` and those of `G.over U` over `(Over.map a).obj X` are both the
sections of `G` over `X.left`, and the restriction stays locally nonempty because `Over.map a` is
cocontinuous (`GrothendieckTopology.CoversTop.of_isCocontinuous`).

The restrictions along identities and composites are identified, up to the identifications of
`Over.mapId` and `Over.mapComp`, by the isomorphisms `Torsor.overMapPullbackId` and
`Torsor.overMapPullbackComp`, whose underlying isomorphisms of sheaves are those of Mathlib's
pseudofunctor `J.pseudofunctorOver (Type w)` of sheaves on slices. They satisfy the coherence
conditions of a pseudofunctor (`Torsor.overMapPullbackComp_assoc`,
`Torsor.overMapPullbackComp_comp_id`, `Torsor.overMapPullbackComp_id_comp`), which gives the
pseudofunctor of torsors `CategoryTheory.Sheaf.torsorPseudofunctor G` with fibre
`Torsor (G.over U)` over `U`. Its fibres are groupoids, and taking the underlying sheaves is a
strong transformation `Sheaf.torsorPseudofunctorForget` to `J.pseudofunctorOver (Type w)`, with
identity naturality isomorphisms. That `torsorPseudofunctor G` is a stack, indeed a gerbe, is
proved in `TauCeti.CategoryTheory.Sites.Descent.TorsorStack`.

## Main declarations

* `CategoryTheory.Sheaf.Torsor.overMapPullback`: the restriction of torsors along `V ⟶ U`.
* `CategoryTheory.Sheaf.Torsor.overMapPullbackId` and
  `CategoryTheory.Sheaf.Torsor.overMapPullbackComp`: its unit and composition isomorphisms, with
  their coherence conditions.
* `CategoryTheory.Sheaf.torsorPseudofunctor`: the pseudofunctor `U ↦ Torsor (G.over U)`.
* `CategoryTheory.Sheaf.torsorPseudofunctorForget`: the strong transformation to the pseudofunctor
  of sheaves on slices that forgets the action.

The pseudofunctor of sheaves on slices `J.pseudofunctorOver` is Joël Riou's.
-/

public section

universe w v u

namespace CategoryTheory.Sheaf

open Opposite Bicategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Torsor

variable {G : Sheaf J GrpCat.{w}}

variable {U V W : C}

/-- The restriction of a torsor under `G.over U` along `a : V ⟶ U`, a torsor under `G.over V`:
its sections over `X : Over V` are the sections over `(Over.map a).obj X`, on which the sections
of `G` over `X.left` act.

The body is exposed because the sheaf of the restriction is, by definition, the restriction of
the sheaf, and its sections are acted on as sections of `P`; statements about the restriction
apply the action of `P` to them. -/
@[expose] def overMapPullbackObj (a : V ⟶ U) (P : Torsor (G.over U)) : Torsor (G.over V) where
  sheaf := (J.overMapPullback (Type w) a).obj P.sheaf
  mulAction X := P.mulAction (op ((Over.map a).obj X.unop))
  map_smul _ _ f g p := P.map_smul ((Over.map a).map f.unop).op g p
  coversTop := P.coversTop.of_isCocontinuous (Over.map a) P.sheaf.obj
  bijective X := P.bijective (op ((Over.map a).obj X.unop))

/-- The restriction of torsors along `a : V ⟶ U`, from torsors under `G.over U` to torsors under
`G.over V`. It lies over the restriction `J.overMapPullback (Type w) a` of sheaves. The body is
exposed for the same reason as that of `overMapPullbackObj`. -/
@[expose] def overMapPullback (a : V ⟶ U) : Torsor (G.over U) ⥤ Torsor (G.over V) where
  obj := overMapPullbackObj a
  map φ := ⟨(J.overMapPullback (Type w) a).map φ.hom,
    fun X g p ↦ φ.map_smul (op ((Over.map a).obj X.unop)) g p⟩

/-- The sheaf of the restriction of a torsor is the restriction of its sheaf. -/
@[simp]
lemma overMapPullback_obj_sheaf (a : V ⟶ U) (P : Torsor (G.over U)) :
    ((overMapPullback a).obj P).sheaf = (J.overMapPullback (Type w) a).obj P.sheaf :=
  (rfl)

/-- The sections of `G` act on the sections of the restriction of a torsor as on the sections of
the torsor over the image under `Over.map a`: the right-hand side is the action of `P` on its
sections over `(Over.map a).obj X`. -/
@[simp]
lemma overMapPullback_obj_smul (a : V ⟶ U) (P : Torsor (G.over U)) {X : Over V}
    (g : (G.over V).obj.obj (op X)) (p : ((overMapPullback a).obj P).sheaf.obj.obj (op X)) :
    g • p = HSMul.hSMul (α := (G.over U).obj.obj (op ((Over.map a).obj X)))
      (β := P.sheaf.obj.obj (op ((Over.map a).obj X))) g p :=
  (rfl)

/-- The underlying morphism of sheaves of the restriction of a morphism of torsors is the
restriction of the underlying morphism of sheaves. -/
@[simp]
lemma overMapPullback_map_hom (a : V ⟶ U) {P Q : Torsor (G.over U)} (φ : P ⟶ Q) :
    ((overMapPullback a).map φ).hom = (J.overMapPullback (Type w) a).map φ.hom :=
  (rfl)

variable (G) in
/-- The restriction of torsors along an identity is the identity, up to the identifications of
`Over.mapId`. -/
def overMapPullbackId (U : C) : overMapPullback (G := G) (𝟙 U) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ isoMk ((J.overMapPullbackId (Type w) U).app P.sheaf)
    (fun X g p ↦ by
      refine ((P.map_smul ((Over.mapId U).inv.app X.unop).op g p).trans (congrArg (· • _) ?_))
      -- The restriction is along a morphism whose underlying morphism of `C` is an identity.
      exact over_obj_map_apply_of_left_eq_id G ((Over.mapId U).inv.app X.unop) rfl g))
    (fun φ ↦ by ext1; exact (J.overMapPullbackId (Type w) U).hom.naturality φ.hom)

variable (G) in
/-- The restriction of torsors along a composite `b ≫ a = ab` is the restriction along `a` followed
by the restriction along `b`, up to the identifications of `Over.map`. The underlying isomorphism
of sheaves is the composition isomorphism `mapComp'` of the pseudofunctor of sheaves on
slices. -/
def overMapPullbackComp (a : V ⟶ U) (b : W ⟶ V) (ab : W ⟶ U) (h : b ≫ a = ab) :
    overMapPullback (G := G) ab ≅ overMapPullback a ⋙ overMapPullback b :=
  NatIso.ofComponents (fun P ↦ isoMk ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type w)).mapComp'
      a.op.toLoc b.op.toLoc ab.op.toLoc (by rw [← h]; rfl))).app P.sheaf) (fun ⟨X⟩ g p ↦ by
      have key : ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type w)).mapComp'
          a.op.toLoc b.op.toLoc ab.op.toLoc (by rw [← h]; rfl))).app P.sheaf).hom.hom.app (op X) =
            P.sheaf.obj.map (Over.homMk (𝟙 X.left) (by simp [← h]) :
              (Over.map a).obj ((Over.map b).obj X) ⟶ (Over.map ab).obj X).op :=
        GrothendieckTopology.pseudofunctorOver_mapComp'_hom_app b a ab h P.sheaf X
      rw [key]
      refine (P.map_smul (Over.homMk (𝟙 X.left) (by simp [← h]) :
        (Over.map a).obj ((Over.map b).obj X) ⟶ (Over.map ab).obj X).op g p).trans
          (congrArg (· • _) ?_)
      exact over_obj_map_apply_of_left_eq_id (U := U) G _ rfl g))
    (fun φ ↦ by
      ext1
      exact ((J.pseudofunctorOver (Type w)).mapComp' a.op.toLoc b.op.toLoc ab.op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.naturality φ.hom)

/-- The underlying morphisms of sheaves of `overMapPullbackId` are those of Mathlib's
`GrothendieckTopology.overMapPullbackId`. -/
@[simp]
lemma overMapPullbackId_hom_app_hom (U : C) (P : Torsor (G.over U)) :
    ((overMapPullbackId G U).hom.app P).hom = (J.overMapPullbackId (Type w) U).hom.app P.sheaf :=
  (rfl)

/-- The underlying morphisms of sheaves of the inverse of `overMapPullbackId` are those of
Mathlib's `GrothendieckTopology.overMapPullbackId`. -/
@[simp]
lemma overMapPullbackId_inv_app_hom (U : C) (P : Torsor (G.over U)) :
    ((overMapPullbackId G U).inv.app P).hom = (J.overMapPullbackId (Type w) U).inv.app P.sheaf :=
  (rfl)

/-- The underlying morphisms of sheaves of `overMapPullbackComp` are the components of the
composition isomorphisms `mapComp'` of the pseudofunctor of sheaves on slices. -/
@[simp]
lemma overMapPullbackComp_hom_app_hom (a : V ⟶ U) (b : W ⟶ V) (ab : W ⟶ U) (h : b ≫ a = ab)
    (P : Torsor (G.over U)) :
    ((overMapPullbackComp G a b ab h).hom.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapComp' a.op.toLoc b.op.toLoc ab.op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.app P.sheaf :=
  (rfl)

/-- The underlying morphisms of sheaves of the inverse of `overMapPullbackComp` are the
components of the inverses of the isomorphisms `mapComp'` of the pseudofunctor of sheaves on
slices. -/
@[simp]
lemma overMapPullbackComp_inv_app_hom (a : V ⟶ U) (b : W ⟶ V) (ab : W ⟶ U) (h : b ≫ a = ab)
    (P : Torsor (G.over U)) :
    ((overMapPullbackComp G a b ab h).inv.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapComp' a.op.toLoc b.op.toLoc ab.op.toLoc
        (by rw [← h]; rfl)).inv.toNatTrans.app P.sheaf :=
  (rfl)

/-- The composition isomorphisms of the restriction of torsors are associative. -/
lemma overMapPullbackComp_assoc {U₀ U₁ U₂ U₃ : C} (a : U₁ ⟶ U₀) (b : U₂ ⟶ U₁) (c : U₃ ⟶ U₂)
    (ab : U₂ ⟶ U₀) (bc : U₃ ⟶ U₁) (abc : U₃ ⟶ U₀) (hab : b ≫ a = ab) (hbc : c ≫ b = bc)
    (habc : c ≫ ab = abc) (habc' : bc ≫ a = abc) (P : Torsor (G.over U₀)) :
    (overMapPullbackComp G ab c abc habc).hom.app P ≫
        (overMapPullback c).map ((overMapPullbackComp G a b ab hab).hom.app P) =
      (overMapPullbackComp G a bc abc habc').hom.app P ≫
        (overMapPullbackComp G b c bc hbc).hom.app ((overMapPullback a).obj P) :=
  hom_ext ((J.pseudofunctorOver (Type w)).mapComp'_hom_app_comp_map_mapComp'_hom_app
    a.op.toLoc b.op.toLoc c.op.toLoc ab.op.toLoc bc.op.toLoc abc.op.toLoc (by rw [← hab]; rfl)
    (by rw [← hbc]; rfl) (by rw [← habc]; rfl) (by rw [← habc']; rfl) P.sheaf)

/-- The unit law of the composition isomorphisms of the restriction of torsors for a composite
`a ≫ 𝟙 U`. -/
lemma overMapPullbackComp_comp_id (a : V ⟶ U) (h : a ≫ 𝟙 U = a) (P : Torsor (G.over U)) :
    (overMapPullbackComp G (𝟙 U) a a h).hom.app P ≫
      (overMapPullback a).map ((overMapPullbackId G U).hom.app P) = 𝟙 _ := by
  apply hom_ext
  apply ObjectProperty.hom_ext
  ext ⟨X⟩ p
  have key := GrothendieckTopology.pseudofunctorOver_mapComp'_hom_app a (𝟙 U) a h P.sheaf X
  -- The components of a composite of morphisms of sheaves of types are, by definition, the
  -- composites of the components; `change` exhibits them so that `key` applies.
  change ((J.overMapPullbackId (Type w) U).hom.app P.sheaf).hom.app _
    ((((J.pseudofunctorOver (Type w)).mapComp' (𝟙 U).op.toLoc a.op.toLoc a.op.toLoc
      (by simp)).hom.toNatTrans.app P.sheaf).hom.app (op X) p) = p
  rw [key]
  simp only [GrothendieckTopology.overMapPullbackId_hom_app_hom_app]
  -- The two restrictions compose to the restriction along an identity.
  refine (Functor.map_comp_apply P.sheaf.obj _
    ((Over.mapId U).inv.app ((Over.map a).obj X)).op p).symm.trans
      ((congrArg (P.sheaf.obj.map · p) (op_comp.symm.trans
        ((congrArg Quiver.Hom.op ?_).trans op_id))).trans (Functor.map_id_apply P.sheaf.obj _ p))
  ext
  simp

/-- The unit law of the composition isomorphisms of the restriction of torsors for a composite
`𝟙 V ≫ a`. -/
lemma overMapPullbackComp_id_comp (a : V ⟶ U) (h : 𝟙 V ≫ a = a) (P : Torsor (G.over U)) :
    (overMapPullbackComp G a (𝟙 V) a h).hom.app P ≫
      (overMapPullbackId G V).hom.app ((overMapPullback a).obj P) = 𝟙 _ := by
  apply hom_ext
  apply ObjectProperty.hom_ext
  ext ⟨X⟩ p
  have key := GrothendieckTopology.pseudofunctorOver_mapComp'_hom_app (𝟙 V) a a h P.sheaf X
  -- As in `overMapPullbackComp_comp_id`.
  change ((J.overMapPullbackId (Type w) V).hom.app ((overMapPullback a).obj P).sheaf).hom.app _
    ((((J.pseudofunctorOver (Type w)).mapComp' a.op.toLoc (𝟙 V).op.toLoc a.op.toLoc
      (by simp)).hom.toNatTrans.app P.sheaf).hom.app (op X) p) = p
  rw [key]
  simp only [GrothendieckTopology.overMapPullbackId_hom_app_hom_app]
  -- The two restrictions compose to the restriction along an identity.
  refine (Functor.map_comp_apply P.sheaf.obj _
    ((Over.map a).map ((Over.mapId V).inv.app X)).op p).symm.trans
      ((congrArg (P.sheaf.obj.map · p) (op_comp.symm.trans
        ((congrArg Quiver.Hom.op ?_).trans op_id))).trans (Functor.map_id_apply P.sheaf.obj _ p))
  ext
  simp

end Torsor

variable (G : Sheaf J GrpCat.{w})

/-- **The pseudofunctor of torsors** of a sheaf of groups `G` on `(C, J)`: its fibre over `U` is
the groupoid of torsors under the restriction `G.over U` of `G` to the slice site `J.over U`, and
its pullback along `V ⟶ U` is the restriction of torsors `Torsor.overMapPullback`. It lies over
the pseudofunctor `J.pseudofunctorOver (Type w)` of sheaves on slices
(`Sheaf.torsorPseudofunctorForget`). -/
-- The body is exposed so that the fibre over `U` is definitionally `Torsor (G.over U.as.unop)`.
@[expose] def torsorPseudofunctor : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max u v w, max u v (w + 1)} :=
  LocallyDiscrete.mkCatPseudofunctor (obj := fun U ↦ Cat.of (Torsor (G.over U.unop)))
    (fun f ↦ Torsor.overMapPullback f.unop) (fun U ↦ Torsor.overMapPullbackId G U.unop)
    (fun f g fg h ↦ Torsor.overMapPullbackComp G f.unop g.unop fg.unop (by rw [← h]; rfl))
    (fun f g h fg gh fgh hfg hgh hfgh hfgh' P ↦ Torsor.overMapPullbackComp_assoc f.unop g.unop
      h.unop fg.unop gh.unop fgh.unop (by rw [← hfg]; rfl) (by rw [← hgh]; rfl)
      (by rw [← hfgh]; rfl) (by rw [← hfgh']; rfl) P)
    (fun f _ P ↦ Torsor.overMapPullbackComp_comp_id f.unop (by simp) P)
    (fun f _ P ↦ Torsor.overMapPullbackComp_id_comp f.unop (by simp) P)

/-- The fibre of the pseudofunctor of torsors over `U` is the category of torsors under
`G.over U`. -/
@[simp]
lemma torsorPseudofunctor_obj (U : LocallyDiscrete Cᵒᵖ) :
    (torsorPseudofunctor G).obj U = Cat.of (Torsor (G.over U.as.unop)) :=
  (rfl)

/-- The fibres of the pseudofunctor of torsors are groupoids: every morphism of torsors is an
isomorphism (`Torsor.isIso_hom`). -/
instance (U : LocallyDiscrete Cᵒᵖ) : IsGroupoid ((torsorPseudofunctor G).obj U) :=
  inferInstanceAs (IsGroupoid (Torsor (G.over U.as.unop)))

/-- The pullback functors of the pseudofunctor of torsors are the restrictions of torsors. -/
@[simp]
lemma torsorPseudofunctor_map_toFunctor {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) :
    ((torsorPseudofunctor G).map f).toFunctor = Torsor.overMapPullback f.as.unop :=
  (rfl)

/-- The unit isomorphisms `mapId` of the pseudofunctor of torsors lie over those of the
pseudofunctor of sheaves on slices. -/
@[simp]
lemma torsorPseudofunctor_mapId_hom_app_hom (U : LocallyDiscrete Cᵒᵖ)
    (P : Torsor (G.over U.as.unop)) :
    (((torsorPseudofunctor G).mapId U).hom.toNatTrans.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapId U).hom.toNatTrans.app P.sheaf :=
  (rfl)

/-- The inverses of the unit isomorphisms `mapId` of the pseudofunctor of torsors lie over those
of the pseudofunctor of sheaves on slices. -/
@[simp]
lemma torsorPseudofunctor_mapId_inv_app_hom (U : LocallyDiscrete Cᵒᵖ)
    (P : Torsor (G.over U.as.unop)) :
    (((torsorPseudofunctor G).mapId U).inv.toNatTrans.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapId U).inv.toNatTrans.app P.sheaf :=
  (rfl)

/-- The composition isomorphisms `mapComp'` of the pseudofunctor of torsors lie over those of the
pseudofunctor of sheaves on slices. -/
@[simp]
lemma torsorPseudofunctor_mapComp'_hom_app_hom {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (g : V ⟶ W) (fg : U ⟶ W) (h : f ≫ g = fg) (P : Torsor (G.over U.as.unop)) :
    (((torsorPseudofunctor G).mapComp' f g fg h).hom.toNatTrans.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapComp' f g fg h).hom.toNatTrans.app P.sheaf := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The inverses of the composition isomorphisms `mapComp'` of the pseudofunctor of torsors lie
over those of the pseudofunctor of sheaves on slices. -/
@[simp]
lemma torsorPseudofunctor_mapComp'_inv_app_hom {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (g : V ⟶ W) (fg : U ⟶ W) (h : f ≫ g = fg) (P : Torsor (G.over U.as.unop)) :
    (((torsorPseudofunctor G).mapComp' f g fg h).inv.toNatTrans.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapComp' f g fg h).inv.toNatTrans.app P.sheaf := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The forgetful strong transformation from the pseudofunctor of torsors to the pseudofunctor of
sheaves on slices: its components send a torsor to its underlying sheaf, and its naturality
isomorphisms are identities. -/
-- The body is exposed so that the components of the image of a torsor are its underlying sheaf
-- by definition, which the descent data of torsors use.
@[expose] def torsorPseudofunctorForget :
    Pseudofunctor.StrongTrans (torsorPseudofunctor G) (J.pseudofunctorOver (Type w)) where
  app U := (Torsor.toSheaf (G.over U.as.unop)).toCatHom
  naturality f := Iso.refl _
  naturality_naturality η := Pseudofunctor.naturality_naturality_of_locallyDiscrete
    (torsorPseudofunctor G) (J.pseudofunctorOver (Type w))
    (fun U ↦ (Torsor.toSheaf (G.over U.as.unop)).toCatHom) (fun _ ↦ Iso.refl _) η
  naturality_id U := by
    ext P
    rfl
  naturality_comp f g := by
    ext P
    rfl

/-- The components of the forgetful strong transformation send a torsor to its sheaf. -/
@[simp]
lemma torsorPseudofunctorForget_app_toFunctor (U : LocallyDiscrete Cᵒᵖ) :
    ((torsorPseudofunctorForget G).app U).toFunctor = Torsor.toSheaf (G.over U.as.unop) :=
  (rfl)

/-- The naturality isomorphisms of the forgetful strong transformation are identities. -/
@[simp]
lemma torsorPseudofunctorForget_naturality {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) :
    (torsorPseudofunctorForget G).naturality f = Iso.refl _ :=
  (rfl)

end CategoryTheory.Sheaf
