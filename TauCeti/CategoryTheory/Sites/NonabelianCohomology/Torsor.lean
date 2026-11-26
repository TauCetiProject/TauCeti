/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.CartesianMonoidal
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Torsors under a sheaf of groups and their classes

Let `G` be a sheaf of groups on a site `(C, J)`. A `G`-torsor is a sheaf of sets `P` with a left
action of `G` which is locally nonempty and on which `G` acts simply transitively, that is, the
map `G × P → P × P`, `(g, p) ↦ (g • p, p)`, is an isomorphism. This file defines `G`-torsors, their
morphisms, and the pointed set `NonabelianH1 G` of isomorphism classes of `G`-torsors, whose base
point is the class of the trivial torsor `G`.

This is the intrinsic, cover-free description of the first cohomology of a sheaf of possibly
nonabelian groups. Mathlib's `CategoryTheory.PresheafOfGroups.H1` is the cocycle description
relative to a fixed family of objects; here no covering is chosen.

## Main declarations

* `CategoryTheory.Sheaf.Torsor G`: a `G`-torsor; the action is objectwise and compatible with
  restriction, the local nonemptiness is phrased with Mathlib's `GrothendieckTopology.CoversTop`.
* `CategoryTheory.Sheaf.Torsor.isIso_hom`: a morphism of `G`-torsors is an isomorphism of
  sheaves, so the category of `G`-torsors is a groupoid.
* `CategoryTheory.Sheaf.Torsor.trivial G`: the trivial torsor, `G` acting on itself by left
  multiplication.
* `CategoryTheory.Sheaf.Torsor.trivialHomEquiv`: morphisms from the trivial torsor to `P` are
  the global sections of `P`.
* `CategoryTheory.Sheaf.Torsor.isoOfSection`: a section of `P` along a functor `u` identifies
  the restrictions of `G` and of `P` along `u`.
* `CategoryTheory.Sheaf.Torsor.exists_sections_eq_of_smul_invariant`: a `G`-invariant morphism
  from a torsor to a sheaf of sets is given by a global section.
* `CategoryTheory.Sheaf.Torsor.isIso_of_bijective_app`: a morphism of sheaves of sets which is
  bijective over every object over which a torsor has a section is an isomorphism.
* `CategoryTheory.Sheaf.Torsor.hom_ext_of_coversTop`: two morphisms of torsors which agree on
  one section over each object of a covering family are equal.
* `CategoryTheory.Sheaf.Torsor.prod P Q`: the product of a `G`-torsor and an `H`-torsor, a torsor
  under `G × H`.
* `CategoryTheory.Sheaf.NonabelianH1 G`: the pointed set of isomorphism classes of `G`-torsors,
  with `NonabelianH1.mk`, `NonabelianH1.lift` and `NonabelianH1.mk_eq_mk_iff`.
* `CategoryTheory.Sheaf.NonabelianH1.mk_eq_one_iff`: a torsor is trivial if and only if it has a
  global section.
* `CategoryTheory.Sheaf.NonabelianH1.subsingleton_of_isTerminal_of_id_mem`: if every covering
  sieve of a terminal object contains its identity, every torsor is trivial.

## References

* [The Stacks project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG),
  Definition 21.4.1 (03AH) and Lemma 21.4.2 (03AI).
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A torsor under a sheaf of groups `G` (Stacks, Definition 21.4.1 (03AH)): a sheaf of sets
with a left action of `G` which is locally nonempty and on which `G` acts simply transitively. -/
structure Torsor (G : Sheaf J GrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf J (Type w)
  /-- The action of the sections of `G` on the sections of the torsor. -/
  [mulAction (U : Cᵒᵖ) : MulAction (G.obj.obj U) (sheaf.obj.obj U)]
  /-- The action commutes with restriction. -/
  map_smul ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (g : G.obj.obj U) (p : sheaf.obj.obj U) :
    sheaf.obj.map f (g • p) = G.obj.map f g • sheaf.obj.map f p
  /-- The torsor is locally nonempty: the objects over which it has a section cover the site. -/
  coversTop : J.CoversTop fun U : {U : C // Nonempty (sheaf.obj.obj (op U))} ↦ U.val
  /-- The action is simply transitive: `(g, p) ↦ (g • p, p)` is a bijection on sections. -/
  bijective (U : Cᵒᵖ) :
    Function.Bijective fun x : G.obj.obj U × sheaf.obj.obj U ↦ (x.1 • x.2, x.2)

attribute [instance] Torsor.mulAction

namespace Torsor

variable {G : Sheaf J GrpCat.{w}}

section Action

variable (P : Torsor G) (U : Cᵒᵖ)

/-- On each object, the action of `G` on the sections of a torsor is pretransitive. -/
instance isPretransitive : MulAction.IsPretransitive (G.obj.obj U) (P.sheaf.obj.obj U) where
  exists_smul_eq p q := by
    obtain ⟨⟨g, p'⟩, h⟩ := (P.bijective U).2 (q, p)
    obtain ⟨hq, rfl⟩ := Prod.ext_iff.1 h
    exact ⟨g, hq⟩

variable {U} in
/-- The action on the sections of a torsor is free. -/
lemma smul_left_injective (p : P.sheaf.obj.obj U) :
    Function.Injective fun g : G.obj.obj U ↦ g • p := fun g h hgh ↦
  (Prod.ext_iff.1 (@(P.bijective U).1 (g, p) (h, p) (Prod.ext hgh rfl))).1

end Action

/-- A morphism of `G`-torsors: a `G`-equivariant morphism of the underlying sheaves. -/
@[ext]
structure Hom (P Q : Torsor G) where
  /-- The underlying morphism of sheaves. -/
  hom : P.sheaf ⟶ Q.sheaf
  /-- The morphism is `G`-equivariant. -/
  map_smul (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U) :
    hom.hom.app U (g • p) = g • hom.hom.app U p

instance : Category (Torsor G) where
  Hom := Hom
  id P := ⟨𝟙 _, fun _ _ _ ↦ rfl⟩
  comp f g := ⟨f.hom ≫ g.hom, fun U a p ↦ by simp [f.map_smul, g.map_smul]⟩

variable {P Q R : Torsor G}

@[ext]
lemma hom_ext {f g : P ⟶ Q} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma id_hom (P : Torsor G) : Hom.hom (𝟙 P) = 𝟙 P.sheaf := rfl

@[simp]
lemma comp_hom (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- A morphism of torsors is injective on sections. -/
lemma injective_app (f : P ⟶ Q) (U : Cᵒᵖ) : Function.Injective (f.hom.hom.app U) := by
  intro p p' h
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (G.obj.obj U) p p'
  rw [f.map_smul] at h
  obtain rfl : g = 1 := Q.smul_left_injective _ (h.symm.trans (one_smul _ _).symm)
  exact (one_smul _ _).symm

/-- A morphism of torsors is an isomorphism of the underlying sheaves: it is injective on
sections, and locally surjective because the source is locally nonempty. -/
instance isIso_hom (f : P ⟶ Q) : IsIso f.hom := by
  refine (Sheaf.isLocallyBijective_iff_isIso (A := Type w) f.hom).1
    ⟨Presheaf.isLocallyInjective_of_injective _ _ (injective_app f), ⟨fun {U} q ↦ ?_⟩⟩
  refine J.superset_covering ?_ (P.coversTop U)
  rintro V a ⟨⟨W, ⟨p⟩⟩, ⟨b⟩⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G.obj.obj (op V))
    (f.hom.hom.app _ (P.sheaf.obj.map b.op p)) (Q.sheaf.obj.map a.op q)
  exact ⟨g • P.sheaf.obj.map b.op p, by rw [f.map_smul, hg]⟩

/-- Every morphism of torsors is an isomorphism. -/
instance : IsGroupoid (Torsor G) where
  all_isIso f := by
    refine ⟨⟨⟨inv f.hom, fun U g q ↦ injective_app f U ?_⟩, ?_, ?_⟩⟩
    · simp [f.map_smul]
    · ext1; simp
    · ext1; simp

variable (G) in
/-- The trivial `G`-torsor: `G` acting on itself by left multiplication.

The body is exposed because the sections of the trivial torsor are, by definition, the sections
of `G`; statements about morphisms out of it apply them to elements of `G`. Use `trivial_sheaf`
and `trivial_smul` rather than unfolding it. -/
@[expose] def trivial : Torsor G where
  sheaf := (sheafCompose J (forget GrpCat.{w})).obj G
  mulAction U := Monoid.toMulAction (G.obj.obj U)
  map_smul _ _ f g p := map_mul (G.obj.map f).hom g p
  coversTop X := J.superset_covering (fun Y _ _ ↦ ⟨⟨Y, ⟨(1 : G.obj.obj (op Y))⟩⟩, ⟨𝟙 Y⟩⟩)
    (J.top_mem X)
  bijective U := (Equiv.prodCongrLeft fun p : G.obj.obj U ↦ Equiv.mulRight p).bijective

/-- The underlying sheaf of the trivial torsor is `G`, viewed as a sheaf of sets. -/
lemma trivial_sheaf : (trivial G).sheaf = (sheafCompose J (forget GrpCat.{w})).obj G :=
  rfl

/-- `G` acts on the trivial torsor by left multiplication. -/
@[simp]
lemma trivial_smul {U : Cᵒᵖ} (g : G.obj.obj U) (p : (trivial G).sheaf.obj.obj U) :
    g • p = @HMul.hMul (G.obj.obj U) (G.obj.obj U) _ _ g p :=
  rfl

/-- Morphisms from the trivial torsor to `P` correspond to global sections of `P`: a morphism
is determined by the image of the unit section, and a global section `s` gives `g ↦ g • s`. -/
def trivialHomEquiv (P : Torsor G) : (trivial G ⟶ P) ≃ P.sheaf.obj.sections where
  toFun f := ⟨fun U ↦ f.hom.hom.app U (1 : G.obj.obj U), fun {U V} a ↦
    (NatTrans.naturality_apply f.hom.hom a (1 : G.obj.obj U)).symm.trans
      (congrArg (f.hom.hom.app V) (map_one (G.obj.map a).hom))⟩
  invFun s := ⟨ObjectProperty.homMk
    { app U := ↾fun g : G.obj.obj U ↦ g • s.val U
      naturality U V a := by
        ext (g : G.obj.obj U)
        exact ((P.map_smul a g (s.val U)).trans (congrArg _ (s.property a))).symm },
    fun U g (h : G.obj.obj U) ↦ mul_smul g h (s.val U)⟩
  left_inv f := by
    ext U (g : G.obj.obj U)
    exact ((congrArg (f.hom.hom.app U) (mul_one g).symm).trans
      (f.map_smul U g (1 : G.obj.obj U))).symm
  right_inv s := by
    ext U
    exact one_smul _ _

@[simp]
lemma trivialHomEquiv_apply_coe (P : Torsor G) (f : trivial G ⟶ P) (U : Cᵒᵖ) :
    (trivialHomEquiv P f).val U = f.hom.hom.app U (1 : G.obj.obj U) := by
  rfl

@[simp]
lemma trivialHomEquiv_symm_apply_hom_app (P : Torsor G) (s : P.sheaf.obj.sections) (U : Cᵒᵖ)
    (g : G.obj.obj U) :
    ((trivialHomEquiv P).symm s).hom.hom.app U g = g • s.val U := by
  rfl

/-- A section `s` of a `G`-torsor `P` along a functor `u : D ⥤ C`, that is a family of sections
`s d` of `P` over `u d` compatible with restriction, identifies `u.op ⋙ G` with `u.op ⋙ P`: a
section `g` of `G` over `u d` goes to `g • s d`. For `u` the forgetful functor from a slice
category, this says that a torsor with a section over an object is trivial over that object. -/
noncomputable def isoOfSection {D : Type*} [Category D] (P : Torsor G) (u : D ⥤ C)
    (s : ∀ d : D, P.sheaf.obj.obj (op (u.obj d)))
    (hs : ∀ ⦃d d' : D⦄ (f : d ⟶ d'), P.sheaf.obj.map (u.map f).op (s d') = s d) :
    u.op ⋙ G.obj ⋙ forget GrpCat ≅ u.op ⋙ P.sheaf.obj :=
  NatIso.ofComponents
    (fun d ↦ (Equiv.ofBijective (fun g : G.obj.obj (op (u.obj d.unop)) ↦ g • s d.unop)
      ⟨P.smul_left_injective _, fun q ↦ MulAction.exists_smul_eq _ _ q⟩).toIso)
    fun {d d'} f ↦ by
      ext (g : G.obj.obj (op (u.obj d.unop)))
      exact ((P.map_smul _ g (s d.unop)).trans (congrArg _ (hs f.unop))).symm

/-- The isomorphism `isoOfSection` acts on the section `s d`. -/
lemma isoOfSection_hom_app_apply {D : Type*} [Category D] (P : Torsor G) (u : D ⥤ C)
    (s : ∀ d : D, P.sheaf.obj.obj (op (u.obj d)))
    (hs : ∀ ⦃d d' : D⦄ (f : d ⟶ d'), P.sheaf.obj.map (u.map f).op (s d') = s d) (d : Dᵒᵖ)
    (g : G.obj.obj (op (u.obj d.unop))) :
    (P.isoOfSection u s hs).hom.app d g = g • s d.unop :=
  (rfl)

/-- If every group of sections of `G` is trivial, every `G`-torsor has a global section: its
sections are subsingletons, and the local sections glue. -/
lemma nonempty_sections_of_subsingleton (P : Torsor G) [∀ U, Subsingleton (G.obj.obj U)] :
    P.sheaf.obj.sections.Nonempty := by
  have (U : Cᵒᵖ) : Subsingleton (P.sheaf.obj.obj U) := ⟨fun p q ↦ by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (G.obj.obj U) p q
    rw [Subsingleton.elim g 1, one_smul]⟩
  obtain ⟨s, -, -⟩ := Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section
    (x := fun i : {U : C // Nonempty (P.sheaf.obj.obj (op U))} ↦ i.property.some)
    (fun _ _ _ _ _ ↦ Subsingleton.elim _ _) P.coversTop P.sheaf.property
  exact ⟨s.val, s.property⟩

/-- If `T` is a terminal object over which every covering sieve contains the identity, as for
the whole space of a local scheme in its small Zariski site, every `G`-torsor has a global
section: some object over which it has a section receives a map from `T`. -/
lemma nonempty_sections_of_isTerminal_of_id_mem (P : Torsor G) {T : C} (hT : IsTerminal T)
    (hJ : ∀ S ∈ J T, S (𝟙 T)) : P.sheaf.obj.sections.Nonempty := by
  obtain ⟨⟨i, ⟨p⟩⟩, ⟨f⟩⟩ := hJ _ (P.coversTop T)
  refine ⟨fun U ↦ P.sheaf.obj.map (hT.from U.unop ≫ f).op p, fun {U V} g ↦ ?_⟩
  have : g.unop ≫ hT.from U.unop = hT.from V.unop := hT.hom_ext _ _
  simp [← this, -IsTerminal.comp_from]

/-- A `G`-invariant morphism from a torsor `P` to a sheaf of sets `F` is constant: its values
are those of a global section of `F`. -/
lemma exists_sections_eq_of_smul_invariant (P : Torsor G) {F : Sheaf J (Type w)}
    (f : P.sheaf ⟶ F) (hf : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
      f.hom.app U (g • p) = f.hom.app U p) :
    ∃ s : F.obj.sections, ∀ (U : Cᵒᵖ) (p : P.sheaf.obj.obj U), f.hom.app U p = s.val U := by
  have key {U : Cᵒᵖ} (p p' : P.sheaf.obj.obj U) : f.hom.app U p = f.hom.app U p' := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (G.obj.obj U) p' p
    exact hf U g p'
  obtain ⟨s, hs, -⟩ := Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section
    (x := fun j : {U : C // Nonempty (P.sheaf.obj.obj (op U))} ↦ f.hom.app _ j.property.some)
    (fun Z j k a b ↦ by
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      exact key _ _)
    P.coversTop F.property
  exact ⟨s, fun ⟨U⟩ p ↦ (key p _).trans (hs ⟨U, ⟨p⟩⟩).symm⟩

/-- A morphism of sheaves of sets which is bijective on sections over every object over which a
`G`-torsor `P` has a section is an isomorphism, because these objects cover the site. -/
lemma isIso_of_bijective_app (P : Torsor G) {F F' : Sheaf J (Type w)} (f : F ⟶ F')
    (hf : ∀ U : C, Nonempty (P.sheaf.obj.obj (op U)) → Function.Bijective (f.hom.app (op U))) :
    IsIso f :=
  Sheaf.isIso_of_coversTop P.coversTop fun i ↦ by
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    rintro ⟨V⟩
    exact (isIso_iff_bijective _).2 (hf V.left ⟨P.sheaf.obj.map V.hom.op i.property.some⟩)

/-- Two morphisms of `G`-torsors are equal as soon as they agree on one section over each object
of a covering family: by equivariance they then agree on every section over every object with a
map to the family, and these objects cover the site. -/
lemma hom_ext_of_coversTop {P Q : Torsor G} {f g : P ⟶ Q} {I : Type*} {Y : I → C}
    (hY : J.CoversTop Y) (p : ∀ i, P.sheaf.obj.obj (op (Y i)))
    (h : ∀ i, f.hom.hom.app _ (p i) = g.hom.hom.app _ (p i)) : f = g := by
  have key {V : C} (i : I) (a : V ⟶ Y i) (x : P.sheaf.obj.obj (op V)) :
      f.hom.hom.app _ x = g.hom.hom.app _ x := by
    obtain ⟨b, rfl⟩ :=
      MulAction.exists_smul_eq (G.obj.obj (op V)) (P.sheaf.obj.map a.op (p i)) x
    rw [f.map_smul, g.map_smul, NatTrans.naturality_apply f.hom.hom,
      NatTrans.naturality_apply g.hom.hom, h]
  ext U x
  refine (((isSheaf_iff_isSheaf_of_type J _).1 Q.sheaf.property).isSeparated _
    (hY U.unop)).ext fun V a ⟨i, ⟨b⟩⟩ ↦ ?_
  exact ((NatTrans.naturality_apply f.hom.hom a.op x).symm.trans (key i b _)).trans
    (NatTrans.naturality_apply g.hom.hom a.op x)

section prod

variable {G H : Sheaf J GrpCat.{w}}

/-- The product `P × Q` of a `G`-torsor `P` and an `H`-torsor `Q`, a torsor under the product
`G × H` of sheaves of groups acting componentwise.

The body is exposed because the sections of `P × Q` are, by definition, the pairs of sections of
`P` and of `Q`; statements about it apply the action to such pairs. Use `prod_sheaf` and
`prod_smul` rather than unfolding it. -/
@[expose] def prod (P : Torsor G) (Q : Torsor H) : Torsor (G ⊗ H) where
  sheaf := P.sheaf ⊗ Q.sheaf
  mulAction U :=
    { smul g x := (g.1 • x.1, g.2 • x.2)
      one_smul x := Prod.ext (one_smul _ x.1) (one_smul _ x.2)
      mul_smul g g' x := Prod.ext (mul_smul g.1 g'.1 x.1) (mul_smul g.2 g'.2 x.2) }
  map_smul U V f g x := Prod.ext (P.map_smul f g.1 x.1) (Q.map_smul f g.2 x.2)
  coversTop X := J.superset_covering (by
      rintro W a ⟨⟨⟨V, ⟨p⟩⟩, ⟨b⟩⟩, ⟨⟨V', ⟨q⟩⟩, ⟨b'⟩⟩⟩
      exact ⟨⟨W, ⟨(P.sheaf.obj.map b.op p, Q.sheaf.obj.map b'.op q)⟩⟩, ⟨𝟙 W⟩⟩)
    (J.intersection_covering (P.coversTop X) (Q.coversTop X))
  bijective U :=
    ((Equiv.prodProdProdComm _ _ _ _).trans
      (((Equiv.ofBijective _ (P.bijective U)).prodCongr
        (Equiv.ofBijective _ (Q.bijective U))).trans
          (Equiv.prodProdProdComm _ _ _ _))).bijective

variable (P : Torsor G) (Q : Torsor H)

/-- The underlying sheaf of the product torsor is the product of the underlying sheaves. -/
lemma prod_sheaf : (P.prod Q).sheaf = P.sheaf ⊗ Q.sheaf :=
  (rfl)

/-- `G × H` acts componentwise on the product torsor. -/
@[simp]
lemma prod_smul {U : Cᵒᵖ} (g : (G ⊗ H).obj.obj U) (x : (P.prod Q).sheaf.obj.obj U) :
    g • x = (g.1 • x.1, g.2 • x.2) :=
  (rfl)

end prod

end Torsor

variable (G : Sheaf J GrpCat.{w})

/-- The pointed set of isomorphism classes of `G`-torsors, the first cohomology of the sheaf of
groups `G` (Stacks, Section 21.4 (03AG)). -/
def NonabelianH1 : Type (max u v (w + 1)) :=
  _root_.Quotient (isIsomorphicSetoid (Torsor G))

namespace NonabelianH1

variable {G}

/-- The class of a `G`-torsor. -/
def mk (P : Torsor G) : NonabelianH1 G :=
  _root_.Quotient.mk _ P

/-- The base point of `NonabelianH1 G` is the class of the trivial torsor. -/
instance : One (NonabelianH1 G) :=
  ⟨mk (Torsor.trivial G)⟩

lemma one_def : (1 : NonabelianH1 G) = mk (Torsor.trivial G) :=
  rfl

@[simp]
lemma mk_trivial : mk (Torsor.trivial G) = 1 :=
  rfl

lemma mk_surjective : Function.Surjective (mk : Torsor G → NonabelianH1 G) :=
  _root_.Quotient.mk_surjective

@[elab_as_elim]
lemma ind {motive : NonabelianH1 G → Prop} (h : ∀ P, motive (mk P)) (x : NonabelianH1 G) :
    motive x :=
  _root_.Quotient.ind h x

/-- Two torsors have the same class if and only if they are isomorphic. -/
lemma mk_eq_mk_iff {P Q : Torsor G} : mk P = mk Q ↔ Nonempty (P ≅ Q) :=
  _root_.Quotient.eq

lemma mk_eq_mk_of_hom {P Q : Torsor G} (f : P ⟶ Q) : mk P = mk Q :=
  mk_eq_mk_iff.2 ⟨asIso f⟩

/-- A function on torsors which is constant along morphisms of torsors descends to their
classes. -/
def lift {α : Sort*} (f : Torsor G → α) (hf : ∀ P Q : Torsor G, (P ⟶ Q) → f P = f Q) :
    NonabelianH1 G → α :=
  _root_.Quotient.lift f fun P Q ⟨e⟩ ↦ hf P Q e.hom

@[simp]
lemma lift_mk {α : Sort*} (f : Torsor G → α) (hf : ∀ P Q : Torsor G, (P ⟶ Q) → f P = f Q)
    (P : Torsor G) : lift f hf (mk P) = f P := by
  rfl

/-- A torsor is trivial if and only if it has a global section
(Stacks, Lemma 21.4.2 (03AI)). -/
lemma mk_eq_one_iff (P : Torsor G) : mk P = 1 ↔ P.sheaf.obj.sections.Nonempty := by
  rw [one_def, eq_comm, mk_eq_mk_iff]
  refine ⟨fun ⟨e⟩ ↦ ⟨_, (Torsor.trivialHomEquiv P e.hom).property⟩, fun ⟨s, hs⟩ ↦ ?_⟩
  exact ⟨asIso ((Torsor.trivialHomEquiv P).symm ⟨s, hs⟩)⟩

/-- If every `G`-torsor has a global section, every `G`-torsor is trivial. -/
lemma subsingleton_of_forall_nonempty_sections
    (h : ∀ P : Torsor G, P.sheaf.obj.sections.Nonempty) : Subsingleton (NonabelianH1 G) where
  allEq x y := by
    induction x using ind with | h P => ?_
    induction y using ind with | h Q => ?_
    rw [(mk_eq_one_iff P).2 (h P), (mk_eq_one_iff Q).2 (h Q)]

/-- For a sheaf of trivial groups, every torsor is trivial. -/
instance [∀ U, Subsingleton (G.obj.obj U)] : Subsingleton (NonabelianH1 G) :=
  subsingleton_of_forall_nonempty_sections fun P ↦ P.nonempty_sections_of_subsingleton

/-- If `T` is a terminal object over which every covering sieve contains the identity, every
`G`-torsor is trivial. -/
lemma subsingleton_of_isTerminal_of_id_mem {T : C} (hT : IsTerminal T)
    (hJ : ∀ S ∈ J T, S (𝟙 T)) : Subsingleton (NonabelianH1 G) :=
  subsingleton_of_forall_nonempty_sections fun P ↦
    P.nonempty_sections_of_isTerminal_of_id_mem hT hJ

end NonabelianH1

end CategoryTheory.Sheaf
