/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
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
* `CategoryTheory.Sheaf.NonabelianH1 G`: the pointed set of isomorphism classes of `G`-torsors,
  with `NonabelianH1.mk`, `NonabelianH1.lift` and `NonabelianH1.mk_eq_mk_iff`.
* `CategoryTheory.Sheaf.NonabelianH1.mk_eq_one_iff`: a torsor is trivial if and only if it has a
  global section.

## References

* [The Stacks project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG),
  Definition 21.4.1 (03AH) and Lemma 21.4.2 (03AI).
-/

public section

open CategoryTheory Opposite

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
  coversTop : J.CoversTop fun U : {U : C // Nonempty (sheaf.obj.obj (op U))} ↦ U.1
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
    { app U := ↾fun g : G.obj.obj U ↦ g • s.1 U
      naturality U V a := by
        ext (g : G.obj.obj U)
        exact ((P.map_smul a g (s.1 U)).trans (congrArg _ (s.2 a))).symm },
    fun U g (h : G.obj.obj U) ↦ mul_smul g h (s.1 U)⟩
  left_inv f := by
    ext U (g : G.obj.obj U)
    exact ((congrArg (f.hom.hom.app U) (mul_one g).symm).trans
      (f.map_smul U g (1 : G.obj.obj U))).symm
  right_inv s := by
    ext U
    exact one_smul _ _

@[simp]
lemma trivialHomEquiv_apply_coe (P : Torsor G) (f : trivial G ⟶ P) (U : Cᵒᵖ) :
    (trivialHomEquiv P f).1 U = f.hom.hom.app U (1 : G.obj.obj U) := by
  rfl

@[simp]
lemma trivialHomEquiv_symm_apply_hom_app (P : Torsor G) (s : P.sheaf.obj.sections) (U : Cᵒᵖ)
    (g : G.obj.obj U) :
    ((trivialHomEquiv P).symm s).hom.hom.app U g = g • s.1 U := by
  rfl

/-- If every group of sections of `G` is trivial, every `G`-torsor has a global section: its
sections are subsingletons, and the local sections glue. -/
lemma nonempty_sections_of_subsingleton (P : Torsor G) [∀ U, Subsingleton (G.obj.obj U)] :
    P.sheaf.obj.sections.Nonempty := by
  have (U : Cᵒᵖ) : Subsingleton (P.sheaf.obj.obj U) := ⟨fun p q ↦ by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (G.obj.obj U) p q
    rw [Subsingleton.elim g 1, one_smul]⟩
  obtain ⟨s, -, -⟩ := Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section
    (x := fun i : {U : C // Nonempty (P.sheaf.obj.obj (op U))} ↦ i.2.some)
    (fun _ _ _ _ _ ↦ Subsingleton.elim _ _) P.coversTop P.sheaf.property
  exact ⟨s.1, s.2⟩

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
  refine ⟨fun ⟨e⟩ ↦ ⟨_, (Torsor.trivialHomEquiv P e.hom).2⟩, fun ⟨s, hs⟩ ↦ ?_⟩
  exact ⟨asIso ((Torsor.trivialHomEquiv P).symm ⟨s, hs⟩)⟩

/-- For a sheaf of trivial groups, every torsor is trivial. -/
instance [∀ U, Subsingleton (G.obj.obj U)] : Subsingleton (NonabelianH1 G) where
  allEq x y := by
    induction x using ind with | h P => ?_
    induction y using ind with | h Q => ?_
    rw [(mk_eq_one_iff P).2 P.nonempty_sections_of_subsingleton,
      (mk_eq_one_iff Q).2 Q.nonempty_sections_of_subsingleton]

end NonabelianH1

end CategoryTheory.Sheaf
