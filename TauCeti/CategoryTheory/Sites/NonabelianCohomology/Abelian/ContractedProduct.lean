/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.ContractedProduct

/-!
# The contracted product of torsors under a sheaf of commutative groups

Let `G` be a sheaf of groups on a site `(C, J)` whose groups of sections are commutative, for
instance the sheaf of groups `abelianSheafToGrpSheaf J A` underlying an abelian sheaf `A`. For two
`G`-torsors `P` and `Q`, the product `P × Q` is a torsor under `G × G`, and extending its structure
group along the multiplication `G × G ⟶ G`, a morphism of sheaves of groups because `G` is
commutative, gives the *contracted product* `P ∧ Q`, a `G`-torsor. Its sections are locally the
classes `[p, q]` of pairs of sections, with `[a • p, q] = a • [p, q] = [p, a • q]`, and a morphism
`P ∧ Q ⟶ R` to a `G`-torsor is the same as a morphism `P × Q ⟶ R` equivariant in each variable.

The contracted product is functorial in the two torsors, associative and commutative by specified
isomorphisms, and has the trivial torsor as unit. These satisfy the coherence conditions, so the
contracted product makes the groupoid of `G`-torsors a symmetric monoidal category, and the
pointed set `NonabelianH1 G` of torsor classes a commutative monoid. Its multiplication is the
group law of the first cohomology of an abelian sheaf, written multiplicatively; inverses are not
constructed here.

## Main declarations

* `CategoryTheory.Sheaf.grpMul G`: the multiplication `G × G ⟶ G` of a sheaf of commutative
  groups.
* `CategoryTheory.Sheaf.Torsor.mul P Q`: the contracted product `P ∧ Q`, an extension of the
  structure group of `P × Q` (`Torsor.mul_def`).
* `CategoryTheory.Sheaf.Torsor.mulMk p q`: the class `[p, q]`, with `Torsor.mulMk_smul_left`,
  `Torsor.mulMk_smul_right` and `Torsor.mulMk_eq_mulMk_iff`; every section of `P ∧ Q` is locally
  such a class (`Torsor.isLocallySurjective_toMul`).
* `CategoryTheory.Sheaf.Torsor.mulLift`: the morphism `P ∧ Q ⟶ R` induced by a bi-equivariant
  morphism `P × Q ⟶ R`; `Torsor.mul_hom_ext` is its uniqueness.
* `CategoryTheory.Sheaf.Torsor.mulMap`: the contracted product of morphisms of torsors, with
  `Torsor.toMul_mulMap` relating it to the product of morphisms.
* `CategoryTheory.Sheaf.Torsor.mulAssocIso`, `CategoryTheory.Sheaf.Torsor.mulCommIso`,
  `CategoryTheory.Sheaf.Torsor.trivialMulIso` and `CategoryTheory.Sheaf.Torsor.mulTrivialIso`:
  associativity, commutativity and the unit isomorphisms, with their naturality and the
  pentagon, triangle and hexagon identities.
* The instances `MonoidalCategory (Torsor G)` and `SymmetricCategory (Torsor G)`.
* The instance `CommMonoid (NonabelianH1 G)`, transferred from Mathlib's skeleton through
  `CategoryTheory.Sheaf.NonabelianH1.mk_eq_toSkeleton`, with unit the existing base point and
  `CategoryTheory.Sheaf.NonabelianH1.mk_mul_mk`.

## References

* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §1.3, for the contracted product and the
  extension of the structure group of a torsor.
* L. Breen, *On the classification of 2-gerbes and 2-stacks*, Astérisque 225 (1994),
  Proposition 2.14, and M. Groechenig, D. Wyss and P. Ziegler, *Mirror symmetry for moduli of
  Higgs bundles via p-adic integration*, Invent. Math. 221 (2020), §2.2.1, where torsors under an
  abelian band act on banded gerbes through their contracted product.
-/

public noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section grpMul

variable (G : Sheaf J GrpCat.{w}) [∀ U, IsMulCommutative (G.obj.obj U)]

/-- The multiplication `G × G ⟶ G`, `(a, b) ↦ a * b`, of a sheaf of commutative groups, a
morphism of sheaves of groups because the groups of sections are commutative. -/
def grpMul : G ⊗ G ⟶ G :=
  ObjectProperty.homMk
    { app U :=
        letI : CommGroup (G.obj.obj U) := { mul_comm := mul_comm' }
        GrpCat.ofHom (mulMonoidHom : G.obj.obj U × G.obj.obj U →* G.obj.obj U)
      naturality U V f := by
        ext x
        exact (map_mul (G.obj.map f).hom x.1 x.2).symm }

variable {G} in
/-- The multiplication of a sheaf of commutative groups sends `(a, b)` to `a * b`. -/
lemma grpMul_hom_app_apply {U : Cᵒᵖ} (a b : G.obj.obj U) :
    (grpMul G).hom.app U (a, b) = a * b :=
  (rfl)

end grpMul

section Sections

variable {F F' K K' : Sheaf J (Type w)}

/-- A tensor product of morphisms of sheaves of sets acts componentwise on pairs of sections. This
is the one place where sections of a product of sheaves of sets are evaluated by unfolding. -/
private lemma tensorHom_hom_app (f : F ⟶ F') (g : K ⟶ K') {U : Cᵒᵖ} (x : (F ⊗ K).obj.obj U) :
    (f ⊗ₘ g).hom.app U x = (f.hom.app U x.1, g.hom.app U x.2) :=
  (rfl)

/-- A composite of morphisms of sheaves of sets maps a section by the two morphisms in turn. -/
private lemma comp_hom_app {F'' : Sheaf J (Type w)} (f : F ⟶ F') (g : F' ⟶ F'') {U : Cᵒᵖ}
    (x : F.obj.obj U) : (f ≫ g).hom.app U x = g.hom.app U (f.hom.app U x) :=
  (rfl)

end Sections

namespace Torsor

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  {G : Sheaf J GrpCat.{w}} [∀ U, IsMulCommutative (G.obj.obj U)]

/-- The contracted product `P ∧ Q` of two torsors under a sheaf of commutative groups `G`: the
`G`-torsor obtained from the `G × G`-torsor `P × Q` by extending its structure group along the
multiplication `G × G ⟶ G`. Its sections are locally the classes `[p, q]`, and
`[a • p, q] = a • [p, q] = [p, a • q]`. Use `mulMk`, `mulLift` and `mul_hom_ext` rather than
unfolding it. -/
def mul (P Q : Torsor G) : Torsor G :=
  (P.prod Q).map (grpMul G)

/-- The contracted product is the extension of the structure group of `P × Q` along the
multiplication `G × G ⟶ G`. -/
lemma mul_def (P Q : Torsor G) : P.mul Q = (P.prod Q).map (grpMul G) :=
  (rfl)

variable {P Q R : Torsor G}

/-- The class `[p, q]` in the contracted product of sections `p` of `P` and `q` of `Q` over the
same object. -/
def mulMk {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U) : (P.mul Q).sheaf.obj.obj U :=
  ((P.prod Q).toMap (grpMul G)).hom.app U (p, q)

variable (P Q) in
/-- The morphism `P × Q ⟶ P ∧ Q`, `(p, q) ↦ [p, q]`. -/
def toMul : P.sheaf ⊗ Q.sheaf ⟶ (P.mul Q).sheaf :=
  (P.prod Q).toMap (grpMul G)

/-- The morphism `P × Q ⟶ P ∧ Q` sends a pair of sections to its class. -/
lemma toMul_hom_app {U : Cᵒᵖ} (x : P.sheaf.obj.obj U × Q.sheaf.obj.obj U) :
    (toMul P Q).hom.app U x = mulMk x.1 x.2 :=
  (rfl)

/-- The class `[p, q]` commutes with restriction. -/
@[simp]
lemma map_mulMk {U V : Cᵒᵖ} (f : U ⟶ V) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U) :
    (P.mul Q).sheaf.obj.map f (mulMk p q) = mulMk (P.sheaf.obj.map f p) (Q.sheaf.obj.map f q) :=
  (NatTrans.naturality_apply (toMul P Q).hom f ((p, q) : (P.sheaf ⊗ Q.sheaf).obj.obj U)).symm

/-- The classes `[a • p, q]` and `a • [p, q]` agree. -/
@[simp]
lemma mulMk_smul_left {U : Cᵒᵖ} (a : G.obj.obj U) (p : P.sheaf.obj.obj U)
    (q : Q.sheaf.obj.obj U) : mulMk (a • p) q = a • mulMk p q :=
  calc mulMk (a • p) q = mulMk (a • p) ((1 : G.obj.obj U) • q) := by rw [one_smul]
    _ = (grpMul G).hom.app U (a, 1) • mulMk p q := (P.prod Q).toMap_smul (grpMul G) (a, 1) (p, q)
    _ = a • mulMk p q := by rw [grpMul_hom_app_apply, mul_one]

/-- The classes `[p, a • q]` and `a • [p, q]` agree. -/
@[simp]
lemma mulMk_smul_right {U : Cᵒᵖ} (a : G.obj.obj U) (p : P.sheaf.obj.obj U)
    (q : Q.sheaf.obj.obj U) : mulMk p (a • q) = a • mulMk p q :=
  calc mulMk p (a • q) = mulMk ((1 : G.obj.obj U) • p) (a • q) := by rw [one_smul]
    _ = (grpMul G).hom.app U (1, a) • mulMk p q := (P.prod Q).toMap_smul (grpMul G) (1, a) (p, q)
    _ = a • mulMk p q := by rw [grpMul_hom_app_apply, one_mul]

/-- A morphism `u : P × Q ⟶ R` to a `G`-torsor which is equivariant in each variable induces a
morphism of torsors `P ∧ Q ⟶ R`, sending `[p, q]` to `u (p, q)`. -/
def mulLift (u : P.sheaf ⊗ Q.sheaf ⟶ R.sheaf)
    (hl : ∀ (U : Cᵒᵖ) (a : G.obj.obj U) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U),
      u.hom.app U (a • p, q) = a • u.hom.app U (p, q))
    (hr : ∀ (U : Cᵒᵖ) (a : G.obj.obj U) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U),
      u.hom.app U (p, a • q) = a • u.hom.app U (p, q)) :
    P.mul Q ⟶ R :=
  (P.prod Q).mapLift u fun U g x ↦ (hl U g.1 x.1 (g.2 • x.2)).trans
    ((congrArg (g.1 • ·) (hr U g.2 x.1 x.2)).trans (mul_smul _ _ _).symm)

/-- The morphism induced by a bi-equivariant `u : P × Q ⟶ R` sends `[p, q]` to `u (p, q)`. -/
@[simp]
lemma mulLift_hom_app_mulMk (u : P.sheaf ⊗ Q.sheaf ⟶ R.sheaf)
    (hl : ∀ (U : Cᵒᵖ) (a : G.obj.obj U) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U),
      u.hom.app U (a • p, q) = a • u.hom.app U (p, q))
    (hr : ∀ (U : Cᵒᵖ) (a : G.obj.obj U) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U),
      u.hom.app U (p, a • q) = a • u.hom.app U (p, q))
    {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U) :
    (mulLift u hl hr).hom.hom.app U (mulMk p q) = u.hom.app U (p, q) :=
  congrArg (fun k ↦ k.hom.app U (p, q)) ((P.prod Q).toMap_mapLift u _)

/-- The morphism induced by a bi-equivariant `u : P × Q ⟶ R` restricts to `u` along
`P × Q ⟶ P ∧ Q`. -/
@[reassoc (attr := simp)]
lemma toMul_mulLift (u : P.sheaf ⊗ Q.sheaf ⟶ R.sheaf)
    (hl : ∀ (U : Cᵒᵖ) (a : G.obj.obj U) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U),
      u.hom.app U (a • p, q) = a • u.hom.app U (p, q))
    (hr : ∀ (U : Cᵒᵖ) (a : G.obj.obj U) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U),
      u.hom.app U (p, a • q) = a • u.hom.app U (p, q)) :
    toMul P Q ≫ (mulLift u hl hr).hom = u :=
  (P.prod Q).toMap_mapLift u _

/-- Morphisms of torsors out of `P ∧ Q` are determined by their values on the classes
`[p, q]`. -/
lemma mul_hom_ext {f g : P.mul Q ⟶ R}
    (h : ∀ (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U),
      f.hom.hom.app U (mulMk p q) = g.hom.hom.app U (mulMk p q)) : f = g :=
  map_hom_ext (by ext U x; exact h U x.1 x.2)

/-- Two classes `[p, q]` and `[p', q']` over the same object agree if and only if
`(p', q) = (a • p, a • q')` for some section `a` of `G`. -/
lemma mulMk_eq_mulMk_iff {U : Cᵒᵖ} {p p' : P.sheaf.obj.obj U} {q q' : Q.sheaf.obj.obj U} :
    mulMk p q = mulMk p' q' ↔ ∃ a : G.obj.obj U, p' = a • p ∧ q = a • q' := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (G.obj.obj U) p p'
    refine ⟨a, rfl, ?_⟩
    obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq (G.obj.obj U) q' q
    rw [mulMk_smul_left, mulMk_smul_right] at h
    rw [(P.mul Q).smul_left_injective _ h]
  · rintro ⟨a, rfl, rfl⟩
    rw [mulMk_smul_left, mulMk_smul_right]

/-- Every section of the contracted product is locally a class `[p, q]`: over each object over
which both `P` and `Q` have a section, it is the class of a pair of sections. -/
instance isLocallySurjective_toMul : Presheaf.IsLocallySurjective J (toMul P Q).hom :=
  isLocallySurjective_of_exists_eq_smul (P := P.prod Q) (toMul P Q) fun _ x a ↦
    ⟨(a • x.1, x.2), (toMul_hom_app _).trans
      ((mulMk_smul_left a x.1 x.2).trans (congrArg (a • ·) (toMul_hom_app x).symm))⟩

/-! ### Functoriality -/

section Functoriality

variable {P' Q' P'' Q'' : Torsor G}

/-- The composite `P × Q ⟶ P' × Q' ⟶ P' ∧ Q'` sends `(p, q)` to `[f p, g q]`. -/
private lemma tensorHom_toMul_hom_app (f : P ⟶ P') (g : Q ⟶ Q') {U : Cᵒᵖ}
    (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U) :
    ((f.hom ⊗ₘ g.hom) ≫ toMul P' Q').hom.app U (p, q) =
      mulMk (f.hom.hom.app U p) (g.hom.hom.app U q) :=
  (comp_hom_app _ _ _).trans ((congrArg _
    (tensorHom_hom_app f.hom g.hom ((p, q) : (P.sheaf ⊗ Q.sheaf).obj.obj U))).trans
      (toMul_hom_app _))

/-- The morphism `P ∧ Q ⟶ P' ∧ Q'`, `[p, q] ↦ [f p, g q]`, induced by morphisms of torsors
`f : P ⟶ P'` and `g : Q ⟶ Q'`. -/
def mulMap (f : P ⟶ P') (g : Q ⟶ Q') : P.mul Q ⟶ P'.mul Q' :=
  mulLift ((f.hom ⊗ₘ g.hom) ≫ toMul P' Q')
    (fun U a p q ↦ (tensorHom_toMul_hom_app f g (a • p) q).trans <|
      ((congrArg (mulMk · _) (f.map_smul U a p)).trans (mulMk_smul_left _ _ _)).trans
        (congrArg (a • ·) (tensorHom_toMul_hom_app f g p q).symm))
    (fun U a p q ↦ (tensorHom_toMul_hom_app f g p (a • q)).trans <|
      ((congrArg (mulMk _) (g.map_smul U a q)).trans (mulMk_smul_right _ _ _)).trans
        (congrArg (a • ·) (tensorHom_toMul_hom_app f g p q).symm))

/-- The morphism induced by `f` and `g` sends `[p, q]` to `[f p, g q]`. -/
@[simp]
lemma mulMap_hom_app_mulMk (f : P ⟶ P') (g : Q ⟶ Q') {U : Cᵒᵖ} (p : P.sheaf.obj.obj U)
    (q : Q.sheaf.obj.obj U) :
    (mulMap f g).hom.hom.app U (mulMk p q) = mulMk (f.hom.hom.app U p) (g.hom.hom.app U q) :=
  (mulLift_hom_app_mulMk _ _ _ p q).trans (tensorHom_toMul_hom_app f g p q)

/-- The canonical morphism `P × Q ⟶ P ∧ Q` is natural in the two torsors. -/
@[reassoc]
lemma toMul_mulMap (f : P ⟶ P') (g : Q ⟶ Q') :
    toMul P Q ≫ (mulMap f g).hom = (f.hom ⊗ₘ g.hom) ≫ toMul P' Q' :=
  toMul_mulLift _ _ _

/-- The identities of `P` and `Q` induce the identity of `P ∧ Q`. -/
@[simp]
lemma mulMap_id : mulMap (𝟙 P) (𝟙 Q) = 𝟙 (P.mul Q) :=
  mul_hom_ext fun _ _ _ ↦ by simp

/-- The contracted product of morphisms is compatible with composition. -/
@[reassoc]
lemma mulMap_comp (f : P ⟶ P') (g : Q ⟶ Q') (f' : P' ⟶ P'') (g' : Q' ⟶ Q'') :
    mulMap (f ≫ f') (g ≫ g') = mulMap f g ≫ mulMap f' g' :=
  mul_hom_ext fun _ _ _ ↦ by simp

end Functoriality

/-! ### The unit, commutativity and associativity isomorphisms -/

section Unit

omit [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)] in
/-- The actions of two sections of `G` on a torsor commute. -/
private lemma smul_smul_comm {U : Cᵒᵖ} (a b : G.obj.obj U) (p : P.sheaf.obj.obj U) :
    a • b • p = b • a • p := by
  rw [smul_smul, smul_smul, mul_comm']

variable (P) in
/-- The action `G × P ⟶ P`, `(a, p) ↦ a • p`, of `G` on a torsor, on the sections of the
trivial torsor. -/
private def actLeft : (trivial G).sheaf ⊗ P.sheaf ⟶ P.sheaf :=
  ObjectProperty.homMk
    { app U := ↾fun x ↦ @HSMul.hSMul (G.obj.obj U) (P.sheaf.obj.obj U) _ _ x.1 x.2
      naturality U V f := by
        ext x
        exact (P.map_smul f _ _).symm }

variable (P) in
/-- The action `P × G ⟶ P`, `(p, a) ↦ a • p`. -/
private def actRight : P.sheaf ⊗ (trivial G).sheaf ⟶ P.sheaf :=
  (β_ P.sheaf (trivial G).sheaf).hom ≫ actLeft P

variable (P) in
/-- The trivial torsor is a left unit for the contracted product: `G ∧ P ≅ P`,
`[a, p] ↦ a • p`. -/
def trivialMulIso : (trivial G).mul P ≅ P :=
  asIso (mulLift (actLeft P) (fun _ a b p ↦ mul_smul (α := G.obj.obj _) a b p)
    fun _ a b p ↦ smul_smul_comm (P := P) b a p)

/-- The isomorphism `G ∧ P ≅ P` sends `[a, p]` to `a • p`. -/
@[simp]
lemma trivialMulIso_hom_hom_hom_app_mulMk {U : Cᵒᵖ} (a : (trivial G).sheaf.obj.obj U)
    (p : P.sheaf.obj.obj U) :
    (trivialMulIso P).hom.hom.hom.app U (mulMk a p) =
      @HSMul.hSMul (G.obj.obj U) (P.sheaf.obj.obj U) _ _ a p := by
  rw [trivialMulIso, asIso_hom]
  exact mulLift_hom_app_mulMk _ _ _ _ _

/-- The inverse of the isomorphism `G ∧ P ≅ P` sends `p` to `[1, p]`. -/
@[simp]
lemma trivialMulIso_inv_hom_hom_app {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) :
    (trivialMulIso P).inv.hom.hom.app U p = mulMk (P := trivial G) (1 : G.obj.obj U) p := by
  have h := (trivialMulIso P).torsor_hom_inv_id_apply
    (mulMk (P := trivial G) (1 : G.obj.obj U) p)
  rw [trivialMulIso_hom_hom_hom_app_mulMk (1 : G.obj.obj U) p, one_smul] at h
  exact h

variable (P) in
/-- The trivial torsor is a right unit for the contracted product: `P ∧ G ≅ P`,
`[p, a] ↦ a • p`. -/
def mulTrivialIso : P.mul (trivial G) ≅ P :=
  asIso (mulLift (actRight P) (fun _ a p b ↦ smul_smul_comm (P := P) b a p)
    fun _ a p b ↦ mul_smul (α := G.obj.obj _) a b p)

/-- The isomorphism `P ∧ G ≅ P` sends `[p, a]` to `a • p`. -/
@[simp]
lemma mulTrivialIso_hom_hom_hom_app_mulMk {U : Cᵒᵖ} (p : P.sheaf.obj.obj U)
    (a : (trivial G).sheaf.obj.obj U) :
    (mulTrivialIso P).hom.hom.hom.app U (mulMk p a) =
      @HSMul.hSMul (G.obj.obj U) (P.sheaf.obj.obj U) _ _ a p := by
  rw [mulTrivialIso, asIso_hom]
  exact mulLift_hom_app_mulMk _ _ _ _ _

/-- The inverse of the isomorphism `P ∧ G ≅ P` sends `p` to `[p, 1]`. -/
@[simp]
lemma mulTrivialIso_inv_hom_hom_app {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) :
    (mulTrivialIso P).inv.hom.hom.app U p = mulMk (Q := trivial G) p (1 : G.obj.obj U) := by
  have h := (mulTrivialIso P).torsor_hom_inv_id_apply
    (mulMk (Q := trivial G) p (1 : G.obj.obj U))
  rw [mulTrivialIso_hom_hom_hom_app_mulMk p (1 : G.obj.obj U), one_smul] at h
  exact h

end Unit

section Comm

variable (P Q) in
/-- The morphism `P × Q ⟶ Q ∧ P`, `(p, q) ↦ [q, p]`. -/
private def swapMul : P.sheaf ⊗ Q.sheaf ⟶ (Q.mul P).sheaf :=
  (β_ P.sheaf Q.sheaf).hom ≫ toMul Q P

variable (P Q) in
/-- The contracted product is commutative: `P ∧ Q ≅ Q ∧ P`, `[p, q] ↦ [q, p]`. -/
def mulCommIso : P.mul Q ≅ Q.mul P :=
  asIso (mulLift (swapMul P Q) (fun _ a p q ↦ mulMk_smul_right a q p)
    fun _ a p q ↦ mulMk_smul_left a q p)

/-- The isomorphism `P ∧ Q ≅ Q ∧ P` sends `[p, q]` to `[q, p]`. -/
@[simp]
lemma mulCommIso_hom_hom_hom_app_mulMk {U : Cᵒᵖ} (p : P.sheaf.obj.obj U)
    (q : Q.sheaf.obj.obj U) :
    (mulCommIso P Q).hom.hom.hom.app U (mulMk p q) = mulMk q p := by
  rw [mulCommIso, asIso_hom]
  exact mulLift_hom_app_mulMk _ _ _ _ _

/-- The inverse of the isomorphism `P ∧ Q ≅ Q ∧ P` sends `[q, p]` to `[p, q]`. -/
@[simp]
lemma mulCommIso_inv_hom_hom_app_mulMk {U : Cᵒᵖ} (p : P.sheaf.obj.obj U)
    (q : Q.sheaf.obj.obj U) :
    (mulCommIso P Q).inv.hom.hom.app U (mulMk q p) = mulMk p q := by
  rw [← mulCommIso_hom_hom_hom_app_mulMk p q]
  exact (mulCommIso P Q).torsor_hom_inv_id_apply _

end Comm

section Assoc

variable (P Q R)

/-- The triple contracted product `P ∧ Q ∧ R`, extending the structure group of the
`G × G × G`-torsor `(P × Q) × R` along the multiplication of three sections. Both bracketings of
the contracted product receive a morphism from it. -/
private def mul₃ : Torsor G :=
  ((P.prod Q).prod R).map (grpMul G ▷ G ≫ grpMul G)

omit [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)] in
private lemma grpMul₃_hom_app {U : Cᵒᵖ} (x : ((G ⊗ G) ⊗ G).obj.obj U) :
    (grpMul G ▷ G ≫ grpMul G).hom.app U x =
      @HMul.hMul (G.obj.obj U) (G.obj.obj U) _ _ (x.1.1 * x.1.2) x.2 :=
  (rfl)

/-- The morphism `(P × Q) × R ⟶ (P ∧ Q) ∧ R`, `((p, q), r) ↦ [[p, q], r]`. -/
private def toMulMulLeft : (P.sheaf ⊗ Q.sheaf) ⊗ R.sheaf ⟶ ((P.mul Q).mul R).sheaf :=
  toMul P Q ▷ R.sheaf ≫ toMul (P.mul Q) R

/-- The morphism `(P × Q) × R ⟶ P ∧ (Q ∧ R)`, `((p, q), r) ↦ [p, [q, r]]`. -/
private def toMulMulRight : (P.sheaf ⊗ Q.sheaf) ⊗ R.sheaf ⟶ (P.mul (Q.mul R)).sheaf :=
  (α_ P.sheaf Q.sheaf R.sheaf).hom ≫ P.sheaf ◁ toMul Q R ≫ toMul P (Q.mul R)

variable {P Q R} in
/-- The morphism `(P × Q) × R ⟶ (P ∧ Q) ∧ R` sends `((p, q), r)` to `[[p, q], r]`. -/
private lemma toMulMulLeft_hom_app {U : Cᵒᵖ}
    (x : ((P.sheaf ⊗ Q.sheaf) ⊗ R.sheaf).obj.obj U) :
    (toMulMulLeft P Q R).hom.app U x = mulMk (mulMk x.1.1 x.1.2) x.2 :=
  (rfl)

variable {P Q R} in
/-- The morphism `(P × Q) × R ⟶ P ∧ (Q ∧ R)` sends `((p, q), r)` to `[p, [q, r]]`. -/
private lemma toMulMulRight_hom_app {U : Cᵒᵖ}
    (x : ((P.sheaf ⊗ Q.sheaf) ⊗ R.sheaf).obj.obj U) :
    (toMulMulRight P Q R).hom.app U x = mulMk x.1.1 (mulMk x.1.2 x.2) :=
  (rfl)

/-- The morphism `P ∧ Q ∧ R ⟶ (P ∧ Q) ∧ R`, `[p, q, r] ↦ [[p, q], r]`. -/
private def mul₃ToLeft : mul₃ P Q R ⟶ (P.mul Q).mul R :=
  ((P.prod Q).prod R).mapLift (toMulMulLeft P Q R) fun U g x ↦ by
    let _ : CommGroup (G.obj.obj U) := { mul_comm := mul_comm' }
    refine (toMulMulLeft_hom_app (g • x)).trans
      (Eq.trans ?_ (congrArg (_ • ·) (toMulMulLeft_hom_app x).symm))
    rw [grpMul₃_hom_app]
    simp only [prod_smul, mulMk_smul_left, mulMk_smul_right, smul_smul, mul_comm, mul_left_comm]

/-- The morphism `P ∧ Q ∧ R ⟶ P ∧ (Q ∧ R)`, `[p, q, r] ↦ [p, [q, r]]`. -/
private def mul₃ToRight : mul₃ P Q R ⟶ P.mul (Q.mul R) :=
  ((P.prod Q).prod R).mapLift (toMulMulRight P Q R) fun U g x ↦ by
    let _ : CommGroup (G.obj.obj U) := { mul_comm := mul_comm' }
    refine (toMulMulRight_hom_app (g • x)).trans
      (Eq.trans ?_ (congrArg (_ • ·) (toMulMulRight_hom_app x).symm))
    rw [grpMul₃_hom_app]
    simp only [prod_smul, mulMk_smul_left, mulMk_smul_right, smul_smul, mul_comm, mul_left_comm]

/-- The contracted product is associative: `(P ∧ Q) ∧ R ≅ P ∧ (Q ∧ R)`,
`[[p, q], r] ↦ [p, [q, r]]`. -/
def mulAssocIso : (P.mul Q).mul R ≅ P.mul (Q.mul R) :=
  (asIso (mul₃ToLeft P Q R)).symm ≪≫ asIso (mul₃ToRight P Q R)

variable {P Q R}

/-- The associativity isomorphism sends `[[p, q], r]` to `[p, [q, r]]`. -/
@[simp]
lemma mulAssocIso_hom_hom_hom_app_mulMk {U : Cᵒᵖ} (p : P.sheaf.obj.obj U)
    (q : Q.sheaf.obj.obj U) (r : R.sheaf.obj.obj U) :
    (mulAssocIso P Q R).hom.hom.hom.app U (mulMk (mulMk p q) r) = mulMk p (mulMk q r) := by
  let t := (((P.prod Q).prod R).toMap (grpMul G ▷ G ≫ grpMul G)).hom.app U ((p, q), r)
  have h₁ : (mul₃ToLeft P Q R).hom.hom.app U t = mulMk (mulMk p q) r :=
    congrArg (fun k ↦ k.hom.app U ((p, q), r)) (((P.prod Q).prod R).toMap_mapLift
      (toMulMulLeft P Q R) _)
  have h₂ : (mul₃ToRight P Q R).hom.hom.app U t = mulMk p (mulMk q r) :=
    congrArg (fun k ↦ k.hom.app U ((p, q), r)) (((P.prod Q).prod R).toMap_mapLift
      (toMulMulRight P Q R) _)
  rw [← h₁, ← h₂]
  exact congrArg (fun k ↦ k.hom.hom.app U t)
    (IsIso.hom_inv_id_assoc (mul₃ToLeft P Q R) (mul₃ToRight P Q R))

/-- The inverse of the associativity isomorphism sends `[p, [q, r]]` to `[[p, q], r]`. -/
@[simp]
lemma mulAssocIso_inv_hom_hom_app_mulMk {U : Cᵒᵖ} (p : P.sheaf.obj.obj U)
    (q : Q.sheaf.obj.obj U) (r : R.sheaf.obj.obj U) :
    (mulAssocIso P Q R).inv.hom.hom.app U (mulMk p (mulMk q r)) = mulMk (mulMk p q) r := by
  rw [← mulAssocIso_hom_hom_hom_app_mulMk]
  exact (mulAssocIso P Q R).torsor_hom_inv_id_apply _

end Assoc

/-! ### Naturality -/

section Naturality

variable {P' Q' R' S : Torsor G}

/-- Morphisms of torsors out of `(P ∧ Q) ∧ R` are determined by their values on the classes
`[[p, q], r]`. -/
lemma mul_mul_hom_ext {f g : (P.mul Q).mul R ⟶ S}
    (h : ∀ (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U) (r : R.sheaf.obj.obj U),
      f.hom.hom.app U (mulMk (mulMk p q) r) = g.hom.hom.app U (mulMk (mulMk p q) r)) : f = g :=
  hom_ext_of_coversTop ((P.prod Q).prod R).coversTop
    (fun i ↦ mulMk (mulMk i.property.some.1.1 i.property.some.1.2) i.property.some.2)
    fun _ ↦ h _ _ _ _

/-- Morphisms of torsors out of `P ∧ (Q ∧ R)` are determined by their values on the classes
`[p, [q, r]]`. -/
lemma mul_mul_hom_ext' {f g : P.mul (Q.mul R) ⟶ S}
    (h : ∀ (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U) (r : R.sheaf.obj.obj U),
      f.hom.hom.app U (mulMk p (mulMk q r)) = g.hom.hom.app U (mulMk p (mulMk q r))) : f = g :=
  hom_ext_of_coversTop ((P.prod Q).prod R).coversTop
    (fun i ↦ mulMk i.property.some.1.1 (mulMk i.property.some.1.2 i.property.some.2))
    fun _ ↦ h _ _ _ _

/-- The associativity isomorphism is natural in the three torsors. -/
@[reassoc]
lemma mulAssocIso_hom_naturality (f : P ⟶ P') (g : Q ⟶ Q') (k : R ⟶ R') :
    mulMap (mulMap f g) k ≫ (mulAssocIso P' Q' R').hom =
      (mulAssocIso P Q R).hom ≫ mulMap f (mulMap g k) :=
  mul_mul_hom_ext fun _ _ _ _ ↦ by simp

/-- The left unit isomorphism `G ∧ P ≅ P` is natural in `P`. -/
@[reassoc]
lemma trivialMulIso_hom_naturality (f : P ⟶ Q) :
    mulMap (𝟙 (trivial G)) f ≫ (trivialMulIso Q).hom = (trivialMulIso P).hom ≫ f :=
  mul_hom_ext fun U a p ↦ by
    simp only [comp_hom_hom_app, mulMap_hom_app_mulMk, trivialMulIso_hom_hom_hom_app_mulMk]
    exact (f.map_smul U a p).symm

/-- The right unit isomorphism `P ∧ G ≅ P` is natural in `P`. -/
@[reassoc]
lemma mulTrivialIso_hom_naturality (f : P ⟶ Q) :
    mulMap f (𝟙 (trivial G)) ≫ (mulTrivialIso Q).hom = (mulTrivialIso P).hom ≫ f :=
  mul_hom_ext fun U p a ↦ by
    simp only [comp_hom_hom_app, mulMap_hom_app_mulMk, mulTrivialIso_hom_hom_hom_app_mulMk]
    exact (f.map_smul U a p).symm

/-- The commutativity isomorphism is natural in the two torsors. -/
@[reassoc]
lemma mulCommIso_hom_naturality (f : P ⟶ P') (g : Q ⟶ Q') :
    mulMap f g ≫ (mulCommIso P' Q').hom = (mulCommIso P Q).hom ≫ mulMap g f :=
  mul_hom_ext fun _ _ _ ↦ by simp

/-- The commutativity isomorphism is its own inverse. -/
@[reassoc (attr := simp)]
lemma mulCommIso_hom_mulCommIso_hom :
    (mulCommIso P Q).hom ≫ (mulCommIso Q P).hom = 𝟙 (P.mul Q) :=
  mul_hom_ext fun _ _ _ ↦ by simp

end Naturality

/-! ### Coherence -/

section Coherence

variable (P Q R S)

/-- Morphisms of torsors out of `((P ∧ Q) ∧ R) ∧ S` are determined by their values on the
classes `[[[p, q], r], s]`. -/
private lemma mul_mul_mul_hom_ext {T : Torsor G} {f g : ((P.mul Q).mul R).mul S ⟶ T}
    (h : ∀ (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) (q : Q.sheaf.obj.obj U) (r : R.sheaf.obj.obj U)
      (s : S.sheaf.obj.obj U), f.hom.hom.app U (mulMk (mulMk (mulMk p q) r) s) =
        g.hom.hom.app U (mulMk (mulMk (mulMk p q) r) s)) : f = g :=
  hom_ext_of_coversTop (((P.prod Q).prod R).prod S).coversTop
    (fun i ↦ mulMk (mulMk (mulMk i.property.some.1.1.1 i.property.some.1.1.2)
      i.property.some.1.2) i.property.some.2) fun _ ↦ h _ _ _ _ _

/-- The pentagon identity for the associativity isomorphisms of the contracted product. -/
@[reassoc]
lemma mulAssocIso_pentagon :
    mulMap (mulAssocIso P Q R).hom (𝟙 S) ≫ (mulAssocIso P (Q.mul R) S).hom ≫
        mulMap (𝟙 P) (mulAssocIso Q R S).hom =
      (mulAssocIso (P.mul Q) R S).hom ≫ (mulAssocIso P Q (R.mul S)).hom :=
  mul_mul_mul_hom_ext P Q R S fun _ _ _ _ _ ↦ by simp

/-- The triangle identity relating the associativity and unit isomorphisms of the contracted
product: `[[p, a], q] ↦ [p, a • q]` and `[[p, a], q] ↦ [a • p, q]` agree. -/
@[reassoc]
lemma mulAssocIso_triangle :
    (mulAssocIso P (trivial G) Q).hom ≫ mulMap (𝟙 P) (trivialMulIso Q).hom =
      mulMap (mulTrivialIso P).hom (𝟙 Q) :=
  mul_mul_hom_ext fun U p a q ↦ by
    simp only [comp_hom_hom_app, mulAssocIso_hom_hom_hom_app_mulMk, mulMap_hom_app_mulMk,
      trivialMulIso_hom_hom_hom_app_mulMk, mulTrivialIso_hom_hom_hom_app_mulMk]
    exact (mulMk_smul_right a p q).trans (mulMk_smul_left a p q).symm

/-- The first hexagon identity relating the commutativity and associativity isomorphisms of the
contracted product. -/
@[reassoc]
lemma mulCommIso_hexagon_forward :
    (mulAssocIso P Q R).hom ≫ (mulCommIso P (Q.mul R)).hom ≫ (mulAssocIso Q R P).hom =
      mulMap (mulCommIso P Q).hom (𝟙 R) ≫ (mulAssocIso Q P R).hom ≫
        mulMap (𝟙 Q) (mulCommIso P R).hom :=
  mul_mul_hom_ext fun _ _ _ _ ↦ by simp

/-- The second hexagon identity relating the commutativity and associativity isomorphisms of
the contracted product. -/
@[reassoc]
lemma mulCommIso_hexagon_reverse :
    (mulAssocIso P Q R).inv ≫ (mulCommIso (P.mul Q) R).hom ≫ (mulAssocIso R P Q).inv =
      mulMap (𝟙 P) (mulCommIso Q R).hom ≫ (mulAssocIso P R Q).inv ≫
        mulMap (mulCommIso P R).hom (𝟙 Q) :=
  mul_mul_hom_ext' fun _ _ _ _ ↦ by simp

end Coherence

/-! ### The symmetric monoidal category of torsors -/

/-- The contracted product makes the torsors under a sheaf of commutative groups a monoidal
category, with the trivial torsor as unit. The tensor product is `Torsor.mul`, and the
structure morphisms are `Torsor.mulMap`, `Torsor.mulAssocIso`, `Torsor.trivialMulIso` and
`Torsor.mulTrivialIso`. -/
instance : MonoidalCategory (Torsor G) :=
  letI : MonoidalCategoryStruct (Torsor G) :=
    { tensorObj P Q := P.mul Q
      whiskerLeft P _ _ g := mulMap (𝟙 P) g
      whiskerRight f Q := mulMap f (𝟙 Q)
      tensorHom f g := mulMap f g
      tensorUnit := trivial G
      associator := mulAssocIso
      leftUnitor := trivialMulIso
      rightUnitor := mulTrivialIso }
  .ofTensorHom (id_tensorHom_id := fun _ _ ↦ mulMap_id)
    (tensorHom_comp_tensorHom := fun _ _ _ _ ↦ (mulMap_comp _ _ _ _).symm)
    (associator_naturality := mulAssocIso_hom_naturality)
    (leftUnitor_naturality := trivialMulIso_hom_naturality)
    (rightUnitor_naturality := mulTrivialIso_hom_naturality)
    (pentagon := mulAssocIso_pentagon) (triangle := mulAssocIso_triangle)

/-- The contracted product of torsors under a sheaf of commutative groups is symmetric, with
braiding `Torsor.mulCommIso`, `[p, q] ↦ [q, p]`. -/
instance : SymmetricCategory (Torsor G) where
  braiding := mulCommIso
  braiding_naturality_right _ _ _ _ := mulCommIso_hom_naturality _ _
  braiding_naturality_left _ _ := mulCommIso_hom_naturality _ _
  hexagon_forward := mulCommIso_hexagon_forward
  hexagon_reverse := mulCommIso_hexagon_reverse
  symmetry _ _ := mulCommIso_hom_mulCommIso_hom

/-- The tensor product of torsors is their contracted product. -/
lemma tensorObj_eq_mul (P Q : Torsor G) : P ⊗ Q = P.mul Q :=
  (rfl)

/-- The unit of the monoidal structure is the trivial torsor. -/
lemma tensorUnit_eq_trivial : 𝟙_ (Torsor G) = trivial G :=
  (rfl)

/-- The tensor product of morphisms of torsors is `Torsor.mulMap`. -/
lemma tensorHom_eq_mulMap {P' Q' : Torsor G} (f : P ⟶ P') (g : Q ⟶ Q') :
    f ⊗ₘ g = mulMap f g :=
  (rfl)

/-- The associator of the monoidal structure is `Torsor.mulAssocIso`. -/
lemma associator_eq_mulAssocIso (P Q R : Torsor G) : α_ P Q R = mulAssocIso P Q R :=
  (rfl)

/-- The left unitor of the monoidal structure is `Torsor.trivialMulIso`. -/
lemma leftUnitor_eq_trivialMulIso (P : Torsor G) : λ_ P = trivialMulIso P :=
  (rfl)

/-- The right unitor of the monoidal structure is `Torsor.mulTrivialIso`. -/
lemma rightUnitor_eq_mulTrivialIso (P : Torsor G) : ρ_ P = mulTrivialIso P :=
  (rfl)

/-- The braiding of the symmetric structure is `Torsor.mulCommIso`. -/
lemma braiding_eq_mulCommIso (P Q : Torsor G) : β_ P Q = mulCommIso P Q :=
  (rfl)

end Torsor

/-! ### The commutative monoid of torsor classes -/

namespace NonabelianH1

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  {G : Sheaf J GrpCat.{w}} [∀ U, IsMulCommutative (G.obj.obj U)]

omit [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  [∀ U, IsMulCommutative (G.obj.obj U)] in
/-- The class of a torsor is its class in Mathlib's skeleton of the category of torsors: the
bridge through which the monoid structure of the skeleton is transferred. -/
lemma mk_eq_toSkeleton (P : Torsor G) : mk P = toSkeleton P :=
  (rfl)

/-- The unit of the skeleton of the monoidal category of torsors is the class of the trivial
torsor. -/
private lemma skeleton_one_eq : (1 : Skeleton (Torsor G)) = toSkeleton (Torsor.trivial G) :=
  Skeleton.one_eq.trans (congrArg toSkeleton Torsor.tensorUnit_eq_trivial)

/-- The classes of torsors under a sheaf of commutative groups form a commutative monoid under
the contracted product, with the class of the trivial torsor as unit. The multiplication is
that of Mathlib's skeleton of the symmetric monoidal category of torsors, and the unit is the
existing base point `1` of `NonabelianH1 G`. -/
instance : CommMonoid (NonabelianH1 G) where
  toMul := inferInstanceAs (Mul (Skeleton (Torsor G)))
  mul_assoc := mul_assoc (G := Skeleton (Torsor G))
  one := 1
  one_mul x := by
    rw [one_def, mk_eq_toSkeleton, ← skeleton_one_eq]
    exact one_mul (M := Skeleton (Torsor G)) x
  mul_one x := by
    rw [one_def, mk_eq_toSkeleton, ← skeleton_one_eq]
    exact mul_one (M := Skeleton (Torsor G)) x
  mul_comm := mul_comm (G := Skeleton (Torsor G))

/-- The product of the classes of two torsors is the class of their contracted product. -/
@[simp]
lemma mk_mul_mk (P Q : Torsor G) : mk P * mk Q = mk (P.mul Q) := by
  rw [mk_eq_toSkeleton, mk_eq_toSkeleton, mk_eq_toSkeleton, ← Torsor.tensorObj_eq_mul]
  exact (Skeleton.toSkeleton_tensorObj P Q).symm

end NonabelianH1

end CategoryTheory.Sheaf
