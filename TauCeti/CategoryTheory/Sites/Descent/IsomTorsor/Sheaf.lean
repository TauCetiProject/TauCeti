/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Basic
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Abelian.Basic

/-!
# The sheaf of isomorphisms of a banded gerbe is a torsor

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a prestack for a Grothendieck topology `J` whose fibre
categories are groupoids, for instance a gerbe, and let `b` be an `A`-banding of `F` by a sheaf of
abelian groups `A`. For objects `x` and `y` of the fibre over `U`, Mathlib's sheaf of morphisms
`F.sheafHom J x y` on the slice site `(Over U, J.over U)` is the sheaf `Isom(x, y)`: its sections
over `T : Over U` are the morphisms, all invertible, between the pullbacks of `x` and `y` to
`T.left`. The coefficients `A(T.left)` act on these sections by `AbelianBanding.homAct`,
postcomposition with the band automorphisms of the pullback of `y`.

This file shows that `Isom(x, y)` is a torsor under the restriction of `A` to `Over U` as soon as
`x` and `y` are locally isomorphic, as any two objects of a gerbe are (Olsson, Lemma 31.3 and
Remark 31.5). The local isomorphism makes `Isom(x, y)` locally nonempty, and the action is simply
transitive on sections over every `T` because the action of the band on isomorphisms is. The
torsor is trivial exactly when `x` and `y` are isomorphic over `U`, and its restriction to a
slice `Over V` is, compatibly with the actions, the `Isom` sheaf of the pullbacks of `x` and
`y`. In sheaf form, the principal comparison `Isom(x, y) × A|U → Isom(x, y) × Isom(x, y)`,
`(p, a) ↦ (p, p • a)`, is an isomorphism of sheaves; this needs no isomorphism between `x` and
`y`, local or global.

This is the sheaf of isomorphisms that the classification of `A`-gerbes compares along
band-preserving morphisms and neutralizations.

## Main declarations

* `CategoryTheory.Pseudofunctor.coversTop_presheafHom`: if `x` and `y` are isomorphic over the
  arrows of a covering sieve of `U`, the objects of `Over U` over which `Isom(x, y)` has a section
  cover the slice site.
* `CategoryTheory.Pseudofunctor.AbelianBanding.homPrincipalEquiv`: the principal comparison
  `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)` on morphisms of a groupoid fibre.
* `CategoryTheory.Pseudofunctor.AbelianBanding.principalSheafIso`: the principal comparison as an
  isomorphism of sheaves on `J.over U`.
* `CategoryTheory.Pseudofunctor.AbelianBanding.overMapCompPresheafHomIso_hom_app_homAct`: the
  identification of the restriction of `Isom(x, y)` to `Over V` with `Isom` of the pullbacks of
  `x` and `y` to `V` respects the actions.
* `CategoryTheory.Pseudofunctor.AbelianBanding.sheafHomTorsor`: `Isom(x, y)` as a torsor under the
  restriction of `A` to `Over U`.
* `CategoryTheory.Pseudofunctor.AbelianBanding.mk_sheafHomTorsor_eq_one_iff`: this torsor is
  trivial if and only if `x` and `y` are isomorphic.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Lemma 31.3 and Remark 31.5
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory MonoidalCategory

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {U : C} {x y : F.obj (.mk (op U))}

/-- If the objects `x` and `y` over `U` become isomorphic after pullback along every arrow of a
covering sieve of `U`, the objects of `Over U` over which the presheaf of morphisms from `x` to
`y` has a section cover the slice site `(Over U, J.over U)`. -/
lemma coversTop_presheafHom
    (h : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)) :
    (J.over U).CoversTop
      fun T : {T : Over U // Nonempty ((F.presheafHom x y).obj (op T))} ↦ T.val := by
  obtain ⟨R, hR, hxy⟩ := h
  intro T
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering (fun V g hg ↦ ?_) (J.pullback_stable T.hom hR)
  rw [Sieve.overEquiv_iff]
  exact ⟨⟨Over.mk (g ≫ T.hom), ⟨(hxy _ hg).some.hom⟩⟩, ⟨𝟙 _⟩⟩

namespace AbelianBanding

section Restriction

variable {A : Sheaf J AddCommGrpCat.{w}} (b : F.AbelianBanding J A)

/-- Restriction along `q : V ⟶ U` identifies the restriction of `Isom(x, y)` to `Over V` with
`Isom` of the pullbacks of `x` and `y` to `V` (`Pseudofunctor.overMapCompPresheafHomIso`), and this
identification commutes with the actions of the coefficients. -/
lemma overMapCompPresheafHomIso_hom_app_homAct {V : C} (q : V ⟶ U) (T : (Over V)ᵒᵖ)
    (p : (F.presheafHom x y).obj (op ((Over.map q).obj T.unop)))
    (a : Multiplicative (A.obj.obj (op T.unop.left))) :
    (F.overMapCompPresheafHomIso x y q).hom.app T (b.homAct p a) =
      b.homAct ((F.overMapCompPresheafHomIso x y q).hom.app T p) a := by
  -- The component of `overMapCompPresheafHomIso` is conjugation by the comparison isomorphisms
  -- `F.mapComp'` at `x` and `y`.
  exact (congrArg (· ≫ _) (b.comp_homAct _ p a)).trans (b.homAct_comp_hom _
    ((Cat.Hom.toNatIso (F.mapComp' q.op.toLoc T.unop.hom.op.toLoc _)).app y) a)

end Restriction

section Principal

variable {A : Sheaf J AddCommGrpCat.{w}} (b : F.AbelianBanding J A)
  [IsGroupoid (F.obj (.mk (op U)))]

/-- In a groupoid fibre, the isomorphism underlying the action of `a` on a morphism `p` is the
action of `a` on the isomorphism underlying `p`. -/
@[simp]
lemma asIso_homAct (p : x ⟶ y) (a : Multiplicative (A.obj.obj (op U))) :
    asIso (b.homAct p a) = b.act (asIso p) a := by
  ext
  simp [homAct_def]

/-- In a groupoid fibre, the difference of `p` and `q` carries `p` to `q`. -/
@[simp]
lemma homAct_difference_asIso (p q : x ⟶ y) :
    b.homAct p (b.difference (asIso p) (asIso q)) = q :=
  (b.homAct_hom (asIso p) _).trans (congrArg Iso.hom (b.act_difference _ _))

variable (x y) in
/-- The principal comparison `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)` of a groupoid fibre, sending
`(p, a)` to `(p, p • a)`; its inverse sends `(p, q)` to `(p, q - p)`. It is
`AbelianBanding.principalEquiv` on the isomorphisms underlying the morphisms, and needs no morphism
`x ⟶ y` to exist. -/
noncomputable def homPrincipalEquiv :
    (x ⟶ y) × Multiplicative (A.obj.obj (op U)) ≃ (x ⟶ y) × (x ⟶ y) where
  toFun pa := (pa.1, b.homAct pa.1 pa.2)
  invFun pq := (pq.1, b.difference (asIso pq.1) (asIso pq.2))
  left_inv pa := by simp
  right_inv pq := by simp

@[simp]
lemma homPrincipalEquiv_apply (pa : (x ⟶ y) × Multiplicative (A.obj.obj (op U))) :
    b.homPrincipalEquiv x y pa = (pa.1, b.homAct pa.1 pa.2) :=
  (rfl)

@[simp]
lemma homPrincipalEquiv_symm_apply (pq : (x ⟶ y) × (x ⟶ y)) :
    (b.homPrincipalEquiv x y).symm pq = (pq.1, b.difference (asIso pq.1) (asIso pq.2)) :=
  (rfl)

end Principal

section Sheaf

variable {A : Sheaf J AddCommGrpCat.{v'}} (b : F.AbelianBanding J A) [F.IsPrestack J]

variable (x y) in
/-- The action of the sections over `T` of the restriction of `A` to `Over U`, viewed as a sheaf of
groups, on the sections over `T` of `Isom(x, y)`: the action `AbelianBanding.homAct` of the
corresponding coefficient of `A(T.left)`. -/
@[implicit_reducible]
noncomputable def sheafHomMulAction (T : (Over U)ᵒᵖ) :
    MulAction (((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat.{v'} U).obj A)).obj.obj T) ((F.sheafHom J x y).obj.obj T) where
  smul a p := b.homAct p ((abelianSheafToGrpSheafObjEquiv _ T).symm a)
  one_smul p := (congrArg (b.homAct p) (map_one _)).trans (b.homAct_one p)
  mul_smul a c p := (congrArg (b.homAct p) (map_mul _ a c)).trans (b.homAct_mul p _ _)

/-- A coefficient acts on a section of `Isom(x, y)` by `AbelianBanding.homAct`. -/
lemma sheafHomMulAction_smul {T : (Over U)ᵒᵖ}
    (a : ((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat.{v'} U).obj A)).obj.obj T) (p : (F.sheafHom J x y).obj.obj T) :
    letI := b.sheafHomMulAction x y T
    a • p = b.homAct p ((abelianSheafToGrpSheafObjEquiv _ T).symm a) :=
  (rfl)

variable [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]

variable (x y) in
/-- The principal comparison `Isom(x, y) × A|U ≅ Isom(x, y) × Isom(x, y)` of sheaves on the slice
site `J.over U`, sending a section `(p, a)` over `T` to `(p, p • a)` (Olsson, Lemma 31.3 and
Remark 31.5). Its components are `AbelianBanding.homPrincipalEquiv`; it exists whether or not `x`
and `y` are locally isomorphic. -/
noncomputable def principalSheafIso :
    F.sheafHom J x y ⊗ (sheafCompose (J.over U) (forget AddCommGrpCat.{v'})).obj
        ((J.overPullback AddCommGrpCat.{v'} U).obj A) ≅
      F.sheafHom J x y ⊗ F.sheafHom J x y :=
  (fullyFaithfulSheafToPresheaf (J.over U) (Type v')).preimageIso
    (NatIso.ofComponents
      (fun T ↦ (((Equiv.refl _).prodCongr Multiplicative.ofAdd).trans
        (b.homPrincipalEquiv _ _)).toIso)
      fun {T T'} f ↦ by
        ext ⟨p, a⟩
        exact Prod.ext rfl
          (b.pullHom_homAct p (.ofAdd a) f.unop.left _ _ (Over.w f.unop) (Over.w f.unop)).symm)

/-- The principal comparison sends a section `(p, a)` to `(p, p • a)`. -/
lemma principalSheafIso_hom_hom_app {T : Over U}
    (p : (F.map T.hom.op.toLoc).toFunctor.obj x ⟶ (F.map T.hom.op.toLoc).toFunctor.obj y)
    (a : A.obj.obj (op T.left)) :
    (b.principalSheafIso x y).hom.hom.app (op T) (p, a) = (p, b.homAct p (.ofAdd a)) :=
  (rfl)

/-- The inverse of the principal comparison sends a section `(p, q)` to `(p, q - p)`. -/
lemma principalSheafIso_inv_hom_app {T : Over U}
    (p q : (F.map T.hom.op.toLoc).toFunctor.obj x ⟶ (F.map T.hom.op.toLoc).toFunctor.obj y) :
    (b.principalSheafIso x y).inv.hom.app (op T) (p, q) =
      (p, (b.difference (asIso p) (asIso q)).toAdd) :=
  (rfl)

variable (x y) in
/-- If `x` and `y` become isomorphic after pullback along every arrow of a covering sieve of `U`,
as any two objects of a gerbe do, the sheaf `Isom(x, y)` on the slice site `J.over U` is a torsor
under the restriction of `A` to `Over U`, acting by `AbelianBanding.homAct` (Olsson, Lemma 31.3
and Remark 31.5). For a gerbe, `IsGerbe.exists_covering_iso x y` supplies the hypothesis.

The body is exposed because the sections of this torsor are, by definition, the sections of
`F.sheafHom J x y`, that is morphisms of fibres; statements about its action apply
`AbelianBanding.homAct` to them. Use `sheafHomTorsor_sheaf` and `sheafHomTorsor_smul` rather than
unfolding it. -/
@[expose] noncomputable def sheafHomTorsor
    (h : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)) :
    Sheaf.Torsor
      ((abelianSheafToGrpSheaf (J.over U)).obj ((J.overPullback AddCommGrpCat.{v'} U).obj A)) where
  sheaf := F.sheafHom J x y
  mulAction := b.sheafHomMulAction x y
  map_smul T T' f a p := by
    obtain ⟨a, rfl⟩ := (abelianSheafToGrpSheafObjEquiv _ T).surjective a
    rw [sheafHomMulAction_smul, sheafHomMulAction_smul,
      abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]
    exact b.pullHom_homAct p a f.unop.left _ _ (Over.w f.unop) (Over.w f.unop)
  coversTop := coversTop_presheafHom h
  bijective T := by
    let E : ((abelianSheafToGrpSheaf (J.over U)).obj
        ((J.overPullback AddCommGrpCat.{v'} U).obj A)).obj.obj T × (F.sheafHom J x y).obj.obj T ≃
        (F.sheafHom J x y).obj.obj T × (F.sheafHom J x y).obj.obj T :=
      (((abelianSheafToGrpSheafObjEquiv _ T).symm.toEquiv.prodCongr (Equiv.refl _)).trans
        ((Equiv.prodComm _ _).trans ((b.homPrincipalEquiv _ _).trans (Equiv.prodComm _ _))))
    -- `E` sends `(a, p)` to `(a • p, p)` by the definitions of `sheafHomMulAction` and
    -- `homPrincipalEquiv`, both in this file.
    exact E.bijective

/-- The underlying sheaf of the torsor `Isom(x, y)` is Mathlib's sheaf of morphisms. -/
@[simp]
lemma sheafHomTorsor_sheaf
    (h : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)) :
    (b.sheafHomTorsor x y h).sheaf = F.sheafHom J x y :=
  (rfl)

/-- A coefficient acts on a section of the torsor `Isom(x, y)` by `AbelianBanding.homAct`. -/
lemma sheafHomTorsor_smul
    (h : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y))
    {T : (Over U)ᵒᵖ} (a : ((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat.{v'} U).obj A)).obj.obj T)
    (p : (b.sheafHomTorsor x y h).sheaf.obj.obj T) :
    a • p = b.homAct p ((abelianSheafToGrpSheafObjEquiv _ T).symm a) :=
  (rfl)

/-- The torsor `Isom(x, y)` is trivial, that is has a global section, if and only if `x` and `y`
are isomorphic over `U`. -/
theorem mk_sheafHomTorsor_eq_one_iff
    (h : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)) :
    Sheaf.NonabelianH1.mk (b.sheafHomTorsor x y h) = 1 ↔ Nonempty (x ≅ y) := by
  rw [Sheaf.NonabelianH1.mk_eq_one_iff, sheafHomTorsor_sheaf]
  refine ⟨fun ⟨s, _⟩ ↦ ⟨asIso (F.presheafHomObjHomEquiv.symm (s (op (Over.mk (𝟙 U)))))⟩,
    fun ⟨e⟩ ↦ ?_⟩
  refine ⟨fun T ↦ (F.sheafHom J x y).obj.map (Over.mkIdTerminal.from T.unop).op
    (F.presheafHomObjHomEquiv e.hom), fun {T T'} g ↦ ?_⟩
  exact (Functor.map_comp_apply (F.sheafHom J x y).obj _ _ _).symm.trans
    (congrArg (fun φ ↦ (F.sheafHom J x y).obj.map φ (F.presheafHomObjHomEquiv e.hom))
      (Quiver.Hom.unop_inj (Over.mkIdTerminal.hom_ext _ _)))

end Sheaf

end AbelianBanding

end CategoryTheory.Pseudofunctor
