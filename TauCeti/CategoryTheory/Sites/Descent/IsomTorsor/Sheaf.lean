/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack
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
Remark 31.5). The local isomorphism makes `Isom(x, y)` locally nonempty
(`Pseudofunctor.coversTop_presheafHom`), and the action is simply transitive on sections over
every `T` because the action of the band on isomorphisms is. The torsor is trivial exactly when
`x` and `y` are isomorphic over `U`. In sheaf form, the principal comparison
`Isom(x, y) × A|U → Isom(x, y) × Isom(x, y)`, `(p, a) ↦ (p, p • a)`, is an isomorphism of
sheaves; this needs no isomorphism between `x` and `y`, local or global.

This is the sheaf of isomorphisms that the classification of `A`-gerbes compares along
band-preserving morphisms and neutralizations.

## Main declarations

* `CategoryTheory.Pseudofunctor.AbelianBanding.principalSheafIso`: the principal comparison as an
  isomorphism of sheaves on `J.over U`.
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

namespace AbelianBanding

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
@[simp]
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
  coversTop := coversTop_presheafHom
    (h.imp fun _ ⟨hR, hxy⟩ ↦ ⟨hR, fun _ f hf ↦ (hxy f hf).map Iso.hom⟩)
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
@[simp]
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
