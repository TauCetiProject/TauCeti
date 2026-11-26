/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Basic
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Abelian.Basic

/-!
# The sheaf of isomorphisms of a banded gerbe is a torsor

Let `b` be an `A`-banding of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` whose fibres are
groupoids, for instance a gerbe, and let `x y` be objects over `U`. Mathlib's presheaf of
morphisms `F.presheafHom x y` on `Over U` is then the presheaf of isomorphisms `Isom(x, y)`, and
`A|_U` acts on it by `homAct`. This file shows that the action is principal at the level of
presheaves and of sheaves: the map `(p, a) ↦ (p, p · a)` is an isomorphism from
`Hom(x, y) × A|_U` onto `Hom(x, y) × Hom(x, y)` (`AbelianBanding.principalPresheafIso`), with
inverse `(p, q) ↦ (p, q - p)`, and for a prestack both sides are sheaves for `J.over U`
(`AbelianBanding.principalSheafIso`); this needs no isomorphism between `x` and `y`, local or
global.

If moreover `x` and `y` are locally isomorphic, as any two objects of a gerbe are, then
`Isom(x, y)` is a torsor under the restriction of `A` to `Over U` (Olsson, Definition 31.1,
Lemma 31.3 and Remark 31.5): the local isomorphisms make `Isom(x, y)` locally nonempty
(`Pseudofunctor.coversTop_presheafHom`), and the action is simply transitive on sections over every
`T` because the action of the band on isomorphisms is. The torsor is trivial exactly when `x` and
`y` are isomorphic over `U`.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.AbelianBanding`:

* `homPrincipalEquiv`: `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)`, `(p, a) ↦ (p, homAct p a)`.
* `coefficientPresheaf`, `actionPresheaf`, `pairPresheaf`: the presheaves `A|_U`,
  `Hom(x, y) × A|_U` and `Hom(x, y) × Hom(x, y)` on `Over U`.
* `principalPresheafIso`: the principal comparison of presheaves.
* `coefficientSheaf`: the sheaf `A|_U` on `J.over U`.
* `principalSheafIso`: the same comparison for the tensor products of sheaves on `J.over U`.
* `sheafHomMulAction`: the action of `A|_U`, as a sheaf of groups, on the sections of `Isom(x, y)`.
* `sheafHomTorsor`: `Isom(x, y)` as a torsor under the restriction of `A` to `Over U`.
* `mk_sheafHomTorsor_eq_one_iff`: this torsor is trivial if and only if `x` and `y` are
  isomorphic.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1, Lemma 31.3 and Remark 31.5
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory MonoidalCategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{v'}} (b : F.AbelianBanding J A)
  {U : C} {x y : F.obj (.mk (op U))}

/-! ### The principal equivalence on one fibre -/

variable (x y) in
/-- **The principal equivalence on morphisms.** In a groupoid fibre, `(p, a) ↦ (p, homAct p a)` is
an equivalence `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)`, with inverse
`(p, q) ↦ (p, difference p q)`. No morphism `x ⟶ y` is assumed to exist. -/
noncomputable def homPrincipalEquiv [IsGroupoid (F.obj (.mk (op U)))] :
    (x ⟶ y) × Multiplicative (A.obj.obj (op U)) ≃ (x ⟶ y) × (x ⟶ y) :=
  letI := Groupoid.ofIsGroupoid (C := F.obj (.mk (op U)))
  ((Groupoid.isoEquivHom x y).symm.prodCongr (Equiv.refl _)).trans
    ((b.principalEquiv x y).trans
      ((Groupoid.isoEquivHom x y).prodCongr (Groupoid.isoEquivHom x y)))

@[simp]
theorem homPrincipalEquiv_apply [IsGroupoid (F.obj (.mk (op U)))]
    (pa : (x ⟶ y) × Multiplicative (A.obj.obj (op U))) :
    b.homPrincipalEquiv x y pa = (pa.1, b.homAct pa.1 pa.2) := by
  simp [homPrincipalEquiv, homAct_def]

@[simp]
theorem homPrincipalEquiv_symm_apply [IsGroupoid (F.obj (.mk (op U)))]
    (pq : (x ⟶ y) × (x ⟶ y)) :
    (b.homPrincipalEquiv x y).symm pq = (pq.1, b.difference (asIso pq.1) (asIso pq.2)) := by
  -- the isomorphism with underlying morphism `p` is `asIso p`, as their `hom` fields agree
  have h (p : x ⟶ y) : letI := Groupoid.ofIsGroupoid (C := F.obj (.mk (op U)))
      (Groupoid.isoEquivHom x y).symm p = asIso p := Iso.ext rfl
  simp [homPrincipalEquiv, h]

/-! ### Presheaves on `Over U` -/

variable (A U) in
/-- The coefficient presheaf `A|_U` on `Over U`, with values in types. -/
abbrev coefficientPresheaf : (Over U)ᵒᵖ ⥤ Type v' :=
  (Over.forget U).op ⋙ A.obj ⋙ forget AddCommGrpCat

variable (F x y) in
/-- The presheaf `Hom(x, y) × Hom(x, y)` of pairs of local morphisms. -/
abbrev pairPresheaf : (Over U)ᵒᵖ ⥤ Type v' :=
  F.presheafHom x y ⊗ F.presheafHom x y

variable (A x y) in
/-- The presheaf `Hom(x, y) × A|_U` of local morphisms with a coefficient. -/
abbrev actionPresheaf : (Over U)ᵒᵖ ⥤ Type v' :=
  F.presheafHom x y ⊗ coefficientPresheaf A U

variable (x y) in
/-- **The principal comparison of presheaves** `Hom(x, y) × A|_U ≅ Hom(x, y) × Hom(x, y)`,
`(p, a) ↦ (p, homAct p a)`, when every fibre is a groupoid. -/
noncomputable def principalPresheafIso [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    actionPresheaf A x y ≅ pairPresheaf F x y :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso ((Equiv.prodCongr (Equiv.refl _) Multiplicative.ofAdd).trans
      (b.homPrincipalEquiv _ _)))
    (fun {T₁ T₂} g ↦ by
      ext ⟨p, a⟩
      -- Evaluate both components by `homPrincipalEquiv_apply`. The restriction maps of the
      -- product presheaves act on pairs componentwise, and that of `F.presheafHom x y` is
      -- `pullHom` along `g.unop.left` (Mathlib's `Pseudofunctor.presheafHom_map`, generated by
      -- `@[simps]` on `presheafHom`), so the two sides agree by `pullHom_homAct`.
      refine (b.homPrincipalEquiv_apply _).trans (.trans ?_ (congrArg
        (ConcreteCategory.hom ((pairPresheaf F x y).map g))
        (b.homPrincipalEquiv_apply (p, .ofAdd a))).symm)
      exact Prod.ext rfl (b.pullHom_homAct p (.ofAdd a) g.unop.left T₂.unop.hom T₂.unop.hom
        (Over.w g.unop) (Over.w g.unop)).symm)

/-- The principal comparison sends `(p, a)` to `(p, homAct p a)`. -/
theorem principalPresheafIso_hom_app [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]
    (T : (Over U)ᵒᵖ) (pa : (actionPresheaf A x y).obj T) :
    (b.principalPresheafIso x y).hom.app T pa =
      (pa.1, b.homAct pa.1 (.ofAdd pa.2)) :=
  b.homPrincipalEquiv_apply (pa.1, .ofAdd pa.2)

/-- The inverse comparison sends `(p, q)` to `(p, difference p q)`. -/
theorem principalPresheafIso_inv_app [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]
    (T : (Over U)ᵒᵖ) (pq : (pairPresheaf F x y).obj T) :
    (b.principalPresheafIso x y).inv.app T pq =
      (pq.1, (b.difference (asIso pq.1) (asIso pq.2)).toAdd) :=
  congrArg (Prod.map _root_.id Multiplicative.toAdd) (b.homPrincipalEquiv_symm_apply pq)

/-! ### Sheaves on `J.over U` -/

variable (J A U) in
/-- The coefficient sheaf `A|_U` on `J.over U`, with values in types. -/
abbrev coefficientSheaf : Sheaf (J.over U) (Type v') :=
  (sheafCompose (J.over U) (forget AddCommGrpCat.{v'})).obj
    ((J.overPullback AddCommGrpCat U).obj A)

variable [F.IsPrestack J]

variable (x y) in
/-- **The principal comparison of sheaves** `Hom(x, y) × A|_U ≅ Hom(x, y) × Hom(x, y)` on
`J.over U`, whose underlying morphism of presheaves is `principalPresheafIso`. -/
noncomputable def principalSheafIso [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    F.sheafHom J x y ⊗ coefficientSheaf J A U ≅ F.sheafHom J x y ⊗ F.sheafHom J x y :=
  (fullyFaithfulSheafToPresheaf (J.over U) (Type v')).preimageIso (b.principalPresheafIso x y)

@[simp]
theorem principalSheafIso_hom_hom [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    (b.principalSheafIso x y).hom.hom = (b.principalPresheafIso x y).hom :=
  (rfl)

@[simp]
theorem principalSheafIso_inv_hom [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    (b.principalSheafIso x y).inv.hom = (b.principalPresheafIso x y).inv :=
  (rfl)

/-! ### The torsor of isomorphisms -/

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
    -- `E` sends `(a, p)` to `(a • p, p)` by `homPrincipalEquiv_apply` and the definition of
    -- `sheafHomMulAction`.
    convert E.bijective using 1
    funext ⟨a, p⟩
    exact congrArg _root_.Prod.swap (b.homPrincipalEquiv_apply (p, _)).symm

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

end CategoryTheory.Pseudofunctor.AbelianBanding
