/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Kummer
public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Galois
-- Exposed via `@[expose]` on `CommAlgCat.FiniteEtale.ofSeparableFieldExt`.
public import TauCeti.RingTheory.Etale.Field
-- Proof-only: affine `Spec` lemmas and cardinality of `Ω`-points of a finite étale algebra.
import TauCeti.AlgebraicGeometry.Scheme.SpecAlgHom
import TauCeti.RingTheory.Etale.Splitting

/-!
# Geometric point actions on stalks of finite étale sheaves

For a finite étale cover `X` of a scheme `S`, the stalk of its étale sheaf of sections
`FiniteEtaleScheme.toSheaf S X` at a geometric point `s` is naturally identified with the
geometric fibre `(FiniteEtaleScheme.fiber s.hom).obj X`
(`FiniteEtaleScheme.toSheafCompSheafFiberIso`).

This file computes the action of morphisms and Galois automorphisms of geometric points on these
stalks:

* A morphism `φ : s₁ ⟶ s₂` of geometric points acts on the stalk of `FiniteEtaleScheme.toSheaf`
  by precomposing lifts with `φ`
  (`fiberCompInclIso_hom_app_toSheafCompSheafFiberIso_hom_app_toPointFunctor_map`).
* Over an affine base `Spec (.of R)`, the stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the sheaf of
  sections of `Spec B` (for a finite étale `R`-algebra `B`) is identified with `B →ₐ[R] Ω`
  (`toSheafSpecStalkEquiv`), naturally in `B` (`toSheafSpecStalkEquiv_map`), and `σ : Ω ≃ₐ[R] Ω`
  acts via `ofOverGaloisStalkAction` by postcomposition `v ↦ σ ∘ v`
  (`toSheafSpecStalkEquiv_ofOverGaloisStalkAction`).
* For any finite étale `Spec R`-scheme `X`, the same identification, cover-naturality, and
  Galois-action formula hold via its coordinate algebra (`toSheafStalkEquiv`,
  `toSheafStalkEquiv_map`, `toSheafStalkEquiv_ofOverGaloisStalkAction`).
* Over a field `K`, the stalk of `Spec B` has cardinality `Module.finrank K B.obj`
  (`natCard_toSheafSpecStalk_eq_finrank`).
* For a Kummer cover `FiniteEtaleScheme.kummerCover t n hn`, the stalk is the set of `n`-th roots
  of `t` in `Ω` (`kummerCoverStalkEquiv`), or `rootsOfUnity n Ω` when `t` maps to `1`
  (`kummerCoverStalkEquivRootsOfUnity`), compatibly with transition maps (`kummerCoverMap`) and
  deck transformations (`kummerCoverDeck`), and `σ : Ω ≃ₐ[R] Ω` acts directly on roots by
  `ω ↦ σ ω`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toSheafOfOverIdStalkEquivFiber`: identifies
  the stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of `FiniteEtaleScheme.toSheaf` with the geometric
  fibre at `Spec Ω ⟶ Spec R`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toSheafSpecStalkEquiv`: identifies the stalk
  of `FiniteEtaleScheme.toSheaf` of `Spec B` with `B →ₐ[R] Ω`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toSheafStalkEquiv`: identifies the stalk of
  `FiniteEtaleScheme.toSheaf` of any finite étale `Spec R`-scheme with the `Ω`-points of its
  coordinate algebra.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.kummerCoverStalkEquiv`,
  `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.kummerCoverStalkEquivRootsOfUnity`: identify
  the stalk of a Kummer cover with `n`-th roots of `t` and with `rootsOfUnity n Ω`.

## Main results

* `fiberCompInclIso_hom_app_toSheafCompSheafFiberIso_hom_app_toPointFunctor_map`: a morphism of
  geometric points acts on stalks of finite étale sheaves by precomposition of lifts.
* `toSheafOfOverIdStalkEquivFiber_map`, `toSheafSpecStalkEquiv_map`, `toSheafStalkEquiv_map`:
  naturality of the stalk identifications with respect to morphisms of finite étale covers.
* `toSheafSpecStalkEquiv_ofOverGaloisStalkAction`,
  `toSheafStalkEquiv_ofOverGaloisStalkAction`: on the stalk of a finite étale cover, `σ` sends the
  point with coordinate map `v` to `σ ∘ v`.
* `natCard_toSheafSpecStalk_eq_finrank`: over a field `K`, the stalk of `Spec B` has cardinality
  `Module.finrank K B.obj`.
* `kummerCoverStalkEquiv_map_kummerCoverMap`, `kummerCoverStalkEquiv_map_kummerCoverDeck`,
  `kummerCoverStalkEquivRootsOfUnity_map_kummerCoverMap`,
  `kummerCoverStalkEquivRootsOfUnity_map_kummerCoverDeck`: transition and deck-transformation
  formulae on the stalk of a Kummer cover.
* `coe_kummerCoverStalkEquiv_ofOverGaloisStalkAction`,
  `coe_kummerCoverStalkEquivRootsOfUnity_ofOverGaloisStalkAction`: on the stalk of a Kummer cover,
  `σ` acts on roots by `ω ↦ σ ω`.

## References

* The Stacks Project, [Tag 03PO](https://stacks.math.columbia.edu/tag/03PO) and
  [Tag 04FN](https://stacks.math.columbia.edu/tag/04FN).
* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/-- On the étale sheaf of sections of a finite étale `S`-scheme `X`, a morphism `φ : s₁ ⟶ s₂`
of geometric points acts on geometric fibres (via `FiniteEtaleScheme.toSheafCompSheafFiberIso`
and `FiniteEtaleScheme.fiberCompInclIso`) by precomposing lifts with `φ`. -/
theorem fiberCompInclIso_hom_app_toSheafCompSheafFiberIso_hom_app_toPointFunctor_map
    {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) (X : FiniteEtaleScheme S)
    (z : (Scheme.pointSmallEtale s₂.hom).sheafFiber.obj ((FiniteEtaleScheme.toSheaf S).obj X)) :
    (FiniteEtaleScheme.fiberCompInclIso s₁.hom).hom.app X
        ((FiniteEtaleScheme.toSheafCompSheafFiberIso s₁.hom).hom.app X
          (((toPointFunctor S).map φ).sheafFiber.app ((FiniteEtaleScheme.toSheaf S).obj X) z)) =
      (Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫
        (FiniteEtaleScheme.fiberCompInclIso s₂.hom).hom.app X
          ((FiniteEtaleScheme.toSheafCompSheafFiberIso s₂.hom).hom.app X z) := by
  let y := (FiniteEtaleScheme.toSheafCompSheafFiberIso s₂.hom).hom.app X z
  have hy : z = (FiniteEtaleScheme.toSheafCompSheafFiberIso s₂.hom).inv.app X y :=
    (Iso.hom_inv_id_app_apply (FiniteEtaleScheme.toSheafCompSheafFiberIso s₂.hom) X z).symm
  have hstep :
      ((toPointFunctor S).map φ).sheafFiber.app ((FiniteEtaleScheme.toSheaf S).obj X) z =
        (FiniteEtaleScheme.toSheafCompSheafFiberIso s₁.hom).inv.app X
          ((FiniteEtaleScheme.fiberCompInclIso s₁.hom).inv.app X
            ((Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫
              (FiniteEtaleScheme.fiberCompInclIso s₂.hom).hom.app X y)) := by
    rw [hy, FiniteEtaleScheme.toSheafCompSheafFiberIso_inv_app_apply,
      FiniteEtaleScheme.toSheafCompSheafFiberIso_inv_app_apply, Iso.inv_hom_id_app_apply]
    exact congrArg (fun g ↦ g (𝟙 _))
      (toPresheafFiber_toPointFunctor_map_sheafFiber_app (A := Type u) φ
        ((FiniteEtaleScheme.toSheaf S).obj X) ((FiniteEtaleScheme.toEtale S).obj X)
        ((FiniteEtaleScheme.fiberCompInclIso s₂.hom).hom.app X y))
  rw [hstep, Iso.inv_hom_id_app_apply, Iso.inv_hom_id_app_apply]

private lemma fiberCompInclIso_hom_app_cast_left {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (X : FiniteEtaleScheme S) {x₁ x₂ : Spec (.of Ω) ⟶ S} (h : x₁ = x₂)
    (y : (FiniteEtaleScheme.fiber x₁).obj X) :
    ((FiniteEtaleScheme.fiberCompInclIso x₂).hom.app X
        (cast (congrArg (fun x ↦ ((FiniteEtaleScheme.fiber x).obj X : Type u)) h) y)).left =
      ((FiniteEtaleScheme.fiberCompInclIso x₁).hom.app X y).left := by
  subst h
  rfl

/-- The stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the étale sheaf of sections of a finite étale
`Spec R`-scheme `X` is equivalent to the geometric fibre of `X` at
`Spec.map (CommRingCat.ofHom (algebraMap R Ω))`. -/
noncomputable def toSheafOfOverIdStalkEquivFiber (R : Type u) [CommRing R] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R))) :
    (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) ≃
      (FiniteEtaleScheme.fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj X :=
  ((FiniteEtaleScheme.toSheafCompSheafFiberIso
    (ofOver (𝟙 (Spec (.of R))) Ω).hom).app X).toEquiv.trans
    (Equiv.cast (congrArg (fun x ↦ ((FiniteEtaleScheme.fiber x).obj X : Type u))
      (Category.comp_id _)))

private lemma fiber_map_cast {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {X Y : FiniteEtaleScheme S} (f : X ⟶ Y) {x₁ x₂ : Spec (.of Ω) ⟶ S} (h : x₁ = x₂)
    (y : (FiniteEtaleScheme.fiber x₁).obj X) :
    cast (congrArg (fun x ↦ ((FiniteEtaleScheme.fiber x).obj Y : Type u)) h)
        ((FiniteEtaleScheme.fiber x₁).map f y) =
      (FiniteEtaleScheme.fiber x₂).map f
        (cast (congrArg (fun x ↦ ((FiniteEtaleScheme.fiber x).obj X : Type u)) h) y) := by
  subst h
  rfl

/-- Naturality of `toSheafOfOverIdStalkEquivFiber` with respect to morphisms of finite étale
`Spec R`-schemes. -/
@[simp]
theorem toSheafOfOverIdStalkEquivFiber_map (R : Type u) [CommRing R] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] {X Y : FiniteEtaleScheme (Spec (.of R))} (f : X ⟶ Y)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X)) :
    toSheafOfOverIdStalkEquivFiber R Ω Y
        ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map f) z) =
      (FiniteEtaleScheme.fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map f
        (toSheafOfOverIdStalkEquivFiber R Ω X z) := by
  dsimp only [toSheafOfOverIdStalkEquivFiber, Equiv.trans_apply, Iso.toEquiv_fun, Iso.app_hom,
    Equiv.cast_apply]
  have hnat := congrArg (fun g ↦ g z)
    ((FiniteEtaleScheme.toSheafCompSheafFiberIso
      (ofOver (𝟙 (Spec (.of R))) Ω).hom).hom.naturality f)
  exact (congrArg (cast _) hnat).trans (fiber_map_cast f (Category.comp_id _) _)

/-- Under `toSheafOfOverIdStalkEquivFiber`, `ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ`
acts on the geometric fibre of `X` by precomposing lifts with `Spec σ`. -/
theorem toSheafOfOverIdStalkEquivFiber_ofOverGaloisStalkAction (R : Type u) [CommRing R]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R)))
    (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X)) :
    (FiniteEtaleScheme.fiberCompInclIso
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
        (toSheafOfOverIdStalkEquivFiber R Ω X
          ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
            ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) z)) =
      (algSpec (.of R)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
        (FiniteEtaleScheme.fiberCompInclIso
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
            (toSheafOfOverIdStalkEquivFiber R Ω X z) := by
  refine Over.OverMorphism.ext ?_
  have hL :
      ((FiniteEtaleScheme.fiberCompInclIso
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
        (toSheafOfOverIdStalkEquivFiber R Ω X
          ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
            ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) z))).left =
      ((algSpec (.of R)).map (CommAlgCat.ofHom σ.toAlgHom).op).left ≫
        ((FiniteEtaleScheme.fiberCompInclIso
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
            (toSheafOfOverIdStalkEquivFiber R Ω X z)).left := by
    dsimp only [toSheafOfOverIdStalkEquivFiber, Equiv.trans_apply, Iso.toEquiv_fun, Iso.app_hom,
      Equiv.cast_apply]
    rw [fiberCompInclIso_hom_app_cast_left X (Category.comp_id _),
      fiberCompInclIso_hom_app_cast_left X (Category.comp_id _),
      ofOverGaloisStalkAction_asIso_hom]
    have hstep := congrArg
      (fun m : Over.mk (ofOver (𝟙 (Spec (.of R))) Ω).hom ⟶
          ((finiteEtaleSchemeProperty (Spec (.of R))).ι.obj X) ↦ m.left)
      (fiberCompInclIso_hom_app_toSheafCompSheafFiberIso_hom_app_toPointFunctor_map
        (homOfAlgHom (𝟙 (Spec (.of R))) σ.toAlgHom) X z)
    simp only [Over.comp_left, Over.homMk_left, homOfAlgHom_hom] at hstep
    exact hstep.trans (congrArg (· ≫ _)
      (TauCeti.AlgebraicGeometry.algSpec_map_ofHom_left
        (R := .of R) (A := CommAlgCat.of R Ω) (B := CommAlgCat.of R Ω) σ.toAlgHom).symm)
  exact hL.trans (Over.comp_left _ _ _ _ _).symm

private theorem algHom_eq_comp_of_ofOverGaloisStalkAction {R Ω : Type u} [CommRing R] [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] {X : FiniteEtaleScheme (Spec (.of R))} {B : CommAlgCat.{u} R}
    {e : X.obj ⟶ (algSpec (.of R)).obj (op B)} (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X))
    (v₁ v₂ : B →ₐ[R] Ω)
    (h₁ : (algSpec (.of R)).map (CommAlgCat.ofHom v₁).op =
      (FiniteEtaleScheme.fiberCompInclIso
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
        (toSheafOfOverIdStalkEquivFiber R Ω X
          ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
            ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) z)) ≫ e)
    (h₂ : (algSpec (.of R)).map (CommAlgCat.ofHom v₂).op =
      (FiniteEtaleScheme.fiberCompInclIso
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
        (toSheafOfOverIdStalkEquivFiber R Ω X z) ≫ e) :
    v₁ = σ.toAlgHom.comp v₂ := by
  have hmap : (algSpec (.of R)).map (CommAlgCat.ofHom v₁).op =
      (algSpec (.of R)).map (CommAlgCat.ofHom (σ.toAlgHom.comp v₂)).op :=
    calc (algSpec (.of R)).map (CommAlgCat.ofHom v₁).op
        = _ ≫ e := h₁
      _ = ((algSpec (.of R)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ _) ≫ e :=
        congrArg (· ≫ e)
          (toSheafOfOverIdStalkEquivFiber_ofOverGaloisStalkAction R Ω X σ z)
      _ = (algSpec (.of R)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ (_ ≫ e) :=
        Category.assoc _ _ _
      _ = (algSpec (.of R)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom v₂).op :=
        congrArg _ h₂.symm
      _ = (algSpec (.of R)).map (CommAlgCat.ofHom (σ.toAlgHom.comp v₂)).op := by
        rw [← Functor.map_comp, ← op_comp, ← CommAlgCat.ofHom_comp]
  have h' := congrArg (fun f : (op (CommAlgCat.of R Ω) ⟶ op B) ↦ f.unop.hom)
    (algSpec.fullyFaithful.map_injective hmap)
  simpa only [Quiver.Hom.unop_op, CommAlgCat.hom_ofHom] using h'

/-- The stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the étale sheaf of sections of the spectrum of a
finite étale `R`-algebra `B` is the set `B →ₐ[R] Ω` of `Ω`-valued points. -/
noncomputable def toSheafSpecStalkEquiv (R : Type u) [CommRing R] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] (B : CommAlgCat.FiniteEtale.{u} R) :
    (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
          ((FiniteEtaleScheme.spec (.of R)).obj (op B))) ≃
      (B.obj →ₐ[R] Ω) :=
  (toSheafOfOverIdStalkEquivFiber R Ω ((FiniteEtaleScheme.spec (.of R)).obj (op B))).trans
    (FiniteEtaleScheme.specFiberEquiv (.of R) Ω B)

/-- `toSheafSpecStalkEquiv` applies `specCompFiberIso` to `toSheafOfOverIdStalkEquivFiber`. -/
theorem toSheafSpecStalkEquiv_apply (R : Type u) [CommRing R] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] (B : CommAlgCat.FiniteEtale.{u} R)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        ((FiniteEtaleScheme.spec (.of R)).obj (op B)))) :
    toSheafSpecStalkEquiv R Ω B z =
      (FiniteEtaleScheme.specCompFiberIso (.of R) Ω).hom.app (op B)
        (toSheafOfOverIdStalkEquivFiber R Ω ((FiniteEtaleScheme.spec (.of R)).obj (op B)) z) :=
  FiniteEtaleScheme.specFiberEquiv_apply (.of R) Ω B _

/-- **Naturality of `toSheafSpecStalkEquiv`.** A morphism `f : B₁ ⟶ B₂` of finite étale
`R`-algebras acts on `Ω`-valued stalk points by precomposition with `f`. -/
@[simp]
theorem toSheafSpecStalkEquiv_map (R : Type u) [CommRing R] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] {B₁ B₂ : CommAlgCat.FiniteEtale.{u} R} (f : B₁ ⟶ B₂)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        ((FiniteEtaleScheme.spec (.of R)).obj (op B₂)))) :
    toSheafSpecStalkEquiv R Ω B₁
        ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map
            ((FiniteEtaleScheme.spec (.of R)).map f.op)) z) =
      (toSheafSpecStalkEquiv R Ω B₂ z).comp f.hom.hom := by
  dsimp only [toSheafSpecStalkEquiv, Equiv.trans_apply]
  rw [toSheafOfOverIdStalkEquivFiber_map, FiniteEtaleScheme.specFiberEquiv_map]

/-- **The Galois action on the stalk of an affine finite étale cover.** Under
`toSheafSpecStalkEquiv`, `σ : Ω ≃ₐ[R] Ω` sends the point with coordinate map `v : B →ₐ[R] Ω` to
`σ ∘ v`. -/
@[simp]
theorem toSheafSpecStalkEquiv_ofOverGaloisStalkAction (R : Type u) [CommRing R] (Ω : Type u)
    [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (B : CommAlgCat.FiniteEtale.{u} R) (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        ((FiniteEtaleScheme.spec (.of R)).obj (op B)))) :
    toSheafSpecStalkEquiv R Ω B
        ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
            ((FiniteEtaleScheme.spec (.of R)).obj (op B))) z) =
      σ.toAlgHom.comp (toSheafSpecStalkEquiv R Ω B z) := by
  have h1 := FiniteEtaleScheme.algSpec_map_specCompFiberIso_hom_app (.of R) Ω (op B)
    (toSheafOfOverIdStalkEquivFiber R Ω _
      ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
          ((FiniteEtaleScheme.spec (.of R)).obj (op B))) z))
  have h2 := FiniteEtaleScheme.algSpec_map_specCompFiberIso_hom_app (.of R) Ω (op B)
    (toSheafOfOverIdStalkEquivFiber R Ω _ z)
  rw [← toSheafSpecStalkEquiv_apply] at h1 h2
  exact algHom_eq_comp_of_ofOverGaloisStalkAction σ z _ _ h1 h2

/-- Natural isomorphism identifying `FiniteEtaleScheme.spec` of the coordinate-algebra functor
with the identity on `FiniteEtaleScheme (Spec (.of R))`, obtained by composing the counit of
`FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme` with
`FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor`. -/
noncomputable def finiteEtaleInverseCompSpecIso (R : Type u) [CommRing R] :
    (FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of R)).inverse ⋙
        FiniteEtaleScheme.spec (.of R) ≅
      𝟭 (FiniteEtaleScheme (Spec (.of R))) :=
  (Functor.isoWhiskerLeft _
      (eqToIso (FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor
        (.of R)))).symm ≪≫
    (FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of R)).counitIso

/-- Over any commutative ring `R`, the stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the étale sheaf
of sections of a finite étale `Spec R`-scheme `X` is the set of `Ω`-valued points of its
coordinate algebra, obtained by transporting `toSheafSpecStalkEquiv` along the inverse counit of
`FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme`. -/
noncomputable def toSheafStalkEquiv (R Ω : Type u) [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R))) :
    (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) ≃
      (((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
        (.of R)).inverse.obj X).unop.obj →ₐ[R] Ω) :=
  (((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.mapIso
    ((FiniteEtaleScheme.toSheaf (Spec (.of R))).mapIso
      ((finiteEtaleInverseCompSpecIso R).symm.app X))).toEquiv).trans
    (toSheafSpecStalkEquiv R Ω
      ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
        (.of R)).inverse.obj X).unop)

/-- `toSheafStalkEquiv` transports a germ along the inverse counit of
`finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme` (`(finiteEtaleInverseCompSpecIso R).inv`) and
then applies `toSheafSpecStalkEquiv`. -/
theorem toSheafStalkEquiv_apply (R Ω : Type u) [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X)) :
    toSheafStalkEquiv R Ω X z =
      toSheafSpecStalkEquiv R Ω
        ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
          (.of R)).inverse.obj X).unop
        ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map
            ((finiteEtaleInverseCompSpecIso R).inv.app X)) z) :=
  (rfl)

/-- **Naturality of `toSheafStalkEquiv`.** A morphism `f : X ⟶ Y` of finite étale
`Spec R`-schemes acts on `Ω`-valued stalk points by precomposition with the induced map on
coordinate algebras. -/
@[simp]
theorem toSheafStalkEquiv_map (R Ω : Type u) [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] {X Y : FiniteEtaleScheme (Spec (.of R))} (f : X ⟶ Y)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X)) :
    toSheafStalkEquiv R Ω Y
        ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map f) z) =
      (toSheafStalkEquiv R Ω X z).comp
        ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
          (.of R)).inverse.map f).unop.hom.hom := by
  have hnat := (finiteEtaleInverseCompSpecIso R).inv.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hnat
  rw [toSheafStalkEquiv_apply, toSheafStalkEquiv_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp, hnat, Functor.map_comp, Functor.map_comp,
    ConcreteCategory.comp_apply,
    ← Quiver.Hom.op_unop
      ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
        (.of R)).inverse.map f),
    toSheafSpecStalkEquiv_map]
  rfl

/-- **The Galois action on the stalk of any finite étale cover over an affine base.** Under
`toSheafStalkEquiv`, `σ : Ω ≃ₐ[R] Ω` sends the point with coordinate map `v` to `σ ∘ v`. -/
@[simp]
theorem toSheafStalkEquiv_ofOverGaloisStalkAction (R Ω : Type u) [CommRing R] [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R))) (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X)) :
    toSheafStalkEquiv R Ω X
        ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) z) =
      σ.toAlgHom.comp (toSheafStalkEquiv R Ω X z) := by
  have hnat := NatTrans.naturality_apply
    (ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom
    ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map
      ((finiteEtaleInverseCompSpecIso R).inv.app X)) z
  dsimp only [Functor.id_obj] at hnat
  rw [toSheafStalkEquiv_apply, toSheafStalkEquiv_apply, ← hnat]
  exact toSheafSpecStalkEquiv_ofOverGaloisStalkAction R Ω _ σ _

/-- Over a field `K`, the stalk at `ofOver (𝟙 (Spec (.of K))) Ω` of the étale sheaf of sections
of `Spec B` has cardinality `Module.finrank K B.obj`. -/
theorem natCard_toSheafSpecStalk_eq_finrank (K Ω : Type u) [Field K] [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] (B : CommAlgCat.FiniteEtale.{u} K) :
    Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of K))).obj
          ((FiniteEtaleScheme.spec (.of K)).obj (op B)))) =
      Module.finrank K B.obj :=
  (Nat.card_congr (toSheafSpecStalkEquiv K Ω B)).trans
    (TauCeti.Algebra.Etale.card_algHom_eq_finrank K B.obj Ω)

/-- For a finite separable field extension `L / K`, the stalk at `ofOver (𝟙 (Spec (.of K))) Ω`
of the étale sheaf of sections of `Spec L` has cardinality `Module.finrank K L`. -/
theorem natCard_toSheafSpecStalk_fieldExt_eq_finrank (K L : Type u) [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K Ω] :
    Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of K))).obj
          ((FiniteEtaleScheme.spec (.of K)).obj
            (op (CommAlgCat.FiniteEtale.ofSeparableFieldExt K L))))) =
      Module.finrank K L :=
  natCard_toSheafSpecStalk_eq_finrank K Ω (CommAlgCat.FiniteEtale.ofSeparableFieldExt K L)

section Kummer

variable (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
variable (t : (CommRingCat.of R)ˣ) (n : ℕ) (hn : IsUnit (n : CommRingCat.of R))

/-- The stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the étale sheaf of sections of the Kummer cover
`Spec R[x]/(x ^ n - t) ⟶ Spec R` is the set of `n`-th roots of the image of `t` in `Ω`. -/
noncomputable def kummerCoverStalkEquiv :
    (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
          (FiniteEtaleScheme.kummerCover t n hn)) ≃
      {ω : Ω // ω ^ n = algebraMap R Ω t} :=
  (toSheafOfOverIdStalkEquivFiber R Ω (FiniteEtaleScheme.kummerCover t n hn)).trans
    (FiniteEtaleScheme.kummerCoverFiberEquiv t Ω n hn)

/-- The `n`-th root attached to a germ in the stalk of a Kummer cover is the value at the
canonical root of the corresponding `R`-algebra map `R[x]/(x ^ n - t) → Ω`. -/
theorem coe_kummerCoverStalkEquiv_apply
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    (kummerCoverStalkEquiv R Ω t n hn z : Ω) =
      toSheafSpecStalkEquiv R Ω (FiniteEtaleScheme.kummerAlgebra t n hn) z (AdjoinRoot.root _) :=
  FiniteEtaleScheme.coe_kummerCoverFiberEquiv_apply t Ω n hn _

/-- On the stalk of a Kummer cover, the transition map from degree `m` to degree `n ∣ m` raises
an `m`-th root of `t` to the power `m / n`. -/
@[simp]
theorem kummerCoverStalkEquiv_map_kummerCoverMap {m : ℕ} (hm : IsUnit (m : CommRingCat.of R))
    (hd : n ∣ m)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t m hm))) :
    (kummerCoverStalkEquiv R Ω t n hn
        ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map
            (FiniteEtaleScheme.kummerCoverMap t hn hm hd)) z) : Ω) =
      (kummerCoverStalkEquiv R Ω t m hm z : Ω) ^ (m / n) := by
  dsimp only [kummerCoverStalkEquiv, Equiv.trans_apply]
  rw [toSheafOfOverIdStalkEquivFiber_map,
    FiniteEtaleScheme.kummerCoverFiberEquiv_map_kummerCoverMap]

/-- On the stalk of a Kummer cover, the deck transformation of an `n`-th root of unity `ζ` of `R`
multiplies an `n`-th root of `t` by the image of `ζ`. -/
@[simp]
theorem kummerCoverStalkEquiv_map_kummerCoverDeck (ζ : rootsOfUnity n R)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    (kummerCoverStalkEquiv R Ω t n hn
        ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map
            (FiniteEtaleScheme.kummerCoverDeck t hn ζ).hom) z) : Ω) =
      algebraMap R Ω (ζ : Rˣ) * kummerCoverStalkEquiv R Ω t n hn z := by
  dsimp only [kummerCoverStalkEquiv, Equiv.trans_apply]
  rw [toSheafOfOverIdStalkEquivFiber_map,
    FiniteEtaleScheme.kummerCoverFiberEquiv_map_kummerCoverDeck]

/-- On the stalk of a Kummer cover, `σ : Ω ≃ₐ[R] Ω` acts on the `n`-th roots of `t` by
`ω ↦ σ ω`. -/
@[simp]
theorem coe_kummerCoverStalkEquiv_ofOverGaloisStalkAction (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    (kummerCoverStalkEquiv R Ω t n hn
        ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z) : Ω) =
      σ (kummerCoverStalkEquiv R Ω t n hn z) := by
  rw [coe_kummerCoverStalkEquiv_apply, coe_kummerCoverStalkEquiv_apply]
  exact DFunLike.congr_fun
    (toSheafSpecStalkEquiv_ofOverGaloisStalkAction R Ω (FiniteEtaleScheme.kummerAlgebra t n hn) σ z)
    (AdjoinRoot.root _)

/-- When `t` maps to `1` in `Ω`, the stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the étale sheaf of
sections of the Kummer cover of degree `n` is the group `rootsOfUnity n Ω` of `n`-th roots of
unity of `Ω`. -/
noncomputable def kummerCoverStalkEquivRootsOfUnity (h : algebraMap R Ω t = 1) :
    (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
          (FiniteEtaleScheme.kummerCover t n hn)) ≃
      rootsOfUnity n Ω :=
  (toSheafOfOverIdStalkEquivFiber R Ω (FiniteEtaleScheme.kummerCover t n hn)).trans
    (FiniteEtaleScheme.kummerCoverFiberEquivRootsOfUnity t Ω n hn h)

/-- The root of unity attached to a germ in the stalk of a Kummer cover over `1` has the same
underlying element of `Ω` as `kummerCoverStalkEquiv`. -/
@[simp]
theorem coe_kummerCoverStalkEquivRootsOfUnity_apply (h : algebraMap R Ω t = 1)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    ((kummerCoverStalkEquivRootsOfUnity R Ω t n hn h z : Ωˣ) : Ω) =
      kummerCoverStalkEquiv R Ω t n hn z :=
  FiniteEtaleScheme.coe_kummerCoverFiberEquivRootsOfUnity_apply t Ω n hn h _

/-- On the stalks `rootsOfUnity n Ω` of a Kummer cover over `1`, the transition map from degree
`m` to degree `n ∣ m` is the power map `ζ ↦ ζ ^ (m / n)`. -/
@[simp]
theorem kummerCoverStalkEquivRootsOfUnity_map_kummerCoverMap {m : ℕ}
    (hm : IsUnit (m : CommRingCat.of R)) (h : algebraMap R Ω t = 1) (hd : n ∣ m)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t m hm))) :
    (kummerCoverStalkEquivRootsOfUnity R Ω t n hn h
        ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map
            (FiniteEtaleScheme.kummerCoverMap t hn hm hd)) z) : Ωˣ) =
      (kummerCoverStalkEquivRootsOfUnity R Ω t m hm h z : Ωˣ) ^ (m / n) := by
  apply Units.ext
  rw [coe_kummerCoverStalkEquivRootsOfUnity_apply, kummerCoverStalkEquiv_map_kummerCoverMap,
    Units.val_pow_eq_pow_val, coe_kummerCoverStalkEquivRootsOfUnity_apply]

/-- On the stalk `rootsOfUnity n Ω` of a Kummer cover over `1`, the deck transformation of an
`n`-th root of unity `ζ` of `R` is multiplication by the image of `ζ` in `rootsOfUnity n Ω`. -/
@[simp]
theorem kummerCoverStalkEquivRootsOfUnity_map_kummerCoverDeck (h : algebraMap R Ω t = 1)
    (ζ : rootsOfUnity n R)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    kummerCoverStalkEquivRootsOfUnity R Ω t n hn h
        ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).map
            (FiniteEtaleScheme.kummerCoverDeck t hn ζ).hom) z) =
      restrictRootsOfUnity (algebraMap R Ω) n ζ *
        kummerCoverStalkEquivRootsOfUnity R Ω t n hn h z := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_kummerCoverStalkEquivRootsOfUnity_apply, kummerCoverStalkEquiv_map_kummerCoverDeck,
    Subgroup.coe_mul, Units.val_mul, restrictRootsOfUnity_coe_apply,
    coe_kummerCoverStalkEquivRootsOfUnity_apply]

/-- On the stalk `rootsOfUnity n Ω` of a Kummer cover over `1`, `σ : Ω ≃ₐ[R] Ω` acts on roots of
unity by `ζ ↦ σ ζ`. -/
@[simp]
theorem coe_kummerCoverStalkEquivRootsOfUnity_ofOverGaloisStalkAction (h : algebraMap R Ω t = 1)
    (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    ((kummerCoverStalkEquivRootsOfUnity R Ω t n hn h
        ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z) : Ωˣ) : Ω) =
      σ (kummerCoverStalkEquivRootsOfUnity R Ω t n hn h z : Ωˣ) := by
  rw [coe_kummerCoverStalkEquivRootsOfUnity_apply, coe_kummerCoverStalkEquivRootsOfUnity_apply]
  exact coe_kummerCoverStalkEquiv_ofOverGaloisStalkAction R Ω t n hn σ z

end Kummer

/-- Over any commutative ring `R`, for any unit `t` and any `n` invertible in `R`, the stalk of
the Kummer cover `Spec R[x]/(x ^ n - t) ⟶ Spec R` at any geometric point `Ω` has cardinality `n`. -/
theorem natCard_kummerCoverStalk (R Ω : Type u) [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] (t : (CommRingCat.of R)ˣ) (n : ℕ) (hn : IsUnit (n : CommRingCat.of R)) :
    Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
          (FiniteEtaleScheme.kummerCover t n hn))) = n := by
  let t' : Ωˣ := Units.map (algebraMap R Ω).toMonoidHom t
  have hn' : IsUnit (n : Ω) := by simpa using hn.map (algebraMap R Ω)
  let P : Polynomial Ω := Polynomial.X ^ n - Polynomial.C (algebraMap R Ω t)
  have hsep : P.Separable := by
    simpa [P, t'] using Polynomial.separable_X_pow_sub_C_unit t' hn'
  have hsplit : (P.map (algebraMap Ω Ω)).Splits := by
    simpa using IsSepClosed.splits_of_separable P hsep
  have heq : {ω : Ω // ω ^ n = algebraMap R Ω t} ≃ P.rootSet Ω :=
    Equiv.subtypeEquivRight fun ω ↦ by
      rw [Polynomial.mem_rootSet_of_ne hsep.ne_zero]
      simp [P, sub_eq_zero]
  calc Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
            (FiniteEtaleScheme.kummerCover t n hn)))
      = Nat.card {ω : Ω // ω ^ n = algebraMap R Ω t} :=
        Nat.card_congr (kummerCoverStalkEquiv R Ω t n hn)
    _ = Nat.card (P.rootSet Ω) := Nat.card_congr heq
    _ = Fintype.card (P.rootSet Ω) := Nat.card_eq_fintype_card
    _ = P.natDegree := Polynomial.card_rootSet_eq_natDegree hsep hsplit
    _ = n := by simp [P]

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
