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
  (`toPointFunctor_map_sheafFiber_app_toSheafCompSheafFiberIso_inv_app_apply`).
* Over an affine base `Spec (.of R)`, the stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the sheaf of
  sections of `Spec B` (for a finite étale `R`-algebra `B`) is identified with `B →ₐ[R] Ω`
  (`toSheafSpecStalkEquiv`), and `σ : Ω ≃ₐ[R] Ω` acts via `ofOverGaloisStalkAction` by
  postcomposition `v ↦ σ ∘ v` (`toSheafSpecStalkEquiv_ofOverGaloisStalkAction`).
* For any finite étale `Spec R`-scheme `X`, the same identification and Galois-action formula hold
  via its coordinate algebra (`toSheafStalkEquiv`, `toSheafStalkEquiv_ofOverGaloisStalkAction`).
* Over a field `K`, the stalk of `Spec B` has cardinality `Module.finrank K B.obj`
  (`natCard_toSheafSpecStalk_eq_finrank`).
* For a Kummer cover `FiniteEtaleScheme.kummerCover t n hn`, the stalk is the set of `n`-th roots
  of `t` in `Ω` (`kummerCoverStalkEquiv`), or `rootsOfUnity n Ω` when `t` maps to `1`
  (`kummerCoverStalkEquivRootsOfUnity`), and `σ : Ω ≃ₐ[R] Ω` acts directly on roots by `ω ↦ σ ω`.

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

* `toPointFunctor_map_sheafFiber_app_toSheafCompSheafFiberIso_inv_app_apply`: a morphism of
  geometric points acts on stalks of finite étale sheaves by precomposition of lifts.
* `toSheafSpecStalkEquiv_ofOverGaloisStalkAction`,
  `toSheafStalkEquiv_ofOverGaloisStalkAction`: on the stalk of a finite étale cover, `σ` sends the
  point with coordinate map `v` to `σ ∘ v`.
* `natCard_toSheafSpecStalk_eq_finrank`: over a field `K`, the stalk of `Spec B` has cardinality
  `Module.finrank K B.obj`.
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

/-- On the étale sheaf of sections of a finite étale `S`-scheme `X`, the stalk map of a morphism
`φ : s₁ ⟶ s₂` of geometric points corresponds, under `FiniteEtaleScheme.toSheafCompSheafFiberIso`,
to precomposition of lifts with `φ`. -/
theorem toPointFunctor_map_sheafFiber_app_toSheafCompSheafFiberIso_inv_app_apply
    {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) (X : FiniteEtaleScheme S)
    (y : (FiniteEtaleScheme.fiber s₂.hom).obj X) :
    ((toPointFunctor S).map φ).sheafFiber.app ((FiniteEtaleScheme.toSheaf S).obj X)
        ((FiniteEtaleScheme.toSheafCompSheafFiberIso s₂.hom).inv.app X y) =
      (FiniteEtaleScheme.toSheafCompSheafFiberIso s₁.hom).inv.app X
        ((FiniteEtaleScheme.fiberCompInclIso s₁.hom).inv.app X
          ((Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫
            (FiniteEtaleScheme.fiberCompInclIso s₂.hom).hom.app X y)) := by
  rw [FiniteEtaleScheme.toSheafCompSheafFiberIso_inv_app_apply,
    FiniteEtaleScheme.toSheafCompSheafFiberIso_inv_app_apply, Iso.inv_hom_id_app_apply]
  exact congrArg (fun g ↦ g (𝟙 _))
    (toPresheafFiber_toPointFunctor_map_sheafFiber_app (A := Type u) φ
      ((FiniteEtaleScheme.toSheaf S).obj X) ((FiniteEtaleScheme.toEtale S).obj X)
      ((FiniteEtaleScheme.fiberCompInclIso s₂.hom).hom.app X y))

/-- The stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the étale sheaf of sections of a finite étale
`Spec R`-scheme `X` is equivalent to the geometric fibre of `X` at
`Spec.map (CommRingCat.ofHom (algebraMap R Ω))`. -/
noncomputable def toSheafOfOverIdStalkEquivFiber (R : Type u) [CommRing R] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R))) :
    (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) ≃
      (FiniteEtaleScheme.fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj X :=
  ((stalkIso (ofOverIdIso R Ω).inv).app
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X)).toEquiv.trans
    ((FiniteEtaleScheme.toSheafCompSheafFiberIso
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).app X).toEquiv

/-- Evaluating `toSheafOfOverIdStalkEquivFiber` transports along `(ofOverIdIso R Ω).inv` and then
applies `FiniteEtaleScheme.toSheafCompSheafFiberIso`. -/
theorem toSheafOfOverIdStalkEquivFiber_apply (R : Type u) [CommRing R] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X)) :
    toSheafOfOverIdStalkEquivFiber R Ω X z =
      (FiniteEtaleScheme.toSheafCompSheafFiberIso
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
        (((toPointFunctor (Spec (.of R))).map (ofOverIdIso R Ω).inv).sheafFiber.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) z) := by
  simp only [toSheafOfOverIdStalkEquivFiber, Equiv.trans_apply, Iso.toEquiv_fun, Iso.app_hom,
    stalkIso_hom]
  -- `toPointFunctor` and `pointSmallEtale` differ only at default transparency.
  rfl

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
  let F := (FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X
  let s₀ := of (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  -- Transport `homOfAlgHom _ σ.toAlgHom` across `ofOverIdIso R Ω` to an endomorphism `φ₀` of `s₀`.
  let φ₀ : s₀ ⟶ s₀ := homOfRingHom σ.toAlgHom.toRingHom
    (by rw [AlgHom.toRingHom_eq_coe]; exact Spec.map_algHom_comp_map_algebraMap σ.toAlgHom)
  have hcomm : (ofOverIdIso R Ω).inv ≫ homOfAlgHom (𝟙 (Spec (.of R))) σ.toAlgHom =
      φ₀ ≫ (ofOverIdIso R Ω).inv := by
    ext : 1
    simp only [comp_hom, ofOverIdIso_inv_hom, homOfAlgHom_hom, Category.id_comp, φ₀,
      homOfRingHom_hom]
    exact (Category.comp_id _).symm
  -- Rewrite the transported Galois action on `z` as `φ₀` acting on the transported germ `z₀`.
  let z₀ := ((toPointFunctor (Spec (.of R))).map (ofOverIdIso R Ω).inv).sheafFiber.app F z
  have hnat : ((toPointFunctor (Spec (.of R))).map (ofOverIdIso R Ω).inv).sheafFiber.app F
        ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app F z) =
      ((toPointFunctor (Spec (.of R))).map φ₀).sheafFiber.app F z₀ := by
    have h := congrArg (fun ψ ↦ ((toPointFunctor (Spec (.of R))).map ψ).sheafFiber.app F) hcomm
    simp only [Functor.map_comp, GrothendieckTopology.Point.Hom.sheafFiber_comp,
      NatTrans.comp_app] at h
    rw [ofOverGaloisStalkAction_asIso_hom]
    exact congrArg (fun g ↦ g z) h
  -- Identify `z₀` with `y` via `toSheafCompSheafFiberIso`, then apply `φ₀` on the geometric fibre.
  let y := toSheafOfOverIdStalkEquivFiber R Ω X z
  have hy_inv : (FiniteEtaleScheme.toSheafCompSheafFiberIso s₀.hom).inv.app X y = z₀ := by
    rw [show y = _ from toSheafOfOverIdStalkEquivFiber_apply R Ω X z]
    exact Iso.hom_inv_id_app_apply (FiniteEtaleScheme.toSheafCompSheafFiberIso s₀.hom) X z₀
  let a : ((finiteEtaleSchemeProperty (Spec (.of R))).ι ⋙
      coyoneda.obj (op (Over.mk s₀.hom))).obj X :=
    (Over.homMk φ₀.hom φ₀.w : Over.mk s₀.hom ⟶ Over.mk s₀.hom) ≫
      (FiniteEtaleScheme.fiberCompInclIso s₀.hom).hom.app X y
  have hstep : toSheafOfOverIdStalkEquivFiber R Ω X
        ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app F z) =
      (FiniteEtaleScheme.fiberCompInclIso s₀.hom).inv.app X a := by
    rw [toSheafOfOverIdStalkEquivFiber_apply, hnat, ← hy_inv,
      toPointFunctor_map_sheafFiber_app_toSheafCompSheafFiberIso_inv_app_apply φ₀ X y,
      Iso.inv_hom_id_app_apply]
  -- Cancel `fiberCompInclIso` and compare scheme morphisms via `algSpec_map_ofHom_left`.
  rw [hstep, Iso.inv_hom_id_app_apply]
  refine Over.OverMorphism.ext ?_
  simp only [a, Over.comp_left, Over.homMk_left, φ₀, homOfRingHom_hom]
  exact (congrArg (· ≫ _)
    (TauCeti.AlgebraicGeometry.algSpec_map_ofHom_left
      (R := .of R) (A := CommAlgCat.of R Ω) (B := CommAlgCat.of R Ω) σ.toAlgHom).symm).trans
    (Over.comp_left _ _ _ _ _).symm

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

/-- Over any commutative ring `R`, the stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the étale sheaf
of sections of a finite étale `Spec R`-scheme `X` is the set of `Ω`-valued points of its
coordinate algebra, obtained by transporting `toSheafSpecStalkEquiv` along the counit of
`FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme`. -/
noncomputable def toSheafStalkEquiv (R Ω : Type u) [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R))) :
    (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) ≃
      (((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
        (.of R)).inverse.obj X).unop.obj →ₐ[R] Ω) :=
  (((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.mapIso
    ((FiniteEtaleScheme.toSheaf (Spec (.of R))).mapIso
      ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
        (.of R)).counitIso.symm.app X ≪≫
        (Functor.isoWhiskerLeft _
          (eqToIso (FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor
            (.of R)))).app X))).toEquiv).trans
    (toSheafSpecStalkEquiv R Ω
      ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
        (.of R)).inverse.obj X).unop)

/-- `toSheafStalkEquiv` transports a germ along the counit of
`finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme` and then applies `toSheafSpecStalkEquiv`. -/
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
            ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
              (.of R)).counitIso.inv.app X ≫
              (Functor.isoWhiskerLeft _
                (eqToIso (FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor
                  (.of R)))).hom.app X)) z) :=
  (rfl)

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
  rw [toSheafStalkEquiv_apply, toSheafStalkEquiv_apply]
  let f := (FiniteEtaleScheme.toSheaf (Spec (.of R))).map
    ((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
      (.of R)).counitIso.inv.app X ≫
      (Functor.isoWhiskerLeft _
        (eqToIso (FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor
          (.of R)))).hom.app X)
  have hnat := ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω
    (A := Type u) σ).asIso.hom.naturality f).symm
  have hnat_z :
      (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map f
          ((ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
            ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) z) =
        (ofOverGaloisStalkAction (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj _)
          ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.map f z) :=
    congrArg (fun g ↦ g z) hnat
  rw [hnat_z]
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
  let t' : (CommRingCat.of Ω)ˣ := Units.map (algebraMap R Ω).toMonoidHom t
  have hn' : IsUnit (n : CommRingCat.of Ω) := by simpa using hn.map (algebraMap R Ω)
  have hn0 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h ↦ by
    rw [h, Nat.cast_zero] at hn'
    exact not_isUnit_zero hn'
  have heq : {ω : Ω // ω ^ n = algebraMap R Ω t} ≃ {ω : Ω // ω ^ n = algebraMap Ω Ω t'} :=
    Equiv.subtypeEquivRight fun ω ↦ by simp [t']
  calc Nat.card _
      = Nat.card {ω : Ω // ω ^ n = algebraMap R Ω t} :=
        Nat.card_congr (kummerCoverStalkEquiv R Ω t n hn)
    _ = Nat.card {ω : Ω // ω ^ n = algebraMap Ω Ω t'} := Nat.card_congr heq
    _ = Nat.card ((Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of Ω))) Ω).hom).sheafFiber.obj
          ((FiniteEtaleScheme.toSheaf (Spec (.of Ω))).obj
            (FiniteEtaleScheme.kummerCover t' n hn'))) :=
        Nat.card_congr (kummerCoverStalkEquiv Ω Ω t' n hn').symm
    _ = Module.finrank Ω (FiniteEtaleScheme.kummerAlgebra t' n hn').obj :=
        natCard_toSheafSpecStalk_eq_finrank Ω Ω (FiniteEtaleScheme.kummerAlgebra t' n hn')
    _ = n := (TauCeti.standardTameCover_free Ω (t' : Ω) n hn0).2

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
