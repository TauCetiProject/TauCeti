/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.FundamentalGroup
public import TauCeti.AlgebraicGeometry.FiniteEtale.Kummer
public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Basic
-- Proof-only: cardinality of `Ω`-points of a finite étale algebra over a field.
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
  by precomposing lifts with `φ` (`toSheafCompSheafFiberIso_inv_app_comp_toPointFunctor_map`).
* Over an affine base `Spec (.of R)`, the stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of the sheaf of
  sections of `Spec B` (for a finite étale `R`-algebra `B`) is identified with `B →ₐ[R] Ω`
  (`toSheafSpecStalkEquiv`), and `σ : Ω ≃ₐ[R] Ω` acts via `galStalkAut` by postcomposition
  `v ↦ σ ∘ v` (`toSheafSpecStalkEquiv_galStalkAut`).
* Over a field `K`, the stalk of `Spec B` has cardinality `Module.finrank K B.obj`
  (`natCard_toSheafSpecStalk_eq_finrank`), and the same Galois-action formula holds for any
  finite étale `K`-scheme `X` via its coordinate algebra
  (`toSheafFieldStalkEquiv`, `toSheafFieldStalkEquiv_galStalkAut`).
* For a Kummer cover `FiniteEtaleScheme.kummerCover t n hn`, the stalk is the set of `n`-th roots
  of `t` in `Ω` (`kummerCoverStalkEquiv`), or `rootsOfUnity n Ω` when `t` maps to `1`
  (`kummerCoverStalkEquivRootsOfUnity`), and `σ : Ω ≃ₐ[R] Ω` acts directly on roots by `ω ↦ σ ω`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toSheafOfOverIdStalkEquivFiber`: identifies
  the stalk at `ofOver (𝟙 (Spec (.of R))) Ω` of `FiniteEtaleScheme.toSheaf` with the geometric
  fibre at `Spec Ω ⟶ Spec R`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toSheafSpecStalkEquiv`: identifies the stalk
  of `FiniteEtaleScheme.toSheaf` of `Spec B` with `B →ₐ[R] Ω`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toSheafFieldStalkEquiv`: identifies the stalk
  of `FiniteEtaleScheme.toSheaf` of any finite étale `K`-scheme with the `Ω`-points of its
  coordinate algebra.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.finiteEtaleOfSeparableFieldExt`: packages a
  finite separable field extension `L / K` as an object of `CommAlgCat.FiniteEtale K`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.kummerCoverStalkEquiv`,
  `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.kummerCoverStalkEquivRootsOfUnity`: identify
  the stalk of a Kummer cover with `n`-th roots of `t` and with `rootsOfUnity n Ω`.

## Main results

* `toSheafCompSheafFiberIso_inv_app_comp_toPointFunctor_map`: a morphism of geometric points acts
  on stalks of finite étale sheaves by precomposition of lifts.
* `toSheafSpecStalkEquiv_galStalkAut`, `toSheafFieldStalkEquiv_galStalkAut`: on the stalk of a
  finite étale cover, `σ` sends the point with coordinate map `v` to `σ ∘ v`.
* `natCard_toSheafSpecStalk_eq_finrank`: over a field `K`, the stalk of `Spec B` has cardinality
  `Module.finrank K B.obj`.
* `coe_kummerCoverStalkEquiv_galStalkAut`, `coe_kummerCoverStalkEquivRootsOfUnity_galStalkAut`:
  on the stalk of a Kummer cover, `σ` acts on roots by `ω ↦ σ ω`.

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
theorem toSheafCompSheafFiberIso_inv_app_comp_toPointFunctor_map
    {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) (X : FiniteEtaleScheme S)
    (y : (FiniteEtaleScheme.fiber s₂.hom).obj X) :
    ((toPointFunctor S).map φ).sheafFiber.app ((FiniteEtaleScheme.toSheaf S).obj X)
        ((FiniteEtaleScheme.toSheafCompSheafFiberIso s₂.hom).inv.app X y) =
      (FiniteEtaleScheme.toSheafCompSheafFiberIso s₁.hom).inv.app X
        ((FiniteEtaleScheme.fiberCompInclIso s₁.hom).inv.app X
          ((Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫
            (FiniteEtaleScheme.fiberCompInclIso s₂.hom).hom.app X y)) := by
  rw [FiniteEtaleScheme.toSheafCompSheafFiberIso_inv_app_apply,
    FiniteEtaleScheme.toSheafCompSheafFiberIso_inv_app_apply]
  let a : ((finiteEtaleSchemeProperty S).ι ⋙ coyoneda.obj (op (Over.mk s₁.hom))).obj X :=
    (Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫
      (FiniteEtaleScheme.fiberCompInclIso s₂.hom).hom.app X y
  have h2 : (FiniteEtaleScheme.fiberCompInclIso s₁.hom).hom.app X
      ((FiniteEtaleScheme.fiberCompInclIso s₁.hom).inv.app X a) = a :=
    congrArg (fun g ↦ g a) ((FiniteEtaleScheme.fiberCompInclIso s₁.hom).inv_hom_id_app X)
  rw [h2]
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
  simp only [toSheafOfOverIdStalkEquivFiber, Equiv.trans_apply, Iso.toEquiv, Equiv.coe_fn_mk,
    Iso.app_hom, stalkIso_hom]
  rfl

/-- Under `toSheafOfOverIdStalkEquivFiber`, `galStalkAut (𝟙 (Spec (.of R))) Ω σ` acts on the
geometric fibre of `X` by precomposing lifts with `Spec σ`. -/
theorem toSheafOfOverIdStalkEquivFiber_galStalkAut (R : Type u) [CommRing R] (Ω : Type u)
    [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (X : FiniteEtaleScheme (Spec (.of R)))
    (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X)) :
    (FiniteEtaleScheme.fiberCompInclIso
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
        (toSheafOfOverIdStalkEquivFiber R Ω X
          ((galStalkAut (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
            ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) z)) =
      (algSpec (.of R)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
        (FiniteEtaleScheme.fiberCompInclIso
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
            (toSheafOfOverIdStalkEquivFiber R Ω X z) := by
  let F := (FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X
  let s₀ := of (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  let φ₀ : s₀ ⟶ s₀ := homOfRingHom σ.toRingHom (by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (Spec.map ∘ CommRingCat.ofHom) (RingHom.ext σ.commutes))
  have hcomm : (ofOverIdIso R Ω).inv ≫ homOfAlgHom (𝟙 (Spec (.of R))) Ω σ.toAlgHom =
      φ₀ ≫ (ofOverIdIso R Ω).inv := by
    ext : 1
    simp only [comp_hom, ofOverIdIso_inv_hom, homOfAlgHom_hom, Category.id_comp, φ₀,
      homOfRingHom_hom]
    exact (Category.comp_id _).symm
  let z₀ := ((toPointFunctor (Spec (.of R))).map (ofOverIdIso R Ω).inv).sheafFiber.app F z
  have hnat : ((toPointFunctor (Spec (.of R))).map (ofOverIdIso R Ω).inv).sheafFiber.app F
        ((galStalkAut (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app F z) =
      ((toPointFunctor (Spec (.of R))).map φ₀).sheafFiber.app F z₀ := by
    have h := congrArg (fun ψ ↦ ((toPointFunctor (Spec (.of R))).map ψ).sheafFiber.app F) hcomm
    simp only [Functor.map_comp, GrothendieckTopology.Point.Hom.sheafFiber_comp,
      NatTrans.comp_app] at h
    rw [galStalkAut_asIso_hom]
    exact congrArg (fun g ↦ g z) h
  let y := toSheafOfOverIdStalkEquivFiber R Ω X z
  have hy_inv : (FiniteEtaleScheme.toSheafCompSheafFiberIso s₀.hom).inv.app X y = z₀ := by
    dsimp only [y]
    rw [toSheafOfOverIdStalkEquivFiber_apply]
    exact congrArg (fun g ↦ g z₀)
      ((FiniteEtaleScheme.toSheafCompSheafFiberIso s₀.hom).hom_inv_id_app X)
  let a : ((finiteEtaleSchemeProperty (Spec (.of R))).ι ⋙
      coyoneda.obj (op (Over.mk s₀.hom))).obj X :=
    (Over.homMk φ₀.hom φ₀.w : Over.mk s₀.hom ⟶ Over.mk s₀.hom) ≫
      (FiniteEtaleScheme.fiberCompInclIso s₀.hom).hom.app X y
  have hstep : toSheafOfOverIdStalkEquivFiber R Ω X
        ((galStalkAut (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app F z) =
      (FiniteEtaleScheme.fiberCompInclIso s₀.hom).inv.app X a := by
    rw [toSheafOfOverIdStalkEquivFiber_apply, hnat, ← hy_inv,
      toSheafCompSheafFiberIso_inv_app_comp_toPointFunctor_map φ₀ X y]
    exact congrArg (fun g ↦ g ((FiniteEtaleScheme.fiberCompInclIso s₀.hom).inv.app X a))
      ((FiniteEtaleScheme.toSheafCompSheafFiberIso s₀.hom).inv_hom_id_app X)
  rw [hstep]
  have ha : (FiniteEtaleScheme.fiberCompInclIso s₀.hom).hom.app X
      ((FiniteEtaleScheme.fiberCompInclIso s₀.hom).inv.app X a) = a :=
    congrArg (fun g ↦ g a) ((FiniteEtaleScheme.fiberCompInclIso s₀.hom).inv_hom_id_app X)
  rw [ha]
  refine Over.OverMorphism.ext ?_
  simp only [a, Over.comp_left, Over.homMk_left, φ₀, homOfRingHom_hom]
  rfl

private theorem algHom_eq_comp_of_galStalkAut {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] {X : FiniteEtaleScheme (Spec (.of R))} {B : CommAlgCat.{u} R}
    {e : X.obj ⟶ (algSpec (.of R)).obj (op B)} (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X))
    (v₁ v₂ : B →ₐ[R] Ω)
    (h₁ : (algSpec (.of R)).map (CommAlgCat.ofHom v₁).op =
      (FiniteEtaleScheme.fiberCompInclIso
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
        (toSheafOfOverIdStalkEquivFiber R Ω X
          ((galStalkAut (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
            ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj X) z)) ≫ e)
    (h₂ : (algSpec (.of R)).map (CommAlgCat.ofHom v₂).op =
      (FiniteEtaleScheme.fiberCompInclIso
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).hom.app X
        (toSheafOfOverIdStalkEquivFiber R Ω X z) ≫ e) :
    v₁ = σ.toAlgHom.comp v₂ := by
  have h1 := congrArg Over.Hom.left h₁
  have h2 := congrArg Over.Hom.left h₂
  have h3 := congrArg Over.Hom.left (toSheafOfOverIdStalkEquivFiber_galStalkAut R Ω X σ z)
  simp only [Over.comp_left] at h1 h2 h3
  have hspec : Spec.map (CommRingCat.ofHom v₁.toRingHom) =
      Spec.map (CommRingCat.ofHom (σ.toAlgHom.comp v₂).toRingHom) :=
    h1.trans <| (congrArg (· ≫ _) h3).trans <|
      (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) h2.symm).trans <|
      (Spec.map_comp (CommRingCat.ofHom v₂.toRingHom) (CommRingCat.ofHom σ.toRingHom)).symm.trans
        (congrArg Spec.map (CommRingCat.ofHom_comp _ _).symm)
  exact AlgHom.ext fun x ↦
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)) x

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
theorem toSheafSpecStalkEquiv_galStalkAut (R : Type u) [CommRing R] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] (B : CommAlgCat.FiniteEtale.{u} R) (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        ((FiniteEtaleScheme.spec (.of R)).obj (op B)))) :
    toSheafSpecStalkEquiv R Ω B
        ((galStalkAut (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
            ((FiniteEtaleScheme.spec (.of R)).obj (op B))) z) =
      σ.toAlgHom.comp (toSheafSpecStalkEquiv R Ω B z) := by
  have h1 := FiniteEtaleScheme.algSpec_map_specCompFiberIso_hom_app (.of R) Ω (op B)
    (toSheafOfOverIdStalkEquivFiber R Ω _
      ((galStalkAut (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
        ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
          ((FiniteEtaleScheme.spec (.of R)).obj (op B))) z))
  have h2 := FiniteEtaleScheme.algSpec_map_specCompFiberIso_hom_app (.of R) Ω (op B)
    (toSheafOfOverIdStalkEquivFiber R Ω _ z)
  rw [← toSheafSpecStalkEquiv_apply] at h1 h2
  exact algHom_eq_comp_of_galStalkAut σ z _ _ h1 h2

/-- Over a field `K`, the stalk at `ofOver (𝟙 (Spec (.of K))) Ω` of the étale sheaf of sections
of a finite étale `K`-scheme `X` is the set of `Ω`-valued points of its coordinate algebra. -/
noncomputable def toSheafFieldStalkEquiv (K Ω : Type u) [Field K] [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] (X : FiniteEtaleScheme (Spec (.of K))) :
    (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.obj
        ((FiniteEtaleScheme.toSheaf (Spec (.of K))).obj X) ≃
      (((FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme
        (.of K)).inverse.obj X).unop.obj →ₐ[K] Ω) :=
  (toSheafOfOverIdStalkEquivFiber K Ω X).trans
    (FintypeCat.equivEquivIso.symm ((FiniteEtaleScheme.fiberIsoFiniteEtaleFiber K Ω).app X))

/-- `toSheafFieldStalkEquiv` applies `fiberIsoFiniteEtaleFiber` to
`toSheafOfOverIdStalkEquivFiber`. -/
theorem toSheafFieldStalkEquiv_apply (K Ω : Type u) [Field K] [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] (X : FiniteEtaleScheme (Spec (.of K)))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of K))).obj X)) :
    toSheafFieldStalkEquiv K Ω X z =
      (FiniteEtaleScheme.fiberIsoFiniteEtaleFiber K Ω).hom.app X
        (toSheafOfOverIdStalkEquivFiber K Ω X z) :=
  (rfl)

/-- **The Galois action on the stalk of a finite étale cover over a field.** Under
`toSheafFieldStalkEquiv`, `σ ∈ Gal(Ω/K)` sends the point with coordinate map `v` to `σ ∘ v`. -/
theorem toSheafFieldStalkEquiv_galStalkAut (K Ω : Type u) [Field K] [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] (X : FiniteEtaleScheme (Spec (.of K))) (σ : Gal(Ω/K))
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of K))).obj X)) :
    toSheafFieldStalkEquiv K Ω X
        ((galStalkAut (𝟙 (Spec (.of K))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of K))).obj X) z) =
      σ.toAlgHom.comp (toSheafFieldStalkEquiv K Ω X z) :=
  algHom_eq_comp_of_galStalkAut σ z _ _
    (FiniteEtaleScheme.algSpec_map_fiberIsoFiniteEtaleFiber_hom_app K Ω X _)
    (FiniteEtaleScheme.algSpec_map_fiberIsoFiniteEtaleFiber_hom_app K Ω X _)

/-- A finite separable field extension `L / K` is a finite étale `K`-algebra. -/
-- Exposed so that `(finiteEtaleOfSeparableFieldExt K L).obj` unfolds definitionally to `L` in
-- downstream statements about `L →ₐ[K] Ω`.
@[expose] noncomputable def finiteEtaleOfSeparableFieldExt (K L : Type u) [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L] :
    CommAlgCat.FiniteEtale.{u} K :=
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.Etale K L := ⟨inferInstance,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  CommAlgCat.FiniteEtale.of K L

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
            (op (finiteEtaleOfSeparableFieldExt K L))))) =
      Module.finrank K L := by
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.Etale K L := ⟨inferInstance,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact (Nat.card_congr (toSheafSpecStalkEquiv K Ω (finiteEtaleOfSeparableFieldExt K L))).trans
    (TauCeti.Algebra.Etale.card_algHom_eq_finrank K L Ω)

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
theorem coe_kummerCoverStalkEquiv_galStalkAut (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    (kummerCoverStalkEquiv R Ω t n hn
        ((galStalkAut (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z) : Ω) =
      σ (kummerCoverStalkEquiv R Ω t n hn z) := by
  rw [coe_kummerCoverStalkEquiv_apply, coe_kummerCoverStalkEquiv_apply]
  exact DFunLike.congr_fun
    (toSheafSpecStalkEquiv_galStalkAut R Ω (FiniteEtaleScheme.kummerAlgebra t n hn) σ z)
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
theorem coe_kummerCoverStalkEquivRootsOfUnity_galStalkAut (h : algebraMap R Ω t = 1)
    (σ : Ω ≃ₐ[R] Ω)
    (z : (Scheme.pointSmallEtale (ofOver (𝟙 (Spec (.of R))) Ω).hom).sheafFiber.obj
      ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
        (FiniteEtaleScheme.kummerCover t n hn))) :
    ((kummerCoverStalkEquivRootsOfUnity R Ω t n hn h
        ((galStalkAut (𝟙 (Spec (.of R))) Ω σ).asIso.hom.app
          ((FiniteEtaleScheme.toSheaf (Spec (.of R))).obj
            (FiniteEtaleScheme.kummerCover t n hn)) z) : Ωˣ) : Ω) =
      σ (kummerCoverStalkEquivRootsOfUnity R Ω t n hn h z : Ωˣ) := by
  rw [coe_kummerCoverStalkEquivRootsOfUnity_apply, coe_kummerCoverStalkEquivRootsOfUnity_apply]
  exact coe_kummerCoverStalkEquiv_galStalkAut R Ω t n hn σ z

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
