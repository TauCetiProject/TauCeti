/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Pullback
public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Affine
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# The canonical symmetric-power comparison on affine spectra

For an arbitrary ring map `φ : R ⟶ S`, the canonical comparison
`(Spec φ)^* (Symⁿ M) ⟶ Symⁿ ((Spec φ)^* M)` is invertible for every quasicoherent module
sheaf `M` on `Spec R`. There are no flatness, finite-presentation or local-freeness hypotheses,
and no assumption on the characteristic.

The comparison is the mate of the pushforward map on sheafified symmetric tensors, not a
separately chosen isomorphism. Under the affine identifications `tildeSymmetricPowerIso` and
`tildeFunctorCompPullbackIso` it becomes the scalar-extension isomorphism
`S ⊗_R Symⁿ M ≅ Symⁿ (S ⊗_R M)` of `RingHom.extendScalarsSymmetricPowerIso`
(`pullback_tildeSymmetricPowerIso_hom`). The identification is checked on monomials, through the
pullback and tilde adjunctions. This is the affine computation needed to check invertibility of
the canonical comparison locally on schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.pullback_tildeSymmetricPowerIso_hom`: the canonical comparison on
  an associated sheaf is the scalar-extension isomorphism, and
  `TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_tilde` solves for it;
* `TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_of_spec`: it is invertible
  on every quasicoherent sheaf on `Spec R`.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped ChangeOfRings

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

-- `tildeSymmetricPowerIso_hom_toOpen_prod` in any degree `n` equal to the length of the
-- monomial. The degree of a monomial in the image of a list map is not definitionally its length.
private lemma tildeSymmetricPowerIso_hom_toOpen_of_eq_prod (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (l : List M) {n : ℕ} (hl : l.length = n) (x : M.symmetricPower n)
    (hx : x.1 = (l.map (SymmetricAlgebra.ι R M)).prod)
    (y : (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val
      (.op U)).symmetricPower n)
    (hy : y.1 = (l.map fun m ↦ SymmetricAlgebra.ι ((Spec R).presheaf.obj (.op U))
      (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
      (tilde.toOpen M U m)).prod) :
    (tildeSymmetricPowerIso n M).hom.val.app (.op U) (tilde.toOpen (M.symmetricPower n) U x) =
      (SheafOfModules.symmetricPowerIso n (tilde M)).inv.val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := (Spec R).presheaf) n).obj
            (tilde M).val)).app (.op U) y) := by
  subst hl
  obtain ⟨x, hx'⟩ := x
  obtain ⟨y, hy'⟩ := y
  dsimp only at hx hy
  subst hx hy
  exact tildeSymmetricPowerIso_hom_toOpen_prod M U l

-- The pullback comparison followed by the symmetric power of a morphism `ψ` out of `f^* M`, on a
-- sheafified symmetric tensor in the image of the adjunction unit. Stating the composite once, in
-- terms of the composite `M ⟶ f_* N`, avoids comparing the two presentations of the sections of
-- `f^* M` over the preimage of an open.
private lemma symmetricPower_map_pullbackSymmetricPowerComparison_app_val_app_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (M : Y.Modules) {N : X.Modules}
    (ψ : (Scheme.Modules.pullback f).obj M ⟶ N) (U : Y.Opensᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj (R := Y.sheaf.obj) M.val U).symmetricPower n) :
    ((SheafOfModules.symmetricPower X.sheaf n).map ψ).val.app
      ((TopologicalSpace.Opens.map f.base).op.obj U)
      (((Scheme.Modules.pullbackSymmetricPowerComparison f n).app M).val.app
        ((TopologicalSpace.Opens.map f.base).op.obj U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((SheafOfModules.symmetricPower Y.sheaf n).obj M)).val.app U
          ((SheafOfModules.symmetricPowerIso n M).inv.val.app U
            (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
              ((PresheafOfModulesOfCommRing.symmetricPower (R := Y.sheaf.obj) n).obj
                M.val)).app U x)))) =
    (SheafOfModules.symmetricPowerIso n N).inv.val.app
      ((TopologicalSpace.Opens.map f.base).op.obj U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := X.sheaf.obj) n).obj N.val)).app
            ((TopologicalSpace.Opens.map f.base).op.obj U)
        (TauCeti.SymmetricAlgebra.homogeneousSubmoduleMapₛₗ
          ((_root_.ModuleCat.semilinearMapAddEquiv
            ((TauCeti.SheafOfModules.commRingCatHom f.toRingCatSheafHom).app U).hom
            (PresheafOfModulesOfCommRing.obj (R := Y.sheaf.obj) M.val U)
            (PresheafOfModulesOfCommRing.obj (R := X.sheaf.obj) N.val
              ((TopologicalSpace.Opens.map f.base).op.obj U))).symm
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
                (Scheme.Modules.pushforward f).map ψ).val.app U)) n x)) := by
  have hw := TauCeti.SheafOfModules.pullbackSymmetricPowerComparison_app_val_app_unit
    (Scheme.Modules.pullbackPushforwardAdjunction f) n M U x
  rw [← Scheme.Modules.pullbackSymmetricPowerComparison_eq] at hw
  refine (congrArg (((SheafOfModules.symmetricPower X.sheaf n).map ψ).val.app
    ((TopologicalSpace.Opens.map f.base).op.obj U)) hw).trans ?_
  refine (SheafOfModules.symmetricPower_map_val_app_unit (R := X.sheaf) n ψ _ _).trans ?_
  refine congrArg (fun y ↦ (SheafOfModules.symmetricPowerIso n N).inv.val.app
    ((TopologicalSpace.Opens.map f.base).op.obj U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := X.sheaf.obj) n).obj N.val)).app
          ((TopologicalSpace.Opens.map f.base).op.obj U) y)) (Subtype.ext ?_)
  refine (ModuleCat.symmetricPower.coe_map_apply
    (ψ.val.app' ((TopologicalSpace.Opens.map f.base).op.obj U)) n _).trans ?_
  refine (congrArg (SymmetricAlgebra.map _ _)
    (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n x)).trans ?_
  refine (RingHom.congr_fun (SymmetricAlgebra.mapₛₗ_eq_map _).symm _).trans ?_
  rw [TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply, ← RingHom.comp_apply,
    SymmetricAlgebra.mapₛₗ_comp_mapₛₗ] <;> intro <;> rfl

/-- Under the affine identifications `tildeSymmetricPowerIso` and `tildeFunctorCompPullbackIso`,
the canonical symmetric-power pullback comparison along `Spec φ` is the scalar-extension
isomorphism `S ⊗_R Symⁿ M ≅ Symⁿ (S ⊗_R M)`. -/
@[reassoc]
theorem pullback_tildeSymmetricPowerIso_hom (n : ℕ) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).map (tildeSymmetricPowerIso n M).hom ≫
        (Scheme.Modules.pullbackSymmetricPowerComparison (Spec.map φ) n).app (tilde M) ≫
        (SheafOfModules.symmetricPower (Spec S).sheaf n).map
          ((tildeFunctorCompPullbackIso φ).hom.app M) =
      (tildeFunctorCompPullbackIso φ).hom.app (M.symmetricPower n) ≫
        tilde.map (φ.hom.extendScalarsSymmetricPowerIso.{u, u, u} n M).hom ≫
        (tildeSymmetricPowerIso n ((ModuleCat.extendScalars φ.hom).obj M)).hom := by
  let P := Scheme.Modules.pullback (Spec.map φ)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)
  -- The two adjunctions reduce the equation to the values of both sides on the associated global
  -- section of a monomial `m₁ ⋯ mₙ`. Both sides send it to the sheafified monomial in the
  -- associated sections of the `1 ⊗ mᵢ`: the left side through the canonical comparison on
  -- sheafified symmetric tensors, the right side through the scalar-extension isomorphism.
  apply (adj.homEquiv _ _).injective
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  -- `erw` crosses the scheme-module and underlying sheaf-category presentations.
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply ModuleCat.symmetricPower.hom_ext
  intro l hl hx
  subst hl
  let x : M.symmetricPower l.length := ⟨_, hx⟩
  -- Evaluate both adjunction transposes on the associated global section of `x`; the
  -- global-section functor and the pushforward retain the underlying functions.
  change ((SheafOfModules.symmetricPower (Spec S).sheaf l.length).map
      ((tildeFunctorCompPullbackIso φ).hom.app M)).val.app (op ⊤)
      (((Scheme.Modules.pullbackSymmetricPowerComparison (Spec.map φ) l.length).app
        (tilde M)).val.app (op ⊤)
        ((P.map (tildeSymmetricPowerIso l.length M).hom).val.app (op ⊤)
          ((adj.unit.app (tilde (M.symmetricPower l.length))).val.app (op ⊤)
            (tilde.toOpen (M.symmetricPower l.length) ⊤ x)))) =
    (tildeSymmetricPowerIso l.length ((ModuleCat.extendScalars φ.hom).obj M)).hom.val.app (op ⊤)
      ((tilde.map (φ.hom.extendScalarsSymmetricPowerIso.{u, u, u} l.length M).hom).val.app (op ⊤)
        (((tildeFunctorCompPullbackIso φ).hom.app (M.symmetricPower l.length)).val.app (op ⊤)
          ((adj.unit.app (tilde (M.symmetricPower l.length))).val.app (op ⊤)
            (tilde.toOpen (M.symmetricPower l.length) ⊤ x))))
  have hunit := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app (op ⊤))
    (adj.unit.naturality (tildeSymmetricPowerIso l.length M).hom))
    (tilde.toOpen (M.symmetricPower l.length) ⊤ x)
  -- Naturality is an equality of sheaf composites; display their values on this section.
  change (adj.unit.app ((SheafOfModules.symmetricPower (Spec R).sheaf l.length).obj
      (tilde M))).val.app (op ⊤) ((tildeSymmetricPowerIso l.length M).hom.val.app (op ⊤)
        (tilde.toOpen (M.symmetricPower l.length) ⊤ x)) =
    (P.map (tildeSymmetricPowerIso l.length M).hom).val.app (op ⊤)
      ((adj.unit.app (tilde (M.symmetricPower l.length))).val.app (op ⊤)
        (tilde.toOpen (M.symmetricPower l.length) ⊤ x)) at hunit
  let C := ((SheafOfModules.symmetricPower (Spec S).sheaf l.length).map
    ((tildeFunctorCompPullbackIso φ).hom.app M)).val.app (op ⊤)
  let K := ((Scheme.Modules.pullbackSymmetricPowerComparison (Spec.map φ) l.length).app
    (tilde M)).val.app (op ⊤)
  -- The left side: move the affine comparison past the unit, compute it on the monomial, and
  -- apply the canonical comparison followed by `Symⁿ` of the affine pullback isomorphism.
  refine (congrArg (fun t ↦ C (K t)) hunit.symm).trans ?_
  refine (congrArg (fun t ↦ C (K ((adj.unit.app
    ((SheafOfModules.symmetricPower (Spec R).sheaf l.length).obj (tilde M))).val.app (op ⊤) t)))
    (tildeSymmetricPowerIso_hom_toOpen_prod M ⊤ l)).trans ?_
  refine (symmetricPower_map_pullbackSymmetricPowerComparison_app_val_app_unit (Spec.map φ)
    l.length (tilde M) ((tildeFunctorCompPullbackIso φ).hom.app M) (op ⊤) _).trans ?_
  -- The right side: the affine pullback isomorphism and the scalar-extension isomorphism send the
  -- monomial to the monomial in the `1 ⊗ mᵢ`, which the affine comparison sheafifies.
  refine Eq.symm ?_
  let e := (φ.hom.extendScalarsSymmetricPowerIso.{u, u, u} l.length M).hom
  have hmap := ConcreteCategory.congr_hom (tilde.toOpen_map_app e ⊤) ((1 : S) ⊗ₜ[R,φ.hom] x)
  refine (congrArg (fun t ↦ (tildeSymmetricPowerIso l.length
      ((ModuleCat.extendScalars φ.hom).obj M)).hom.val.app (op ⊤) ((tilde.map e).val.app (op ⊤) t))
    (tildeFunctorCompPullbackIso_hom_app_unit_toOpen φ (M.symmetricPower l.length) x)).trans ?_
  refine (congrArg ((tildeSymmetricPowerIso l.length
      ((ModuleCat.extendScalars φ.hom).obj M)).hom.val.app (op ⊤)) hmap).trans ?_
  refine tildeSymmetricPowerIso_hom_toOpen_of_eq_prod _ ⊤
    (l.map fun m ↦ (1 : S) ⊗ₜ[R,φ.hom] m) (List.length_map _) _ ?_ _ ?_
  · exact (φ.hom.coe_extendScalarsSymmetricPowerIso_hom_one_tmul_prod M l hx).trans
      (congrArg List.prod (List.map_map ..).symm)
  · refine (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ _ _).trans ?_
    refine (map_list_prod (SymmetricAlgebra.mapₛₗ _) _).trans ?_
    refine (congrArg List.prod List.map_map).trans
      (Eq.trans ?_ (congrArg List.prod List.map_map).symm)
    -- Pulled-back associated sections correspond to `1 ⊗ m` under the affine pullback isomorphism.
    refine congrArg List.prod (List.map_congr_left fun m _ ↦ ?_)
    refine (SymmetricAlgebra.mapₛₗ_ι _ _).trans ?_
    exact congrArg (SymmetricAlgebra.ι _ _) (tildeFunctorCompPullbackIso_hom_app_unit_toOpen φ M m)


/-- The canonical symmetric-power pullback map on an associated sheaf is the composite of the
affine comparisons with the scalar-extension isomorphism. -/
theorem pullbackSymmetricPowerComparison_tilde (n : ℕ) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullbackSymmetricPowerComparison (Spec.map φ) n).app (tilde M) =
      (Scheme.Modules.pullback (Spec.map φ)).map (tildeSymmetricPowerIso n M).inv ≫
        (tildeFunctorCompPullbackIso φ).hom.app (M.symmetricPower n) ≫
        tilde.map (φ.hom.extendScalarsSymmetricPowerIso.{u, u, u} n M).hom ≫
        (tildeSymmetricPowerIso n ((ModuleCat.extendScalars φ.hom).obj M)).hom ≫
        (SheafOfModules.symmetricPower (Spec S).sheaf n).map
          ((tildeFunctorCompPullbackIso φ).inv.app M) := by
  let a := (Scheme.Modules.pullback (Spec.map φ)).mapIso (tildeSymmetricPowerIso n M)
  let c := (SheafOfModules.symmetricPower (Spec S).sheaf n).mapIso
    ((tildeFunctorCompPullbackIso φ).app M)
  -- Display the mapped isomorphisms so the cancellation does not depend on the
  -- different scheme-module presentations in their characteristic equations.
  change _ = a.inv ≫ _ ≫ _ ≫ _ ≫ c.inv
  apply (Iso.eq_inv_comp a).mpr
  have h := (Iso.eq_comp_inv c).mpr
    ((Category.assoc _ _ _).trans (pullback_tildeSymmetricPowerIso_hom φ n M))
  exact h.trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)))

/-- The canonical symmetric-power pullback comparison is invertible for every quasicoherent sheaf
on an affine spectrum and every ring map, including nonflat maps. -/
instance isIso_pullbackSymmetricPowerComparison_of_spec (n : ℕ) (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison (Spec.map φ) n).app M) := by
  let e := @asIso _ _ _ _ M.fromTildeΓ
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M)
  apply (NatTrans.isIso_app_iff_of_iso
    (Scheme.Modules.pullbackSymmetricPowerComparison (Spec.map φ) n) e).mp
  let N := moduleSpecΓFunctor.obj M
  rw [pullbackSymmetricPowerComparison_tilde]
  -- The composite is the forward map of the corresponding composite of isomorphisms.
  exact Iso.isIso_hom ((Scheme.Modules.pullback (Spec.map φ)).mapIso
    (tildeSymmetricPowerIso n N).symm ≪≫ (tildeFunctorCompPullbackIso φ).app (N.symmetricPower n) ≪≫
    (tilde.functor S).mapIso (φ.hom.extendScalarsSymmetricPowerIso.{u, u, u} n N) ≪≫
    tildeSymmetricPowerIso n ((ModuleCat.extendScalars φ.hom).obj N) ≪≫
    (SheafOfModules.symmetricPower (Spec S).sheaf n).mapIso
      ((tildeFunctorCompPullbackIso φ).app N).symm)

end

end TauCeti.AlgebraicGeometry
