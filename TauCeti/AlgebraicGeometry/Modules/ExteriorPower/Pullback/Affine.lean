/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Basic

/-!
# The canonical exterior-power comparison on affine spectra

For an arbitrary ring map `φ : R ⟶ S`, the canonical comparison
`(Spec φ)^* (⋀ⁿ M) ⟶ ⋀ⁿ ((Spec φ)^* M)` is invertible for every quasicoherent module
sheaf `M` on `Spec R`. There are no flatness, finite-presentation or local-freeness hypotheses.

The comparison is the mate of the pushforward map on sheafified wedges, not a separately
chosen isomorphism. We identify it with `tildePullbackExteriorPowerIso`, obtained from the
scalar-extension isomorphism for modules. The identification follows by evaluating the
pullback and tilde adjunctions on decomposable wedges. It supplies the affine computation
needed to check invertibility of the canonical comparison locally on schemes.

## References

* The Stacks Project, Lemma 10.13.6 (Tag 0C6F).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2(e).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped ChangeOfRings

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

-- The scalar-extension route in the comparison square, evaluated on a decomposable wedge.
private lemma tilde_baseChange_wedge (n : ℕ) (M : ModuleCat.{u} R) (m : Fin n → M) :
    (tilde.map (TauCeti.extendScalarsExteriorPowerIso.{u, u, u} φ.hom n M).hom).val.app (op ⊤)
        (((tildeFunctorCompPullbackIso φ).hom.app (M.exteriorPower n)).val.app (op ⊤)
          (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            (tilde (M.exteriorPower n))).val.app (op ⊤)
              (tilde.toOpen (M.exteriorPower n) ⊤ (ModuleCat.exteriorPower.mk m)))) =
      tilde.toOpen (((ModuleCat.extendScalars φ.hom).obj M).exteriorPower n) ⊤
        (ModuleCat.exteriorPower.mk (M := (ModuleCat.extendScalars φ.hom).obj M)
          (fun i ↦ (1 : S) ⊗ₜ[R,φ.hom] m i)) := by
  let b := (TauCeti.extendScalarsExteriorPowerIso.{u, u, u} φ.hom n M).hom
  have hmap := ConcreteCategory.congr_hom (tilde.toOpen_map_app b ⊤)
    ((1 : S) ⊗ₜ[R,φ.hom] ModuleCat.exteriorPower.mk m)
  refine (congrArg ((tilde.map b).val.app (op ⊤))
    (tildeFunctorCompPullbackIso_hom_app_unit_toOpen φ (M.exteriorPower n)
      (ModuleCat.exteriorPower.mk m))).trans (hmap.trans ?_)
  exact congrArg (tilde.toOpen (((ModuleCat.extendScalars φ.hom).obj M).exteriorPower n) ⊤)
    ((TauCeti.extendScalarsExteriorPowerIso_hom_tmul_mk φ.hom n M 1 m).trans (one_smul _ _))

/-- Under the affine tilde and pullback comparisons, the canonical exterior-power pullback map
is the scalar-extension map for exterior powers. -/
@[reassoc]
theorem pullback_tildeExteriorPowerIso_hom (n : ℕ) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).map (tildeExteriorPowerIso n M).hom ≫
        (Scheme.Modules.pullbackExteriorPowerComparison (Spec.map φ) n).app (tilde M) ≫
        (SheafOfModules.exteriorPower (Spec S).sheaf n).map
          ((tildeFunctorCompPullbackIso φ).hom.app M) =
      (tildeFunctorCompPullbackIso φ).hom.app (M.exteriorPower n) ≫
        tilde.map (TauCeti.extendScalarsExteriorPowerIso.{u, u, u} φ.hom n M).hom ≫
        (tildeExteriorPowerIso n ((ModuleCat.extendScalars φ.hom).obj M)).hom := by
  let P := Scheme.Modules.pullback (Spec.map φ)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)
  -- The two adjunctions reduce equality to decomposable wedges of module elements.
  apply (adj.homEquiv _ _).injective
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  -- `erw` crosses the scheme-module and underlying sheaf-category presentations.
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply ModuleCat.exteriorPower.hom_ext
  ext m
  simp only [ModuleCat.AlternatingMap.postcomp_apply]
  -- Evaluate both adjunction transposes on the associated global section of a wedge;
  -- the global-section functor and the pushforward retain the underlying functions.
  change ((SheafOfModules.exteriorPower (Spec S).sheaf n).map
      ((tildeFunctorCompPullbackIso φ).hom.app M)).val.app (op ⊤)
      (((Scheme.Modules.pullbackExteriorPowerComparison (Spec.map φ) n).app (tilde M)).val.app
        (op ⊤) ((P.map (tildeExteriorPowerIso n M).hom).val.app (op ⊤)
          ((adj.unit.app (tilde (M.exteriorPower n))).val.app (op ⊤)
            (tilde.toOpen (M.exteriorPower n) ⊤ (ModuleCat.exteriorPower.mk m))))) =
    (tildeExteriorPowerIso n ((ModuleCat.extendScalars φ.hom).obj M)).hom.val.app (op ⊤)
      ((tilde.map (TauCeti.extendScalarsExteriorPowerIso.{u, u, u} φ.hom n M).hom).val.app (op ⊤)
        (((tildeFunctorCompPullbackIso φ).hom.app (M.exteriorPower n)).val.app (op ⊤)
          ((adj.unit.app (tilde (M.exteriorPower n))).val.app (op ⊤)
            (tilde.toOpen (M.exteriorPower n) ⊤ (ModuleCat.exteriorPower.mk m)))))
  have hunit := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app (op ⊤))
    (adj.unit.naturality (tildeExteriorPowerIso n M).hom))
    (tilde.toOpen (M.exteriorPower n) ⊤ (ModuleCat.exteriorPower.mk m))
  -- Naturality is an equality of sheaf composites; display their values on this section.
  change (adj.unit.app ((SheafOfModules.exteriorPower (Spec R).sheaf n).obj (tilde M))).val.app
    (op ⊤) ((tildeExteriorPowerIso n M).hom.val.app (op ⊤)
      (tilde.toOpen (M.exteriorPower n) ⊤ (ModuleCat.exteriorPower.mk m))) =
    (P.map (tildeExteriorPowerIso n M).hom).val.app (op ⊤)
      ((adj.unit.app (tilde (M.exteriorPower n))).val.app (op ⊤)
        (tilde.toOpen (M.exteriorPower n) ⊤ (ModuleCat.exteriorPower.mk m))) at hunit
  let C := ((SheafOfModules.exteriorPower (Spec S).sheaf n).map
    ((tildeFunctorCompPullbackIso φ).hom.app M)).val.app (op ⊤)
  let K := ((Scheme.Modules.pullbackExteriorPowerComparison (Spec.map φ) n).app
    (tilde M)).val.app (op ⊤)
  -- The canonical route sends a sheafified wedge to the wedge of pulled-back sections.
  refine (congrArg (fun t ↦ C (K t)) hunit.symm).trans ?_
  refine (congrArg (fun t ↦ C (K ((adj.unit.app
    ((SheafOfModules.exteriorPower (Spec R).sheaf n).obj (tilde M))).val.app (op ⊤) t)))
    (tildeExteriorPowerIso_hom_toOpen_mk n M ⊤ m)).trans ?_
  have hw := TauCeti.SheafOfModules.pullbackExteriorPowerComparison_app_val_app_unit_mk
    adj n (tilde M) (op ⊤) (fun i ↦ tilde.toOpen M ⊤ (m i))
  rw [← Scheme.Modules.pullbackExteriorPowerComparison_eq] at hw
  refine (congrArg C hw).trans ?_
  have hc := SheafOfModules.exteriorPower_map_val_app_mk n
    ((tildeFunctorCompPullbackIso φ).hom.app M) (op ⊤)
    (fun i ↦ (adj.unit.app (tilde M)).val.app (op ⊤) (tilde.toOpen M ⊤ (m i)))
  refine hc.trans ?_
  -- The scalar-extension route has the same values, since pulled-back associated sections
  -- correspond to `1 ⊗ m` under the affine pullback isomorphism.
  let B := (ModuleCat.extendScalars φ.hom).obj M
  refine Eq.trans ?_ (congrArg ((tildeExteriorPowerIso n B).hom.val.app (op ⊤))
    (tilde_baseChange_wedge φ n M m)).symm
  refine Eq.trans ?_ (tildeExteriorPowerIso_hom_toOpen_mk n B ⊤ _).symm
  congr 3
  funext i
  exact tildeFunctorCompPullbackIso_hom_app_unit_toOpen φ M (m i)

/-- The canonical exterior-power pullback map on an associated sheaf is exactly the forward
map of the affine scalar-extension isomorphism. -/
theorem pullbackExteriorPowerComparison_tilde (n : ℕ) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullbackExteriorPowerComparison (Spec.map φ) n).app (tilde M) =
      (tildePullbackExteriorPowerIso φ n).hom.app M := by
  rw [tildePullbackExteriorPowerIso_hom_app]
  let a := (Scheme.Modules.pullback (Spec.map φ)).mapIso (tildeExteriorPowerIso n M)
  let c := (SheafOfModules.exteriorPower (Spec S).sheaf n).mapIso
    ((tildeFunctorCompPullbackIso φ).app M)
  -- Display the mapped isomorphisms so the cancellation does not depend on the
  -- different scheme-module presentations in their characteristic equations.
  change _ = a.inv ≫ _ ≫ _ ≫ _ ≫ c.inv
  apply (Iso.eq_inv_comp a).mpr
  have h := (Iso.eq_comp_inv c).mpr
    ((Category.assoc _ _ _).trans (pullback_tildeExteriorPowerIso_hom φ n M))
  exact h.trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)))

/-- The canonical exterior-power pullback comparison is invertible for every quasicoherent
sheaf on an affine spectrum and every ring map, including nonflat maps. -/
instance isIso_pullbackExteriorPowerComparison_of_spec (n : ℕ) (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackExteriorPowerComparison (Spec.map φ) n).app M) := by
  let e := @asIso _ _ _ _ M.fromTildeΓ
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M)
  apply (NatTrans.isIso_app_iff_of_iso
    (Scheme.Modules.pullbackExteriorPowerComparison (Spec.map φ) n) e).mp
  rw [pullbackExteriorPowerComparison_tilde]
  exact inferInstanceAs (IsIso (((tildePullbackExteriorPowerIso φ n).app
    (moduleSpecΓFunctor.obj M)).hom))

/-- Exterior powers commute with pullback of a quasicoherent sheaf along a ring map. The
forward map is the canonical mate of the pushforward comparison on sheafified wedges. -/
def pullbackExteriorPowerIsoOfSpec (n : ℕ) (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback (Spec.map φ)).obj
        ((SheafOfModules.exteriorPower (Spec R).sheaf n).obj M) ≅
      (SheafOfModules.exteriorPower (Spec S).sheaf n).obj
        ((Scheme.Modules.pullback (Spec.map φ)).obj M) :=
  asIso ((Scheme.Modules.pullbackExteriorPowerComparison (Spec.map φ) n).app M)

/-- The forward affine comparison is the canonical exterior-power pullback map. -/
@[simp]
theorem pullbackExteriorPowerIsoOfSpec_hom (n : ℕ) (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (pullbackExteriorPowerIsoOfSpec φ n M).hom =
      (Scheme.Modules.pullbackExteriorPowerComparison (Spec.map φ) n).app M :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
