/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# Pulling back a quasi-coherent module to a point

Let `M` be a quasi-coherent `𝒪_X`-module on a scheme `X` and let `x` be a point of `X`. This file
computes the global sections of the pullback of `M` along the canonical morphisms
`Spec 𝒪_{X,x} ⟶ X` and `Spec κ(x) ⟶ X`:

* the stalk `M_x` is `Γ(Spec 𝒪_{X,x}, M|_{Spec 𝒪_{X,x}})` (`Scheme.Modules.stalkEquivΓPullback`);
* the fibre `κ(x) ⊗_{𝒪_{X,x}} M_x` is `Γ(Spec κ(x), M|_{Spec κ(x)})`
  (`Scheme.Modules.fiberEquivΓPullback`).

In both cases the germ `s_x` of a section `s` over an affine open `U ∋ x` (respectively `1 ⊗ s_x`)
corresponds to the pullback of `s`. The first statement combines the affine base change of
sections (`CommRingCat.Hom.moduleSpecΓPullbackIso`) along the germ map `Γ(X, U) → 𝒪_{X,x}` with
the description of `M_x` as `𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)`
(`Scheme.Modules.isBaseChange_germLinearMap`); the second applies affine base change once more,
along the residue map `𝒪_{X,x} → κ(x)`.

For a finite locally free sheaf `E`, the module fibre `κ(x) ⊗_{𝒪_{X,x}} E_x` describes the
fibre over `x` of the geometric total space of `E`
(`TauCeti.AlgebraicGeometry.totalSpaceFiberSpecIso`).

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 and Exercise II.5.8.
* The Stacks Project, [Tag 01I9](https://stacks.math.columbia.edu/tag/01I9).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open TauCeti.AlgebraicGeometry.Scheme (fromSpecStalk_preimage_eq_top
  fromSpecResidueField_preimage_eq_top)
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) (x : U)

/-- The canonical morphism `Spec 𝒪_{X,x} ⟶ X` factors through every affine open `U ∋ x` as
`Spec` of the germ map followed by the affine chart of `U`. -/
private lemma specMap_germ_comp_fromSpec :
    Spec.map (X.presheaf.germ U x x.2) ≫ hU.fromSpec = X.fromSpecStalk x :=
  hU.fromSpecStalk_eq_fromSpecStalk x.2

variable [M.IsQuasicoherent]

/-- The stalk `M_x` is the extension of scalars of the sections of `M` on the affine chart of `U`
along the germ map `Γ(X, U) → 𝒪_{X,x}`. -/
private def stalkIsoExtendScalars :
    ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x) ≅
      (ModuleCat.extendScalars (X.presheaf.germ U x x.2).hom).obj
        (moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) :=
  letI := (X.presheaf.germ U x x.2).hom.toAlgebra
  ((M.isBaseChange_germLinearMap hU x).equiv.symm.trans
      ((M.fromSpecSectionsEquiv hU).baseChange Γ(X, U) (X.presheaf.stalk x))).toModuleIso

private lemma stalkIsoExtendScalars_hom_germ (s : Γ(M, U)) :
    (stalkIsoExtendScalars M hU x).hom (M.presheaf.germ U x x.2 s) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Γ(X, U), (X.presheaf.germ U x x.2).hom]
        (M.fromSpecSectionsEquiv hU s) := by
  let := (X.presheaf.germ U x x.2).hom.toAlgebra
  have hb := M.isBaseChange_germLinearMap hU x
  have h₁ : hb.equiv.symm (M.presheaf.germ U x x.2 s) = 1 ⊗ₜ s := by
    rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul, germLinearMap_apply]
  -- The isomorphism is the linear equivalence `hb.equiv.symm` followed by a base change.
  exact (congrArg ((M.fromSpecSectionsEquiv hU).baseChange Γ(X, U) (X.presheaf.stalk x)) h₁).trans
    (LinearEquiv.baseChange_tmul ..)

/-- The pullback of the restriction of `M` to the affine chart of `U` along `Spec` of the germ map
is the pullback of `M` along any morphism `g` equal to `Spec 𝒪_{X,x} ⟶ Spec Γ(X, U) ⟶ X`. The
morphism `g` is kept general so that proofs can substitute the equation instead of reducing the
canonical morphism `X.fromSpecStalk x`. -/
private def pullbackChartIso {g : Spec (X.presheaf.stalk x) ⟶ X}
    (hg : Spec.map (X.presheaf.germ U x x.2) ≫ hU.fromSpec = g) :
    (pullback (Spec.map (X.presheaf.germ U x x.2))).obj (M.restrict hU.fromSpec) ≅
      (pullback g).obj M :=
  (pullback (Spec.map (X.presheaf.germ U x x.2))).mapIso
      ((restrictFunctorIsoPullback hU.fromSpec).app M) ≪≫
    (pullbackComp (Spec.map (X.presheaf.germ U x x.2)) hU.fromSpec).app M ≪≫
    (pullbackCongr hg).app M

omit [M.IsQuasicoherent] in
private lemma pullbackChartIso_hom_app {g : Spec (X.presheaf.stalk x) ⟶ X}
    (hg : Spec.map (X.presheaf.germ U x x.2) ≫ hU.fromSpec = g) (hgU : ⊤ ≤ g ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    (pullbackChartIso M hU x hg).hom.app ⊤
        (Scheme.Hom.pullbackSectionsLE (Spec.map (X.presheaf.germ U x x.2))
          (M.restrict hU.fromSpec) ⊤ ⊤ (Scheme.Hom.preimage_top _).ge
          (M.fromSpecSectionsEquiv hU s)) =
      Scheme.Hom.pullbackSectionsLE g M U ⊤ hgU s := by
  subst hg
  simp only [pullbackChartIso, Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
    Functor.mapIso_hom, Iso.app_hom]
  rw [Scheme.Hom.pullbackSectionsLE_naturality,
    restrictFunctorIsoPullback_hom_app_app_fromSpecSectionsEquiv,
    Scheme.Hom.pullbackSectionsLE_comp_hom, Scheme.Hom.pullbackSectionsLE_congr]

/-- The stalk `M_x` is isomorphic to the global sections of the pullback of `M` along any
morphism `g` equal to `Spec 𝒪_{X,x} ⟶ Spec Γ(X, U) ⟶ X`, as `𝒪_{X,x}`-modules. -/
private def stalkToΓPullback {g : Spec (X.presheaf.stalk x) ⟶ X}
    (hg : Spec.map (X.presheaf.germ U x x.2) ≫ hU.fromSpec = g) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] moduleSpecΓFunctor.obj ((pullback g).obj M) :=
  (stalkIsoExtendScalars M hU x).toLinearEquiv.trans <|
    ((X.presheaf.germ U x x.2).moduleSpecΓPullbackIso
      (M.restrict hU.fromSpec)).toLinearEquiv.trans
      (moduleSpecΓFunctor.mapIso (pullbackChartIso M hU x hg)).toLinearEquiv

private lemma stalkToΓPullback_germ {g : Spec (X.presheaf.stalk x) ⟶ X}
    (hg : Spec.map (X.presheaf.germ U x x.2) ≫ hU.fromSpec = g) (hgU : ⊤ ≤ g ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    stalkToΓPullback M hU x hg (M.presheaf.germ U x x.2 s) =
      Scheme.Hom.pullbackSectionsLE g M U ⊤ hgU s := by
  subst hg
  rw [stalkToΓPullback, LinearEquiv.trans_apply, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, stalkIsoExtendScalars_hom_germ,
    CommRingCat.Hom.moduleSpecΓPullbackIso_hom]
  -- The base-change map is stated on the scalar-extension carrier, which `rw` cannot match.
  erw [CommRingCat.Hom.moduleSpecΓPullback_app_one_tmul]
  -- Global sections over `Spec` evaluate morphisms on `⊤`, and `⊤` is the preimage of `⊤`; the
  -- carriers agree only after unfolding `moduleSpecΓFunctor`.
  change (pullbackChartIso M hU x rfl).hom.app ⊤
      (((pullbackPushforwardAdjunction (Spec.map (X.presheaf.germ U x x.2))).unit.app
        (M.restrict hU.fromSpec)).app ⊤ (M.fromSpecSectionsEquiv hU s)) = _
  rw [← Scheme.Hom.pullbackSections_apply, ← pullbackChartIso_hom_app M hU x rfl hgU s]
  exact congrArg _ (Scheme.Hom.pullbackSectionsLE_self _ _ _ _).symm

/-- **Sections of the pullback to the local scheme at `x` are the stalk.** For a quasi-coherent
`𝒪_X`-module `M` and a point `x` of an affine open `U`, the stalk `M_x` is the module of global
sections of the pullback of `M` along `Spec 𝒪_{X,x} ⟶ X`, as `𝒪_{X,x}`-modules. The germ of a
section over `U` goes to its pullback (`stalkEquivΓPullback_germ`). -/
def stalkEquivΓPullback :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      moduleSpecΓFunctor.obj ((pullback (X.fromSpecStalk x)).obj M) :=
  stalkToΓPullback M hU x (specMap_germ_comp_fromSpec hU x)

/-- `stalkEquivΓPullback` sends the germ of a section over `U` to its pullback. -/
@[simp]
lemma stalkEquivΓPullback_germ (s : Γ(M, U)) :
    stalkEquivΓPullback M hU x (M.presheaf.germ U x x.2 s) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M U ⊤
        (fromSpecStalk_preimage_eq_top x.2).ge s :=
  stalkToΓPullback_germ M hU x (specMap_germ_comp_fromSpec hU x) _ s

/-- The inverse of `stalkEquivΓPullback` sends the pullback of a section over `U` to its germ. -/
@[simp]
lemma stalkEquivΓPullback_symm_pullbackSectionsLE (s : Γ(M, U)) :
    (stalkEquivΓPullback M hU x).symm
        (Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M U ⊤
          (fromSpecStalk_preimage_eq_top x.2).ge s) =
      M.presheaf.germ U x x.2 s :=
  (LinearEquiv.symm_apply_eq _).2 (stalkEquivΓPullback_germ M hU x s).symm

/-- Pulling back along `Spec κ(x) ⟶ Spec 𝒪_{X,x}` and then along `Spec 𝒪_{X,x} ⟶ X` is pulling
back along `Spec κ(x) ⟶ X`. -/
private def residuePullbackIso (y : X) :
    (pullback (Spec.map (X.residue y))).obj ((pullback (X.fromSpecStalk y)).obj M) ≅
      (pullback (X.fromSpecResidueField y)).obj M :=
  (pullbackComp (Spec.map (X.residue y)) (X.fromSpecStalk y)).app M

omit [M.IsQuasicoherent] in
/-- `residuePullbackIso` sends iterated pullbacks of sections over an affine open `U ∋ x` to
direct pullbacks. -/
private lemma residuePullbackIso_hom_app (s : Γ(M, U)) :
    (residuePullbackIso M x).hom.app ⊤
        (Scheme.Hom.pullbackSectionsLE (Spec.map (X.residue x))
          ((pullback (X.fromSpecStalk x)).obj M) ⊤ ⊤ (Scheme.Hom.preimage_top _).ge
          (Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M U ⊤
            (fromSpecStalk_preimage_eq_top x.2).ge s)) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M U ⊤
        (fromSpecResidueField_preimage_eq_top x.2).ge s :=
  Scheme.Hom.pullbackSectionsLE_comp_hom _ _ _ _ _ _ _ _

/-- Extension of scalars of `stalkEquivΓPullback` along the residue map `𝒪_{X,x} → κ(x)`. -/
private def stalkBaseChangeEquiv :
    (ModuleCat.extendScalars (X.residue x).hom).obj
        (ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x)) ≃ₗ[X.residueField x]
      (ModuleCat.extendScalars (X.residue x).hom).obj
        (moduleSpecΓFunctor.obj ((pullback (X.fromSpecStalk x)).obj M)) :=
  letI := (X.residue x).hom.toAlgebra
  (stalkEquivΓPullback M hU x).baseChange (X.presheaf.stalk x) (X.residueField x) _ _

private lemma stalkBaseChangeEquiv_one_tmul (m : M.presheaf.stalk x) :
    stalkBaseChangeEquiv M hU x
        ((1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom] m) =
      (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom]
        stalkEquivΓPullback M hU x m :=
  letI := (X.residue x).hom.toAlgebra
  LinearEquiv.baseChange_tmul ..

/-- **Sections of the pullback to the residue field at `x` are the fibre.** For a quasi-coherent
`𝒪_X`-module `M` and a point `x` of an affine open `U`, the fibre `κ(x) ⊗_{𝒪_{X,x}} M_x` of `M` at
`x` is the `κ(x)`-vector space of global sections of the pullback of `M` along
`Spec κ(x) ⟶ X`. The vector `1 ⊗ s_x` goes to the pullback of `s`
(`fiberEquivΓPullback_one_tmul_germ`). -/
def fiberEquivΓPullback :
    (ModuleCat.extendScalars (X.residue x).hom).obj
        (ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x)) ≃ₗ[X.residueField x]
      moduleSpecΓFunctor.obj ((pullback (X.fromSpecResidueField x)).obj M) :=
  (stalkBaseChangeEquiv M hU x).trans <|
    ((X.residue x).moduleSpecΓPullbackIso
      ((pullback (X.fromSpecStalk x)).obj M)).toLinearEquiv.trans
      (moduleSpecΓFunctor.mapIso (residuePullbackIso M x)).toLinearEquiv

/-- `fiberEquivΓPullback` sends `1 ⊗ s_x` to the pullback of the section `s` over `U`. -/
@[simp]
lemma fiberEquivΓPullback_one_tmul_germ (s : Γ(M, U)) :
    fiberEquivΓPullback M hU x
        ((1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom]
          M.presheaf.germ U x x.2 s) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M U ⊤
        (fromSpecResidueField_preimage_eq_top x.2).ge s := by
  -- `fiberEquivΓPullback` is a composite of three equivalences; evaluate them one at a time.
  change (moduleSpecΓFunctor.mapIso (residuePullbackIso M x)).toLinearEquiv
      (((X.residue x).moduleSpecΓPullbackIso _).toLinearEquiv
        (stalkBaseChangeEquiv M hU x ((1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x,
          (X.residue x).hom] M.presheaf.germ U x x.2 s))) = _
  rw [stalkBaseChangeEquiv_one_tmul, stalkEquivΓPullback_germ]
  -- The pulled-back section lives in `Γ(-, ⊤)`, while the base-change map is stated on the
  -- scalar-extension carrier of global sections, so neither `rw` nor `simp` can match the
  -- remaining two steps; spell them out.
  change (residuePullbackIso M x).hom.app ⊤
      (((X.residue x).moduleSpecΓPullbackIso ((pullback (X.fromSpecStalk x)).obj M)).hom
        ((1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom]
          (Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M U ⊤
            (fromSpecStalk_preimage_eq_top x.2).ge s :
              moduleSpecΓFunctor.obj ((pullback (X.fromSpecStalk x)).obj M)))) = _
  rw [CommRingCat.Hom.moduleSpecΓPullbackIso_hom]
  erw [CommRingCat.Hom.moduleSpecΓPullback_app_one_tmul]
  -- Global sections over `Spec` evaluate morphisms on `⊤`, and `⊤` is the preimage of `⊤`; the
  -- carriers agree only after unfolding `moduleSpecΓFunctor`.
  change (residuePullbackIso M x).hom.app ⊤
      (((pullbackPushforwardAdjunction (Spec.map (X.residue x))).unit.app
        ((pullback (X.fromSpecStalk x)).obj M)).app ⊤
          (Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M U ⊤
            (fromSpecStalk_preimage_eq_top x.2).ge s)) = _
  rw [← Scheme.Hom.pullbackSections_apply, ← residuePullbackIso_hom_app M x s]
  exact congrArg _ (Scheme.Hom.pullbackSectionsLE_self _ _ _ _).symm

end AlgebraicGeometry.Scheme.Modules
