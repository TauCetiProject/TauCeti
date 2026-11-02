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

In both cases the germ `s_x` of a section `s` over any open `V ∋ x` (respectively `1 ⊗ s_x`)
corresponds to the pullback of `s`. The first statement is built on an affine open `U ∋ x`: it
combines the affine base change of sections (`CommRingCat.Hom.moduleSpecΓPullbackIso`) along the
germ map `Γ(X, U) → 𝒪_{X,x}` with the description of `M_x` as `𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)`
(`Scheme.Modules.isBaseChange_germLinearMap`). Germs of sections over other opens are fractions of
germs of sections over `U`, and pulling back sections is semilinear over the germ map, so the
equivalence sends every germ to the corresponding pullback; in particular it does not depend on
`U`. The second statement applies affine base change once more, along the residue map
`𝒪_{X,x} → κ(x)`.

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

variable {X : Scheme.{u}} (M : X.Modules)

section Chart

variable {U : X.Opens} (hU : IsAffineOpen U) (x : U)

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

private lemma stalkToΓPullback_germ_chart {g : Spec (X.presheaf.stalk x) ⟶ X}
    (hg : Spec.map (X.presheaf.germ U x x.2) ≫ hU.fromSpec = g) (hgU : ⊤ ≤ g ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    stalkToΓPullback M hU x hg (M.presheaf.germ U x x.2 s) =
      Scheme.Hom.pullbackSectionsLE g M U ⊤ hgU s := by
  rw [stalkToΓPullback, LinearEquiv.trans_apply, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, stalkIsoExtendScalars_hom_germ]
  exact (congrArg (moduleSpecΓFunctor.mapIso (pullbackChartIso M hU x hg)).hom
    (CommRingCat.Hom.moduleSpecΓPullbackIso_hom_one_tmul _ _ _)).trans
    (pullbackChartIso_hom_app M hU x hg hgU s)

end Chart

section Point

variable {x : X}

/-- Pulling back a section to `Spec 𝒪_{X,x}` commutes with restricting it to a smaller open
neighbourhood of `x`. -/
private lemma pullbackSectionsLE_fromSpecStalk_res {V W : X.Opens} (hx : x ∈ W) (hWV : W ≤ V)
    (s : Γ(M, V)) :
    Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤
        (fromSpecStalk_preimage_eq_top (hWV hx)).ge s =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M W ⊤
        (fromSpecStalk_preimage_eq_top hx).ge (M.presheaf.map (homOfLE hWV).op s) := by
  rw [Scheme.Hom.pullbackSectionsLE_apply, Scheme.Hom.pullbackSectionsLE_apply,
    ← Scheme.Hom.pullbackSections_restrict, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Sections with the same germ at `x` have the same pullback to `Spec 𝒪_{X,x}`. -/
private lemma pullbackSectionsLE_fromSpecStalk_eq_of_germ_eq {V W : X.Opens} (hV : x ∈ V)
    (hW : x ∈ W) {s : Γ(M, V)} {t : Γ(M, W)}
    (h : M.presheaf.germ V x hV s = M.presheaf.germ W x hW t) :
    Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤
        (fromSpecStalk_preimage_eq_top hV).ge s =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M W ⊤
        (fromSpecStalk_preimage_eq_top hW).ge t := by
  obtain ⟨V', hV', i, j, hij⟩ := M.presheaf.germ_eq x hV hW s t h
  rw [pullbackSectionsLE_fromSpecStalk_res M hV' i.le,
    pullbackSectionsLE_fromSpecStalk_res M hV' j.le]
  exact congrArg _ hij

/-- On an open neighbourhood `V` of `x`, the morphism `Spec 𝒪_{X,x} ⟶ X` acts on functions as
the germ map followed by the identification `Γ(Spec 𝒪_{X,x}, ⊤) ≅ 𝒪_{X,x}`. -/
private lemma appLE_fromSpecStalk {V : X.Opens} (hx : x ∈ V) (r : Γ(X, V)) :
    (X.fromSpecStalk x).appLE V ⊤ (fromSpecStalk_preimage_eq_top hx).ge r =
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (X.presheaf.germ V x hx r) := by
  have h : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_preimage_eq_top hx).ge).op :
      op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ op ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp, h, CategoryTheory.Functor.map_id,
    Category.comp_id, CommRingCat.comp_apply]

/-- Pulling back a section to `Spec 𝒪_{X,x}` turns multiplication by a function into
multiplication by its germ. -/
private lemma pullbackSectionsLE_fromSpecStalk_smul {V : X.Opens} (hx : x ∈ V) (r : Γ(X, V))
    (s : Γ(M, V)) :
    (Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤ (fromSpecStalk_preimage_eq_top hx).ge
        (r • s) : moduleSpecΓFunctor.obj ((pullback (X.fromSpecStalk x)).obj M)) =
      X.presheaf.germ V x hx r •
        (Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤
          (fromSpecStalk_preimage_eq_top hx).ge s :
            moduleSpecΓFunctor.obj ((pullback (X.fromSpecStalk x)).obj M)) := by
  rw [map_smulₛₗ, appLE_fromSpecStalk]
  -- `moduleSpecΓFunctor` restricts scalars along `𝒪_{X,x} ≅ Γ(Spec 𝒪_{X,x}, ⊤)`.
  rfl

end Point

section Chart

variable [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (x : U)

/-- The chart-dependent comparison `stalkToΓPullback` sends the germ of a section over any open
`V ∋ x` to its pullback. -/
private lemma stalkToΓPullback_germ {V : X.Opens} (hx : (x : X) ∈ V) (s : Γ(M, V)) :
    stalkToΓPullback M hU x (specMap_germ_comp_fromSpec hU x) (M.presheaf.germ V x hx s) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤
        (fromSpecStalk_preimage_eq_top hx).ge s := by
  set e := stalkToΓPullback M hU x (specMap_germ_comp_fromSpec hU x)
  have hl := hU.isLocalization_stalk x
  have := M.isLocalizedModule_germLinearMap hU x
  -- Write the germ of `s` as a fraction `t_x / a_x` of sections over the affine chart `U`.
  obtain ⟨⟨t, a⟩, hta⟩ := IsLocalizedModule.surj (hU.primeIdealOf x).asIdeal.primeCompl
    (M.germLinearMap x) (M.presheaf.germ V x hx s)
  rw [Submonoid.smul_def, germLinearMap_apply, ← algebraMap_smul_stalk,
    TopCat.Presheaf.stalk_open_algebraMap] at hta
  have h₁ : X.presheaf.germ U x x.2 a • e (M.presheaf.germ V x hx s) =
      e (M.presheaf.germ U x x.2 t) :=
    (e.map_smul _ _).symm.trans (congrArg e hta)
  have hW : (x : X) ∈ U ⊓ V := ⟨x.2, hx⟩
  have h₂ : M.presheaf.germ U x x.2 t = M.presheaf.germ (U ⊓ V) x hW
      (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a.1 •
        M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s) := by
    rw [germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact hta.symm
  have hu : IsUnit (X.presheaf.germ U x x.2 a) :=
    IsLocalization.map_units (X.presheaf.stalk x) a
  -- Both sides become equal after multiplication by the unit `a_x`.
  refine hu.smul_left_cancel.1 (h₁.trans ((stalkToΓPullback_germ_chart M hU x _
    (fromSpecStalk_preimage_eq_top x.2).ge t).trans
    ((pullbackSectionsLE_fromSpecStalk_eq_of_germ_eq M x.2 hW h₂).trans
      ((pullbackSectionsLE_fromSpecStalk_smul M hW _ _).trans ?_))))
  exact congrArg₂ (· • ·) (TopCat.Presheaf.germ_res_apply ..)
    (pullbackSectionsLE_fromSpecStalk_res M hW inf_le_right s).symm

end Chart

/-- Every point has an affine open neighbourhood. -/
private lemma exists_isAffineOpen_mem (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U :=
  let ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  ⟨U, hU, hx⟩

variable [M.IsQuasicoherent]

/-- `stalkToΓPullback` for a point `y` of an affine open `U`, stated at a point `x` equal to `y`.
Proofs substitute the equation, so that the kernel never has to identify `↑⟨x, hxU⟩` with `x`
inside the coercion of this equivalence to a function, which it can only do by unfolding the
equivalence. -/
private def stalkEquivOfChart {U : X.Opens} (hU : IsAffineOpen U) (y : U) {x : X}
    (hy : (y : X) = x) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      moduleSpecΓFunctor.obj ((pullback (X.fromSpecStalk x)).obj M) := by
  subst hy
  exact stalkToΓPullback M hU y (specMap_germ_comp_fromSpec hU y)

private lemma stalkEquivOfChart_germ {U : X.Opens} (hU : IsAffineOpen U) (y : U) {x : X}
    (hy : (y : X) = x) {V : X.Opens} (hx : x ∈ V) (s : Γ(M, V)) :
    stalkEquivOfChart M hU y hy (M.presheaf.germ V x hx s) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤
        (fromSpecStalk_preimage_eq_top hx).ge s := by
  subst hy
  exact stalkToΓPullback_germ M hU y hx s

variable (x : X)

/-- **Sections of the pullback to the local scheme at `x` are the stalk.** For a quasi-coherent
`𝒪_X`-module `M` and a point `x` of `X`, the stalk `M_x` is the module of global sections of the
pullback of `M` along `Spec 𝒪_{X,x} ⟶ X`, as `𝒪_{X,x}`-modules. The germ of a section over any
open `V ∋ x` goes to its pullback (`stalkEquivΓPullback_germ`). -/
def stalkEquivΓPullback :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      moduleSpecΓFunctor.obj ((pullback (X.fromSpecStalk x)).obj M) :=
  stalkEquivOfChart M (exists_isAffineOpen_mem x).choose_spec.1
    ⟨x, (exists_isAffineOpen_mem x).choose_spec.2⟩ rfl

variable {x}

/-- `stalkEquivΓPullback` sends the germ of a section over an open `V ∋ x` to its pullback. -/
@[simp]
lemma stalkEquivΓPullback_germ {V : X.Opens} (hx : x ∈ V) (s : Γ(M, V)) :
    stalkEquivΓPullback M x (M.presheaf.germ V x hx s) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤
        (fromSpecStalk_preimage_eq_top hx).ge s := by
  rw [stalkEquivΓPullback]
  exact stalkEquivOfChart_germ M _ _ _ hx s

/-- The inverse of `stalkEquivΓPullback` sends the pullback of a section over an open `V ∋ x` to
its germ. -/
@[simp]
lemma stalkEquivΓPullback_symm_pullbackSectionsLE {V : X.Opens} (hx : x ∈ V) (s : Γ(M, V)) :
    (stalkEquivΓPullback M x).symm
        (Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤
          (fromSpecStalk_preimage_eq_top hx).ge s) =
      M.presheaf.germ V x hx s :=
  (LinearEquiv.symm_apply_eq _).2 (stalkEquivΓPullback_germ M hx s).symm

variable (x)

omit [M.IsQuasicoherent] in
/-- Pulling back along `Spec κ(x) ⟶ Spec 𝒪_{X,x}` and then along `Spec 𝒪_{X,x} ⟶ X` is pulling
back along `Spec κ(x) ⟶ X`. -/
private def residuePullbackIso :
    (pullback (Spec.map (X.residue x))).obj ((pullback (X.fromSpecStalk x)).obj M) ≅
      (pullback (X.fromSpecResidueField x)).obj M :=
  (pullbackComp (Spec.map (X.residue x)) (X.fromSpecStalk x)).app M

omit [M.IsQuasicoherent] in
/-- `residuePullbackIso` sends iterated pullbacks of sections over an open `V ∋ x` to direct
pullbacks. -/
private lemma residuePullbackIso_hom_app {V : X.Opens} (hx : x ∈ V) (s : Γ(M, V)) :
    (residuePullbackIso M x).hom.app ⊤
        (Scheme.Hom.pullbackSectionsLE (Spec.map (X.residue x))
          ((pullback (X.fromSpecStalk x)).obj M) ⊤ ⊤ (Scheme.Hom.preimage_top _).ge
          (Scheme.Hom.pullbackSectionsLE (X.fromSpecStalk x) M V ⊤
            (fromSpecStalk_preimage_eq_top hx).ge s)) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤
        (fromSpecResidueField_preimage_eq_top hx).ge s :=
  Scheme.Hom.pullbackSectionsLE_comp_hom _ _ _ _ _ _ _ _

/-- Extension of scalars of `stalkEquivΓPullback` along the residue map `𝒪_{X,x} → κ(x)`. -/
private def stalkBaseChangeEquiv :
    (ModuleCat.extendScalars (X.residue x).hom).obj
        (ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x)) ≃ₗ[X.residueField x]
      (ModuleCat.extendScalars (X.residue x).hom).obj
        (moduleSpecΓFunctor.obj ((pullback (X.fromSpecStalk x)).obj M)) :=
  letI := (X.residue x).hom.toAlgebra
  (stalkEquivΓPullback M x).baseChange (X.presheaf.stalk x) (X.residueField x) _ _

private lemma stalkBaseChangeEquiv_one_tmul (m : M.presheaf.stalk x) :
    stalkBaseChangeEquiv M x
        ((1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom] m) =
      (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom]
        stalkEquivΓPullback M x m :=
  letI := (X.residue x).hom.toAlgebra
  LinearEquiv.baseChange_tmul ..

/-- **Sections of the pullback to the residue field at `x` are the fibre.** For a quasi-coherent
`𝒪_X`-module `M` and a point `x` of `X`, the fibre `κ(x) ⊗_{𝒪_{X,x}} M_x` of `M` at `x` is the
`κ(x)`-vector space of global sections of the pullback of `M` along `Spec κ(x) ⟶ X`. For a section
`s` over any open `V ∋ x`, the vector `1 ⊗ s_x` goes to the pullback of `s`
(`fiberEquivΓPullback_one_tmul_germ`). -/
def fiberEquivΓPullback :
    (ModuleCat.extendScalars (X.residue x).hom).obj
        (ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x)) ≃ₗ[X.residueField x]
      moduleSpecΓFunctor.obj ((pullback (X.fromSpecResidueField x)).obj M) :=
  (stalkBaseChangeEquiv M x).trans <|
    ((X.residue x).moduleSpecΓPullbackIso
      ((pullback (X.fromSpecStalk x)).obj M)).toLinearEquiv.trans
      (moduleSpecΓFunctor.mapIso (residuePullbackIso M x)).toLinearEquiv

variable {x}

/-- `fiberEquivΓPullback` sends `1 ⊗ s_x` to the pullback of a section `s` over an open
`V ∋ x`. -/
@[simp]
lemma fiberEquivΓPullback_one_tmul_germ {V : X.Opens} (hx : x ∈ V) (s : Γ(M, V)) :
    fiberEquivΓPullback M x
        ((1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom]
          M.presheaf.germ V x hx s) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤
        (fromSpecResidueField_preimage_eq_top hx).ge s := by
  -- `fiberEquivΓPullback` is a composite of three equivalences. Neither `rw` nor `simp` can apply
  -- `LinearEquiv.trans_apply` to it: the composite is not type-correct at instance transparency,
  -- because the residue field is viewed as a scalar extension of `𝒪_{X,x}`. Unfold it by hand.
  change (moduleSpecΓFunctor.mapIso (residuePullbackIso M x)).toLinearEquiv
      (((X.residue x).moduleSpecΓPullbackIso _).toLinearEquiv
        (stalkBaseChangeEquiv M x ((1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x,
          (X.residue x).hom] M.presheaf.germ V x hx s))) = _
  rw [stalkBaseChangeEquiv_one_tmul, stalkEquivΓPullback_germ, Iso.toLinearEquiv_apply]
  exact (congrArg (moduleSpecΓFunctor.mapIso (residuePullbackIso M x)).hom
    (CommRingCat.Hom.moduleSpecΓPullbackIso_hom_one_tmul _ _ _)).trans
    (residuePullbackIso_hom_app M x hx s)

/-- The inverse of `fiberEquivΓPullback` sends the pullback of a section `s` over an open `V ∋ x`
to `1 ⊗ s_x`. -/
@[simp]
lemma fiberEquivΓPullback_symm_pullbackSectionsLE {V : X.Opens} (hx : x ∈ V) (s : Γ(M, V)) :
    (fiberEquivΓPullback M x).symm
        (Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤
          (fromSpecResidueField_preimage_eq_top hx).ge s) =
      (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom]
        M.presheaf.germ V x hx s :=
  (LinearEquiv.symm_apply_eq _).2 (fiberEquivΓPullback_one_tmul_germ M hx s).symm


end AlgebraicGeometry.Scheme.Modules
