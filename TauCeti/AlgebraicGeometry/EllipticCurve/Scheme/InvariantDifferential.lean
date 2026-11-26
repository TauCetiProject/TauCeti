/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Conormal
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.FormalPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange.Basic
import TauCeti.Algebra.Regular.SMul
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection

/-!
# The Weierstrass invariant differential and adapted `x`-coordinate

For an elliptic Weierstrass curve `W` over `R`, `W.projModelFormalPoint : Spec R⟦X⟧ ⟶ W.projModel`
pulls `W.projModelZero` back to `(X)` (`zeroSectionDivisor_comap_projModelFormalPoint`).
Multiplication by `X` defines `W.formalConormalIso` over `Spec R⟦X⟧`
(`formalConormalIso_hom_comp_map_sheafι`), whose restriction along `X = 0` (`constantCoeff`) is the
**Weierstrass differential** `W.weierstrassDifferential : 𝟙_ (Spec (.of R)).Modules ≅
W.projModelZero.conormalSheaf` (`weierstrassDifferential_def`). It is base-change invariant
(`conormalBasisPullback_weierstrassDifferential_projModelBaseChange`) and scales by `C.u⁻¹` along
`W.projModelVariableChangeIso C`
(`conormalBasisPullbackOfIso_weierstrassDifferential_projModelVariableChangeIso`).

For sections `P, Q` missing `W.projModelZero` everywhere and `ω = u • W.weierstrassDifferential`
(`weierstrassDifferentialScalar`), the **`ω`-adapted `x`-coordinate**
`W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = (u⁻¹)² · (x(Q) - x(P))` is invariant under pointed
cartesian squares (`map_projModelAdaptedXCoord_of_isPullback`).

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Princeton Univ. Press, 1985,
  2.1.6, 2.2.4, and 2.2.9.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and IV.1.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry PowerSeries
open AlgebraicGeometry.Scheme (ΓSpecIso ΓSpecUnitsMulEquiv coe_ΓSpecUnitsMulEquiv
  SpecMap_appTop_ΓSpecIso_inv)
open AlgebraicGeometry.Scheme.Modules (unitSmulIso unitSmulIso_hom unitSmulIso_mul unitSmulIso_inj
  existsUnique_unitSmulIso_eq globalSectionsSmul pullbackObjUnitIso)
open AlgebraicGeometry.Scheme.Hom (conormalBasisPullback conormalBasisPullback_congr
  conormalBasisPullback_comp conormalBasisPullback_unitSmulIso
  conormalBasisPullback_eq_basisPullback conormalBasisPullbackOfIso conormalBasisPullbackOfIso_def
  conormalBasisPullbackOfIso_congr conormalBasisPullbackOfIso_unitSmulIso)

universe u

namespace WeierstrassCurve

noncomputable section

variable {R R' : Type u} [CommRing R] [CommRing R'] (W : WeierstrassCurve R)

/-- Extending scalars along `φ : R →+* R'` carries the formal point of `W.map φ` to that of `W`. -/
@[reassoc (attr := simp)]
theorem projModelFormalPoint_projModelBaseChange (φ : R →+* R') :
    (W.map φ).projModelFormalPoint ≫ W.projModelBaseChange φ =
      Spec.map (CommRingCat.ofHom (PowerSeries.map φ)) ≫ W.projModelFormalPoint := by
  rw [projModelFormalPoint_def, projModelFormalPoint_def, projModelPoint_projModelBaseChange,
    SpecMap_projModelPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨by ext; simp, 1, funext fun k ↦ ?_⟩; fin_cases k <;> simp [map_formalW]

open Matrix in
/-- `(W.projModelVariableChangeIso C).hom` reparametrises the formal point by
`C.formalCoordinate W`. -/
@[reassoc]
theorem projModelFormalPoint_projModelVariableChangeIso_hom (C : VariableChange R) :
    (C • W).projModelFormalPoint ≫ (W.projModelVariableChangeIso C).hom =
      Spec.map (CommRingCat.ofHom (substAlgHom (C.formalCoordinate W).hasSubst).toRingHom) ≫
        W.projModelFormalPoint := by
  let D := C.formalDenom W
  have hDd : D * invOfUnit D (C.u ^ 3) = 1 :=
    mul_invOfUnit D (C.u ^ 3) (C.constantCoeff_formalDenom W)
  let uD : R⟦X⟧ˣ := Units.mkOfMulEqOne D (invOfUnit D (C.u ^ 3)) hDd
  have hx : ((C.map (algebraMap R R⟦X⟧)).toMatrix *ᵥ ![X, -1, formalW (C • W)]) 0 =
      PowerSeries.C (C.u : R) ^ 2 * X + PowerSeries.C C.r * formalW (C • W) := by
    simp [VariableChange.toMatrix_def, algebraMap_eq]; ring
  have h1 : ((C.map (algebraMap R R⟦X⟧)).toMatrix *ᵥ ![X, -1, formalW (C • W)]) 1 = -D := by
    simp [VariableChange.toMatrix_def, D, VariableChange.formalDenom_def]; ring
  have hz : ((C.map (algebraMap R R⟦X⟧)).toMatrix *ᵥ ![X, -1, formalW (C • W)]) 2 =
      formalW (C • W) := by
    simp [VariableChange.toMatrix_def]
  have hj : IsUnit (((C.map (algebraMap R R⟦X⟧)).toMatrix *ᵥ ![X, -1, formalW (C • W)]) 1) :=
    h1 ▸ (C.isUnit_formalDenom W).neg
  rw [projModelFormalPoint_def, projModelPoint_projModelVariableChangeIso_hom _ hj,
    SpecMap_substAlgHom_projModelFormalPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨rfl, uD, funext fun k ↦ ?_⟩
  have huD : (uD : R⟦X⟧) = D := Units.val_mkOfMulEqOne hDd
  rw [C.subst_formalCoordinate_formalW W, C.formalCoordinate_toPowerSeries W]
  fin_cases k
  · -- x-coordinate
    simp only [Fin.zero_eta, Fin.isValue, hx, Matrix.cons_val_zero, Units.smul_def, Pi.smul_apply,
      smul_eq_mul, huD]
    linear_combination -((PowerSeries.C (C.u : R) ^ 2 * X +
      PowerSeries.C C.r * formalW (C • W)) * hDd)
  · -- y-coordinate
    simp only [Fin.mk_one, Fin.isValue, h1, Matrix.cons_val_one, Matrix.cons_val_zero,
      Units.smul_def, Pi.smul_apply, smul_eq_mul, huD]
    ring
  · -- z-coordinate
    simp only [Fin.reduceFinMk, Fin.isValue, hz, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Units.smul_def, Pi.smul_apply, smul_eq_mul, huD]
    linear_combination -(formalW (C • W) * hDd)

private lemma isSMulRegular_formalParamTop (U : (Spec (.of R⟦X⟧)).affineOpens) :
    IsSMulRegular Γ(Spec (.of R⟦X⟧), U) ((Spec (.of R⟦X⟧)).presheaf.map
      (homOfLE (le_top : U.val ≤ ⊤)).op ((ΓSpecIso (.of R⟦X⟧)).inv X)) :=
  (isAffineOpen_top (Spec (.of R⟦X⟧))).isSMulRegular_map le_top <|
    (TauCeti.isSMulRegular_map_iff (ΓSpecIso (.of R⟦X⟧)).symm.commRingCatIsoToRingEquiv X).mpr
      PowerSeries.X_mul_injective

private lemma ker_comap_projModelFormalPoint :
    W.projModelZero.ker.comap W.projModelFormalPoint =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {((ΓSpecIso (.of R⟦X⟧)).inv X)}) := by
  rw [← W.zeroSectionDivisor_def, W.zeroSectionDivisor_comap_projModelFormalPoint, Ideal.map_span,
    Set.image_singleton]

private lemma ideal_ker_comap_projModelFormalPoint (U : (Spec (.of R⟦X⟧)).affineOpens) :
    (W.projModelZero.ker.comap W.projModelFormalPoint).ideal U =
      Ideal.span {((Spec (.of R⟦X⟧)).presheaf.map (homOfLE (le_top : U.val ≤ ⊤)).op
        ((ΓSpecIso (.of R⟦X⟧)).inv X))} := by
  rw [W.ker_comap_projModelFormalPoint, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
    Set.image_singleton]

private theorem isEffectiveCartier_ker_comap_projModelFormalPoint :
    (W.projModelZero.ker.comap W.projModelFormalPoint).IsEffectiveCartier :=
  W.ker_comap_projModelFormalPoint ▸
    Scheme.IdealSheafData.isEffectiveCartier_ofIdealTop_span_singleton _
      isSMulRegular_formalParamTop

/-- The zero-section ideal sheaf of an elliptic Weierstrass curve is an effective Cartier
divisor. -/
theorem isEffectiveCartier_ker_projModelZero [W.IsElliptic] :
    W.projModelZero.ker.IsEffectiveCartier :=
  W.zeroSectionDivisor_def ▸ W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier

private def formalZeroIso :
    𝟙_ (Spec (.of R⟦X⟧)).Modules ≅ (W.projModelZero.ker.comap W.projModelFormalPoint).sheaf :=
  (W.projModelZero.ker.comap W.projModelFormalPoint).unitIsoOfForallIdealEqSpan
    isSMulRegular_formalParamTop W.ideal_ker_comap_projModelFormalPoint

private lemma formalZeroIso_hom_sheafι :
    W.formalZeroIso.hom ≫ (W.projModelZero.ker.comap W.projModelFormalPoint).sheafι =
      globalSectionsSmul (𝟙_ (Spec (.of R⟦X⟧)).Modules) ((ΓSpecIso (.of R⟦X⟧)).inv X) := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_; ext r
  simp only [Scheme.Modules.globalSectionsSmul_app, Scheme.Modules.smul_apply, formalZeroIso]
  exact (W.projModelZero.ker.comap W.projModelFormalPoint).sheafι_app_unitIsoOfForallIdealEqSpan_hom
    isSMulRegular_formalParamTop W.ideal_ker_comap_projModelFormalPoint U r

/-- Global basis of `(W.projModelFormalPoint)^* W.projModelZero.ker.sheaf` on `Spec R⟦X⟧`
generated by `X` (`formalConormalIso_hom_comp_map_sheafι`). -/
def formalConormalIso [W.IsElliptic] :
    𝟙_ (Spec (.of R⟦X⟧)).Modules ≅
      (Scheme.Modules.pullback W.projModelFormalPoint).obj W.projModelZero.ker.sheaf :=
  have := W.projModelZero.ker.isIso_pullbackSheafHom W.projModelFormalPoint
    W.isEffectiveCartier_ker_projModelZero W.isEffectiveCartier_ker_comap_projModelFormalPoint
  W.formalZeroIso ≪≫ (asIso (W.projModelZero.ker.pullbackSheafHom W.projModelFormalPoint)).symm

/-- Composing `W.formalConormalIso.hom` with the pulled-back ideal inclusion into `𝒪_{Spec R⟦X⟧}`
is scalar multiplication by `X`. -/
lemma formalConormalIso_hom_comp_map_sheafι [W.IsElliptic] :
    W.formalConormalIso.hom ≫
        ((Scheme.Modules.pullback W.projModelFormalPoint).map W.projModelZero.ker.sheafι ≫
          (pullbackObjUnitIso W.projModelFormalPoint).hom) =
      globalSectionsSmul (𝟙_ (Spec (.of R⟦X⟧)).Modules) ((ΓSpecIso (.of R⟦X⟧)).inv X) := by
  have := W.projModelZero.ker.isIso_pullbackSheafHom W.projModelFormalPoint
    W.isEffectiveCartier_ker_projModelZero W.isEffectiveCartier_ker_comap_projModelFormalPoint
  have hpull : W.projModelZero.ker.pullbackSheafHom W.projModelFormalPoint ≫
      (W.projModelZero.ker.comap W.projModelFormalPoint).sheafιUnit = _ :=
    W.projModelZero.ker.pullbackSheafHom_sheafι W.projModelFormalPoint
  rw [← hpull, formalConormalIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    IsIso.inv_hom_id_assoc]
  exact W.formalZeroIso_hom_sheafι

/-- **The Weierstrass invariant differential** of `W`: the canonical basis
`𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf` (`weierstrassDifferential_def`). -/
def weierstrassDifferential [W.IsElliptic] :
    𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf :=
  W.projModelZero.ker.basisPullback W.projModelZero.ker
    (p := W.projModelFormalPoint) (p' := W.projModelZero)
    (f := Spec.map (CommRingCat.ofHom (constantCoeff (R := R)))) (g := 𝟙 W.projModel)
    (by rw [W.SpecMap_constantCoeff_projModelFormalPoint, Category.comp_id])
    W.projModelZero.ker.comap_id.symm W.isEffectiveCartier_ker_projModelZero
    W.isEffectiveCartier_ker_projModelZero W.formalConormalIso

/-- `weierstrassDifferential` is the pullback along `X = 0` of `W.formalConormalIso`. -/
theorem weierstrassDifferential_def [W.IsElliptic] :
    W.weierstrassDifferential =
      W.projModelZero.ker.basisPullback W.projModelZero.ker
        (p := W.projModelFormalPoint) (p' := W.projModelZero)
        (f := Spec.map (CommRingCat.ofHom (constantCoeff (R := R)))) (g := 𝟙 W.projModel)
        (by rw [W.SpecMap_constantCoeff_projModelFormalPoint, Category.comp_id])
        W.projModelZero.ker.comap_id.symm W.isEffectiveCartier_ker_projModelZero
        W.isEffectiveCartier_ker_projModelZero W.formalConormalIso := by rfl

section Comparison

variable {W} {W' : WeierstrassCurve R'} [W.IsElliptic] [W'.IsElliptic]

private lemma basisPullback_formalConormalIso {ψ : R⟦X⟧ →+* R'⟦X⟧} {g : W'.projModel ⟶ W.projModel}
    (hg : W'.projModelFormalPoint ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelFormalPoint)
    (hI : W'.projModelZero.ker = W.projModelZero.ker.comap g)
    (v : R'⟦X⟧ˣ) (hψX : ψ X = X * (v : R'⟦X⟧)) :
    W.projModelZero.ker.basisPullback W'.projModelZero.ker hg hI
        W.isEffectiveCartier_ker_projModelZero W'.isEffectiveCartier_ker_projModelZero
        W.formalConormalIso =
      unitSmulIso (ΓSpecUnitsMulEquiv (.of R'⟦X⟧) v) W'.formalConormalIso := by
  let F := Spec.map (CommRingCat.ofHom ψ); let vTop := ΓSpecUnitsMulEquiv (.of R'⟦X⟧) v
  let μ' := (Scheme.Modules.pullback W'.projModelFormalPoint).map W'.projModelZero.ker.sheafι ≫
    (pullbackObjUnitIso W'.projModelFormalPoint).hom
  have := W'.projModelZero.ker.isIso_pullbackSheafHom W'.projModelFormalPoint
    W'.isEffectiveCartier_ker_projModelZero W'.isEffectiveCartier_ker_comap_projModelFormalPoint
  have : Mono μ' := by
    dsimp only [μ']; rw [← W'.projModelZero.ker.pullbackSheafHom_sheafι]; exact mono_comp _ _
  ext1; refine (cancel_mono μ').mp ?_
  have hlhs : (W.projModelZero.ker.basisPullback W'.projModelZero.ker hg hI
      W.isEffectiveCartier_ker_projModelZero W'.isEffectiveCartier_ker_projModelZero
      W.formalConormalIso).hom ≫ μ' =
      globalSectionsSmul (𝟙_ (Spec (.of R'⟦X⟧)).Modules)
        (F.appTop ((ΓSpecIso (.of R⟦X⟧)).inv X)) := by
    rw [Scheme.IdealSheafData.basisPullback_hom, Category.assoc, Category.assoc,
      W.projModelZero.ker.pullbackComparison_comp_map_sheafι W'.projModelZero.ker hg hI,
      ← Functor.map_comp_assoc, W.formalConormalIso_hom_comp_map_sheafι,
      Scheme.Modules.pullback_map_globalSectionsSmul,
      ← Scheme.Modules.globalSectionsSmul_naturality_assoc (pullbackObjUnitIso F).inv,
      Iso.inv_hom_id, Category.comp_id]
  have hrhs : (unitSmulIso vTop W'.formalConormalIso).hom ≫ μ' =
      globalSectionsSmul (𝟙_ (Spec (.of R'⟦X⟧)).Modules)
        ((ΓSpecIso (.of R'⟦X⟧)).inv X * (vTop : Γ(Spec (.of R'⟦X⟧), ⊤))) := by
    rw [unitSmulIso_hom, Category.assoc, W'.formalConormalIso_hom_comp_map_sheafι,
      ← Scheme.Modules.globalSectionsSmul_mul]
  rw [hlhs, hrhs]; congr 1
  dsimp only [F, vTop]; rw [coe_ΓSpecUnitsMulEquiv, SpecMap_appTop_ΓSpecIso_inv]; simp [hψX]

private theorem conormalBasisPullback_weierstrassDifferential_of_formal
    {φ : R →+* R'} {ψ : R⟦X⟧ →+* R'⟦X⟧} {g : W'.projModel ⟶ W.projModel}
    (hg : IsPullback g W'.projModelOver W.projModelOver (Spec.map (CommRingCat.ofHom φ)))
    (h₀ : W'.projModelZero ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ W.projModelZero)
    (hF : W'.projModelFormalPoint ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelFormalPoint)
    (hε : (constantCoeff (R := R')).comp ψ = φ.comp (constantCoeff (R := R)))
    (v : R'⟦X⟧ˣ) (hψX : ψ X = X * (v : R'⟦X⟧)) :
    conormalBasisPullback W.projModelZero_projModelOver W'.projModelZero_projModelOver
        hg h₀ W.weierstrassDifferential =
      unitSmulIso (ΓSpecUnitsMulEquiv (.of R') (Units.map (constantCoeff (R := R')).toMonoidHom v))
        W'.weierstrassDifferential := by
  let f := Spec.map (CommRingCat.ofHom φ); let F := Spec.map (CommRingCat.ofHom ψ)
  let ε := Spec.map (CommRingCat.ofHom (constantCoeff (R := R)))
  let ε' := Spec.map (CommRingCat.ofHom (constantCoeff (R := R')))
  have hI := Scheme.Hom.ker_eq_comap_of_isPullback_section W.projModelZero_projModelOver
    W'.projModelZero_projModelOver hg h₀
  have hIC := W.isEffectiveCartier_ker_projModelZero
  have hI'C := W'.isEffectiveCartier_ker_projModelZero
  have hεSpec : f ≫ ε = ε' ≫ F := by
    simp only [f, F, ε, ε', ← Spec.map_comp, ← CommRingCat.ofHom_comp, hε]
  -- Paste `ε` (`X = 0` on `W`) with `(F, g)` along `f ≫ ε = ε' ≫ F`, factor out `ε'` on `W'`,
  -- and evaluate `F^* W.formalConormalIso` via `basisPullback_formalConormalIso`.
  have hsq' : W'.projModelZero ≫ g = (ε' ≫ F) ≫ W.projModelFormalPoint := by
    rw [Category.assoc, ← hF, W'.SpecMap_constantCoeff_projModelFormalPoint_assoc]
  have hpaste : conormalBasisPullback W.projModelZero_projModelOver W'.projModelZero_projModelOver
      hg h₀ W.weierstrassDifferential =
      W.projModelZero.ker.basisPullback W'.projModelZero.ker hsq' hI hIC hI'C
        W.formalConormalIso := by
    rw [conormalBasisPullback_eq_basisPullback W.projModelZero_projModelOver
        W'.projModelZero_projModelOver hg h₀ hIC hI'C, weierstrassDifferential_def,
      W.projModelZero.ker.basisPullback_comp W.projModelZero.ker W'.projModelZero.ker _ _ h₀ hI
        (by rw [Category.comp_id, h₀, Category.assoc, W.SpecMap_constantCoeff_projModelFormalPoint])
        (by rw [Category.comp_id, hI]) hIC hIC hI'C]
    exact W.projModelZero.ker.basisPullback_congr W'.projModelZero.ker hεSpec
      (by simp : g ≫ 𝟙 W.projModel = g) _ _ hsq' hI hIC hI'C W.formalConormalIso
  have hunpaste : W.projModelZero.ker.basisPullback W'.projModelZero.ker hsq' hI hIC hI'C
      W.formalConormalIso =
      W'.projModelZero.ker.basisPullback W'.projModelZero.ker
        (by rw [W'.SpecMap_constantCoeff_projModelFormalPoint, Category.comp_id] :
          W'.projModelZero ≫ 𝟙 W'.projModel = ε' ≫ W'.projModelFormalPoint)
        W'.projModelZero.ker.comap_id.symm hI'C hI'C
        (W.projModelZero.ker.basisPullback W'.projModelZero.ker hF hI hIC hI'C
          W.formalConormalIso) := by
    rw [W.projModelZero.ker.basisPullback_comp W'.projModelZero.ker W'.projModelZero.ker hF hI
      (by rw [W'.SpecMap_constantCoeff_projModelFormalPoint, Category.comp_id])
      W'.projModelZero.ker.comap_id.symm (by rw [Category.id_comp]; exact hsq')
      (by rw [Category.id_comp, hI]) hIC hI'C hI'C]
    exact W.projModelZero.ker.basisPullback_congr W'.projModelZero.ker rfl (Category.id_comp g).symm
      _ _ hsq' hI hIC hI'C W.formalConormalIso
  rw [hpaste, hunpaste, basisPullback_formalConormalIso hF hI v hψX,
    Scheme.IdealSheafData.basisPullback_unitSmulIso, ← weierstrassDifferential_def]
  congr 1; ext1
  rw [Units.coe_map, coe_ΓSpecUnitsMulEquiv, coe_ΓSpecUnitsMulEquiv, Units.coe_map]
  exact SpecMap_appTop_ΓSpecIso_inv (CommRingCat.ofHom (constantCoeff (R := R'))) (v : R'⟦X⟧)

end Comparison

/-- **Base change of the Weierstrass differential.** -/
@[simp]
theorem conormalBasisPullback_weierstrassDifferential_projModelBaseChange [W.IsElliptic]
    (φ : R →+* R') :
    conormalBasisPullback W.projModelZero_projModelOver (W.map φ).projModelZero_projModelOver
        (W.isPullback_projModelBaseChange φ) (W.projModelZero_projModelBaseChange φ)
        W.weierstrassDifferential = (W.map φ).weierstrassDifferential := by
  simpa using conormalBasisPullback_weierstrassDifferential_of_formal (W := W) (W' := W.map φ)
    (W.isPullback_projModelBaseChange φ) (W.projModelZero_projModelBaseChange φ)
    (W.projModelFormalPoint_projModelBaseChange φ)
    (by ext; simp [← PowerSeries.coeff_zero_eq_constantCoeff]) 1 (by simp)

/-- **Transformation of the Weierstrass differential under a change of variables.** -/
theorem conormalBasisPullbackOfIso_weierstrassDifferential_projModelVariableChangeIso
    [W.IsElliptic] (C : VariableChange R) :
    conormalBasisPullbackOfIso W.projModelZero_projModelOver (C • W).projModelZero_projModelOver
        (W.projModelVariableChangeIso C) (W.projModelVariableChangeIso_hom_projModelOver C)
        (W.projModelZero_projModelVariableChangeIso_hom C) W.weierstrassDifferential =
      unitSmulIso (ΓSpecUnitsMulEquiv (.of R) C.u⁻¹) (C • W).weierstrassDifferential := by
  obtain ⟨v₀, hv₀⟩ := PowerSeries.X_dvd_iff.mpr (C.formalCoordinate W).constantCoeff_toPowerSeries
  have hv₀_const : constantCoeff v₀ = (↑C.u⁻¹ : R) := by
    have h1 := C.coeff_one_formalCoordinate W
    rwa [hv₀, coeff_succ_X_mul, coeff_zero_eq_constantCoeff] at h1
  have hv₀_unit : IsUnit v₀ := isUnit_iff_constantCoeff.mpr (hv₀_const ▸ C.u⁻¹.isUnit)
  let v : R⟦X⟧ˣ := hv₀_unit.unit; have hv_val : (v : R⟦X⟧) = v₀ := hv₀_unit.unit_spec
  have hε : (constantCoeff (R := R)).comp (substAlgHom (C.formalCoordinate W).hasSubst).toRingHom =
      (RingHom.id R).comp (constantCoeff (R := R)) := by
    ext p; simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_substAlgHom, RingHom.id_apply]
    exact constantCoeff_subst_of_constantCoeff_zero
      (C.formalCoordinate W).constantCoeff_toPowerSeries p
  have hId : Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 (Spec (.of R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hsq : IsPullback (W.projModelVariableChangeIso C).hom (C • W).projModelOver
      W.projModelOver (Spec.map (CommRingCat.ofHom (RingHom.id R))) :=
    hId.symm ▸ .of_horiz_isIso ⟨by simp⟩
  have h₀ : (C • W).projModelZero ≫ (W.projModelVariableChangeIso C).hom =
      Spec.map (CommRingCat.ofHom (RingHom.id R)) ≫ W.projModelZero := by
    rw [hId, W.projModelZero_projModelVariableChangeIso_hom C, Category.id_comp]
  rw [conormalBasisPullbackOfIso_def, conormalBasisPullback_congr W.projModelZero_projModelOver
      (C • W).projModelZero_projModelOver hId.symm rfl _ _ hsq h₀,
    conormalBasisPullback_weierstrassDifferential_of_formal hsq h₀
      (W.projModelFormalPoint_projModelVariableChangeIso_hom C) hε v
      (by simp [substAlgHom_X, ← hv₀, hv_val])]
  congr 2; ext; simp [hv_val, hv₀_const]

section Scalar

variable {W} [W.IsElliptic]

variable (W) in
/-- The unique unit `u : Rˣ` such that `ω = u • W.weierstrassDifferential`. -/
def weierstrassDifferentialScalar
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) : Rˣ :=
  (ΓSpecUnitsMulEquiv (.of R)).symm (existsUnique_unitSmulIso_eq ω W.weierstrassDifferential).choose

/-- Rescaling `W.weierstrassDifferential` by `W.weierstrassDifferentialScalar ω` recovers `ω`. -/
@[simp]
theorem unitSmulIso_weierstrassDifferentialScalar
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    unitSmulIso (ΓSpecUnitsMulEquiv (.of R) (W.weierstrassDifferentialScalar ω))
        W.weierstrassDifferential = ω := by
  rw [weierstrassDifferentialScalar, MulEquiv.apply_symm_apply]
  exact (existsUnique_unitSmulIso_eq ω W.weierstrassDifferential).choose_spec.1

/-- `u = W.weierstrassDifferentialScalar ω` if and only if `u • W.weierstrassDifferential = ω`. -/
theorem eq_weierstrassDifferentialScalar_iff {u : Rˣ}
    {ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf} :
    u = W.weierstrassDifferentialScalar ω ↔
      unitSmulIso (ΓSpecUnitsMulEquiv (.of R) u) W.weierstrassDifferential = ω :=
  ⟨fun h ↦ h ▸ W.unitSmulIso_weierstrassDifferentialScalar ω, fun h ↦
    (ΓSpecUnitsMulEquiv (.of R)).injective ((unitSmulIso_inj _ _ W.weierstrassDifferential).mp
      (h.trans (W.unitSmulIso_weierstrassDifferentialScalar ω).symm))⟩

/-- `W.weierstrassDifferential` has scalar `1` relative to itself. -/
@[simp]
theorem weierstrassDifferentialScalar_weierstrassDifferential :
    W.weierstrassDifferentialScalar W.weierstrassDifferential = 1 :=
  (eq_weierstrassDifferentialScalar_iff.mpr (by simp)).symm

/-- Rescaling `ω` by `u : Rˣ` multiplies `weierstrassDifferentialScalar` by `u`. -/
@[simp]
theorem weierstrassDifferentialScalar_unitSmulIso (u : Rˣ)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    W.weierstrassDifferentialScalar (unitSmulIso (ΓSpecUnitsMulEquiv (.of R) u) ω) =
      u * W.weierstrassDifferentialScalar ω := by
  symm; rw [eq_weierstrassDifferentialScalar_iff, map_mul, unitSmulIso_mul,
    W.unitSmulIso_weierstrassDifferentialScalar]

/-- Pulling `ω` back along `φ : R →+* R'` maps `weierstrassDifferentialScalar` along `φ`. -/
@[simp]
theorem weierstrassDifferentialScalar_conormalBasisPullback_projModelBaseChange
    (φ : R →+* R') (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    (W.map φ).weierstrassDifferentialScalar
        (conormalBasisPullback W.projModelZero_projModelOver (W.map φ).projModelZero_projModelOver
          (W.isPullback_projModelBaseChange φ) (W.projModelZero_projModelBaseChange φ) ω) =
      Units.map φ.toMonoidHom (W.weierstrassDifferentialScalar ω) := by
  symm; rw [eq_weierstrassDifferentialScalar_iff]
  conv_rhs => rw [← W.unitSmulIso_weierstrassDifferentialScalar ω]
  rw [conormalBasisPullback_unitSmulIso,
    W.conormalBasisPullback_weierstrassDifferential_projModelBaseChange φ]
  congr 1; ext1
  rw [coe_ΓSpecUnitsMulEquiv, Units.coe_map, Units.coe_map, coe_ΓSpecUnitsMulEquiv]
  exact (SpecMap_appTop_ΓSpecIso_inv (CommRingCat.ofHom φ)
    (W.weierstrassDifferentialScalar ω : R)).symm

/-- Under `C : VariableChange R`, `weierstrassDifferentialScalar` is multiplied by `C.u⁻¹`. -/
theorem weierstrassDifferentialScalar_conormalBasisPullbackOfIso_projModelVariableChangeIso
    (C : VariableChange R) (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    (C • W).weierstrassDifferentialScalar
        (conormalBasisPullbackOfIso W.projModelZero_projModelOver
          (C • W).projModelZero_projModelOver (W.projModelVariableChangeIso C)
          (W.projModelVariableChangeIso_hom_projModelOver C)
          (W.projModelZero_projModelVariableChangeIso_hom C) ω) =
      W.weierstrassDifferentialScalar ω * C.u⁻¹ := by
  symm; rw [eq_weierstrassDifferentialScalar_iff]
  conv_rhs => rw [← W.unitSmulIso_weierstrassDifferentialScalar ω]
  rw [conormalBasisPullbackOfIso_unitSmulIso,
    W.conormalBasisPullbackOfIso_weierstrassDifferential_projModelVariableChangeIso C,
    ← unitSmulIso_mul, ← map_mul]

/-- Pulling `ω` back along `e : W'.projModel ≅ W.projModel` induced by `C : VariableChange R`
(`C • W = W'`) yields `W'.weierstrassDifferential` if and only if
`C.u = W.weierstrassDifferentialScalar ω`. -/
theorem conormalBasisPullbackOfIso_eq_weierstrassDifferential_iff
    {W' : WeierstrassCurve R} [W'.IsElliptic] (C : VariableChange R) (hC : C • W = W')
    {e : W'.projModel ≅ W.projModel} (he : e.hom ≫ W.projModelOver = W'.projModelOver)
    (he₀ : W'.projModelZero ≫ e.hom = W.projModelZero)
    (heC : e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    conormalBasisPullbackOfIso W.projModelZero_projModelOver W'.projModelZero_projModelOver
        e he he₀ ω = W'.weierstrassDifferential ↔ C.u = W.weierstrassDifferentialScalar ω := by
  subst hC
  have he' : e.hom = (W.projModelVariableChangeIso C).hom := by simpa using heC
  rw [conormalBasisPullbackOfIso_congr W.projModelZero_projModelOver
    (C • W).projModelZero_projModelOver he' he he₀
    (W.projModelVariableChangeIso_hom_projModelOver C)
    (W.projModelZero_projModelVariableChangeIso_hom C) ω]
  set ω' := conormalBasisPullbackOfIso W.projModelZero_projModelOver
    (C • W).projModelZero_projModelOver (W.projModelVariableChangeIso C)
    (W.projModelVariableChangeIso_hom_projModelOver C)
    (W.projModelZero_projModelVariableChangeIso_hom C) ω
  have hiff : ω' = (C • W).weierstrassDifferential ↔
      (C • W).weierstrassDifferentialScalar ω' = 1 :=
    ⟨fun h ↦ by rw [h, weierstrassDifferentialScalar_weierstrassDifferential],
      fun h ↦ by rw [← (C • W).unitSmulIso_weierstrassDifferentialScalar ω', h, map_one,
        Scheme.Modules.unitSmulIso_one]⟩
  rw [hiff,
    W.weierstrassDifferentialScalar_conormalBasisPullbackOfIso_projModelVariableChangeIso C ω,
    mul_inv_eq_one, eq_comm]

end Scalar

section AdaptedXCoord

section Def

variable [W.IsElliptic] {P Q : Spec (.of R) ⟶ W.projModel} (hP : P ≫ W.projModelOver = 𝟙 _)
  (hQ : Q ≫ W.projModelOver = 𝟙 _) (hP₀ : ∀ s, P s ≠ W.projModelZero s)
  (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
  (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)

/-- **The `ω`-adapted `x`-coordinate** `(u⁻¹)² · (x₂ - x₁)` of `Q` relative to `P` and `ω`. -/
def projModelAdaptedXCoord : R :=
  (↑(W.weierstrassDifferentialScalar ω)⁻¹ : R) ^ 2 *
    (W.projModelSectionX hQ hQ₀ - W.projModelSectionX hP hP₀)

/-- Explicit formula `(u⁻¹)² · (x₂ - x₁)` for `projModelAdaptedXCoord` on affine points. -/
theorem projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint {x₁ y₁ x₂ y₂ : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hP' : P = W.projModelAffinePoint h₁) (hQ' : Q = W.projModelAffinePoint h₂) :
    W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω =
      (↑(W.weierstrassDifferentialScalar ω)⁻¹ : R) ^ 2 * (x₂ - x₁) := by
  rw [projModelAdaptedXCoord, W.projModelSectionX_eq_of_eq_projModelAffinePoint hP hP₀ h₁ hP',
    W.projModelSectionX_eq_of_eq_projModelAffinePoint hQ hQ₀ h₂ hQ']

/-- On affine points `P = [x₁ : y₁ : 1]` and `Q = [x₂ : y₂ : 1]`, `projModelAdaptedXCoord = 1` iff
`x₂ - x₁ = (W.weierstrassDifferentialScalar ω)²`. -/
theorem projModelAdaptedXCoord_eq_one_iff_of_eq_projModelAffinePoint {x₁ y₁ x₂ y₂ : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hP' : P = W.projModelAffinePoint h₁) (hQ' : Q = W.projModelAffinePoint h₂) :
    W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1 ↔
      x₂ - x₁ = (W.weierstrassDifferentialScalar ω : R) ^ 2 := by
  rw [W.projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint hP hQ hP₀ hQ₀ ω h₁ h₂ hP' hQ']
  set u := W.weierstrassDifferentialScalar ω; have hu : (u : R) * (↑u⁻¹ : R) = 1 := u.mul_inv
  exact ⟨fun h ↦ by linear_combination (u : R) ^ 2 * h - (x₂ - x₁) * ((u : R) * ↑u⁻¹ + 1) * hu,
    fun h ↦ by linear_combination (↑u⁻¹ : R) ^ 2 * h + ((u : R) * ↑u⁻¹ + 1) * hu⟩

end Def

/-- `projModelAdaptedXCoord` depends only on `P`, `Q`, and `ω` (not on the section or non-meeting
proofs). -/
theorem projModelAdaptedXCoord_congr [W.IsElliptic] {P₁ P₂ Q₁ Q₂ : Spec (.of R) ⟶ W.projModel}
    (hP : P₁ = P₂) (hQ : Q₁ = Q₂)
    {ω₁ ω₂ : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf} (hω : ω₁ = ω₂)
    {hP₁ : P₁ ≫ W.projModelOver = 𝟙 _} {hQ₁ : Q₁ ≫ W.projModelOver = 𝟙 _}
    {hP₁₀ : ∀ s, P₁ s ≠ W.projModelZero s} {hQ₁₀ : ∀ s, Q₁ s ≠ W.projModelZero s}
    {hP₂ : P₂ ≫ W.projModelOver = 𝟙 _} {hQ₂ : Q₂ ≫ W.projModelOver = 𝟙 _}
    {hP₂₀ : ∀ s, P₂ s ≠ W.projModelZero s} {hQ₂₀ : ∀ s, Q₂ s ≠ W.projModelZero s} :
    W.projModelAdaptedXCoord hP₁ hQ₁ hP₁₀ hQ₁₀ ω₁ =
      W.projModelAdaptedXCoord hP₂ hQ₂ hP₂₀ hQ₂₀ ω₂ := by
  subst hP hQ hω; rfl

variable {W} {W' : WeierstrassCurve R'} [W.IsElliptic] [W'.IsElliptic]

private theorem projModelAdaptedXCoord_eq_of_iso {W₁ W₂ : WeierstrassCurve R}
    [W₁.IsElliptic] [W₂.IsElliptic] (e : W₁.projModel ≅ W₂.projModel)
    (he : e.hom ≫ W₂.projModelOver = W₁.projModelOver)
    (h0 : W₁.projModelZero ≫ e.hom = W₂.projModelZero)
    {P₁ Q₁ : Spec (.of R) ⟶ W₁.projModel} {P₂ Q₂ : Spec (.of R) ⟶ W₂.projModel}
    (hP₁ : P₁ ≫ W₁.projModelOver = 𝟙 _) (hQ₁ : Q₁ ≫ W₁.projModelOver = 𝟙 _)
    (hP₁₀ : ∀ s, P₁ s ≠ W₁.projModelZero s) (hQ₁₀ : ∀ s, Q₁ s ≠ W₁.projModelZero s)
    (hP₂ : P₂ ≫ W₂.projModelOver = 𝟙 _) (hQ₂ : Q₂ ≫ W₂.projModelOver = 𝟙 _)
    (hP₂₀ : ∀ s, P₂ s ≠ W₂.projModelZero s) (hQ₂₀ : ∀ s, Q₂ s ≠ W₂.projModelZero s)
    (hPe : P₁ ≫ e.hom = P₂) (hQe : Q₁ ≫ e.hom = Q₂)
    (ω₂ : 𝟙_ (Spec (.of R)).Modules ≅ W₂.projModelZero.conormalSheaf) :
    W₁.projModelAdaptedXCoord hP₁ hQ₁ hP₁₀ hQ₁₀
        (conormalBasisPullbackOfIso W₂.projModelZero_projModelOver W₁.projModelZero_projModelOver
          e he h0 ω₂) = W₂.projModelAdaptedXCoord hP₂ hQ₂ hP₂₀ hQ₂₀ ω₂ := by
  obtain ⟨C, ⟨rfl, heC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he h0
  have he' : e.hom = (W₂.projModelVariableChangeIso C).hom := by simpa using heC
  obtain ⟨x₁, y₁, h₁, rfl⟩ := (C • W₂).exists_eq_projModelAffinePoint hP₁ hP₁₀
  obtain ⟨x₂, y₂, h₂, rfl⟩ := (C • W₂).exists_eq_projModelAffinePoint hQ₁ hQ₁₀
  have hP₂' : P₂ = W₂.projModelAffinePoint ((Affine.variableChange_equation W₂ C x₁ y₁).mpr h₁) :=
    by rw [← hPe, he', projModelAffinePoint_projModelVariableChangeIso_hom]
  have hQ₂' : Q₂ = W₂.projModelAffinePoint ((Affine.variableChange_equation W₂ C x₂ y₂).mpr h₂) :=
    by rw [← hQe, he', projModelAffinePoint_projModelVariableChangeIso_hom]
  rw [(C • W₂).projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint hP₁ hQ₁ hP₁₀ hQ₁₀ _
      h₁ h₂ rfl rfl,
    W₂.projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint hP₂ hQ₂ hP₂₀ hQ₂₀ ω₂ _ _ hP₂' hQ₂',
    conormalBasisPullbackOfIso_congr W₂.projModelZero_projModelOver
      (C • W₂).projModelZero_projModelOver he' he h0
      (W₂.projModelVariableChangeIso_hom_projModelOver C)
      (W₂.projModelZero_projModelVariableChangeIso_hom C) ω₂,
    W₂.weierstrassDifferentialScalar_conormalBasisPullbackOfIso_projModelVariableChangeIso C ω₂]
  simp only [mul_inv_rev, inv_inv, Units.val_mul]; ring

/-- **Invariance of `projModelAdaptedXCoord` under pointed base change.** -/
theorem map_projModelAdaptedXCoord_of_isPullback {φ : R' →+* R} {F : W.projModel ⟶ W'.projModel}
    (hF : IsPullback F W.projModelOver W'.projModelOver (Spec.map (CommRingCat.ofHom φ)))
    (h0 : W.projModelZero ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ W'.projModelZero)
    {P Q : Spec (.of R) ⟶ W.projModel} {P' Q' : Spec (.of R') ⟶ W'.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
    (hP' : P' ≫ W'.projModelOver = 𝟙 _) (hQ' : Q' ≫ W'.projModelOver = 𝟙 _)
    (hP'₀ : ∀ s, P' s ≠ W'.projModelZero s) (hQ'₀ : ∀ s, Q' s ≠ W'.projModelZero s)
    (hPF : P ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ P')
    (hQF : Q ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ Q')
    (ω' : 𝟙_ (Spec (.of R')).Modules ≅ W'.projModelZero.conormalSheaf) :
    φ (W'.projModelAdaptedXCoord hP' hQ' hP'₀ hQ'₀ ω') =
      W.projModelAdaptedXCoord hP hQ hP₀ hQ₀
        (conormalBasisPullback W'.projModelZero_projModelOver W.projModelZero_projModelOver
          hF h0 ω') := by
  have hB := W'.isPullback_projModelBaseChange φ; let e := hF.isoIsPullback _ _ hB
  have he : e.hom ≫ (W'.map φ).projModelOver = W.projModelOver := hF.isoIsPullback_hom_snd _ _ hB
  have hF' : e.hom ≫ W'.projModelBaseChange φ = F := hF.isoIsPullback_hom_fst _ _ hB
  have h0' : W.projModelZero ≫ e.hom = (W'.map φ).projModelZero :=
    hB.hom_ext (by simp [hF', h0, projModelZero_projModelBaseChange]) (by simp [he])
  obtain ⟨x₁', y₁', h₁', rfl⟩ := W'.exists_eq_projModelAffinePoint hP' hP'₀
  obtain ⟨x₂', y₂', h₂', rfl⟩ := W'.exists_eq_projModelAffinePoint hQ' hQ'₀
  have hPe : P ≫ e.hom = (W'.map φ).projModelAffinePoint (h₁'.map φ) := hB.hom_ext
    (by rw [Category.assoc, hF', hPF, projModelAffinePoint_projModelBaseChange]) (by simp [he, hP])
  have hQe : Q ≫ e.hom = (W'.map φ).projModelAffinePoint (h₂'.map φ) := hB.hom_ext
    (by rw [Category.assoc, hF', hQF, projModelAffinePoint_projModelBaseChange]) (by simp [he, hQ])
  have hP_φ₀ := (W'.map φ).projModelAffinePoint_apply_ne_projModelZero (h₁'.map φ)
  have hQ_φ₀ := (W'.map φ).projModelAffinePoint_apply_ne_projModelZero (h₂'.map φ)
  have hbase : φ (W'.projModelAdaptedXCoord hP' hQ' hP'₀ hQ'₀ ω') =
      (W'.map φ).projModelAdaptedXCoord (projModelAffinePoint_projModelOver _)
        (projModelAffinePoint_projModelOver _) hP_φ₀ hQ_φ₀
        (conormalBasisPullback W'.projModelZero_projModelOver (W'.map φ).projModelZero_projModelOver
          hB (W'.projModelZero_projModelBaseChange φ) ω') := by
    rw [W'.projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint hP' hQ' hP'₀ hQ'₀ ω'
        h₁' h₂' rfl rfl,
      (W'.map φ).projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint _ _ hP_φ₀ hQ_φ₀ _
        (h₁'.map φ) (h₂'.map φ) rfl rfl,
      W'.weierstrassDifferentialScalar_conormalBasisPullback_projModelBaseChange φ ω']
    simp [Units.coe_map_inv]
  rw [hbase, ← projModelAdaptedXCoord_eq_of_iso e he h0' hP hQ hP₀ hQ₀
      (projModelAffinePoint_projModelOver _) (projModelAffinePoint_projModelOver _) hP_φ₀ hQ_φ₀
      hPe hQe _, conormalBasisPullbackOfIso_def, conormalBasisPullback_comp]
  exact congrArg (W.projModelAdaptedXCoord hP hQ hP₀ hQ₀)
    (conormalBasisPullback_congr W'.projModelZero_projModelOver W.projModelZero_projModelOver
      (Category.id_comp _) hF' _ _ hF h0 ω')

end AdaptedXCoord

end

end WeierstrassCurve
