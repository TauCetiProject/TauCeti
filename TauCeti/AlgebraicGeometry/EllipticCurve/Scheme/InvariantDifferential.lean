/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Conormal
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.FormalPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange.Basic
import TauCeti.Algebra.Regular.SMul

/-!
# The Weierstrass invariant differential on the conormal sheaf of the zero section

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, with projective model
`W.projModel` over `Spec R` and zero section `W.projModelZero : Spec R ⟶ W.projModel`. In the
coordinate `z = -X / Y` at infinity, the formal point
`W.projModelFormalPoint : Spec R⟦X⟧ ⟶ W.projModel` pulls the zero-section divisor back to the
principal effective Cartier divisor `(X)` (`zeroSectionDivisor_comap_projModelFormalPoint`).
Multiplication by `X` therefore defines a global basis of that pulled-back ideal sheaf over
`Spec R⟦X⟧`; restricting along `X = 0` (`Spec` of `PowerSeries.constantCoeff : R⟦X⟧ →+* R`) yields
the canonical **Weierstrass differential**
`W.weierstrassDifferential : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf`,
corresponding in local coordinates to `dz = dx / (2y + a₁x + a₃)` (Katz–Mazur, 2.2.4; Silverman,
III.1 and IV.1).

Because the comparison is carried out directly on the formal-point divisor `(X)` over `Spec R⟦X⟧`,
both functoriality laws hold over arbitrary (possibly nonreduced, arbitrary-characteristic)
coefficient rings without case distinctions:
* **Base change** (`conormalBasisPullback_weierstrassDifferential_projModelBaseChange`): along any
  ring homomorphism `φ : R →+* R'`, `W.weierstrassDifferential` pulls back to
  `(W.map φ).weierstrassDifferential`.
* **Change of variables**
  (`conormalBasisPullback_weierstrassDifferential_projModelVariableChangeIso_hom`): along the
  isomorphism `(C • W).projModel ≅ W.projModel` induced by `C : VariableChange R`
  (`(x, y) ↦ (u²x + r, u³y + su²x + t)`), the formal parameter transforms by a series with linear
  coefficient `u⁻¹` (`VariableChange.coeff_one_formalCoordinate`), so `W.weierstrassDifferential`
  pulls back to `u⁻¹ • (C • W).weierstrassDifferential`.

## Main declarations

* `WeierstrassCurve.projModelFormalPoint_projModelBaseChange`: the formal point commutes with
  change of coefficient ring;
* `WeierstrassCurve.projModelFormalPoint_projModelVariableChangeIso_hom`: a Weierstrass change of
  variables reparametrises the formal point by `C.formalCoordinate W`;
* `WeierstrassCurve.weierstrassDifferential`: the canonical basis
  `𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf` of an elliptic Weierstrass curve;
* `WeierstrassCurve.conormalBasisPullback_weierstrassDifferential_projModelBaseChange` and
  `WeierstrassCurve.conormalBasisPullback_weierstrassDifferential_projModelVariableChangeIso_hom`:
  its behaviour under base change and Weierstrass changes of variables;
* `WeierstrassCurve.weierstrassDifferentialScalar`: the unique unit `u : Rˣ` scaling
  `W.weierstrassDifferential` to a given conormal basis `ω`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.1.6 and 2.2.4.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and IV.1.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry PowerSeries

universe u

namespace WeierstrassCurve

noncomputable section

variable {R R' : Type u} [CommRing R] [CommRing R'] (W : WeierstrassCurve R)

/-! ### Functoriality of the formal point -/

/-- Extending scalars along `φ : R →+* R'` carries the formal point `[X : -1 : w(X)]` of `W.map φ`
to the formal point of `W` along `PowerSeries.map φ`. -/
@[reassoc (attr := simp)]
theorem projModelFormalPoint_projModelBaseChange (φ : R →+* R') :
    (W.map φ).projModelFormalPoint ≫ W.projModelBaseChange φ =
      Spec.map (CommRingCat.ofHom (PowerSeries.map φ)) ≫ W.projModelFormalPoint := by
  rw [projModelFormalPoint_def, projModelFormalPoint_def, projModelPoint_projModelBaseChange,
    SpecMap_projModelPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨by ext; simp, 1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp [map_formalW]

open Matrix in
/-- The isomorphism `(C • W).projModel ≅ W.projModel` induced by a Weierstrass change of variables
`C` reparametrises the formal point by `C.formalCoordinate W`. -/
@[reassoc]
theorem projModelFormalPoint_projModelVariableChangeIso_hom (C : VariableChange R) :
    (C • W).projModelFormalPoint ≫ (W.projModelVariableChangeIso C).hom =
      Spec.map (CommRingCat.ofHom (substAlgHom (C.formalCoordinate W).hasSubst).toRingHom) ≫
        W.projModelFormalPoint := by
  let D := C.formalDenom W
  let d := invOfUnit D (C.u ^ 3)
  have hDd : D * d = 1 := mul_invOfUnit D (C.u ^ 3) (C.constantCoeff_formalDenom W)
  let uD : R⟦X⟧ˣ := Units.mkOfMulEqOne D d hDd
  have hj : IsUnit (((C.map (algebraMap R R⟦X⟧)).toMatrix *ᵥ ![X, -1, formalW (C • W)]) 1) := by
    have h1 : ((C.map (algebraMap R R⟦X⟧)).toMatrix *ᵥ ![X, -1, formalW (C • W)]) 1 = -D := by
      simp [VariableChange.toMatrix_def, D, VariableChange.formalDenom_def]
      ring
    rw [h1]
    exact (C.isUnit_formalDenom W).neg
  rw [projModelFormalPoint_def, projModelPoint_projModelVariableChangeIso_hom _ hj,
    SpecMap_substAlgHom_projModelFormalPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨rfl, uD, funext fun k ↦ ?_⟩
  have huD : (uD : R⟦X⟧) = D := rfl
  rw [C.subst_formalCoordinate_formalW W, C.formalCoordinate_toPowerSeries W]
  fin_cases k <;>
    simp [VariableChange.toMatrix_def, Units.smul_def, smul_eq_mul, huD, algebraMap_eq]
  · linear_combination -((PowerSeries.C (C.u : R) ^ 2 * X +
      PowerSeries.C C.r * formalW (C • W)) * hDd)
  · simp only [D, VariableChange.formalDenom_def, map_mul, map_pow]
    ring
  · linear_combination -(formalW (C • W) * hDd)

/-! ### The Weierstrass differential via the formal parameter -/

private def formalParamTop (R : Type u) [CommRing R] : Γ(Spec (.of R⟦X⟧), ⊤) :=
  (Scheme.ΓSpecIso (.of R⟦X⟧)).inv X

private lemma isSMulRegular_formalParamTop (U : (Spec (.of R⟦X⟧)).affineOpens) :
    IsSMulRegular Γ(Spec (.of R⟦X⟧), U)
      ((Spec (.of R⟦X⟧)).presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (formalParamTop R)) := by
  have hx : IsSMulRegular Γ(Spec (.of R⟦X⟧), ⊤) (formalParamTop R) :=
    (TauCeti.isSMulRegular_map_iff (Scheme.ΓSpecIso (.of R⟦X⟧)).symm.commRingCatIsoToRingEquiv
      X).mpr PowerSeries.X_mul_injective
  exact (isAffineOpen_top (Spec (.of R⟦X⟧))).isSMulRegular_map le_top hx

private lemma ideal_ker_comap_projModelFormalPoint (U : (Spec (.of R⟦X⟧)).affineOpens) :
    (W.projModelZero.ker.comap W.projModelFormalPoint).ideal U =
      Ideal.span (Set.singleton ((Spec (.of R⟦X⟧)).presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        (formalParamTop R))) := by
  rw [← W.zeroSectionDivisor_def, W.zeroSectionDivisor_comap_projModelFormalPoint, Ideal.map_span,
    Set.image_singleton, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
    Set.image_singleton]
  rfl

private theorem isEffectiveCartier_ker_comap_projModelFormalPoint :
    (W.projModelZero.ker.comap W.projModelFormalPoint).IsEffectiveCartier := by
  rw [← W.zeroSectionDivisor_def, W.zeroSectionDivisor_comap_projModelFormalPoint, Ideal.map_span,
    Set.image_singleton]
  exact Scheme.IdealSheafData.isEffectiveCartier_ofIdealTop_span_singleton _
    isSMulRegular_formalParamTop

private theorem isEffectiveCartier_ker_projModelZero [W.IsElliptic] :
    W.projModelZero.ker.IsEffectiveCartier := by
  rw [← W.zeroSectionDivisor_def]
  exact W.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier

/-- Global basis of `(W.projModelZero.ker.comap W.projModelFormalPoint).sheaf` on `Spec R⟦X⟧`
given by multiplication by the formal parameter `X`. -/
private def formalZeroIso :
    𝟙_ (Spec (.of R⟦X⟧)).Modules ≅
      (W.projModelZero.ker.comap W.projModelFormalPoint).sheaf :=
  (W.projModelZero.ker.comap W.projModelFormalPoint).unitIsoOfForallIdealEqSpan
    isSMulRegular_formalParamTop W.ideal_ker_comap_projModelFormalPoint

private lemma formalZeroIso_hom_sheafι :
    W.formalZeroIso.hom ≫ (W.projModelZero.ker.comap W.projModelFormalPoint).sheafι =
      Scheme.Modules.globalSectionsSmul (𝟙_ (Spec (.of R⟦X⟧)).Modules) (formalParamTop R) := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext r
  simp only [Scheme.Modules.globalSectionsSmul_app, Scheme.Modules.smul_apply, formalZeroIso]
  exact (W.projModelZero.ker.comap
    W.projModelFormalPoint).sheafι_app_unitIsoOfForallIdealEqSpan_hom
    isSMulRegular_formalParamTop W.ideal_ker_comap_projModelFormalPoint U r

/-- Global basis of `(W.projModelFormalPoint)^* W.projModelZero.ker.sheaf` on `Spec R⟦X⟧`
induced by `formalZeroIso` and `isIso_pullbackSheafHom`. -/
private def formalConormalIso [W.IsElliptic] :
    𝟙_ (Spec (.of R⟦X⟧)).Modules ≅
      (Scheme.Modules.pullback W.projModelFormalPoint).obj W.projModelZero.ker.sheaf :=
  have := W.projModelZero.ker.isIso_pullbackSheafHom W.projModelFormalPoint
    W.isEffectiveCartier_ker_projModelZero W.isEffectiveCartier_ker_comap_projModelFormalPoint
  W.formalZeroIso ≪≫ (asIso (W.projModelZero.ker.pullbackSheafHom W.projModelFormalPoint)).symm

private lemma formalConormalIso_hom_comp_map_sheafι [W.IsElliptic] :
    W.formalConormalIso.hom ≫
        ((Scheme.Modules.pullback W.projModelFormalPoint).map W.projModelZero.ker.sheafι ≫
          (Scheme.Modules.pullbackObjUnitIso W.projModelFormalPoint).hom) =
      Scheme.Modules.globalSectionsSmul (𝟙_ (Spec (.of R⟦X⟧)).Modules) (formalParamTop R) := by
  have := W.projModelZero.ker.isIso_pullbackSheafHom W.projModelFormalPoint
    W.isEffectiveCartier_ker_projModelZero W.isEffectiveCartier_ker_comap_projModelFormalPoint
  rw [← W.projModelZero.ker.pullbackSheafHom_sheafι W.projModelFormalPoint]
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (IsIso.inv_hom_id_assoc
      (W.projModelZero.ker.pullbackSheafHom W.projModelFormalPoint)
      (W.projModelZero.ker.comap W.projModelFormalPoint).sheafι)).trans
    W.formalZeroIso_hom_sheafι

/-- **The Weierstrass invariant differential** of an elliptic Weierstrass curve `W` over `R`: the
canonical basis `𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf` obtained by restricting
the formal-parameter generator `X` of `W.projModelZero.ker` along `X = 0`. -/
def weierstrassDifferential [W.IsElliptic] :
    𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf :=
  W.projModelZero.ker.basisPullback W.projModelZero.ker
    (p := W.projModelFormalPoint) (p' := W.projModelZero)
    (f := Spec.map (CommRingCat.ofHom (constantCoeff (R := R)))) (g := 𝟙 W.projModel)
    (by rw [W.SpecMap_constantCoeff_projModelFormalPoint, Category.comp_id])
    W.projModelZero.ker.comap_id.symm
    W.isEffectiveCartier_ker_projModelZero
    W.isEffectiveCartier_ker_projModelZero
    W.formalConormalIso

/-! ### Unified formal-point comparison for base change and variable change -/

section Comparison

variable {W} {W' : WeierstrassCurve R'} [W.IsElliptic] [W'.IsElliptic]

private lemma SpecMap_appTop_ΓSpecIso_inv {A B : Type u} [CommRing A] [CommRing B]
    (ψ : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom ψ)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (ψ a) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  exact (ConcreteCategory.comp_apply _ _ a).symm.trans (by rw [← h])

private lemma basisPullback_formalConormalIso {ψ : R⟦X⟧ →+* R'⟦X⟧} {g : W'.projModel ⟶ W.projModel}
    (hg : W'.projModelFormalPoint ≫ g =
      Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelFormalPoint)
    (hI : W'.projModelZero.ker = W.projModelZero.ker.comap g)
    (v : R'⟦X⟧ˣ) (hψX : ψ X = X * (v : R'⟦X⟧)) :
    W.projModelZero.ker.basisPullback W'.projModelZero.ker hg hI
        W.isEffectiveCartier_ker_projModelZero
        W'.isEffectiveCartier_ker_projModelZero
        W.formalConormalIso =
      Scheme.Modules.unitSmulIso
        (Units.map (Scheme.ΓSpecIso (.of R'⟦X⟧)).inv.hom.toMonoidHom v)
        W'.formalConormalIso := by
  let F := Spec.map (CommRingCat.ofHom ψ)
  let vTop : Γ(Spec (.of R'⟦X⟧), ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (.of R'⟦X⟧)).inv.hom.toMonoidHom v
  let μ' := (Scheme.Modules.pullback W'.projModelFormalPoint).map W'.projModelZero.ker.sheafι ≫
    (Scheme.Modules.pullbackObjUnitIso W'.projModelFormalPoint).hom
  have hIso : IsIso (W'.projModelZero.ker.pullbackSheafHom W'.projModelFormalPoint) :=
    W'.projModelZero.ker.isIso_pullbackSheafHom W'.projModelFormalPoint
      W'.isEffectiveCartier_ker_projModelZero W'.isEffectiveCartier_ker_comap_projModelFormalPoint
  have hMono : Mono μ' := by
    dsimp only [μ']
    rw [← W'.projModelZero.ker.pullbackSheafHom_sheafι W'.projModelFormalPoint]
    exact mono_comp _ _
  ext1
  refine (cancel_mono μ').mp ?_
  have hlhs : (W.projModelZero.ker.basisPullback W'.projModelZero.ker hg hI
      W.isEffectiveCartier_ker_projModelZero
      W'.isEffectiveCartier_ker_projModelZero
      W.formalConormalIso).hom ≫ μ' =
      Scheme.Modules.globalSectionsSmul (𝟙_ (Spec (.of R'⟦X⟧)).Modules)
        (F.appTop (formalParamTop R)) := by
    rw [Scheme.IdealSheafData.basisPullback_hom, Category.assoc, Category.assoc,
      W.projModelZero.ker.pullbackComparison_comp_map_sheafι W'.projModelZero.ker hg hI,
      ← Functor.map_comp_assoc, W.formalConormalIso_hom_comp_map_sheafι,
      Scheme.Modules.pullback_map_globalSectionsSmul,
      ← Scheme.Modules.globalSectionsSmul_naturality_assoc
        (Scheme.Modules.pullbackObjUnitIso F).inv,
      Iso.inv_hom_id, Category.comp_id]
  have hrhs : (Scheme.Modules.unitSmulIso vTop W'.formalConormalIso).hom ≫ μ' =
      Scheme.Modules.globalSectionsSmul (𝟙_ (Spec (.of R'⟦X⟧)).Modules)
        (formalParamTop R' * (vTop : Γ(Spec (.of R'⟦X⟧), ⊤))) := by
    rw [Scheme.Modules.unitSmulIso_hom, Category.assoc, W'.formalConormalIso_hom_comp_map_sheafι,
      ← Scheme.Modules.globalSectionsSmul_mul]
  have hval : F.appTop (formalParamTop R) =
      formalParamTop R' * (vTop : Γ(Spec (.of R'⟦X⟧), ⊤)) := by
    have hvTop : (vTop : Γ(Spec (.of R'⟦X⟧), ⊤)) = (Scheme.ΓSpecIso (.of R'⟦X⟧)).inv v := rfl
    dsimp only [F, formalParamTop]
    rw [hvTop, SpecMap_appTop_ΓSpecIso_inv, hψX, map_mul]
  rw [hlhs, hrhs, hval]

private lemma conormalBasisPullback_weierstrassDifferential_eq_basisPullback
    {f : Spec (.of R') ⟶ Spec (.of R)} {g : W'.projModel ⟶ W.projModel}
    (hg : IsPullback g W'.projModelOver W.projModelOver f)
    (h₀ : W'.projModelZero ≫ g = f ≫ W.projModelZero)
    (hI : W'.projModelZero.ker = W.projModelZero.ker.comap g) :
    Scheme.Hom.conormalBasisPullback W.projModelZero_projModelOver W'.projModelZero_projModelOver
        hg h₀ W.weierstrassDifferential =
      W.projModelZero.ker.basisPullback W'.projModelZero.ker
        (p := W.projModelFormalPoint) (p' := W'.projModelZero)
        (f := f ≫ Spec.map (CommRingCat.ofHom (constantCoeff (R := R))))
        (g := g ≫ 𝟙 W.projModel)
        (by rw [Category.comp_id, h₀, Category.assoc, W.SpecMap_constantCoeff_projModelFormalPoint])
        (by rw [Category.comp_id, hI])
        W.isEffectiveCartier_ker_projModelZero W'.isEffectiveCartier_ker_projModelZero
        W.formalConormalIso := by
  rw [Scheme.Hom.conormalBasisPullback_eq_basisPullback W.projModelZero_projModelOver
    W'.projModelZero_projModelOver hg h₀
    W.isEffectiveCartier_ker_projModelZero W'.isEffectiveCartier_ker_projModelZero]
  exact W.projModelZero.ker.basisPullback_comp W.projModelZero.ker W'.projModelZero.ker
    (by rw [W.SpecMap_constantCoeff_projModelFormalPoint, Category.comp_id])
    W.projModelZero.ker.comap_id.symm h₀ hI
    (by rw [Category.comp_id, h₀, Category.assoc, W.SpecMap_constantCoeff_projModelFormalPoint])
    (by rw [Category.comp_id, hI])
    W.isEffectiveCartier_ker_projModelZero W.isEffectiveCartier_ker_projModelZero
    W'.isEffectiveCartier_ker_projModelZero W.formalConormalIso

private theorem conormalBasisPullback_weierstrassDifferential_of_formal
    {φ : R →+* R'} {ψ : R⟦X⟧ →+* R'⟦X⟧} {g : W'.projModel ⟶ W.projModel}
    (hg : IsPullback g W'.projModelOver W.projModelOver (Spec.map (CommRingCat.ofHom φ)))
    (h₀ : W'.projModelZero ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ W.projModelZero)
    (hF : W'.projModelFormalPoint ≫ g =
      Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelFormalPoint)
    (hε : (constantCoeff (R := R')).comp ψ = φ.comp (constantCoeff (R := R)))
    (v : R'⟦X⟧ˣ) (hψX : ψ X = X * (v : R'⟦X⟧)) :
    Scheme.Hom.conormalBasisPullback W.projModelZero_projModelOver W'.projModelZero_projModelOver
        hg h₀ W.weierstrassDifferential =
      Scheme.Modules.unitSmulIso
        (Units.map (Scheme.ΓSpecIso (.of R')).inv.hom.toMonoidHom
          (Units.map (constantCoeff (R := R')).toMonoidHom v))
        W'.weierstrassDifferential := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let F := Spec.map (CommRingCat.ofHom ψ)
  let ε := Spec.map (CommRingCat.ofHom (constantCoeff (R := R)))
  let ε' := Spec.map (CommRingCat.ofHom (constantCoeff (R := R')))
  have hI : W'.projModelZero.ker = W.projModelZero.ker.comap g :=
    Scheme.Hom.ker_eq_comap_of_isPullback_section W.projModelZero_projModelOver
      W'.projModelZero_projModelOver hg h₀
  have hIC := W.isEffectiveCartier_ker_projModelZero
  have hI'C := W'.isEffectiveCartier_ker_projModelZero
  have hεSpec : f ≫ ε = ε' ≫ F := by
    simp only [f, F, ε, ε', ← Spec.map_comp, ← CommRingCat.ofHom_comp, hε]
  have hpath2 : W.projModelZero.ker.basisPullback W'.projModelZero.ker
        (p := W.projModelFormalPoint) (p' := W'.projModelZero)
        (f := ε' ≫ F) (g := 𝟙 W'.projModel ≫ g)
        (by rw [Category.id_comp, Category.assoc, ← hF,
          W'.SpecMap_constantCoeff_projModelFormalPoint_assoc])
        (by rw [Category.id_comp, hI]) hIC hI'C W.formalConormalIso =
      W'.projModelZero.ker.basisPullback W'.projModelZero.ker
        (p := W'.projModelFormalPoint) (p' := W'.projModelZero)
        (f := ε') (g := 𝟙 W'.projModel)
        (by rw [W'.SpecMap_constantCoeff_projModelFormalPoint, Category.comp_id])
        W'.projModelZero.ker.comap_id.symm hI'C hI'C
        (W.projModelZero.ker.basisPullback W'.projModelZero.ker hF hI hIC hI'C
          W.formalConormalIso) :=
    (W.projModelZero.ker.basisPullback_comp W'.projModelZero.ker W'.projModelZero.ker
      hF hI (by rw [W'.SpecMap_constantCoeff_projModelFormalPoint, Category.comp_id])
      W'.projModelZero.ker.comap_id.symm
      (by rw [Category.id_comp, Category.assoc, ← hF,
        W'.SpecMap_constantCoeff_projModelFormalPoint_assoc])
      (by rw [Category.id_comp, hI]) hIC hI'C hI'C W.formalConormalIso).symm
  have hcongr := W.projModelZero.ker.basisPullback_congr W'.projModelZero.ker
    hεSpec (by simp : g ≫ 𝟙 W.projModel = 𝟙 W'.projModel ≫ g)
    (by rw [Category.comp_id, h₀, Category.assoc, W.SpecMap_constantCoeff_projModelFormalPoint])
    (by rw [Category.comp_id, hI])
    (by rw [Category.id_comp, Category.assoc, ← hF,
      W'.SpecMap_constantCoeff_projModelFormalPoint_assoc])
    (by rw [Category.id_comp, hI]) hIC hI'C W.formalConormalIso
  rw [conormalBasisPullback_weierstrassDifferential_eq_basisPullback hg h₀ hI, hcongr, hpath2,
    basisPullback_formalConormalIso hF hI v hψX,
    Scheme.IdealSheafData.basisPullback_unitSmulIso]
  congr 1
  ext1
  exact SpecMap_appTop_ΓSpecIso_inv (constantCoeff (R := R')) (v : R'⟦X⟧)

end Comparison

/-- **Base change of the Weierstrass differential.** Along `φ : R →+* R'`, the Weierstrass
differential of `W` pulls back to that of `W.map φ`. -/
@[simp]
theorem conormalBasisPullback_weierstrassDifferential_projModelBaseChange [W.IsElliptic]
    (φ : R →+* R') :
    have : (W.map φ).IsElliptic := inferInstance
    Scheme.Hom.conormalBasisPullback W.projModelZero_projModelOver
        (W.map φ).projModelZero_projModelOver
        (W.isPullback_projModelBaseChange φ)
        (W.projModelZero_projModelBaseChange φ)
        W.weierstrassDifferential =
      (W.map φ).weierstrassDifferential := by
  let _ : (W.map φ).IsElliptic := inferInstance
  have h := conormalBasisPullback_weierstrassDifferential_of_formal
    (W := W) (W' := W.map φ) (φ := φ) (ψ := PowerSeries.map φ)
    (W.isPullback_projModelBaseChange φ) (W.projModelZero_projModelBaseChange φ)
    (W.projModelFormalPoint_projModelBaseChange φ)
    (by ext; simp [← PowerSeries.coeff_zero_eq_constantCoeff]) 1 (by simp)
  simpa using h

/-- **Transformation of the Weierstrass differential under a change of variables.** Along the
isomorphism `(C • W).projModel ≅ W.projModel` induced by `C : VariableChange R`, the Weierstrass
differential `W.weierstrassDifferential` pulls back to `C.u⁻¹ • (C • W).weierstrassDifferential`
(Silverman, III.1; Katz–Mazur, 2.2.4). -/
theorem conormalBasisPullback_weierstrassDifferential_projModelVariableChangeIso_hom [W.IsElliptic]
    (C : VariableChange R) :
    Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R)))
        (g := (W.projModelVariableChangeIso C).hom)
        W.projModelZero_projModelOver (C • W).projModelZero_projModelOver
        (IsPullback.of_horiz_isIso ⟨by simp⟩)
        (by rw [W.projModelZero_projModelVariableChangeIso_hom C, Category.id_comp])
        W.weierstrassDifferential =
      Scheme.Modules.unitSmulIso
        (Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom C.u⁻¹)
        (C • W).weierstrassDifferential := by
  obtain ⟨v₀, hv₀⟩ := PowerSeries.X_dvd_iff.mpr (C.formalCoordinate W).constantCoeff_toPowerSeries
  have hv₀_const : constantCoeff v₀ = (↑C.u⁻¹ : R) := by
    have h1 := C.coeff_one_formalCoordinate W
    rwa [hv₀, coeff_succ_X_mul, coeff_zero_eq_constantCoeff] at h1
  have hv₀_unit : IsUnit v₀ :=
    isUnit_iff_constantCoeff.mpr (hv₀_const ▸ C.u⁻¹.isUnit)
  let v : R⟦X⟧ˣ := hv₀_unit.unit
  have hv_val : (v : R⟦X⟧) = v₀ := hv₀_unit.unit_spec
  have hε : (constantCoeff (R := R)).comp (substAlgHom (C.formalCoordinate W).hasSubst).toRingHom =
      (RingHom.id R).comp (constantCoeff (R := R)) := by
    ext p
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_substAlgHom, RingHom.id_apply]
    exact constantCoeff_subst_of_constantCoeff_zero
      (C.formalCoordinate W).constantCoeff_toPowerSeries p
  have hId : Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 (Spec (.of R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hsq : IsPullback (W.projModelVariableChangeIso C).hom (C • W).projModelOver
      W.projModelOver (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [hId]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have h₀ : (C • W).projModelZero ≫ (W.projModelVariableChangeIso C).hom =
      Spec.map (CommRingCat.ofHom (RingHom.id R)) ≫ W.projModelZero := by
    rw [hId, W.projModelZero_projModelVariableChangeIso_hom C, Category.id_comp]
  have key := conormalBasisPullback_weierstrassDifferential_of_formal
    (W := W) (W' := C • W) (φ := RingHom.id R)
    (ψ := (substAlgHom (C.formalCoordinate W).hasSubst).toRingHom)
    hsq h₀ (W.projModelFormalPoint_projModelVariableChangeIso_hom C) hε v
    (by simp [substAlgHom_X, ← hv₀, hv_val])
  have hcongr := Scheme.Hom.conormalBasisPullback_congr
    (f₁ := 𝟙 (Spec (.of R))) (g₁ := (W.projModelVariableChangeIso C).hom)
    W.projModelZero_projModelOver (C • W).projModelZero_projModelOver hId.symm rfl
    (IsPullback.of_horiz_isIso ⟨by simp⟩)
    (by rw [W.projModelZero_projModelVariableChangeIso_hom C, Category.id_comp])
    hsq h₀ W.weierstrassDifferential
  rw [hcongr, key]
  congr 2
  ext
  simp [hv_val, hv₀_const]

/-! ### Scalar comparison with the Weierstrass differential -/

section Scalar

variable {W} [W.IsElliptic]

private def specUnitsMulEquiv (A : Type u) [CommRing A] : Aˣ ≃* Γ(Spec (.of A), ⊤)ˣ :=
  Units.mapEquiv (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv

private lemma specUnitsMulEquiv_apply (A : Type u) [CommRing A] (u : Aˣ) :
    specUnitsMulEquiv A u = Units.map ↑(Scheme.ΓSpecIso (.of A)).inv.hom u :=
  rfl

variable (W) in
/-- The unique unit `u : Rˣ` such that a conormal basis
`ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf` equals
`u • W.weierstrassDifferential`. -/
def weierstrassDifferentialScalar
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) : Rˣ :=
  (specUnitsMulEquiv R).symm
    (Scheme.Modules.existsUnique_unitSmulIso_eq ω W.weierstrassDifferential).choose

/-- Rescaling `W.weierstrassDifferential` by `W.weierstrassDifferentialScalar ω` recovers `ω`. -/
@[simp]
theorem unitSmulIso_weierstrassDifferentialScalar
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    Scheme.Modules.unitSmulIso
        (Units.map ↑(Scheme.ΓSpecIso (.of R)).inv.hom
          (W.weierstrassDifferentialScalar ω))
        W.weierstrassDifferential = ω := by
  rw [← specUnitsMulEquiv_apply, weierstrassDifferentialScalar, MulEquiv.apply_symm_apply]
  exact (Scheme.Modules.existsUnique_unitSmulIso_eq ω W.weierstrassDifferential).choose_spec.1

/-- A unit `u : Rˣ` equals `W.weierstrassDifferentialScalar ω` if and only if
`u • W.weierstrassDifferential = ω`. -/
theorem eq_weierstrassDifferentialScalar_iff {u : Rˣ}
    {ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf} :
    u = W.weierstrassDifferentialScalar ω ↔
      Scheme.Modules.unitSmulIso (Units.map ↑(Scheme.ΓSpecIso (.of R)).inv.hom u)
        W.weierstrassDifferential = ω := by
  refine ⟨fun h ↦ h ▸ W.unitSmulIso_weierstrassDifferentialScalar ω, fun h ↦ ?_⟩
  exact (specUnitsMulEquiv R).injective
    ((Scheme.Modules.unitSmulIso_inj _ _ W.weierstrassDifferential).mp
      (h.trans (W.unitSmulIso_weierstrassDifferentialScalar ω).symm))

/-- The canonical Weierstrass differential has scalar `1` relative to itself. -/
@[simp]
theorem weierstrassDifferentialScalar_weierstrassDifferential :
    W.weierstrassDifferentialScalar W.weierstrassDifferential = 1 :=
  (eq_weierstrassDifferentialScalar_iff.mpr (by simp)).symm

/-- Rescaling a conormal basis `ω` by a unit `u : Rˣ` multiplies its Weierstrass differential scalar
by `u`. -/
@[simp]
theorem weierstrassDifferentialScalar_unitSmulIso (u : Rˣ)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    W.weierstrassDifferentialScalar
        (Scheme.Modules.unitSmulIso
          (Units.map ↑(Scheme.ΓSpecIso (.of R)).inv.hom u) ω) =
      u * W.weierstrassDifferentialScalar ω := by
  symm
  rw [eq_weierstrassDifferentialScalar_iff, map_mul, Scheme.Modules.unitSmulIso_mul,
    W.unitSmulIso_weierstrassDifferentialScalar]

/-- Pulling back a conormal basis `ω` along the base change induced by `φ : R →+* R'` maps its
Weierstrass differential scalar along `φ`. -/
@[simp]
theorem weierstrassDifferentialScalar_conormalBasisPullback_projModelBaseChange
    (φ : R →+* R') (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    (W.map φ).weierstrassDifferentialScalar
        (Scheme.Hom.conormalBasisPullback W.projModelZero_projModelOver
          (W.map φ).projModelZero_projModelOver (W.isPullback_projModelBaseChange φ)
          (W.projModelZero_projModelBaseChange φ) ω) =
      Units.map φ.toMonoidHom (W.weierstrassDifferentialScalar ω) := by
  symm
  rw [eq_weierstrassDifferentialScalar_iff]
  conv_rhs => rw [← W.unitSmulIso_weierstrassDifferentialScalar ω]
  rw [Scheme.Hom.conormalBasisPullback_unitSmulIso,
    W.conormalBasisPullback_weierstrassDifferential_projModelBaseChange φ]
  congr 1
  ext1
  exact (SpecMap_appTop_ΓSpecIso_inv φ (W.weierstrassDifferentialScalar ω : R)).symm

/-- Under a Weierstrass change of variables `C : VariableChange R`, the Weierstrass differential
scalar of the pulled-back conormal basis is multiplied by `C.u⁻¹`. -/
theorem weierstrassDifferentialScalar_conormalBasisPullback_projModelVariableChangeIso_hom
    (C : VariableChange R) (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    (C • W).weierstrassDifferentialScalar
        (Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R)))
          (g := (W.projModelVariableChangeIso C).hom)
          W.projModelZero_projModelOver (C • W).projModelZero_projModelOver
          (IsPullback.of_horiz_isIso ⟨by simp⟩)
          (by rw [W.projModelZero_projModelVariableChangeIso_hom C, Category.id_comp]) ω) =
      W.weierstrassDifferentialScalar ω * C.u⁻¹ := by
  symm
  rw [eq_weierstrassDifferentialScalar_iff]
  conv_rhs => rw [← W.unitSmulIso_weierstrassDifferentialScalar ω]
  rw [Scheme.Hom.conormalBasisPullback_unitSmulIso,
    W.conormalBasisPullback_weierstrassDifferential_projModelVariableChangeIso_hom C,
    ← Scheme.Modules.unitSmulIso_mul]
  congr 1
  ext1
  simp

end Scalar

end

end WeierstrassCurve
