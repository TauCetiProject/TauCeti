/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Defect
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.Algebra.Module.AuslanderReiten.TensorCokernel
import TauCeti.LinearAlgebra.TensorProduct.Balanced.Unit
import Mathlib.Algebra.Algebra.Opposite

/-!
# Tensor description of Ext from a finite projective resolution of length one

Let `A` be an algebra over a commutative ring `k`. Right multiplication on the regular left module
acts covariantly on `Extⁿ_A(M,A)`. Pushforward along `a ↦ a • y` gives the balanced map
`Extⁿ_A(M,A) ⊗_A Y → Extⁿ_A(M,Y)`, natural in `Y`. In degree one this is an
isomorphism when `M` has a resolution of length one by finite projectives. The map itself is
independent of the resolution.

The comparison uses `LinearMap.auslanderReitenTransposeTensorEquivCokernel`,
`ModuleCat.covariantDefectEquivHomQuotient`, and `TauCeti.homCokernelEquivExt`.
For finite acyclic quivers this tensor description is used with
`M = D(kQ)` in the hereditary description of the inverse Auslander–Reiten translate.

## References

* J. Grant, *The Nakayama automorphism of a self-injective preprojective algebra*, Proposition 2.5.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Abelian MulOpposite TauCeti
open scoped ModuleCat.Algebra

namespace ModuleCat

universe u v

variable (k : Type v) {A : Type u} [CommRing k] [Ring A] [Algebra k A]

/-- Right multiplication in the coefficient module gives a right `A`-action on `Extⁿ_A(M,A)`. -/
scoped instance extRegularModule (M : ModuleCat.{u} A) (n : ℕ) :
    Module Aᵐᵒᵖ (Ext M (of A A) n) :=
  Module.compHom _
    ((RingEquiv.moduleEndSelf A).trans (endRingEquiv (of A A)).symm).toRingHom

/-- The right action on `Extⁿ_A(M,A)` pushes forward along right multiplication. -/
theorem op_smul_extRegular {M : ModuleCat.{u} A} {n : ℕ} (a : A) (x : Ext M (of A A) n) :
    op a • x = x.comp (Ext.mk₀ (ofHom (LinearMap.toSpanSingleton A A a))) (add_zero n) := by
  exact Ext.smul_end_def _ x

variable {M Y Z : ModuleCat.{u} A} {n : ℕ}

/-- The canonical balanced evaluation map from extensions by the regular module to extensions
by `Y`, induced by pushout along `a ↦ a • y` on a simple tensor with `y`. -/
noncomputable def extRegularTensor (M Y : ModuleCat.{u} A) (n : ℕ) :
    BalancedTensorProduct k A (Ext M (of A A) n) Y →ₗ[k] Ext M Y n :=
  BalancedTensorProduct.lift
    ((Ext.bilinearCompOfLinear k M (of A A) Y n 0 n (add_zero n)).compl₂
      ((Ext.linearEquiv₀ (R := k)).symm.toLinearMap.comp
        (homSelfLinearEquiv k Y).symm.toLinearMap)) (by
    intro a x y
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearEquiv.coe_coe,
      Ext.linearEquiv₀_symm_apply, Ext.bilinearCompOfLinear_apply_apply,
      homSelfLinearEquiv_symm_apply, op_smul_extRegular, Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀]
    congr 2
    exact hom_ext (LinearMap.toSpanSingleton_comp_toSpanSingleton y a))

/-- On a simple tensor the evaluation pushes forward along `a ↦ a • y`. -/
@[simp]
theorem extRegularTensor_tmul (x : Ext M (of A A) n) (y : Y) :
    extRegularTensor k M Y n (BalancedTensorProduct.tmul k A x y) =
      x.comp (Ext.mk₀ (ofHom (LinearMap.toSpanSingleton A Y y))) (add_zero n) := by
  simp [extRegularTensor]

/-- Balanced evaluation commutes with pushforward in the coefficient module. -/
theorem extRegularTensor_naturality (g : Y ⟶ Z)
    (t : BalancedTensorProduct k A (Ext M (of A A) n) Y) :
    extRegularTensor k M Z n (BalancedTensorProduct.lTensor k _ g.hom t) =
      (extRegularTensor k M Y n t).comp (Ext.mk₀ g) (add_zero n) := by
  induction t using BalancedTensorProduct.induction_on with
  | ht x y =>
    simp only [BalancedTensorProduct.lTensor_tmul, extRegularTensor_tmul,
      Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    congr 2
    exact hom_ext (LinearMap.comp_toSpanSingleton g.hom y).symm
  | ha t s ht hs => simp [ht, hs]

variable {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    [Module.Finite A S.X₁] [Module.Projective A S.X₁]
    [Module.Finite A S.X₂] [Module.Projective A S.X₂]

variable {W : Type u} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]

private noncomputable def transposeTensorEquivExt (eW : W ≃ₗ[A] Y) :
    BalancedTensorProduct k A (AuslanderReitenTranspose S.f.hom) W ≃ₗ[k] Ext S.X₃ Y 1 :=
  (LinearMap.auslanderReitenTransposeTensorEquivCokernel S.f.hom).trans
    ((covariantDefectEquivHomQuotient k eW S.f).trans (homCokernelEquivExt k hS Y))

@[simp]
private theorem transposeTensorEquivExt_mk (eW : W ≃ₗ[A] Y)
    (φ : Module.Dual A S.X₁) (w : W) :
    transposeTensorEquivExt k hS eW
        (BalancedTensorProduct.tmul k A (AuslanderReitenTranspose.mk S.f.hom φ) w) =
      hS.extClass.comp (Ext.mk₀ (ofHom (eW.toLinearMap.comp (φ.smulRight w)))) (add_zero 1) := by
  simp only [transposeTensorEquivExt, LinearEquiv.trans_apply,
    LinearMap.auslanderReitenTransposeTensorEquivCokernel_tmul, covariantDefectEquivHomQuotient_mk]
  rw [homCokernelEquivExt_mk k hS Y]
  congr 4
  ext b
  simp

private noncomputable def transposeEquivExtRegular :
    AuslanderReitenTranspose S.f.hom ≃ₗ[k] Ext S.X₃ (of A A) 1 :=
  (BalancedTensorProduct.rid k A _).symm.trans
    (transposeTensorEquivExt k hS (LinearEquiv.refl A A : A ≃ₗ[A] of A A))

@[simp]
private theorem transposeEquivExtRegular_mk (φ : Module.Dual A S.X₁) :
    transposeEquivExtRegular k hS (AuslanderReitenTranspose.mk S.f.hom φ) =
      hS.extClass.comp (Ext.mk₀ (ofHom φ)) (add_zero 1) := by
  rw [transposeEquivExtRegular, LinearEquiv.trans_apply, BalancedTensorProduct.rid_symm_apply,
    transposeTensorEquivExt_mk]
  congr 2
  ext b
  simp

private theorem transposeEquivExtRegular_op_smul (a : A)
    (t : AuslanderReitenTranspose S.f.hom) :
    transposeEquivExtRegular k hS (op a • t) = op a • transposeEquivExtRegular k hS t := by
  obtain ⟨φ, rfl⟩ := AuslanderReitenTranspose.mk_surjective S.f.hom t
  rw [← map_smul, transposeEquivExtRegular_mk, transposeEquivExtRegular_mk, op_smul_extRegular,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  congr 2

/-- A length-one resolution of `M` by finite projectives makes the canonical evaluation
`Ext¹_A(M,A) ⊗_A Y → Ext¹_A(M,Y)` bijective. -/
theorem extRegularTensor_bijective_of_shortExact (hS : S.ShortExact) (Y : ModuleCat.{u} A) :
    Function.Bijective (extRegularTensor k S.X₃ Y 1) := by
  let e := BalancedTensorProduct.congr (transposeEquivExtRegular k hS) (LinearEquiv.refl k Y)
    (transposeEquivExtRegular_op_smul k hS) (fun _ _ ↦ by simp only [LinearEquiv.refl_apply])
  have htmul (t : AuslanderReitenTranspose S.f.hom) (y : Y) :
      e (BalancedTensorProduct.tmul k A t y) =
        BalancedTensorProduct.tmul k A (transposeEquivExtRegular k hS t) y :=
    BalancedTensorProduct.congr_tmul _ _ _ _ t y
  have he : (extRegularTensor k S.X₃ Y 1).comp e.toLinearMap =
      (transposeTensorEquivExt k hS (LinearEquiv.refl A Y)).toLinearMap := by
    apply BalancedTensorProduct.hom_ext
    intro t y
    obtain ⟨φ, rfl⟩ := AuslanderReitenTranspose.mk_surjective S.f.hom t
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [htmul, extRegularTensor_tmul,
      transposeEquivExtRegular_mk, transposeTensorEquivExt_mk,
      Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    congr 2
  have hb : Function.Bijective ((extRegularTensor k S.X₃ Y 1).comp e.toLinearMap) :=
    he ▸ (transposeTensorEquivExt k hS (LinearEquiv.refl A Y)).bijective
  exact (Function.Bijective.of_comp_iff _ e.bijective).mp hb

/-- A finitely presented module of projective dimension at most one satisfies the tensor formula
for `Ext¹` with every coefficient module. -/
theorem extRegularTensor_bijective (M Y : ModuleCat.{u} A)
    [Module.FinitePresentation A M] [HasProjectiveDimensionLT M 2] :
    Function.Bijective (extRegularTensor k M Y 1) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' A M
  have : Module.Finite A (LinearMap.ker f) := .of_fg (Module.FinitePresentation.fg_ker f hf)
  have hker := (f.hasProjectiveDimensionLE_succ_iff_ker hf 0).mp
    (inferInstanceAs (HasProjectiveDimensionLT M 2))
  have : HasProjectiveDimensionLT (of A (LinearMap.ker f)) 1 := hker
  have : Module.Projective A (LinearMap.ker f) :=
    (of A (LinearMap.ker f)).projective_of_module_projective
  exact extRegularTensor_bijective_of_shortExact k (LinearMap.shortExact_shortComplexKer hf) Y

/-- The canonical `Ext¹_A(M,A) ⊗_A Y ≃ Ext¹_A(M,Y)` for a finitely presented module of projective
dimension at most one. -/
noncomputable def extRegularTensorEquiv (M Y : ModuleCat.{u} A)
    [Module.FinitePresentation A M] [HasProjectiveDimensionLT M 2] :
    BalancedTensorProduct k A (Ext M (of A A) 1) Y ≃ₗ[k] Ext M Y 1 :=
  LinearEquiv.ofBijective _ (extRegularTensor_bijective k M Y)

/-- The tensor equivalence evaluates by the canonical pushforward map. -/
@[simp]
theorem extRegularTensorEquiv_apply [Module.FinitePresentation A M]
    [HasProjectiveDimensionLT M 2] (t : BalancedTensorProduct k A (Ext M (of A A) 1) Y) :
    extRegularTensorEquiv k M Y t = extRegularTensor k M Y 1 t := (rfl)

end ModuleCat
