/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Coefficient
public import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny
import TauCeti.AlgebraicGeometry.AbelianVariety.FaithfullyFlat
import TauCeti.AlgebraicGeometry.GroupScheme.Isogeny.FactorisationDual
import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Inverting isogenies of abelian varieties

An isogeny of abelian varieties has a two-sided inverse up to multiplication by its rank at the
target identity. It becomes an isomorphism with coefficients in any ring where that rank is a unit.
In the rational coefficient category, invertibility is equivalent to having a two-sided integral
inverse up to multiplication by a common nonzero integer.

The integral factorization uses `GroupScheme.factorisationDual`, which descends multiplication
through the isogeny using its scheme-theoretic kernel. The construction thus works for inseparable
isogenies as well. See Milne, *Abelian Varieties* (2008), Chapter I, Remark 8.6 and §10.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct nonZeroDivisors

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u v

variable {K : Type u} [Field K] {A B : AbelianVariety K}

open scoped Hom CategoryTheory.MonObj

/-- An isogeny admits a homomorphism in the reverse direction whose two composites with the
isogeny are multiplication by its rank at the target identity. -/
theorem IsIsogeny.exists_comp_eq_mulBy_finrank {f : A ⟶ B} (hf : IsIsogeny f) :
    ∃ g : B ⟶ A,
      f ≫ g = mulBy A ((Hom.toSchemeHom f).finrank B.zeroPoint) ∧
      g ≫ f = mulBy B ((Hom.toSchemeHom f).finrank B.zeroPoint) := by
  let d := (Hom.toSchemeHom f).finrank B.zeroPoint
  let φ : CommGrp.mk A.toOver ⟶ CommGrp.mk B.toOver := f.hom
  have hφ : GroupScheme.IsIsogeny φ.hom := (isIsogeny_iff_groupScheme_isIsogeny f).mp hf
  have := hφ.isFinite
  have := hφ.flat
  have : LocallyOfFinitePresentation ((Hom.toSchemeHom f) ≫ B.toOver.hom) := by
    rw [Hom.toSchemeHom_comp_hom]
    infer_instance
  have : LocallyOfFinitePresentation φ.hom.hom.hom.left :=
    locallyOfFinitePresentation_of_comp (Hom.toSchemeHom f) B.toOver.hom
  have hd : GroupScheme.IsogenyOfDegree φ.hom d := by
    refine ⟨hφ, fun s ↦ ?_⟩
    let s₀ : Spec (.of K) := IsLocalRing.closedPoint K
    calc
      _ = GroupScheme.degree φ.hom s₀ := congrArg _ (Subsingleton.elim s s₀)
      _ = _ := GroupScheme.degree_eq_finrank φ.hom s₀
      _ = d := by
        simp only [d, B.zeroPoint_def, Hom.toSchemeHom, toOverHom_eq_forget₂Grp_map]
        rfl
  let g : B ⟶ A := InducedCategory.homMk (GroupScheme.factorisationDual φ hd)
  have cast_mulBy (X : AbelianVariety K) :
      (d : CategoryTheory.End (CommGrp.mk X.toOver)).asHom = (mulBy X d).hom := by
    apply CommGrp.hom_ext
    rw [← Int.cast_natCast, CommGrp.intCast_hom_hom_hom, mulBy_eq_zpow,
      ← Hom.homMulEquiv_apply, map_zpow, Hom.homMulEquiv_apply, Grp.Hom.hom_hom_zpow]
    rfl
  exact ⟨g,
    InducedCategory.hom_ext ((GroupScheme.comp_factorisationDual φ hd).trans (cast_mulBy A)),
    InducedCategory.hom_ext ((GroupScheme.factorisationDual_comp φ hd).trans (cast_mulBy B))⟩

private theorem isIso_coefficientFunctor_map_of_comp_eq_mulBy (R : Type v) [CommRing R]
    {f : A ⟶ B} {g : B ⟶ A} {n : ℤ} (hn : IsUnit (n : R))
    (hA : f ≫ g = mulBy A n) (hB : g ≫ f = mulBy B n) :
    IsIso ((coefficientFunctor R).map f) := by
  obtain ⟨r, hr⟩ := hn
  let F : AbelianVariety K ⥤ WithCoefficients R K := coefficientFunctor R
  refine ⟨⟨(↑r⁻¹ : R) • F.map g, ?_, ?_⟩⟩
  · rw [Linear.comp_smul, ← F.map_comp, hA, coefficientFunctor_map_mulBy,
      ← Int.cast_smul_eq_zsmul R, ← hr, smul_smul, Units.inv_mul, one_smul]
  · rw [Linear.smul_comp, ← F.map_comp, hB, coefficientFunctor_map_mulBy,
      ← Int.cast_smul_eq_zsmul R, ← hr, smul_smul, Units.inv_mul, one_smul]

/-- An isogeny becomes invertible with coefficients in `R` if its rank is a unit in `R`. -/
theorem IsIsogeny.isIso_coefficientFunctor_map_of_isUnit_finrank (R : Type v) [CommRing R]
    {f : A ⟶ B} (hf : IsIsogeny f)
    (hu : IsUnit ((Hom.toSchemeHom f).finrank B.zeroPoint : R)) :
    IsIso ((coefficientFunctor R).map f) := by
  obtain ⟨g, hA, hB⟩ := hf.exists_comp_eq_mulBy_finrank
  exact isIso_coefficientFunctor_map_of_comp_eq_mulBy R
    (n := ((Hom.toSchemeHom f).finrank B.zeroPoint : ℤ)) (by simpa only [Int.cast_natCast] using hu)
    hA hB

/-- Every isogeny becomes an isomorphism in the rational coefficient category. -/
theorem IsIsogeny.isIso_rational_coefficientFunctor_map {f : A ⟶ B} (hf : IsIsogeny f) :
    IsIso ((coefficientFunctor ℚ).map f) := by
  have := hf.isFinite
  have := hf.flat
  obtain ⟨a, ha⟩ := hf.surjective.surj B.zeroPoint
  have hpos : 0 < (Hom.toSchemeHom f).finrank B.zeroPoint :=
    ha ▸ (Hom.toSchemeHom f).one_le_finrank_map a
  exact hf.isIso_coefficientFunctor_map_of_isUnit_finrank ℚ
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast hpos.ne'))

/-- An endomorphism that is an isogeny maps to a unit of the rational endomorphism algebra. -/
theorem IsIsogeny.isUnit_end0 {f : A ⟶ A} (hf : IsIsogeny f) :
    IsUnit ((Algebra.TensorProduct.includeRight : End A →ₐ[ℤ] End0 A) (End.ofHom f)) := by
  let X : WithCoefficients ℚ K := ⟨A⟩
  let fQ := (coefficientFunctor ℚ).map f
  let g : X ⟶ X := (WithCoefficients.homLinearEquiv X X).symm (CoefficientHom.ofHom ℚ f)
  let e : (coefficientFunctor ℚ).obj A ≅ X := eqToIso (coefficientFunctor_obj ℚ A)
  have hi : IsIso fQ := hf.isIso_rational_coefficientFunctor_map
  have hg : g = e.inv ≫ fQ ≫ e.hom := by
    simp [g, e, fQ, X]
  have hu : IsUnit (CategoryTheory.End.of g) := by
    apply (CategoryTheory.isUnit_iff_isIso _).mpr
    rw [hg]
    infer_instance
  simpa only [WithCoefficients.endAlgEquiv_apply, g, LinearEquiv.apply_symm_apply,
    CoefficientHom.endEquiv_ofHom] using hu.map (WithCoefficients.endAlgEquiv X)

private noncomputable def rationalHomLinearEquiv (A B : AbelianVariety K) :
    ((coefficientFunctor ℚ).obj A ⟶ (coefficientFunctor ℚ).obj B) ≃ₗ[ℚ] CoefficientHom ℚ A B :=
  (Linear.homCongr ℚ (eqToIso (coefficientFunctor_obj ℚ A))
    (eqToIso (coefficientFunctor_obj ℚ B))).trans (WithCoefficients.homLinearEquiv ⟨A⟩ ⟨B⟩)

private theorem rationalHomLinearEquiv_map (f : A ⟶ B) :
    rationalHomLinearEquiv A B ((coefficientFunctor ℚ).map f) = CoefficientHom.ofHom ℚ f := by
  simp only [rationalHomLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    eqToIso.inv, eqToIso.hom, coefficientFunctor_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.apply_symm_apply]

/-- An integral homomorphism becomes invertible with rational coefficients exactly when another
integral homomorphism composes with it on both sides to multiplication by the same nonzero
integer. -/
theorem isIso_rational_coefficientFunctor_map_iff (f : A ⟶ B) :
    IsIso ((coefficientFunctor ℚ).map f) ↔
      ∃ (n : ℤ) (g : B ⟶ A), n ≠ 0 ∧ f ≫ g = mulBy A n ∧ g ≫ f = mulBy B n := by
  refine ⟨fun _ ↦ ?_, fun ⟨n, g, hn, hA, hB⟩ ↦
    isIso_coefficientFunctor_map_of_comp_eq_mulBy ℚ
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast hn)) hA hB⟩
  let F : AbelianVariety K ⥤ WithCoefficients ℚ K := coefficientFunctor ℚ
  let e := rationalHomLinearEquiv B A
  obtain ⟨n, g, hn, hg₀⟩ := CoefficientHom.exists_zsmul_eq_ofHom (A := B) (B := A)
    (e (inv (F.map f)))
  have hg : n • inv (F.map f) = F.map g := e.injective (by
    rw [map_zsmul, hg₀, rationalHomLinearEquiv_map])
  have hA : F.map (f ≫ g) = F.map (mulBy A n) := by
    rw [F.map_comp, ← hg, Preadditive.comp_zsmul, IsIso.hom_inv_id, coefficientFunctor_map_mulBy]
  have hB : F.map (g ≫ f) = F.map (mulBy B n) := by
    rw [F.map_comp, ← hg, Preadditive.zsmul_comp, IsIso.inv_hom_id, coefficientFunctor_map_mulBy]
  -- Each rational composition identity yields an integral identity after taking a power.
  have exists_pow_eq (X : AbelianVariety K) {a b : X ⟶ X}
      (h : (coefficientFunctor ℚ).map a = (coefficientFunctor ℚ).map b) :
      ∃ d : ℤ⁰, a ^ (d : ℤ) = b ^ (d : ℤ) := by
    let loc := TensorProduct.mk ℤ ℚ (Additive (X ⟶ X)) 1
    have hl : loc (Additive.ofMul a) = loc (Additive.ofMul b) := by
      simpa only [loc, TensorProduct.mk_apply, rationalHomLinearEquiv_map,
        CoefficientHom.ofHom_def] using
        (congrArg (rationalHomLinearEquiv X X) h)
    obtain ⟨d, hd⟩ := (IsLocalizedModule.eq_iff_exists ℤ⁰ loc).mp hl
    exact ⟨d, by simpa only [Submonoid.smul_def, toMul_zsmul, toMul_ofMul] using
      (congrArg Additive.toMul hd)⟩
  obtain ⟨dA, hdA⟩ := exists_pow_eq A hA
  obtain ⟨dB, hdB⟩ := exists_pow_eq B hB
  -- The product of the two exponents works for both compositions.
  let d := (dA : ℤ) * (dB : ℤ)
  have hd : d ≠ 0 :=
    mul_ne_zero (nonZeroDivisors.ne_zero dA.prop) (nonZeroDivisors.ne_zero dB.prop)
  refine ⟨n * d, g ^ d, mul_ne_zero hn hd, ?_, ?_⟩
  · dsimp only [d]
    rw [Hom.comp_zpow, zpow_mul, hdA]
    simp only [mulBy_eq_zpow, ← zpow_mul, mul_assoc]
  · dsimp only [d]
    rw [Hom.zpow_comp, zpow_mul', hdB]
    simp only [mulBy_eq_zpow, ← zpow_mul, mul_assoc, mul_comm (dA : ℤ) (dB : ℤ)]

end TauCeti.AlgebraicGeometry.AbelianVariety
