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

The integral factorization uses `GroupScheme.factorisationDual`, which descends multiplication
through the isogeny using its scheme-theoretic kernel. The construction thus works for inseparable
isogenies as well. See Milne, *Abelian Varieties* (2008), Chapter I, Remark 8.6 and §10.
-/

public section

open CategoryTheory AlgebraicGeometry

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

end TauCeti.AlgebraicGeometry.AbelianVariety
