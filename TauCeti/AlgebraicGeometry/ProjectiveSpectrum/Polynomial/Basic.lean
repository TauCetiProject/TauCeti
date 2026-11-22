/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import TauCeti.RingTheory.MvPolynomial.HomogeneousLocalization
public import TauCeti.RingTheory.MvPolynomial.SymmetricPresentation
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality

/-!
# Polynomial projective spectra

The projective spectrum of a polynomial ring with finitely many degree-one variables is
projective over its coefficient ring. Its graded symmetric-algebra presentation gives the
closed immersion into the ambient scheme used by `Scheme.IsProjectiveOver`.

For a singleton variable type the unique standard chart is the whole scheme, and its
coefficient morphism is an isomorphism. This supplies the empty finite product of projective
schemes over an affine base.
-/

public section

open CategoryTheory HomogeneousLocalization
open MvPolynomial TauCeti.MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (R σ : Type u) [CommRing R]

section Singleton

variable [Unique σ]

/-- The standard open for the only variable is the entire polynomial projective spectrum. -/
theorem basicOpen_X_eq_top :
    basicOpen (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X default) = ⊤ := by
  have h := iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule σ R)
    (MvPolynomial.X : σ → MvPolynomial σ R) (MvPolynomial.irrelevant_eq_span_X σ R).le
  rwa [iSup_unique] at h

/-- Polynomial projective space on one homogeneous coordinate is its affine base. -/
instance isIso_toSpecCoeff_unique :
    IsIso (toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R)) := by
  have : IsIso (awayι (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X default)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X R default)) one_pos) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      ((opensRange_awayι _ _ _ one_pos).trans (basicOpen_X_eq_top R σ))
  have : IsIso (CommRingCat.ofHom (algebraMap R
      (Away (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X (default : σ))))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (TauCeti.MvPolynomial.bijective_algebraMap_awayX R σ)
  have : IsIso (awayι (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X default)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X R default)) one_pos ≫
      toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R)) := by
    rw [awayι_toSpecCoeff]
    infer_instance
  exact IsIso.of_isIso_comp_left (awayι (MvPolynomial.homogeneousSubmodule σ R)
    (MvPolynomial.X default) ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X R default)) one_pos) _

end Singleton

/-- A polynomial projective spectrum lies over its coefficient ring. -/
noncomputable instance polynomialOver :
    (Proj (MvPolynomial.homogeneousSubmodule σ R)).Over (Spec (.of R)) :=
  ⟨toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R)⟩

/-- The structure map of a polynomial projective spectrum is its coefficient morphism. -/
@[simp]
theorem over_polynomial :
    Proj (MvPolynomial.homogeneousSubmodule σ R) ↘ Spec (.of R) =
      toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R) := rfl

/-- The projective embedding induced by the graded symmetric-algebra presentation. -/
noncomputable def polynomialProjectiveEmbedding :
    Proj (MvPolynomial.homogeneousSubmodule σ R) ⟶
      Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (σ →₀ R)) :=
  map (MvPolynomial.symmetricPresentation R σ)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _
      (MvPolynomial.symmetricPresentation_surjective R σ))

/-- The graded presentation induces a closed immersion, for any coordinate type. -/
instance isClosedImmersion_polynomialProjectiveEmbedding :
    IsClosedImmersion (polynomialProjectiveEmbedding R σ) :=
  isClosedImmersion_map _ _ (MvPolynomial.symmetricPresentation_surjective R σ)

/-- The polynomial projective embedding preserves coefficients. -/
@[reassoc (attr := simp)]
theorem polynomialProjectiveEmbedding_projToSpec :
    polynomialProjectiveEmbedding R σ ≫ TauCeti.SymmetricAlgebra.projToSpec R (σ →₀ R) =
      toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R) := by
  rw [polynomialProjectiveEmbedding, TauCeti.SymmetricAlgebra.projToSpec_def, ← toSpecCoeff_def]
  apply map_toSpecCoeff
  intro r
  apply Subtype.ext
  simp

/-- A coordinate open pulls back to the polynomial standard open with the same index. -/
@[simp]
theorem polynomialProjectiveEmbedding_preimage_basicOpen (i : σ) :
    polynomialProjectiveEmbedding R σ ⁻¹ᵁ
        basicOpen (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (σ →₀ R))
          (SymmetricAlgebra.ι R (σ →₀ R) (Finsupp.single i 1)) =
      basicOpen (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i) := by
  rw [polynomialProjectiveEmbedding, map_preimage_basicOpen,
    MvPolynomial.symmetricPresentation_ι_single]

/-- The projective embedding is a morphism over the coefficient ring. -/
instance isOver_polynomialProjectiveEmbedding :
    (polynomialProjectiveEmbedding R σ).IsOver (Spec (.of R)) where
  comp_over := polynomialProjectiveEmbedding_projToSpec R σ

/-- A polynomial projective spectrum on finitely many coordinates is projective over the base. -/
instance isProjectiveOver_polynomial [Finite σ] :
    (Proj (MvPolynomial.homogeneousSubmodule σ R)).IsProjectiveOver R := by
  have : Module.Finite R (σ →₀ R) := Module.Finite.finsupp
  exact Scheme.IsProjectiveOver.of_isClosedImmersion R (polynomialProjectiveEmbedding R σ)


section Charts

/-- The standard affine cover of a polynomial projective spectrum. -/
noncomputable abbrev polynomialAffineOpenCover :
    (Proj (homogeneousSubmodule σ R)).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan _ (X : σ → MvPolynomial σ R)
    (fun i ↦ (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i))
    (fun _ ↦ one_pos) (irrelevant_eq_span_X σ R).le

variable {σ}

/-- Two coordinate charts representing the same projective morphism have normalized
coordinates differing by one unit on the source scheme. -/
theorem awayXRatio_rescaling {Z : Scheme.{u}} (i k : σ)
    (p : Z ⟶ Spec (.of (Away (homogeneousSubmodule σ R) (X i))))
    (q : Z ⟶ Spec (.of (Away (homogeneousSubmodule σ R) (X k))))
    (h : p ≫ awayι _ (X i) ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) one_pos =
      q ≫ awayι _ (X k) ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R k)) one_pos) :
    ∃ c : Γ(Z, ⊤)ˣ, ∀ l,
      ((Scheme.ΓSpecIso _).inv ≫ q.appTop).hom (awayXRatio k l) =
        c * ((Scheme.ΓSpecIso _).inv ≫ p.appTop).hom (awayXRatio i l) := by
  have hu := isUnit_appTop_awayMk (homogeneousSubmodule σ R) one_pos
    ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) ((mem_homogeneousSubmodule _
      _).mpr (isHomogeneous_X R k)) p q h
  refine ⟨hu.unit, fun l ↦ ?_⟩
  rw [IsUnit.unit_spec, mul_comm]
  simp only [awayXRatio_def]
  exact appTop_awayMk_eq_mul _ one_pos ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i))
    ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R k)) p q h (X l)
    (by simpa using isHomogeneous_X R l)

/-- Pulling a projective coordinate open back along an affine chart tests the
corresponding normalized coordinate on global sections. -/
theorem preimage_basicOpen_X {Z : Scheme.{u}} (i k : σ)
    (p : Z ⟶ Spec (.of (Away (homogeneousSubmodule σ R) (X i)))) :
    (p ≫ awayι _ (X i) ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) one_pos) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule σ R) (X k) =
      Z.basicOpen (((Scheme.ΓSpecIso _).inv ≫ p.appTop).hom (awayXRatio i k)) := by
  rw [Scheme.Hom.comp_preimage, awayι_preimage_basicOpen _
    ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) one_pos
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R k)) one_pos,
    TauCeti.MvPolynomial.isLocalizationElem_X (R := R) i k]
  refine (congrArg (p ⁻¹ᵁ ·) (basicOpen_eq_of_affine
    (R := CommRingCat.of (Away (homogeneousSubmodule σ R) (X i)))
    (awayXRatio (R := R) i k)).symm).trans ?_
  exact Scheme.preimage_basicOpen _ _


end Charts

end AlgebraicGeometry.Proj
