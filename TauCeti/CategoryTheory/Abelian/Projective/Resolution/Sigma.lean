/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Coproducts of projective resolutions

Let `C` be an abelian category in which coproducts indexed by `J` exist and are exact. The
coproduct of projective resolutions `Pⱼ` of objects `Xⱼ` is a projective resolution of `∐ Xⱼ`
(`CategoryTheory.ProjectiveResolution.sigma`): coproducts of projectives are projective
(`CategoryTheory.Projective.of_isColimit_cofan`), and since coproducts are exact the coproduct of
the quasi-isomorphisms `Pⱼ ⟶ Xⱼ` is a quasi-isomorphism (`TauCeti.quasiIsoAt_sigmaMap_iff`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.4.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits

universe w

variable {C : Type*} [Category* C] [Abelian C] {J : Type w} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C]

namespace ProjectiveResolution

/-- The coproduct of projective resolutions `Pⱼ` of objects `Xⱼ` is a projective resolution of
`∐ Xⱼ`, with augmentation `∐ Pⱼ ⟶ ∐ Xⱼ` induced by the augmentations of the `Pⱼ`. -/
@[expose] def sigma {X : J → C} (P : ∀ j, ProjectiveResolution (X j)) :
    ProjectiveResolution (∐ X) where
  complex := ∐ fun j ↦ (P j).complex
  projective k := Projective.of_iso
    (PreservesCoproduct.iso (HomologicalComplex.eval C _ k) fun j ↦ (P j).complex).symm
    (Projective.of_isColimit_cofan (X := fun j ↦ (P j).complex.X k) (coproductIsCoproduct _))
  π := Sigma.desc fun j ↦ (P j).π ≫ (ChainComplex.single₀ C).map (Sigma.ι X j)
  quasiIso := by
    have h : (Sigma.desc fun j ↦ (P j).π ≫ (ChainComplex.single₀ C).map (Sigma.ι X j)) =
        Limits.Sigma.map (fun j ↦ (P j).π) ≫ sigmaComparison (ChainComplex.single₀ C) X :=
      Sigma.hom_ext _ _ fun j ↦ by simp
    have : QuasiIso (Limits.Sigma.map fun j ↦ (P j).π) :=
      ⟨fun q ↦ (TauCeti.quasiIsoAt_sigmaMap_iff _).2 fun j ↦ inferInstance⟩
    rw [h]
    infer_instance

/-- The complex of the coproduct resolution is the coproduct of the complexes `Pⱼ`. -/
@[simp]
lemma sigma_complex {X : J → C} (P : ∀ j, ProjectiveResolution (X j)) :
    (sigma P).complex = ∐ fun j ↦ (P j).complex :=
  rfl

/-- On the summand `Pⱼ`, the augmentation of the coproduct resolution is that of `Pⱼ` followed by
the inclusion `Xⱼ ⟶ ∐ X`. -/
@[simp, reassoc]
lemma ι_sigma_π {X : J → C} (P : ∀ j, ProjectiveResolution (X j)) (j : J) :
    Sigma.ι (fun j ↦ (P j).complex) j ≫ (sigma P).π =
      (P j).π ≫ (ChainComplex.single₀ C).map (Sigma.ι X j) :=
  Sigma.ι_comp_desc _ _

end ProjectiveResolution

end CategoryTheory
