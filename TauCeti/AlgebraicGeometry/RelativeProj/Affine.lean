/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# Relative Proj over an affine scheme

For a graded algebra `A` with quasi-coherent homogeneous components on an affine scheme `X`,
the relative `Proj` is canonically the projective spectrum of its graded algebra of global
sections. The inverse comparison is the chart over the whole base, and the comparison respects
the structure morphisms to `X`. This lets constructions on an affine relative `Proj` use the
ordinary projective spectrum without changing the base scheme.

The comparison specializes the chart pullback square
`CategoryTheory.CommMon.isPullback_relativeProjCover` to the whole affine base, following the
analogous affine comparison for relative Spec in
`CategoryTheory.CommMon.relativeSpecIsoSpec`.

## References

* [The Stacks Project, Lemma 27.15.4](https://stacks.math.columbia.edu/tag/01NQ)
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X : Scheme.{u}} [IsAffine X]
variable (A : CommMon (GradedObject ℕ X.Modules)) [∀ n, (A.X n).IsQuasicoherent]

/-- Over an affine base, the chart of relative `Proj` over the whole base is an isomorphism. -/
instance isIso_relativeProjCover_f_top :
    IsIso (A.relativeProjCover.f ⟨⊤, isAffineOpen_top X⟩) := by
  have : IsIso (Scheme.Opens.ι (⊤ : X.Opens)) :=
    inferInstanceAs (IsIso X.topIso.hom)
  exact (A.isPullback_relativeProjCover ⟨⊤, isAffineOpen_top X⟩).isIso_snd_of_isIso

/-- Relative `Proj` over an affine scheme is the projective spectrum of the graded algebra
of global sections. Its inverse is the chart inclusion over the whole base. -/
def relativeProjIsoProj : A.relativeProj ≅ Proj (A.gradedSectionsGrading ⊤) :=
  (asIso (A.relativeProjCover.f ⟨⊤, isAffineOpen_top X⟩)).symm

/-- The inverse affine comparison is the chart inclusion over the whole base.
This is a named rewrite so the generic isomorphism inverse laws remain available to `simp`. -/
lemma relativeProjIsoProj_inv :
    A.relativeProjIsoProj.inv = A.relativeProjCover.f ⟨⊤, isAffineOpen_top X⟩ :=
  (rfl)

/-- The inverse affine comparison respects the structure morphisms to the base scheme. -/
@[reassoc]
lemma relativeProjIsoProj_inv_relativeProjToBase :
    A.relativeProjIsoProj.inv ≫ A.relativeProjToBase =
      Proj.toSpecCoeff (A.gradedSectionsGrading ⊤) ≫ X.isoSpec.inv := by
  exact (A.relativeProjCover_f_relativeProjToBase ⟨⊤, isAffineOpen_top X⟩).trans
    (congrArg (Proj.toSpecCoeff (A.gradedSectionsGrading ⊤) ≫ ·)
      (IsAffineOpen.fromSpec_top (X := X)))

/-- Affine comparison identifies the structure morphism of relative `Proj` with the coefficient
projection followed by the affine identification of the base. -/
@[reassoc (attr := simp)]
lemma relativeProjIsoProj_hom_toBase :
    A.relativeProjIsoProj.hom ≫
        (Proj.toSpecCoeff (A.gradedSectionsGrading ⊤) ≫ X.isoSpec.inv) =
      A.relativeProjToBase := by
  exact (A.relativeProjIsoProj.inv_comp_eq.mp
    A.relativeProjIsoProj_inv_relativeProjToBase).symm

end

end CategoryTheory.CommMon
