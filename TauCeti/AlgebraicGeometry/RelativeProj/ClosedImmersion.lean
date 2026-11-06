/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.GeneratedInDegreeOne
public import TauCeti.AlgebraicGeometry.RelativeProj.Map

/-!
# The relative `Proj` of an algebra generated in degree one embeds in `Proj_X(Sym A₁)`

Let `A` be a graded quasicoherent algebra on a scheme `X` that is generated in degree one
(`TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.IsGeneratedInDegreeOne`), and let
`φ : B ⟶ A` be a morphism of graded quasicoherent algebras that is an epimorphism `B₁ ⟶ A₁` in
degree one. Then `φ` is surjective in every positive degree on affine sections
(`GradedQuasicoherentAlgebra.grade_subset_range_gradedSectionsGradedHom_of_epi_one`), so the
induced morphism `Proj_X(A) ⟶ Proj_X(B)` over `X` is a closed immersion (Stacks, Lemmas 27.11.3
and 27.11.5 (01N0, 01N1), on affine charts), by
`CategoryTheory.CommMon.isClosedImmersion_relativeProjMap`.

The main example is the morphism `Sym A₁ ⟶ A` extending the identity of `A₁`
(`TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraLift`), an epimorphism in degree one by the
instance `TauCeti.AlgebraicGeometry.epi_gradedSymmetricAlgebraLift_one`: the relative `Proj` of an
algebra generated in degree one is a closed subscheme of `Proj_X(Sym A₁)`.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`:

* `exists_mem_basicOpen_gradedSectionsGradedHom_of_epi_one`: over an affine open over which `A` is
  generated in degree one, the standard opens of the images of the degree-one sections of `B`
  cover the chart `Proj (⨁ n, Γ(Aₙ, U))`.
* `isClosedImmersion_relativeProjMap_of_epi_one`: if `A` is generated in degree one,
  `Proj_X(A) ⟶ Proj_X(B)` is a closed immersion.

## References

* [The Stacks Project, Lemma 27.11.3 (01N0)](https://stacks.math.columbia.edu/tag/01N0)
* [The Stacks Project, Lemma 27.11.5 (01N1)](https://stacks.math.columbia.edu/tag/01N1)
-/

public section

open CategoryTheory DirectSum

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

open _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {A B : GradedQuasicoherentAlgebra X} (φ : B ⟶ A)
  [Epi (φ.hom.hom.hom 1)]

/-- **The standard opens of the images of the degree-one sections cover the charts.** Over an
affine open `U` over which `A` is generated in degree one, if `φ : B ⟶ A` is an epimorphism in
degree one, every point of `Proj (⨁ n, Γ(Aₙ, U))` lies in `D₊(a)` for the image `a` under `φ` of a
section of `B` of degree one. -/
theorem exists_mem_basicOpen_gradedSectionsGradedHom_of_epi_one (U : X.Opens)
    (hU : IsAffineOpen U)
    (h : Algebra.adjoin Γ(X, U) ((A.obj.gradedSectionsGrading U 0 : Set (⨁ n, Γ(A.obj.X n, U))) ∪
      A.obj.gradedSectionsGrading U 1) = ⊤)
    (y : Proj (A.obj.gradedSectionsGrading U)) :
    ∃ b ∈ B.obj.gradedSectionsGrading U 1,
      y ∈ Proj.basicOpen _ (CommMon.gradedSectionsGradedHom φ.hom U b) := by
  obtain ⟨⟨_, ha⟩, hya⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((Proj.iSup_basicOpen_eq_top_of_adjoin_eq_top _
      ((GradedAlgebra.adjoin_grade_zero_union_grade_one_eq_top_iff _).mp h)).ge
        (Set.mem_univ y))
  obtain ⟨a, rfl⟩ := DirectSum.mem_summand.mp ha
  -- The instances are passed explicitly, since `B.obj.X` and `B.obj.toMon.X` are only unfolded
  -- to each other by elaboration.
  obtain ⟨z, rfl⟩ := @Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen _ (B.obj.X 1)
    (A.obj.X 1) (φ.hom.hom.hom 1) ‹_› _ _ U hU a
  refine ⟨DirectSum.of _ 1 z, CommMon.of_mem_gradedSectionsGrading _ 1 z, ?_⟩
  rwa [CommMon.gradedSectionsGradedHom_apply, CommMon.gradedSectionsMap_of]

/-- **The relative `Proj` of an algebra generated in degree one is a closed subscheme.** If `A` is
generated in degree one and `φ : B ⟶ A` is an epimorphism `B₁ ⟶ A₁` in degree one, then the
morphism `Proj_X(A) ⟶ Proj_X(B)` over `X` induced by `φ` is a closed immersion. For the morphism
`Sym A₁ ⟶ A` extending the identity of `A₁`, this embeds `Proj_X(A)` in `Proj_X(Sym A₁)`. -/
@[stacks 01N1]
theorem isClosedImmersion_relativeProjMap_of_epi_one (hA : A.IsGeneratedInDegreeOne) :
    IsClosedImmersion (CommMon.relativeProjMap φ.hom
      fun U hU ↦ HomogeneousIdeal.irrelevant_le_map_of_grade_subset_range _
        (grade_subset_range_gradedSectionsGradedHom_of_epi_one φ U hU
          (hA.adjoin_grade_zero_union_grade_one_eq_top U hU))) :=
  CommMon.isClosedImmersion_relativeProjMap _ fun U hU ↦
    grade_subset_range_gradedSectionsGradedHom_of_epi_one φ U hU
      (hA.adjoin_grade_zero_union_grade_one_eq_top U hU)

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra
